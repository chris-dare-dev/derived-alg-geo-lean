"""Pure, bounded recovery transitions for the loop controller.

The CLI owns persistence, locks, provenance and provider authority. This module
never dispatches a worker or treats a research review as permission to publish.
"""

from __future__ import annotations

import copy
import hashlib
import json
import math
import re
import time
from typing import Any


class RecoveryError(ValueError):
    """Invalid recovery evidence or transition."""


PASSING = {"pass", "pass_with_lift"}
VERDICTS = PASSING | {"needs_changes", "blocked"}
CONTRACT_KEYS = (
    "schema", "spec_id", "spec_digest", "openspec_change", "openspec_digest",
    "predecessor_prs", "issue", "chunk", "reviewers", "max_review_rounds",
    "no_rechunking",
)
DEFAULTS = {
    "max_episodes": 2,
    "max_total_rounds": 9,
    "max_plan_submissions": 2,
    "max_elapsed_seconds": 604800,
}


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     allow_nan=False).encode()).hexdigest()


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RecoveryError(message)


def _text(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _clock(now: float | None) -> float:
    value = time.time() if now is None else now
    _require(isinstance(value, (float, int)) and not isinstance(value, bool)
             and math.isfinite(value), "invalid current time")
    return float(value)


def validate_policy(raw: dict[str, Any]) -> dict[str, Any]:
    _require(isinstance(raw, dict), "recovery policy must be an object")
    allowed = set(DEFAULTS) | {"objective_id", "implementer", "history"}
    _require(not (set(raw) - allowed), "unknown recovery policy fields")
    policy = {**DEFAULTS, "history": [], **copy.deepcopy(raw)}
    for key in ("objective_id", "implementer"):
        _require(_text(policy.get(key)), f"recovery policy requires {key}")
    for key in DEFAULTS:
        _require(type(policy[key]) is int and policy[key] > 0,
                 f"{key} must be a positive integer")
    _require(isinstance(policy["history"], list), "history must be a list")
    seen = set()
    for entry in policy["history"]:
        _require(isinstance(entry, dict) and set(entry) == {"path", "sha256"},
                 "history entries require exactly path and sha256")
        _require(_text(entry["path"]) and isinstance(entry["sha256"], str)
                 and re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]) is not None,
                 "invalid history path or digest")
        _require(entry["path"] not in seen, "duplicate history path")
        seen.add(entry["path"])
    return policy


def _contract(state: dict[str, Any]) -> dict[str, Any]:
    return {key: copy.deepcopy(state[key]) for key in CONTRACT_KEYS if key in state}


def _snapshot(state: dict[str, Any]) -> dict[str, Any]:
    return copy.deepcopy({key: value for key, value in state.items() if key != "recovery"})


def _sealed(snapshot: dict[str, Any]) -> dict[str, Any]:
    return {"snapshot": copy.deepcopy(snapshot), "digest": digest(snapshot)}


def _rounds(snapshot: dict[str, Any], *, historical: bool = False) -> None:
    rounds = snapshot.get("rounds")
    reviewers = snapshot.get("reviewers")
    _require(isinstance(rounds, list), "ledger rounds must be a list")
    _require(isinstance(reviewers, list) and bool(reviewers)
             and all(_text(role) for role in reviewers)
             and len(set(reviewers)) == len(reviewers), "invalid reviewer panel")
    if not historical:
        _require(len(rounds) <= 3, "attempt exceeded three review rounds")
    for index, row in enumerate(rounds, 1):
        _require(isinstance(row, dict) and row.get("number") == index,
                 "review rounds must be numbered consecutively")
        commit = row.get("commit")
        pattern = r"[0-9a-fA-F]{7,64}" if historical else r"[0-9a-f]{40}"
        _require(isinstance(commit, str) and re.fullmatch(pattern, commit) is not None,
                 "review commit must be a full 40-character SHA")
        reviews = row.get("reviews")
        _require(isinstance(reviews, list), "reviews must be a list")
        seen = set()
        for review in reviews:
            _require(isinstance(review, dict), "invalid review")
            role = review.get("reviewer")
            _require(role in reviewers and role not in seen, "unknown or duplicate reviewer")
            seen.add(role)
            _require(review.get("verdict") in VERDICTS, "invalid review verdict")
            text = review.get("finding_text")
            _require(_text(text), "review requires verbatim finding_text")
            _require(review.get("finding_digest") == hashlib.sha256(text.encode()).hexdigest(),
                     "review transcript digest mismatch")
            if not historical:
                validate_review(commit, review["verdict"], text)
        adjudication = row.get("adjudication")
        if adjudication is not None:
            _require(isinstance(adjudication, dict)
                     and adjudication.get("verdict") in VERDICTS, "invalid adjudication")
            if adjudication["verdict"] in PASSING:
                _require(seen == set(reviewers)
                         and all(review["verdict"] in PASSING for review in reviews),
                         "passing adjudication requires a complete passing panel")
        if index < len(rounds):
            _require(adjudication is not None and adjudication["verdict"] not in PASSING,
                     "cannot allocate after an open or passing round")


def validate_review(commit: str, verdict: str, text: str) -> None:
    _require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
             "review requires a full lowercase 40-character SHA")
    _require(verdict in VERDICTS and _text(text), "invalid review verdict or text")
    lines = text.rstrip().splitlines()
    expected = [f"Reviewed commit: {commit}", f"Close: {verdict.upper()}"]
    _require(lines[-2:] == expected, "review requires exact final commit and Close lines")
    _require(sum(line.startswith("Close:") for line in lines) == 1
             and sum(line.startswith("Reviewed commit:") for line in lines) == 1,
             "review has contradictory or repeated binding lines")


def _all_snapshots(state: dict[str, Any]) -> list[dict[str, Any]]:
    recovery = state["recovery"]
    return [entry["snapshot"] for entry in recovery["history"] + recovery["attempts"]]


def inherited_findings(state: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Return every negative transcript, including negatives in this attempt."""
    result = {}
    snapshots = _all_snapshots(state) + [state]
    for source, snapshot in enumerate(snapshots):
        for row in snapshot.get("rounds", []):
            for review in row.get("reviews", []):
                if review.get("verdict") in PASSING:
                    continue
                finding = {"reviewer": review["reviewer"], "commit": row["commit"],
                           "verdict": review["verdict"], "text": review["finding_text"]}
                identifier = digest(finding)
                result.setdefault(identifier, {**finding, "source": source})
    return result


def total_rounds(state: dict[str, Any]) -> int:
    return sum(len(item["rounds"]) for item in _all_snapshots(state)) + len(state["rounds"])


def _budget(state: dict[str, Any], now: float | None, *, allocate: bool = False) -> str | None:
    recovery = state["recovery"]
    if _clock(now) >= recovery["started_at"] + recovery["policy"]["max_elapsed_seconds"]:
        return "elapsed execution budget exhausted"
    if allocate and total_rounds(state) >= recovery["policy"]["max_total_rounds"]:
        return "aggregate review round budget exhausted"
    return None


def _park(state: dict[str, Any], reason: str) -> dict[str, Any]:
    state["recovery"]["phase"] = "parked"
    state["recovery"]["park_reason"] = reason
    state["status"] = "blocked"
    return state


def validate(state: dict[str, Any]) -> None:
    _require(isinstance(state, dict) and isinstance(state.get("recovery"), dict),
             "ledger has no recovery envelope")
    recovery = state["recovery"]
    expected = {"version", "policy", "policy_digest", "contract", "contract_digest",
                "started_at", "history", "attempts", "episodes", "phase", "park_reason"}
    _require(set(recovery) == expected and recovery["version"] == 1,
             "unsupported recovery envelope schema")
    policy = validate_policy(recovery["policy"])
    _require(policy == recovery["policy"] and digest(policy) == recovery["policy_digest"],
             "recovery policy changed")
    _require(_contract(state) == recovery["contract"]
             and digest(recovery["contract"]) == recovery["contract_digest"],
             "original acceptance contract changed")
    _require(state.get("max_review_rounds") == 3, "recovery requires three-round attempts")
    _clock(recovery["started_at"])
    _require(recovery["phase"] in {"active", "investigating", "plan_review", "ready", "parked"},
             "invalid recovery phase")
    for kind in ("history", "attempts"):
        _require(isinstance(recovery[kind], list), f"invalid {kind}")
        for sealed in recovery[kind]:
            _require(isinstance(sealed, dict) and set(sealed) == {"snapshot", "digest"}
                     and digest(sealed["snapshot"]) == sealed["digest"],
                     "immutable historical snapshot changed")
            _rounds(sealed["snapshot"], historical=kind == "history")
            if kind == "attempts":
                _require(_contract(sealed["snapshot"]) == recovery["contract"],
                         "archived attempt contract changed")
    _require(len(recovery["history"]) == len(policy["history"]), "historical inventory changed")
    _rounds(state)
    episodes = recovery["episodes"]
    _require(isinstance(episodes, list) and len(episodes) <= policy["max_episodes"],
             "recovery episode budget exceeded")
    _require(len(recovery["attempts"]) <= len(episodes), "attempt has no recovery authorization")
    for index, episode in enumerate(episodes):
        _require(set(episode) == {"reason", "submissions", "resumed"}
                 and _text(episode["reason"]) and type(episode["resumed"]) is bool,
                 "invalid recovery episode")
        submissions = episode["submissions"]
        _require(isinstance(submissions, list)
                 and len(submissions) <= policy["max_plan_submissions"], "plan budget exceeded")
        for submission in submissions:
            _require(set(submission) == {"plan", "digest", "review"}
                     and digest(submission["plan"]) == submission["digest"], "recovery plan changed")
            _plan(state, submission["plan"], exact_findings=False)
            if submission["review"] is not None:
                _review(state, submission, submission["review"])
        if episode["resumed"]:
            _require(submissions and submissions[-1]["review"] is not None
                     and submissions[-1]["review"]["verdict"] == "ready",
                     "successor lacks independent recovery acceptance")
        if index < len(episodes) - 1:
            _require(episode["resumed"], "unfinished previous recovery episode")
    _require(sum(episode["resumed"] for episode in episodes) == len(recovery["attempts"]),
             "archived attempts and admitted successors disagree")
    if recovery["phase"] in {"investigating", "plan_review", "ready"}:
        _require(bool(episodes) and not episodes[-1]["resumed"], "missing active recovery episode")
    if recovery["phase"] == "active" and episodes:
        _require(episodes[-1]["resumed"], "unaccepted episode cannot become active")
    if recovery["phase"] in {"plan_review", "ready"}:
        _require(bool(episodes[-1]["submissions"]), "missing recovery plan")
        review = episodes[-1]["submissions"][-1]["review"]
        _require((recovery["phase"] == "plan_review" and review is None)
                 or (recovery["phase"] == "ready" and review is not None
                     and review["verdict"] == "ready"), "recovery phase contradicts plan review")


def initialize(state: dict[str, Any], policy: dict[str, Any],
               history: list[dict[str, Any]] | None = None, *, now: float | None = None) -> dict[str, Any]:
    _require("recovery" not in state, "recovery already initialized")
    normalized = validate_policy(policy)
    imported = history or []
    _require(len(imported) == len(normalized["history"]), "historical inventory is incomplete")
    _require(state.get("max_review_rounds") == 3, "recovery requires three-round attempts")
    for snapshot in imported:
        _require(isinstance(snapshot, dict) and "recovery" not in snapshot,
                 "import raw legacy ledgers only; nested recovery histories are unsupported")
        _require(snapshot.get("status") == "blocked", "historical ledger must be terminal blocked")
        _rounds(snapshot, historical=True)
    _rounds(state)
    contract = _contract(state)
    state["recovery"] = {
        "version": 1, "policy": normalized, "policy_digest": digest(normalized),
        "contract": contract, "contract_digest": digest(contract), "started_at": _clock(now),
        "history": [_sealed(snapshot) for snapshot in imported], "attempts": [],
        "episodes": [], "phase": "active", "park_reason": "",
    }
    if imported or state.get("status") == "blocked":
        return abandon(state, "historical or terminal failure requires investigation", now=now)
    return state


def reserve_round(state: dict[str, Any], commit: str, *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    _require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
             "review requires a full lowercase 40-character SHA")
    _require(state["recovery"]["phase"] == "active", "recovery must finish before code review")
    current = state["rounds"][-1] if state["rounds"] else None
    if current and current["adjudication"] is None:
        _require(current["commit"] == commit, "previous review round is still open")
        if reason := _budget(state, now):
            return _park(state, reason)
        return state
    _require(not current or current["adjudication"]["verdict"] not in PASSING,
             "passing attempt is terminal")
    if reason := _budget(state, now, allocate=True):
        return _park(state, reason)
    _require(len(state["rounds"]) < 3, "attempt exhausted; investigation is required")
    state["rounds"].append({"number": len(state["rounds"]) + 1, "commit": commit,
                            "reviews": [], "adjudication": None})
    state["status"] = "reviewing"
    return state


def abandon(state: dict[str, Any], reason: str, *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    _require(_text(reason), "investigation requires an explicit reason")
    _require(state["recovery"]["phase"] == "active", "recovery episode already active")
    current = state["rounds"][-1] if state["rounds"] else None
    _require(not current or not current["adjudication"]
             or current["adjudication"]["verdict"] not in PASSING, "cannot abandon a passing attempt")
    if exhaustion := _budget(state, now, allocate=True):
        return _park(state, exhaustion)
    recovery = state["recovery"]
    if len(recovery["episodes"]) >= recovery["policy"]["max_episodes"]:
        return _park(state, "recovery episode budget exhausted")
    recovery["episodes"].append({"reason": reason, "submissions": [], "resumed": False})
    recovery["phase"] = "investigating"
    state["status"] = "blocked"
    return state


def after_adjudication(state: dict[str, Any], *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    _require(state["recovery"]["phase"] == "active", "attempt is not active")
    _require(bool(state["rounds"]) and state["rounds"][-1]["adjudication"] is not None,
             "no completed adjudication")
    current = state["rounds"][-1]
    _require({review["reviewer"] for review in current["reviews"]} == set(state["reviewers"]),
             "adjudication requires a complete panel")
    if reason := _budget(state, now):
        return _park(state, reason)
    verdict = current["adjudication"]["verdict"]
    if verdict in PASSING:
        _resolutions(state)
        state["status"] = "passed"
    elif verdict == "blocked" or len(state["rounds"]) >= 3:
        return abandon(state, "adversarial review exhausted the current method", now=now)
    else:
        state["status"] = "improve_required"
    return state


def _plan(state: dict[str, Any], plan: dict[str, Any], *, exact_findings: bool = True) -> None:
    fields = {"author", "cause", "diagnosis", "evidence", "strategy", "checks",
              "finding_ids", "contract_digest"}
    _require(isinstance(plan, dict) and set(plan) == fields, "invalid recovery plan fields")
    for key in ("author", "cause", "diagnosis", "strategy"):
        _require(_text(plan[key]), f"recovery plan requires {key}")
    for key in ("evidence", "checks"):
        _require(isinstance(plan[key], list) and bool(plan[key])
                 and all(_text(value) for value in plan[key]), f"recovery plan requires {key}")
    _require(plan["contract_digest"] == state["recovery"]["contract_digest"],
             "recovery plan changed original acceptance")
    ids = plan["finding_ids"]
    _require(isinstance(ids, list) and all(_text(value) for value in ids)
             and len(set(ids)) == len(ids), "invalid recovery finding inventory")
    if exact_findings:
        _require(set(ids) == set(inherited_findings(state)), "recovery plan must include every inherited finding")


def submit_plan(state: dict[str, Any], plan: dict[str, Any], *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    _require(state["recovery"]["phase"] == "investigating", "not accepting an investigation plan")
    if reason := _budget(state, now, allocate=True):
        return _park(state, reason)
    _plan(state, plan)
    episode = state["recovery"]["episodes"][-1]
    _require(len(episode["submissions"]) < state["recovery"]["policy"]["max_plan_submissions"],
             "plan submission cap reached")
    episode["submissions"].append({"plan": copy.deepcopy(plan), "digest": digest(plan), "review": None})
    state["recovery"]["phase"] = "plan_review"
    return state


def _review(state: dict[str, Any], submission: dict[str, Any], review: dict[str, Any]) -> None:
    _require(isinstance(review, dict)
             and set(review) == {"reviewer", "plan_digest", "verdict", "assessment"},
             "invalid recovery review fields")
    _require(_text(review["reviewer"]) and _text(review["assessment"]), "recovery review lacks assessment or reviewer")
    _require(review["reviewer"].strip().casefold() not in {
        submission["plan"]["author"].strip().casefold(),
        state["recovery"]["policy"]["implementer"].strip().casefold()},
             "recovery reviewer must be independent of plan author and implementer")
    _require(review["plan_digest"] == submission["digest"], "review binds another recovery plan")
    _require(review["verdict"] in {"ready", "needs_changes"}, "invalid recovery review verdict")


def review_plan(state: dict[str, Any], review: dict[str, Any], *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    _require(state["recovery"]["phase"] == "plan_review", "no pending recovery review")
    if reason := _budget(state, now, allocate=True):
        return _park(state, reason)
    episode = state["recovery"]["episodes"][-1]
    submission = episode["submissions"][-1]
    _review(state, submission, review)
    submission["review"] = copy.deepcopy(review)
    if review["verdict"] == "ready":
        state["recovery"]["phase"] = "ready"
    elif len(episode["submissions"]) >= state["recovery"]["policy"]["max_plan_submissions"]:
        return _park(state, "recovery plan submission budget exhausted")
    else:
        state["recovery"]["phase"] = "investigating"
    return state


def resume(state: dict[str, Any], *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    recovery = state["recovery"]
    if recovery["phase"] == "active" and recovery["episodes"] and not state["rounds"]:
        if reason := _budget(state, now, allocate=True):
            return _park(state, reason)
        return state
    _require(state["recovery"]["phase"] == "ready", "independent recovery acceptance is required")
    if reason := _budget(state, now, allocate=True):
        return _park(state, reason)
    _plan(state, recovery["episodes"][-1]["submissions"][-1]["plan"])
    recovery["attempts"].append(_sealed(_snapshot(state)))
    recovery["episodes"][-1]["resumed"] = True
    recovery["phase"] = "active"
    state["rounds"] = []
    state["status"] = "initialized"
    return state


def _resolutions(state: dict[str, Any]) -> None:
    findings = set(inherited_findings(state))
    for review in state["rounds"][-1]["reviews"]:
        resolutions = review.get("resolutions", {})
        _require(isinstance(resolutions, dict) and set(resolutions) == findings
                 and all(_text(value) for value in resolutions.values()),
                 "passing reviews must resolve every inherited finding with evidence")


def require_publishable(state: dict[str, Any], *, now: float | None = None) -> None:
    validate(state)
    _require(state["recovery"]["phase"] == "active" and state.get("status") == "passed",
             "objective is not publishable")
    _require(_budget(state, now) is None, "elapsed execution budget exhausted")
    _require(bool(state["rounds"]), "no reviewed code")
    current = state["rounds"][-1]
    _require(current["adjudication"] is not None
             and current["adjudication"]["verdict"] in PASSING, "no passing code adjudication")
    _resolutions(state)


def next_action(state: dict[str, Any], *, now: float | None = None) -> dict[str, Any]:
    validate(state)
    recovery = state["recovery"]
    remaining = max(0, recovery["started_at"] + recovery["policy"]["max_elapsed_seconds"] - _clock(now))
    result = {"objective_id": recovery["policy"]["objective_id"],
              "total_rounds": total_rounds(state), "remaining_seconds": remaining,
              "contract_digest": recovery["contract_digest"],
              "findings": inherited_findings(state)}
    if recovery["episodes"] and recovery["episodes"][-1]["submissions"]:
        result["plan_digest"] = recovery["episodes"][-1]["submissions"][-1]["digest"]
    phase = recovery["phase"]
    reason = _budget(state, now)
    if phase == "parked" or reason:
        return {**result, "action": "park", "reason": reason or recovery["park_reason"]}
    if phase != "active":
        if reason := _budget(state, now, allocate=True):
            return {**result, "action": "park", "reason": reason}
        action = {"investigating": "investigate", "plan_review": "review_plan", "ready": "resume"}[phase]
        return {**result, "action": action, "finding_ids": sorted(inherited_findings(state))}
    current = state["rounds"][-1] if state["rounds"] else None
    if current and current["adjudication"] is None:
        missing = sorted(set(state["reviewers"]) - {review["reviewer"] for review in current["reviews"]})
        return {**result, "action": "review" if missing else "adjudicate", "reviewers": missing,
                "commit": current["commit"], "round": current["number"]}
    if current and current["adjudication"]["verdict"] in PASSING:
        require_publishable(state, now=now)
        return {**result, "action": "publish", "commit": current["commit"]}
    if reason := _budget(state, now, allocate=True):
        return {**result, "action": "park", "reason": reason}
    return {**result, "action": "revise" if current else "implement"}
