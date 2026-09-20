#!/usr/bin/env python3
"""Spec-driven controller for bounded, review-heavy repository loops.

This tool deliberately keeps the control plane small and explicit.  It validates
an immutable batch specification, performs a read-only preflight, records
independent reviews for frozen code chunks, and exposes remote mutations only
when the specification enables the corresponding action.

The controller is not a substitute for mathematical or repository review.  It
is the ledger and safety boundary that makes those reviews auditable and keeps
an unattended run from silently widening its scope.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

try:
    import yaml
except ImportError as exc:  # pragma: no cover - repository CI installs PyYAML
    raise SystemExit(f"PyYAML is required to run loop_engine.py: {exc}") from exc


try:
    from _output import force_utf8_output
except ImportError:  # pragma: no cover - direct invocation from another cwd
    def force_utf8_output() -> None:
        """Best-effort UTF-8 output fallback for standalone invocation."""


RUN_SCHEMA = "derived-alg-geo-lean.loop-run/v1"
MAX_ALLOWED_ROUNDS = 5
REQUIRED_ADVERSARIES = {
    "mathematics-adversary",
    "repository-boundary-adversary",
    "abstraction-adversary",
}
ACTION_TO_MUTATION = {
    "comment": "comment_issue",
    "close": "close_issue",
    "push": "push_branch",
    "create-pr": "create_pr",
    "approve": "approve_pr",
    "merge": "merge_pr",
}
ISSUE_ID_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
BRANCH_RE = re.compile(r"^agent/[a-z0-9][a-z0-9._/-]*$")
CLOSING_KEYWORD_RE = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s+#(\d+)\b", re.I)
# Common non-closing issue-link phrases accepted for progress PRs.
NON_CLOSING_REFERENCE_RE = re.compile(
    r"\b(?:ref(?:s)?|references?|related\s+to|part\s+of|progress\s+on|see)\s+#(\d+)\b",
    re.I,
)
SUCCESS_CONCLUSIONS = {"SUCCESS", "success", "PASSED", "passed"}
MERGE_METHODS = {"merge", "squash", "rebase"}
CHUNK_CLOSURES = {"complete", "progress"}
DEFAULT_MERGE_POLICY = {
    "method": "squash",
    "delete_branch": False,
    "allow_method_override": False,
    "allow_delete_branch_override": False,
    "allow_auto": False,
    "allow_admin": False,
}


class LoopError(RuntimeError):
    """A user-actionable validation, ledger, or preflight error."""


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def openspec_change_dir(root: Path, spec: dict[str, Any]) -> Path:
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    change = require_string(openspec, "change", "spec.openspec")
    return ensure_inside(root, root / "openspec" / "changes" / change)


def openspec_digest(root: Path, spec: dict[str, Any]) -> str:
    """Hash the committed OpenSpec planning artifacts referenced by a run."""

    change_dir = openspec_change_dir(root, spec)
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    parts: list[dict[str, str]] = []
    for relative in openspec["required_artifacts"]:
        path = ensure_inside(root, change_dir / relative)
        parts.append({"path": relative, "content": path.read_text(encoding="utf-8")})
    return digest(parts)


def validate_openspec_artifacts(root: Path, spec: dict[str, Any]) -> None:
    """Check the OpenSpec change shape without requiring a global Node install.

    The OpenSpec CLI remains the authoritative richer validator when available;
    this portable structural check keeps repository gates usable on Lean-only
    runners that do not install npm tooling.
    """

    openspec_root = ensure_inside(root, root / "openspec")
    if not (openspec_root / "config.yaml").is_file():
        raise LoopError("openspec/config.yaml is missing; initialize OpenSpec before enabling a run")
    change_dir = openspec_change_dir(root, spec)
    if not change_dir.is_dir():
        raise LoopError(f"OpenSpec change does not exist: {change_dir.relative_to(root)}")
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    for relative in openspec["required_artifacts"]:
        path = ensure_inside(root, change_dir / relative)
        if not path.is_file():
            raise LoopError(f"OpenSpec artifact is missing: {path.relative_to(root)}")
        if not path.read_text(encoding="utf-8").strip():
            raise LoopError(f"OpenSpec artifact is empty: {path.relative_to(root)}")
    required_text = "\n".join(
        ensure_inside(root, change_dir / relative).read_text(encoding="utf-8")
        for relative in openspec["required_artifacts"]
    )
    if "proposal.md" in openspec["required_artifacts"] and "## Why" not in required_text:
        raise LoopError("OpenSpec proposal must contain a Why section")
    spec_texts = [
        ensure_inside(root, change_dir / relative).read_text(encoding="utf-8")
        for relative in openspec["required_artifacts"]
        if "/specs/" in f"/{relative}" or relative.startswith("specs/")
    ]
    if not any("### Requirement:" in text and "#### Scenario:" in text for text in spec_texts):
        raise LoopError("OpenSpec delta must contain at least one requirement and one scenario")
    requirement_names = {
        match.group(1).strip()
        for text in spec_texts
        for match in re.finditer(r"^### Requirement:\s*(.+?)\s*$", text, re.MULTILINE)
    }
    missing_requirements = {
        requirement
        for issue in spec["issues"]
        for chunk in issue["chunks"]
        for requirement in chunk["requirements"]
        if requirement not in requirement_names
    }
    if missing_requirements:
        raise LoopError(
            "run chunks reference OpenSpec requirements that are absent: "
            + ", ".join(sorted(missing_requirements))
        )
    if "tasks.md" in openspec["required_artifacts"]:
        tasks = ensure_inside(root, change_dir / "tasks.md").read_text(encoding="utf-8")
        if not re.search(r"^- \[[ xX]\] \d+\.\d+\s+.+", tasks, re.MULTILINE):
            raise LoopError("OpenSpec tasks.md must contain numbered checkbox tasks")


def repo_path(root: Path, value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = root / path
    return path.resolve()


def ensure_inside(root: Path, path: Path) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise LoopError(f"path must stay inside repository: {path}") from exc
    return path


def run_command(root: Path, args: list[str], *, check: bool = False) -> subprocess.CompletedProcess[str]:
    command = list(args)
    # PowerShell resolves the npm-generated openspec.ps1 shim, but Python's
    # Windows process launcher needs an executable extension.  The .cmd shim
    # has the same behavior and is available wherever the CLI is installed.
    if sys.platform == "win32" and command and command[0] == "openspec":
        command[0] = "openspec.cmd"
    result = subprocess.run(
        command,
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if check and result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"command failed ({result.returncode}): {' '.join(command)}\n{detail}")
    return result


def git(root: Path, *args: str, check: bool = True) -> str:
    result = run_command(root, ["git", *args], check=check)
    return result.stdout.strip()


def gh_json(root: Path, args: list[str]) -> Any:
    result = run_command(root, ["gh", *args], check=False)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"gh command failed ({result.returncode}): gh {' '.join(args)}\n{detail}")
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise LoopError(f"gh command returned invalid JSON: gh {' '.join(args)}") from exc


def load_spec(path: Path, root: Path | None = None) -> dict[str, Any]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise LoopError(f"specification does not exist: {path}") from exc
    except OSError as exc:
        raise LoopError(f"could not read specification {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise LoopError("specification root must be a YAML mapping")
    validate_spec(data)
    if root is not None:
        validate_openspec_artifacts(root, data)
    return data


def require_mapping(value: Any, name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise LoopError(f"{name} must be a mapping")
    return value


def require_string(mapping: dict[str, Any], key: str, name: str) -> str:
    value = mapping.get(key)
    if not isinstance(value, str) or not value.strip():
        raise LoopError(f"{name}.{key} must be a non-empty string")
    return value.strip()


def require_bool(mapping: dict[str, Any], key: str, name: str) -> bool:
    value = mapping.get(key)
    if not isinstance(value, bool):
        raise LoopError(f"{name}.{key} must be a boolean")
    return value


def merge_policy(spec: dict[str, Any]) -> dict[str, Any]:
    """Return the explicit merge policy, retaining safe v1 defaults."""

    configured = spec.get("merge", {})
    if not isinstance(configured, dict):
        raise LoopError("spec.merge must be a mapping")
    policy = {**DEFAULT_MERGE_POLICY, **configured}
    if policy["method"] not in MERGE_METHODS:
        raise LoopError("spec.merge.method must be merge, squash, or rebase")
    for key in (
        "delete_branch",
        "allow_method_override",
        "allow_delete_branch_override",
        "allow_auto",
        "allow_admin",
    ):
        if not isinstance(policy[key], bool):
            raise LoopError(f"spec.merge.{key} must be a boolean")
    return policy


def validate_spec(spec: dict[str, Any]) -> None:
    """Validate the stable, intentionally small v1 specification schema."""

    if spec.get("schema") != RUN_SCHEMA:
        raise LoopError(f"schema must be {RUN_SCHEMA!r}")
    require_string(spec, "id", "spec")
    require_string(spec, "repository", "spec")
    require_string(spec, "remote", "spec")
    require_string(spec, "actor", "spec")
    base_branch = require_string(spec, "base_branch", "spec")
    base_ref = require_string(spec, "base_ref", "spec")
    if base_branch in {"main", "master"} and not base_ref:
        raise LoopError("spec.base_ref is required for the protected base branch")
    mode = spec.get("mode")
    if mode not in {"stack", "independent"}:
        raise LoopError("spec.mode must be 'stack' or 'independent'")
    require_bool(spec, "enabled", "spec")

    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    change = require_string(openspec, "change", "spec.openspec")
    if not ISSUE_ID_RE.fullmatch(change):
        raise LoopError("spec.openspec.change must use lowercase kebab-case")
    artifacts = openspec.get("required_artifacts")
    if not isinstance(artifacts, list) or not artifacts or any(
        not isinstance(artifact, str)
        or not artifact.strip()
        or Path(artifact).is_absolute()
        or ".." in Path(artifact).parts
        for artifact in artifacts
    ):
        raise LoopError("spec.openspec.required_artifacts must be non-empty safe relative paths")
    if "proposal.md" not in artifacts or "design.md" not in artifacts or "tasks.md" not in artifacts:
        raise LoopError("OpenSpec run references must include proposal.md, design.md, and tasks.md")
    if not any(artifact.startswith("specs/") and artifact.endswith(".md") for artifact in artifacts):
        raise LoopError("OpenSpec run references must include a delta under specs/")
    validation_mode = openspec.get("validation", "structural")
    if validation_mode not in {"structural", "cli-advisory", "cli-required"}:
        raise LoopError("spec.openspec.validation must be structural, cli-advisory, or cli-required")

    limits = require_mapping(spec.get("limits"), "spec.limits")
    min_issues = limits.get("min_issues", 2)
    max_issues = limits.get("max_issues", 3)
    max_rounds = limits.get("max_review_rounds_per_chunk", 3)
    for value, name in (
        (min_issues, "limits.min_issues"),
        (max_issues, "limits.max_issues"),
        (max_rounds, "limits.max_review_rounds_per_chunk"),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 1:
            raise LoopError(f"{name} must be a positive integer")
    if max_issues > 3:
        raise LoopError("limits.max_issues cannot exceed 3 for an unattended pilot")
    if max_rounds > MAX_ALLOWED_ROUNDS:
        raise LoopError(
            f"limits.max_review_rounds_per_chunk cannot exceed {MAX_ALLOWED_ROUNDS}"
        )
    if min_issues > max_issues:
        raise LoopError("limits.min_issues cannot exceed limits.max_issues")

    issues = spec.get("issues")
    if not isinstance(issues, list):
        raise LoopError("spec.issues must be a list")
    if not min_issues <= len(issues) <= max_issues:
        raise LoopError(
            f"spec.issues must contain between {min_issues} and {max_issues} issues; got {len(issues)}"
        )
    numbers: set[int] = set()
    issue_ids: set[str] = set()
    for index, issue in enumerate(issues):
        name = f"spec.issues[{index}]"
        issue = require_mapping(issue, name)
        number = issue.get("number")
        if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
            raise LoopError(f"{name}.number must be a positive integer")
        if number in numbers:
            raise LoopError(f"duplicate issue number: {number}")
        numbers.add(number)
        slug = require_string(issue, "slug", name)
        if not ISSUE_ID_RE.fullmatch(slug):
            raise LoopError(f"{name}.slug must use lowercase kebab-case")
        if slug in issue_ids:
            raise LoopError(f"duplicate issue slug: {slug}")
        issue_ids.add(slug)
        dependencies = issue.get("depends_on", [])
        if not isinstance(dependencies, list) or any(
            not isinstance(dependency, int) or isinstance(dependency, bool) or dependency <= 0
            for dependency in dependencies
        ):
            raise LoopError(f"{name}.depends_on must be a list of positive issue numbers")
        chunks = issue.get("chunks")
        if not isinstance(chunks, list) or not chunks:
            raise LoopError(f"{name}.chunks must contain at least one frozen chunk")
        chunk_ids: set[str] = set()
        for chunk_index, chunk in enumerate(chunks):
            chunk_name = f"{name}.chunks[{chunk_index}]"
            chunk = require_mapping(chunk, chunk_name)
            chunk_id = require_string(chunk, "id", chunk_name)
            if not ISSUE_ID_RE.fullmatch(chunk_id):
                raise LoopError(f"{chunk_name}.id must use lowercase kebab-case")
            if chunk_id in chunk_ids:
                raise LoopError(f"duplicate chunk id {chunk_id} in issue {number}")
            chunk_ids.add(chunk_id)
            require_string(chunk, "scope", chunk_name)
            files = chunk.get("files")
            if not isinstance(files, list) or not files or any(
                not isinstance(file, str) or not file.strip() for file in files
            ):
                raise LoopError(f"{chunk_name}.files must be a non-empty list of paths")
            acceptance = chunk.get("acceptance")
            if not isinstance(acceptance, list) or not acceptance or any(
                not isinstance(item, str) or not item.strip() for item in acceptance
            ):
                raise LoopError(f"{chunk_name}.acceptance must be a non-empty list of statements")
            requirements = chunk.get("requirements")
            if not isinstance(requirements, list) or not requirements or any(
                not isinstance(item, str) or not item.strip() for item in requirements
            ):
                raise LoopError(f"{chunk_name}.requirements must name at least one OpenSpec requirement")
            closure = chunk.get("closure", "complete")
            if closure not in CHUNK_CLOSURES:
                raise LoopError(f"{chunk_name}.closure must be 'complete' or 'progress'")

    eligibility = spec.get("eligibility", {})
    if not isinstance(eligibility, dict):
        raise LoopError("spec.eligibility must be a mapping")
    allow_epic_issues = eligibility.get("allow_epic_issues", [])
    if not isinstance(allow_epic_issues, list) or any(
        not isinstance(number, int) or isinstance(number, bool) or number <= 0
        for number in allow_epic_issues
    ):
        raise LoopError("spec.eligibility.allow_epic_issues must be a list of positive issue numbers")
    if len(set(allow_epic_issues)) != len(allow_epic_issues):
        raise LoopError("spec.eligibility.allow_epic_issues must not contain duplicates")
    unselected_epic_opt_ins = set(allow_epic_issues) - numbers
    if unselected_epic_opt_ins:
        raise LoopError(
            "spec.eligibility.allow_epic_issues must be a subset of selected issues: "
            + ", ".join(str(number) for number in sorted(unselected_epic_opt_ins))
        )

    reviewer_spec = require_mapping(spec.get("review"), "spec.review")
    reviewers = reviewer_spec.get("reviewers")
    if not isinstance(reviewers, list) or not reviewers or any(
        not isinstance(reviewer, str) or not reviewer.strip() for reviewer in reviewers
    ):
        raise LoopError("spec.review.reviewers must be a non-empty list of names")
    reviewer_set = set(reviewers)
    missing = REQUIRED_ADVERSARIES - reviewer_set
    if missing:
        raise LoopError(f"spec.review.reviewers is missing adversarial roles: {', '.join(sorted(missing))}")
    if len(reviewer_set) != len(reviewers):
        raise LoopError("spec.review.reviewers must not contain duplicate names")
    reviewer_spec.get("independent", True)
    if reviewer_spec.get("independent", True) is not True:
        raise LoopError("spec.review.independent must remain true")

    mutations = require_mapping(spec.get("mutations"), "spec.mutations")
    for action in ACTION_TO_MUTATION.values():
        require_bool(mutations, action, "spec.mutations")
    merge_policy(spec)
    closure = require_mapping(spec.get("closure"), "spec.closure")
    if closure.get("code_issue") != "pr_merge_keyword":
        raise LoopError("spec.closure.code_issue must be 'pr_merge_keyword'")
    require_bool(closure, "allow_non_pr", "spec.closure")
    if "allow_progress_pr" in closure and not isinstance(closure["allow_progress_pr"], bool):
        raise LoopError("spec.closure.allow_progress_pr must be a boolean")
    has_progress_chunk = any(
        chunk.get("closure", "complete") == "progress"
        for issue in issues
        for chunk in issue["chunks"]
    )
    if has_progress_chunk and closure.get("allow_progress_pr") is not True:
        raise LoopError("progress chunks require spec.closure.allow_progress_pr=true")
    runner = require_mapping(spec.get("runner"), "spec.runner")
    checks = runner.get("required_checks")
    if not isinstance(checks, list) or not checks or any(
        not isinstance(check, str) or not check.strip() for check in checks
    ):
        raise LoopError("spec.runner.required_checks must be a non-empty list")
    roadmap = spec.get("roadmap_gate", "required")
    if roadmap not in {"required", "advisory", "disabled"}:
        raise LoopError("spec.roadmap_gate must be required, advisory, or disabled")

    if mode == "independent":
        issue_numbers = {issue["number"] for issue in issues}
        selected_dependencies = {
            dependency
            for issue in issues
            for dependency in issue.get("depends_on", [])
            if dependency in issue_numbers
        }
        if selected_dependencies:
            raise LoopError("independent mode cannot contain dependencies between selected issues")


def issue_entry(spec: dict[str, Any], number: int) -> dict[str, Any]:
    for issue in spec["issues"]:
        if issue["number"] == number:
            return issue
    raise LoopError(f"issue #{number} is not included in spec {spec['id']}")


def chunk_entry(spec: dict[str, Any], number: int, chunk_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    issue = issue_entry(spec, number)
    for chunk in issue["chunks"]:
        if chunk["id"] == chunk_id:
            return issue, chunk
    raise LoopError(f"chunk {chunk_id!r} is not included for issue #{number}")


def print_validation(path: Path, root: Path) -> int:
    try:
        spec = load_spec(path, root)
    except LoopError as exc:
        print(f"FAIL spec {path}: {exc}")
        return 1
    print(f"PASS spec {spec['id']} ({path})")
    print(f"  openspec change={spec['openspec']['change']} validation={spec['openspec'].get('validation', 'structural')}")
    print(f"  mode={spec['mode']} enabled={spec['enabled']} issues={len(spec['issues'])}")
    print(f"  reviewers={', '.join(spec['review']['reviewers'])}")
    print(f"  max_review_rounds_per_chunk={spec['limits']['max_review_rounds_per_chunk']}")
    epic_opt_ins = spec.get("eligibility", {}).get("allow_epic_issues", [])
    if epic_opt_ins:
        print(f"  explicitly_authorized_epic_issues={','.join(str(number) for number in epic_opt_ins)}")
    policy = merge_policy(spec)
    print(
        "  merge="
        f"{policy['method']} delete_branch={policy['delete_branch']} "
        f"auto={policy['allow_auto']} admin={policy['allow_admin']}"
    )
    if not spec["enabled"]:
        print("  NOTE pilot is disabled; no remote mutation is authorized")
    return 0


def normalize_remote(url: str) -> str:
    value = url.strip()
    if value.startswith("git@github.com:"):
        value = "github.com/" + value.split(":", 1)[1]
    value = re.sub(r"^https?://", "", value)
    value = re.sub(r"^ssh://git@", "", value)
    value = value.removesuffix(".git").rstrip("/")
    value = re.sub(r"^github\.com/", "", value)
    return value.lower()


def blocked_by_entries(issue: dict[str, Any]) -> list[Any]:
    """Normalize GitHub's blockedBy connection without treating an empty mapping as truthy."""

    blocked_by = issue.get("blockedBy")
    if isinstance(blocked_by, dict):
        nodes = blocked_by.get("nodes")
        if isinstance(nodes, list):
            if nodes:
                return nodes
            total = blocked_by.get("totalCount")
            return [{}] if isinstance(total, int) and total > 0 else []
        total = blocked_by.get("totalCount")
        return [{}] if isinstance(total, int) and total > 0 else []
    if isinstance(blocked_by, list):
        return blocked_by
    return []


def gh_authenticated(root: Path) -> str:
    data = gh_json(root, ["api", "user"])
    login = data.get("login") if isinstance(data, dict) else None
    if not isinstance(login, str) or not login:
        raise LoopError("gh api user did not return an authenticated login")
    return login


def existing_prs(root: Path, repository: str) -> list[dict[str, Any]]:
    data = gh_json(
        root,
        [
            "pr",
            "list",
            "--repo",
            repository,
            "--state",
            "all",
            "--limit",
            "200",
            "--json",
            "number,state,isDraft,headRefName,headRefOid,closingIssuesReferences",
        ],
    )
    if not isinstance(data, list):
        raise LoopError("gh pr list returned an unexpected response")
    return data


def issue_state(root: Path, repository: str, number: int) -> dict[str, Any]:
    data = gh_json(
        root,
        [
            "issue",
            "view",
            str(number),
            "--repo",
            repository,
            "--json",
            "number,state,title,labels,blockedBy",
        ],
    )
    if not isinstance(data, dict):
        raise LoopError(f"gh issue view #{number} returned an unexpected response")
    return data


def roadmap_gate_args(base_ref: str) -> list[str]:
    """Scope roadmap consistency failures to entries authored after base_ref."""

    return [
        "python",
        "scripts/check_roadmap.py",
        "--require-api",
        f"--scope-to-diff={base_ref}",
    ]


def preflight(root: Path, spec_path: Path) -> int:
    try:
        spec = load_spec(spec_path, root)
    except LoopError as exc:
        print(f"FAIL preflight: {exc}")
        return 1
    if not spec["enabled"]:
        print(f"DISABLED preflight: spec {spec['id']} is not enabled; no remote actions run")
        return 2

    failures: list[str] = []
    warnings: list[str] = []
    repository = spec["repository"]
    remote = spec["remote"]
    try:
        status = git(root, "status", "--porcelain", "--untracked-files=all")
        if status:
            failures.append("worktree is dirty; unattended runs require a clean checkout")
        current_branch = git(root, "branch", "--show-current")
        current_head = git(root, "rev-parse", "HEAD")
        base_head = git(root, "rev-parse", "--verify", spec["base_ref"])
        if current_head != base_head:
            failures.append(f"HEAD {current_head} is not exactly {spec['base_ref']} ({base_head})")
        if current_branch in {spec["base_branch"], ""}:
            failures.append("preflight must run from a detached or dedicated agent branch, not the protected base")
        remote_url = normalize_remote(git(root, "remote", "get-url", remote))
        if remote_url != repository.lower():
            failures.append(f"remote {remote!r} points to {remote_url!r}, expected {repository!r}")
    except LoopError as exc:
        failures.append(str(exc))

    try:
        login = gh_authenticated(root)
        print(f"PASS gh authentication: {login}")
        if login != spec["actor"]:
            failures.append(f"authenticated actor {login!r} is not the manifest actor {spec['actor']!r}")
    except LoopError as exc:
        failures.append(str(exc))

    prs: list[dict[str, Any]] = []
    try:
        prs = existing_prs(root, repository)
    except LoopError as exc:
        failures.append(str(exc))

    try:
        protection = gh_json(
            root,
            [
                "api",
                f"repos/{repository}/branches/{spec['base_branch']}/protection/required_status_checks",
            ],
        )
        protected_checks = set(protection.get("contexts") or [])
        protected_checks.update(
            item.get("context")
            for item in protection.get("checks") or []
            if isinstance(item, dict) and isinstance(item.get("context"), str)
        )
        missing_protection = set(spec["runner"]["required_checks"]) - protected_checks
        if missing_protection:
            failures.append(
                "base branch protection is missing required checks: "
                + ", ".join(sorted(missing_protection))
            )
        else:
            print("PASS base branch protection: required checks are configured")
    except LoopError as exc:
        failures.append(f"could not verify base branch protection: {exc}")

    selected_numbers = {issue["number"] for issue in spec["issues"]}
    selected_dependencies = {
        dependency
        for issue in spec["issues"]
        for dependency in issue.get("depends_on", [])
        if dependency in selected_numbers
    }
    if spec["mode"] == "stack" and selected_dependencies and not spec["mutations"]["merge_pr"]:
        failures.append(
            "stack mode includes selected issue dependencies but mutations.merge_pr is false; "
            "enable merge explicitly or use independent issues"
        )

    for issue in spec["issues"]:
        number = issue["number"]
        try:
            live = issue_state(root, repository, number)
        except LoopError as exc:
            failures.append(str(exc))
            continue
        if live.get("state") != "OPEN":
            failures.append(f"issue #{number} is not open (state={live.get('state')})")
        labels = {
            label.get("name", "").lower()
            for label in live.get("labels", [])
            if isinstance(label, dict)
        }
        forbidden = labels & {"blocked", "epic", "research", "type:spike"}
        allow_epic_issues = set(spec.get("eligibility", {}).get("allow_epic_issues", []))
        if "epic" in forbidden and number in allow_epic_issues:
            forbidden.remove("epic")
            print(f"PASS issue #{number}: epic label explicitly authorized by manifest")
        if forbidden:
            failures.append(f"issue #{number} has ineligible labels: {', '.join(sorted(forbidden))}")
        blocked_by = blocked_by_entries(live)
        if blocked_by:
            failures.append(f"issue #{number} has live blocked-by dependencies")
        for dependency in issue.get("depends_on", []):
            if dependency in selected_numbers:
                continue
            try:
                dependency_state = issue_state(root, repository, dependency)
            except LoopError as exc:
                failures.append(str(exc))
                continue
            if dependency_state.get("state") != "CLOSED":
                failures.append(f"issue #{number} depends on open issue #{dependency}")
        expected_branch = f"agent/{issue['slug']}"
        # The preflight is intentionally run on the exact clean head from
        # `base_ref`, and the planned issue branch is the normal place to do
        # that.  Rejecting that branch name made a valid loop state
        # impossible: the controller required a dedicated branch while also
        # rejecting the dedicated branch it had planned.  Existing-PR checks
        # below still fail closed if the branch has already been used.
        for pr in prs:
            if pr.get("headRefName") == expected_branch:
                failures.append(f"a PR already exists for planned branch {expected_branch} (#{pr.get('number')})")
            closing = pr.get("closingIssuesReferences") or []
            if any(reference.get("number") == number for reference in closing if isinstance(reference, dict)):
                if pr.get("state") == "OPEN":
                    failures.append(f"issue #{number} already has open PR #{pr.get('number')}")

    openspec_validation = spec["openspec"].get("validation", "structural")
    if openspec_validation in {"cli-advisory", "cli-required"}:
        cli = run_command(root, ["openspec", "validate", spec["openspec"]["change"], "--strict", "--no-interactive"], check=False)
        if cli.returncode != 0:
            detail = (cli.stdout or cli.stderr).strip().splitlines()
            message = detail[-1] if detail else "OpenSpec CLI validation failed"
            if openspec_validation == "cli-required":
                failures.append(f"OpenSpec CLI validation failed: {message}")
            else:
                warnings.append(f"OpenSpec CLI validation advisory failure: {message}")
        elif cli.stdout.strip():
            print("PASS OpenSpec CLI validation")
    elif openspec_validation == "structural":
        print("PASS OpenSpec structural validation")

    roadmap_gate = spec.get("roadmap_gate", "required")
    if roadmap_gate != "disabled":
        roadmap = run_command(root, roadmap_gate_args(spec["base_ref"]), check=False)
        if roadmap.returncode != 0:
            message = (roadmap.stdout or roadmap.stderr).strip().splitlines()
            detail = message[-1] if message else "roadmap gate failed"
            if roadmap_gate == "required":
                failures.append(f"roadmap gate failed: {detail}")
            else:
                warnings.append(f"roadmap gate advisory failure: {detail}")

    if warnings:
        for warning in warnings:
            print(f"WARN {warning}")
    if failures:
        for failure in failures:
            print(f"FAIL {failure}")
        print(f"PREFLIGHT FAIL ({len(failures)} failure(s))")
        return 1
    print("PREFLIGHT PASS: clean base, authenticated provider, eligible issues, and gates are ready")
    return 0


def state_path(root: Path, spec: dict[str, Any], requested: str | None, chunk_id: str) -> Path:
    directory = repo_path(root, requested or spec.get("state_dir", ".loop-runs"))
    ensure_inside(root, directory)
    return ensure_inside(root, directory / f"{chunk_id}.json")


def require_selected_dependencies_passed(
    root: Path,
    spec: dict[str, Any],
    issue: dict[str, Any],
    requested_state_dir: str | None,
) -> None:
    """Require every selected predecessor chunk to have a passing ledger."""

    selected_numbers = {entry["number"] for entry in spec["issues"]}
    for dependency in issue.get("depends_on", []):
        if dependency not in selected_numbers:
            continue
        dependency_issue = issue_entry(spec, dependency)
        for dependency_chunk in dependency_issue["chunks"]:
            path = state_path(root, spec, requested_state_dir, dependency_chunk["id"])
            if not path.is_file():
                raise LoopError(
                    f"issue #{issue['number']} depends on chunk {dependency_chunk['id']!r}, "
                    "but its review ledger does not exist"
                )
            dependency_state = load_state(path)
            if (
                dependency_state.get("spec_digest") != digest(spec)
                or dependency_state.get("openspec_digest") != openspec_digest(root, spec)
            ):
                raise LoopError(
                    f"issue #{issue['number']} depends on a ledger for {dependency_chunk['id']!r} "
                    "that was created from a different manifest or OpenSpec plan"
                )
            if dependency_state.get("status") != "passed":
                raise LoopError(
                    f"issue #{issue['number']} depends on chunk {dependency_chunk['id']!r}, "
                    f"whose ledger status is {dependency_state.get('status')!r}"
                )
            if dependency_state.get("chunk", {}).get("closure") != "complete":
                raise LoopError(
                    f"issue #{issue['number']} depends on progress chunk {dependency_chunk['id']!r}; "
                    "a progress ledger cannot unlock a downstream issue"
                )
            dependency_live = issue_state(root, spec["repository"], dependency)
            if str(dependency_live.get("state", "")).upper() != "CLOSED":
                raise LoopError(
                    f"issue #{issue['number']} depends on issue #{dependency} remaining open; "
                    "the upstream complete chunk must be merged and closed first"
                )


def load_state(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise LoopError(f"ledger state does not exist: {path}") from exc
    except (OSError, json.JSONDecodeError) as exc:
        raise LoopError(f"could not read ledger state {path}: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != f"{RUN_SCHEMA}/ledger":
        raise LoopError(f"invalid ledger state schema: {path}")
    return data


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def ledger_init(root: Path, spec_path: Path, number: int, chunk_id: str, requested_state_dir: str | None) -> int:
    try:
        spec = load_spec(spec_path, root)
        issue, chunk = chunk_entry(spec, number, chunk_id)
        require_selected_dependencies_passed(root, spec, issue, requested_state_dir)
        path = state_path(root, spec, requested_state_dir, chunk_id)
        if path.exists():
            existing = load_state(path)
            if existing.get("spec_digest") != digest(spec) or existing.get("openspec_digest") != openspec_digest(root, spec):
                raise LoopError(f"ledger already exists with a different spec: {path}")
            print(f"PASS ledger already initialized: {path}")
            return 0
        state = {
            "schema": f"{RUN_SCHEMA}/ledger",
            "spec_id": spec["id"],
            "spec_digest": digest(spec),
            "openspec_change": spec["openspec"]["change"],
            "openspec_digest": openspec_digest(root, spec),
            "issue": {"number": issue["number"], "slug": issue["slug"]},
            "chunk": {
                "id": chunk["id"],
                "scope": chunk["scope"],
                "files": list(chunk["files"]),
                "requirements": list(chunk["requirements"]),
                "acceptance": list(chunk["acceptance"]),
                "closure": chunk.get("closure", "complete"),
            },
            "reviewers": list(spec["review"]["reviewers"]),
            "max_review_rounds": spec["limits"]["max_review_rounds_per_chunk"],
            "no_rechunking": True,
            "status": "initialized",
            "created_at": utc_now(),
            "rounds": [],
        }
        write_json(path, state)
        print(f"PASS ledger initialized: {path}")
        return 0
    except LoopError as exc:
        print(f"FAIL ledger init: {exc}")
        return 1


def latest_round(state: dict[str, Any]) -> dict[str, Any] | None:
    rounds = state.get("rounds", [])
    return rounds[-1] if rounds else None


def ensure_review_round(state: dict[str, Any], commit: str) -> dict[str, Any]:
    current = latest_round(state)
    if current is not None and current.get("adjudication") is None:
        if current.get("commit") != commit:
            raise LoopError(
                f"round {current.get('number')} is still open for commit {current.get('commit')}; "
                "adjudicate it before reviewing a different commit"
            )
        return current
    next_number = (current.get("number", 0) + 1) if current else 1
    if next_number > state["max_review_rounds"]:
        raise LoopError(
            "review round cap reached; no further critique/improve iteration is permitted"
        )
    current = {
        "number": next_number,
        "commit": commit,
        "reviews": [],
        "adjudication": None,
    }
    state["rounds"].append(current)
    state["status"] = "reviewing"
    return current


def ledger_record_review(
    state_file: Path,
    reviewer: str,
    commit: str,
    verdict: str,
    finding: str | None,
) -> int:
    try:
        state = load_state(state_file)
        if state.get("status") in {"passed", "blocked"}:
            raise LoopError(f"ledger is terminal with status {state['status']!r}; no further reviews are allowed")
        if reviewer not in state["reviewers"]:
            raise LoopError(f"reviewer {reviewer!r} is not authorized by this ledger")
        if verdict not in {"pass", "needs_changes", "blocked"}:
            raise LoopError("review verdict must be pass, needs_changes, or blocked")
        if not re.fullmatch(r"[0-9a-fA-F]{7,64}", commit):
            raise LoopError("commit must be a hexadecimal git object id")
        round_state = ensure_review_round(state, commit)
        if any(item.get("reviewer") == reviewer for item in round_state["reviews"]):
            raise LoopError(f"reviewer {reviewer!r} already submitted for round {round_state['number']}")
        round_state["reviews"].append(
            {
                "reviewer": reviewer,
                "verdict": verdict,
                "finding": finding or "",
                "recorded_at": utc_now(),
            }
        )
        write_json(state_file, state)
        print(f"PASS review recorded: {reviewer} round={round_state['number']} commit={commit}")
        return 0
    except LoopError as exc:
        print(f"FAIL ledger record-review: {exc}")
        return 1


def ledger_adjudicate(state_file: Path, verdict: str, note: str | None) -> int:
    try:
        state = load_state(state_file)
        if verdict not in {"pass", "needs_changes", "blocked"}:
            raise LoopError("adjudication must be pass, needs_changes, or blocked")
        current = latest_round(state)
        if current is None:
            raise LoopError("cannot adjudicate before reviews are recorded")
        if current.get("adjudication") is not None:
            raise LoopError(f"round {current['number']} is already adjudicated")
        recorded = {item.get("reviewer") for item in current["reviews"]}
        missing = set(state["reviewers"]) - recorded
        if missing:
            raise LoopError(f"cannot adjudicate; missing reviewers: {', '.join(sorted(missing))}")
        if verdict == "pass" and any(item.get("verdict") != "pass" for item in current["reviews"]):
            raise LoopError("pass adjudication requires every reviewer verdict to be pass")
        if verdict == "needs_changes" and current["number"] >= state["max_review_rounds"]:
            verdict = "blocked"
            note = (note + " | " if note else "") + "review-round cap reached; stop without another iteration"
        current["adjudication"] = {"verdict": verdict, "note": note or "", "recorded_at": utc_now()}
        state["status"] = {"pass": "passed", "needs_changes": "improve_required", "blocked": "blocked"}[verdict]
        write_json(state_file, state)
        print(f"PASS adjudicated: round={current['number']} verdict={verdict}")
        return 0
    except LoopError as exc:
        print(f"FAIL ledger adjudicate: {exc}")
        return 1


def ledger_show(state_file: Path) -> int:
    try:
        state = load_state(state_file)
    except LoopError as exc:
        print(f"FAIL ledger show: {exc}")
        return 1
    print(json.dumps(state, indent=2, sort_keys=True))
    return 0


def authorize_action(spec: dict[str, Any], action: str) -> None:
    if not spec["enabled"]:
        raise LoopError(f"spec {spec['id']} is disabled; enable it only after preflight review")
    mutation = ACTION_TO_MUTATION[action]
    if spec["mutations"].get(mutation) is not True:
        raise LoopError(f"remote action {action!r} is not enabled by spec.mutations.{mutation}")


def selected_issue_for_action(spec: dict[str, Any], number: int) -> dict[str, Any]:
    return issue_entry(spec, number)


def action_comment(root: Path, spec: dict[str, Any], number: int, body: str, dry_run: bool) -> int:
    authorize_action(spec, "comment")
    selected_issue_for_action(spec, number)
    args = ["gh", "issue", "comment", str(number), "--repo", spec["repository"], "--body", body]
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <body>")
        return 0
    run_command(root, args, check=True)
    print(f"PASS issue comment written: #{number}")
    return 0


def action_close(
    root: Path,
    spec: dict[str, Any],
    number: int,
    merged_pr: int | None,
    comment: str | None,
    dry_run: bool,
) -> int:
    authorize_action(spec, "close")
    selected_issue_for_action(spec, number)
    if merged_pr is None and not spec["closure"]["allow_non_pr"]:
        raise LoopError("code issue closure requires --merged-pr; non-PR closure is disabled")
    if merged_pr is not None:
        pr = gh_json(
            root,
            [
                "pr",
                "view",
                str(merged_pr),
                "--repo",
                spec["repository"],
                "--json",
                "state,mergedAt,closingIssuesReferences",
            ],
        )
        if pr.get("state") != "MERGED" or not pr.get("mergedAt"):
            raise LoopError(f"PR #{merged_pr} is not merged; refusing to close issue #{number}")
        closing = pr.get("closingIssuesReferences") or []
        if not any(reference.get("number") == number for reference in closing if isinstance(reference, dict)):
            raise LoopError(f"PR #{merged_pr} does not close issue #{number}; refusing to close it")
    args = ["gh", "issue", "close", str(number), "--repo", spec["repository"]]
    if comment:
        args.extend(["--comment", comment])
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS issue closed: #{number}")
    return 0


def planned_branches(spec: dict[str, Any]) -> set[str]:
    return {f"agent/{issue['slug']}" for issue in spec["issues"]}


def action_push(root: Path, spec: dict[str, Any], branch: str | None, force_with_lease: bool, dry_run: bool) -> int:
    authorize_action(spec, "push")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise LoopError("refusing to push a dirty worktree; commit the frozen chunk first")
    current = git(root, "branch", "--show-current")
    requested = branch or current
    if requested != current:
        raise LoopError(f"--branch {requested!r} does not match current branch {current!r}")
    if not BRANCH_RE.fullmatch(current) or current not in planned_branches(spec):
        raise LoopError(f"push branch must be one of the spec's dedicated agent branches; got {current!r}")
    if force_with_lease and not spec.get("allow_force_push", False):
        raise LoopError("force-with-lease is disabled by the specification")
    args = ["git", "push"]
    if force_with_lease:
        args.append("--force-with-lease")
    args.extend([spec["remote"], current])
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS branch pushed: {current}")
    return 0


def read_body_file(root: Path, value: str) -> str:
    path = ensure_inside(root, repo_path(root, value))
    try:
        body = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise LoopError(f"could not read PR body file {path}: {exc}") from exc
    if not body.strip():
        raise LoopError("PR body must not be empty")
    return body


def normalize_scoped_path(value: str) -> str:
    """Normalize a repository-relative path without erasing dot directories."""

    normalized = value.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized.rstrip("/")


def path_is_in_frozen_chunk(path: str, allowed_prefixes: Iterable[str]) -> bool:
    normalized = normalize_scoped_path(path)
    return any(
        normalized == normalize_scoped_path(prefix)
        or normalized.startswith(normalize_scoped_path(prefix) + "/")
        for prefix in allowed_prefixes
    )


def validate_pr_body_closure(body: str, number: int, chunk_closure: str) -> None:
    """Enforce complete-vs-progress issue-link semantics before PR creation."""

    closing_numbers = {int(match.group(1)) for match in CLOSING_KEYWORD_RE.finditer(body)}
    extra_closures = closing_numbers - {number}
    if extra_closures:
        raise LoopError(
            "PR body closes issues outside the current frozen chunk: "
            + ", ".join(f"#{issue}" for issue in sorted(extra_closures))
        )
    if chunk_closure == "complete":
        if number not in closing_numbers:
            raise LoopError(f"complete PR body must contain a closing keyword for issue #{number}")
        return
    if chunk_closure != "progress":
        raise LoopError(f"unsupported chunk closure mode: {chunk_closure!r}")
    if closing_numbers:
        raise LoopError("progress PR body must not contain a closing keyword; use 'Refs #N' or similar")
    references = {int(match.group(1)) for match in NON_CLOSING_REFERENCE_RE.finditer(body)}
    if number not in references:
        raise LoopError(f"progress PR body must contain a non-closing reference to issue #{number}")


def reviewed_commit_matches_head(root: Path, reviewed_commit: str, head_oid: str) -> bool:
    """Resolve a short/full ledger revision, then compare full SHAs exactly."""

    if not re.fullmatch(r"[0-9a-fA-F]{7,40}", reviewed_commit):
        return False
    if not re.fullmatch(r"[0-9a-fA-F]{40}", head_oid):
        return False
    resolved = git(
        root,
        "rev-parse",
        "--verify",
        "--end-of-options",
        f"{reviewed_commit}^{{commit}}",
        check=False,
    )
    return resolved.lower() == head_oid.lower()


def verify_local_chunk_files(root: Path, spec: dict[str, Any], state: dict[str, Any]) -> None:
    base_ref = spec["base_ref"]
    result = run_command(root, ["git", "diff", "--name-only", f"{base_ref}...HEAD"], check=False)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"could not inspect the frozen chunk diff: {detail}")
    changed = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if not changed:
        raise LoopError("frozen chunk has no committed file changes relative to the protected base")
    allowed = state["chunk"]["files"]
    outside = [path for path in changed if not path_is_in_frozen_chunk(path, allowed)]
    if outside:
        raise LoopError("chunk diff contains files outside the frozen list: " + ", ".join(outside))


def verify_remote_chunk_files(pr: dict[str, Any], state: dict[str, Any]) -> None:
    files = pr.get("files") or []
    paths = [file.get("path") for file in files if isinstance(file, dict) and isinstance(file.get("path"), str)]
    if not paths:
        raise LoopError("PR has no readable changed-file list; refusing to approve an unbound chunk")
    outside = [path for path in paths if not path_is_in_frozen_chunk(path, state["chunk"]["files"])]
    if outside:
        raise LoopError("PR contains files outside the frozen list: " + ", ".join(outside))


def action_create_pr(
    root: Path,
    spec: dict[str, Any],
    number: int,
    ledger_file: Path,
    title: str,
    body_file: str,
    draft: bool,
    dry_run: bool,
) -> int:
    authorize_action(spec, "create-pr")
    issue = selected_issue_for_action(spec, number)
    current = git(root, "branch", "--show-current")
    expected = f"agent/{issue['slug']}"
    if current != expected:
        raise LoopError(f"current branch {current!r} does not match issue branch {expected!r}")
    state = load_state(ledger_file)
    if state.get("issue", {}).get("number") != number:
        raise LoopError("PR ledger issue does not match the requested issue")
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("PR ledger was created from a different run manifest")
    if state.get("openspec_digest") != openspec_digest(root, spec):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; reinitialize the frozen chunk")
    if state.get("status") == "blocked":
        raise LoopError("cannot create a PR from a blocked chunk ledger")
    verify_local_chunk_files(root, spec, state)
    body = read_body_file(root, body_file)
    chunk_closure = state.get("chunk", {}).get("closure", "complete")
    validate_pr_body_closure(body, number, chunk_closure)
    args = [
        "gh",
        "pr",
        "create",
        "--repo",
        spec["repository"],
        "--base",
        spec["base_branch"],
        "--head",
        current,
        "--title",
        title,
        "--body-file",
        str(ensure_inside(root, repo_path(root, body_file))),
    ]
    if draft:
        args.append("--draft")
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS PR created for issue #{number}")
    return 0


def check_required_checks(root: Path, spec: dict[str, Any], pr_number: int) -> None:
    data = gh_json(
        root,
        ["pr", "view", str(pr_number), "--repo", spec["repository"], "--json", "headRefOid,statusCheckRollup"],
    )
    latest: dict[str, dict[str, Any]] = {}
    for check in data.get("statusCheckRollup") or []:
        if not isinstance(check, dict):
            continue
        name = check.get("name") or check.get("context")
        if not isinstance(name, str):
            continue
        timestamp = str(check.get("completedAt") or check.get("startedAt") or "")
        previous = latest.get(name)
        if previous is None or timestamp >= str(previous.get("_timestamp", "")):
            check = dict(check)
            check["_timestamp"] = timestamp
            latest[name] = check
    missing: list[str] = []
    failed: list[str] = []
    for required in spec["runner"]["required_checks"]:
        check = latest.get(required)
        if check is None:
            missing.append(required)
            continue
        conclusion = check.get("conclusion") or check.get("state") or check.get("status")
        if conclusion not in SUCCESS_CONCLUSIONS:
            failed.append(f"{required}={conclusion}")
    if missing or failed:
        detail = []
        if missing:
            detail.append("missing " + ", ".join(missing))
        if failed:
            detail.append("not successful " + ", ".join(failed))
        raise LoopError("required checks are not green: " + "; ".join(detail))


def action_approve(
    root: Path,
    spec: dict[str, Any],
    pr_number: int,
    ledger_file: Path,
    body: str,
    dry_run: bool,
) -> int:
    authorize_action(spec, "approve")
    state = load_state(ledger_file)
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("ledger was created from a different run manifest")
    if state.get("openspec_digest") != openspec_digest(root, spec):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; reinitialize the frozen chunk")
    if state.get("status") != "passed":
        raise LoopError(f"ledger status is {state.get('status')!r}; approval requires status 'passed'")
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") != "pass":
        raise LoopError("approval requires a passing adjudicated review round")
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "headRefOid,state,isDraft,files",
        ],
    )
    if pr.get("state") != "OPEN" or pr.get("isDraft"):
        raise LoopError("approval requires an open, non-draft PR")
    if not reviewed_commit_matches_head(root, current.get("commit", ""), pr.get("headRefOid", "")):
        raise LoopError("PR head does not match the commit reviewed by the passing ledger")
    verify_remote_chunk_files(pr, state)
    check_required_checks(root, spec, pr_number)
    args = [
        "gh",
        "pr",
        "review",
        str(pr_number),
        "--repo",
        spec["repository"],
        "--approve",
        "--body",
        body,
    ]
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <body>")
        return 0
    run_command(root, args, check=True)
    print(f"PASS PR approved: #{pr_number}")
    return 0


def build_merge_command(
    spec: dict[str, Any],
    pr_number: int,
    head_sha: str,
    method: str | None,
    auto: bool,
    admin: bool,
    delete_branch: bool | None,
) -> list[str]:
    """Build a race-resistant merge command from an explicitly authorized policy."""

    policy = merge_policy(spec)
    selected_method = method or policy["method"]
    if selected_method not in MERGE_METHODS:
        raise LoopError("merge method must be merge, squash, or rebase")
    if method is not None and method != policy["method"] and not policy["allow_method_override"]:
        raise LoopError("merge method override is disabled by spec.merge.allow_method_override")
    if auto and not policy["allow_auto"]:
        raise LoopError("auto-merge is disabled by spec.merge.allow_auto")
    if admin and not policy["allow_admin"]:
        raise LoopError("admin merge is disabled by spec.merge.allow_admin")
    if auto and admin:
        raise LoopError("--auto and --admin are mutually exclusive")
    selected_delete_branch = policy["delete_branch"]
    if delete_branch is not None:
        if not policy["allow_delete_branch_override"]:
            raise LoopError(
                "branch-deletion override is disabled by "
                "spec.merge.allow_delete_branch_override"
            )
        selected_delete_branch = delete_branch

    args = [
        "gh",
        "pr",
        "merge",
        str(pr_number),
        "--repo",
        spec["repository"],
        f"--{selected_method}",
        "--match-head-commit",
        head_sha,
        "--delete-branch" if selected_delete_branch else "--delete-branch=false",
    ]
    if auto:
        args.append("--auto")
    if admin:
        args.append("--admin")
    return args


def action_merge(
    root: Path,
    spec: dict[str, Any],
    pr_number: int,
    ledger_file: Path,
    method: str | None,
    auto: bool,
    admin: bool,
    delete_branch: bool | None,
    dry_run: bool,
) -> int:
    authorize_action(spec, "merge")
    merge_policy(spec)
    state = load_state(ledger_file)
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("merge ledger was created from a different run manifest")
    if state.get("openspec_digest") != openspec_digest(root, spec):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; refusing to merge")
    if state.get("status") != "passed":
        raise LoopError("merge requires a passing review ledger")
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") != "pass":
        raise LoopError("merge requires a passing adjudicated review round")
    args = build_merge_command(
        spec,
        pr_number,
        current["commit"],
        method,
        auto,
        admin,
        delete_branch,
    )
    if not admin:
        check_required_checks(root, spec, pr_number)
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "state,isDraft,headRefOid,files",
        ],
    )
    if pr.get("state") != "OPEN" or pr.get("isDraft"):
        raise LoopError("merge requires an open, non-draft PR")
    if not reviewed_commit_matches_head(root, current.get("commit", ""), pr.get("headRefOid", "")):
        raise LoopError("PR head does not match the commit reviewed by the passing ledger")
    verify_remote_chunk_files(pr, state)
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    if auto:
        print(f"PASS PR queued for auto-merge: #{pr_number}")
    elif admin:
        print(f"PASS PR admin-merged: #{pr_number}")
    else:
        print(f"PASS PR merged: #{pr_number}")
    return 0


def add_common_spec_parser(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--spec", required=True, type=Path, help="path to the YAML loop specification")
    parser.add_argument("--repo-root", type=Path, default=Path.cwd(), help="repository root")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    validate_parser = sub.add_parser("validate", help="validate a loop specification")
    add_common_spec_parser(validate_parser)

    preflight_parser = sub.add_parser("preflight", help="run read-only repository/provider preflight")
    add_common_spec_parser(preflight_parser)

    ledger_parser = sub.add_parser("ledger", help="create and update the bounded review ledger")
    ledger_sub = ledger_parser.add_subparsers(dest="ledger_command", required=True)
    init_parser = ledger_sub.add_parser("init")
    add_common_spec_parser(init_parser)
    init_parser.add_argument("--issue", required=True, type=int)
    init_parser.add_argument("--chunk-id", required=True)
    init_parser.add_argument("--state-dir")
    record_parser = ledger_sub.add_parser("record-review")
    record_parser.add_argument("--state", required=True, type=Path)
    record_parser.add_argument("--reviewer", required=True)
    record_parser.add_argument("--commit", required=True)
    record_parser.add_argument("--verdict", required=True, choices=["pass", "needs_changes", "blocked"])
    record_parser.add_argument("--finding")
    adjudicate_parser = ledger_sub.add_parser("adjudicate")
    adjudicate_parser.add_argument("--state", required=True, type=Path)
    adjudicate_parser.add_argument("--verdict", required=True, choices=["pass", "needs_changes", "blocked"])
    adjudicate_parser.add_argument("--note")
    show_parser = ledger_sub.add_parser("show")
    show_parser.add_argument("--state", required=True, type=Path)

    action_parser = sub.add_parser("action", help="perform an explicitly authorized remote action")
    action_sub = action_parser.add_subparsers(dest="action_command", required=True)
    comment_parser = action_sub.add_parser("comment")
    add_common_spec_parser(comment_parser)
    comment_parser.add_argument("--issue", required=True, type=int)
    comment_parser.add_argument("--body", required=True)
    comment_parser.add_argument("--dry-run", action="store_true")
    close_parser = action_sub.add_parser("close")
    add_common_spec_parser(close_parser)
    close_parser.add_argument("--issue", required=True, type=int)
    close_parser.add_argument("--merged-pr", type=int)
    close_parser.add_argument("--comment")
    close_parser.add_argument("--dry-run", action="store_true")
    push_parser = action_sub.add_parser("push")
    add_common_spec_parser(push_parser)
    push_parser.add_argument("--branch")
    push_parser.add_argument("--force-with-lease", action="store_true")
    push_parser.add_argument("--dry-run", action="store_true")
    create_parser = action_sub.add_parser("create-pr")
    add_common_spec_parser(create_parser)
    create_parser.add_argument("--issue", required=True, type=int)
    create_parser.add_argument("--ledger", required=True, type=Path)
    create_parser.add_argument("--title", required=True)
    create_parser.add_argument("--body-file", required=True)
    create_parser.add_argument("--draft", action="store_true")
    create_parser.add_argument("--dry-run", action="store_true")
    approve_parser = action_sub.add_parser("approve")
    add_common_spec_parser(approve_parser)
    approve_parser.add_argument("--pr", required=True, type=int)
    approve_parser.add_argument("--ledger", required=True, type=Path)
    approve_parser.add_argument("--body", required=True)
    approve_parser.add_argument("--dry-run", action="store_true")
    merge_parser = action_sub.add_parser("merge")
    add_common_spec_parser(merge_parser)
    merge_parser.add_argument("--pr", required=True, type=int)
    merge_parser.add_argument("--ledger", required=True, type=Path)
    merge_parser.add_argument("--method", choices=sorted(MERGE_METHODS))
    merge_parser.add_argument("--auto", action="store_true", help="request provider auto-merge")
    merge_parser.add_argument("--admin", action="store_true", help="request an explicit administrator merge")
    delete_group = merge_parser.add_mutually_exclusive_group()
    delete_group.add_argument("--delete-branch", dest="delete_branch", action="store_true")
    delete_group.add_argument("--keep-branch", dest="delete_branch", action="store_false")
    merge_parser.set_defaults(delete_branch=None)
    merge_parser.add_argument("--dry-run", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    force_utf8_output()
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "validate":
            root = args.repo_root.resolve()
            return print_validation(repo_path(root, args.spec), root)
        if args.command == "preflight":
            root = args.repo_root.resolve()
            return preflight(root, repo_path(root, args.spec))
        if args.command == "ledger":
            if args.ledger_command == "init":
                root = args.repo_root.resolve()
                return ledger_init(root, repo_path(root, args.spec), args.issue, args.chunk_id, args.state_dir)
            if args.ledger_command == "record-review":
                return ledger_record_review(args.state.resolve(), args.reviewer, args.commit, args.verdict, args.finding)
            if args.ledger_command == "adjudicate":
                return ledger_adjudicate(args.state.resolve(), args.verdict, args.note)
            if args.ledger_command == "show":
                return ledger_show(args.state.resolve())
        if args.command == "action":
            root = args.repo_root.resolve()
            spec = load_spec(repo_path(root, args.spec), root)
            if args.action_command == "comment":
                return action_comment(root, spec, args.issue, args.body, args.dry_run)
            if args.action_command == "close":
                return action_close(root, spec, args.issue, args.merged_pr, args.comment, args.dry_run)
            if args.action_command == "push":
                return action_push(root, spec, args.branch, args.force_with_lease, args.dry_run)
            if args.action_command == "create-pr":
                return action_create_pr(
                    root,
                    spec,
                    args.issue,
                    args.ledger.resolve(),
                    args.title,
                    args.body_file,
                    args.draft,
                    args.dry_run,
                )
            if args.action_command == "approve":
                return action_approve(root, spec, args.pr, args.ledger.resolve(), args.body, args.dry_run)
            if args.action_command == "merge":
                return action_merge(
                    root,
                    spec,
                    args.pr,
                    args.ledger.resolve(),
                    args.method,
                    args.auto,
                    args.admin,
                    args.delete_branch,
                    args.dry_run,
                )
    except LoopError as exc:
        print(f"FAIL {exc}")
        return 1
    except (OSError, ValueError, TypeError) as exc:
        print(f"FAIL unexpected local controller error: {exc}")
        return 1
    parser.error("unhandled command")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
