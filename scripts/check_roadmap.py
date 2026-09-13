#!/usr/bin/env python3
"""Assert `.claude/roadmap/*.yaml` still agrees with the GitHub tracker.

Every other `check_*.py` here is offline. This one is not, and that is the
whole difficulty: the roadmap's `gh_issue` / `gh_sub_issues` / `blocked_by`
fields are the only mapping from planning to tracker, and nothing verified them
until this script existed. By then three of eleven epic entries were wrong --
found by hand, not by a gate.

## It reports; it never repairs

The obvious shape is a syncer. That shape is wrong, and #620 records why: when
this file listed #188 under `contract-v1-e9` and GitHub had no parent on #188
at all, the ROADMAP held the correct intent. A syncer treating GitHub as
authoritative would have "fixed" it by deleting #188 -- making the two agree by
discarding the record of where the work belonged.

So every finding names which side is missing what, and the fix is a human
decision about which side was right.

## A check that could not look is not a check that passed

Without `gh`, or without auth, this prints NOT_RUN and says why. It does not
print PASS. `--require-api` turns that into exit 1, and CI passes it: the one
environment guaranteed to have the API must not silently skip. Locally the
default is a degraded report rather than a failure, so a contributor without
`gh` is not blocked from running the other gates.

## Rules

  RM-01  every issue the roadmap references exists on the tracker
  RM-02  an epic's `gh_sub_issues` equals its GitHub children, both ways
  RM-03  a `deliverable`'s GitHub parent is its entry's parent
  RM-04  a `task` is milestone-direct: no GitHub parent, milestone agrees
  RM-05  `blocked_by` mirrors GitHub's blocked-by, on OPEN items
  RM-06  no LIVE issue on a roadmap-owned milestone goes unreferenced
         (live = the issue is open, or its milestone is)
  RM-07  an entry's `status` agrees with its issue being open or closed
  RM-08  a pull request that CLOSES an issue advances that issue's entry
         in the same pull request (pull_request events only)

RM-05 is scoped to open items on purpose. A closed item's blockers are history:
#618 was closed as a decision while still marked blocked by #134 and #178, and
re-litigating that in a build gate would be noise, not signal.

RM-07 is the rule that would have caught the two worst tracker defects this
repository has had, both found by hand:

  * #192 was closed 27 seconds BEFORE its own closing comment said "the review
    keeps this epic open", while the roadmap said `in_progress` throughout.
  * #554 was closed as COMPLETED with 9 of 13 deliverables unchecked -- the
    preservation proofs, the K-flat resolutions, the nonzero example -- while
    the entry added in the very same merge said `status: in_progress`. Leaving
    it closed would have signalled SF8.5 complete to #522, which depends on
    exactly the theorem still missing.

## RM-07 is judged per-branch, and only RM-07

RM-07 is the only rule here that compares a FILE IN THE BRANCH against LIVE
tracker state, so it is the only one an unrelated merge can turn red. On a pull
request CI passes `--scope-to-diff=origin/main`, and RM-07 then fails only on
entries the branch actually changed since it forked; entries it inherited
unchanged are printed as notes and left to `main`. Pushes to `main` and merge
queue entries pass no such flag and judge all of them, so nothing escapes -- it
moves WHERE a finding is reported, never WHETHER.

The other rules are deliberately left unscoped even though RM-01, RM-02, RM-05
and RM-06 read the same live state. They check structure, which changes far
less often than `status` does, and none of them has yet produced the repo-wide
red that RM-07 produced on 2026-09-12. Scope them when they do, not before.

RM-01..RM-06 all check STRUCTURE -- existence, parentage, milestone, blockers,
coverage -- and every one of them passed on both. Nothing compared what the
roadmap says about PROGRESS against what the tracker says about it, so a
closure that contradicted the plan was invisible to the gate that exists to
keep the two in agreement.

Like every other rule here it reports and never repairs: a closed issue whose
entry still reads `in_progress` means either the closure was premature or the
roadmap owes an update, and only a human knows which. Entries with no `status`,
or a status outside the judged vocabulary, are counted in the summary rather
than skipped in silence.

RM-06 is the rule the others cannot express. Every one of RM-02..RM-05 checks
something the roadmap already mentions, so an issue the roadmap has never heard
of is invisible to all of them -- which is exactly how #618 sat outside the file
until `kind: task` was added. It is the `C-12` shape, one layer out.

Usage:  python3 scripts/check_roadmap.py [--require-api] [repo_root]
"""

import json
import pathlib
import subprocess
import sys

from _output import force_utf8_output

REPO = "chris-dare-dev/derived-alg-geo-lean"
LEAF_KINDS = ("deliverable", "task")

#: RM-07's vocabulary. `status` is free text in the YAML, so the rule judges
#: only the values whose meaning for an ISSUE is unambiguous, and reports how
#: many entries it could not judge rather than passing over them quietly.
#:
#: `refuted` is terminal alongside `done`: a dependency the project decided it
#: does not need is finished with, and its issue closing is correct.
RM07_DONE_STATUSES = frozenset({"done", "refuted"})
#: Work remains, so the issue should still be open. `parked` is here rather
#: than with the terminal ones deliberately: paused is not finished, and an
#: issue closed while its entry reads `parked` is exactly the kind of quiet
#: disappearance this rule exists to surface.
RM07_OPEN_STATUSES = frozenset(
    {"planned", "in_progress", "partial", "blocked", "missing", "parked"})

#: RM-06 gaps recorded rather than tolerated silently. THIS LIST MAY ONLY
#: SHRINK: adding to it records a new gap instead of fixing one, and the next
#: reader cannot tell those apart.
#:
#: EMPTY as of 2026-08-19, and it took two steps to get here. It began at 27,
#: of which 26 were closed issues on CLOSED milestones -- finished work that
#: cannot go missing, so RM-06 was scoped to live work (#639) and they stopped
#: being findings rather than being forgiven. That left #554, the one real gap,
#: which had been invisible inside the 27. It now has a roadmap entry
#: (stability-families-e14-5) and a GitHub parent, so it is referenced and the
#: list is empty.
#:
#: An empty list is the intended steady state. A number appearing here again
#: means someone chose to record a gap instead of closing it.
RM06_KNOWN_GAPS: set[int] = set()


def fail(rule, detail):
    print(f"FAIL  {rule}  {detail}")


def not_run(reason, require_api):
    print(f"NOT_RUN  scripts/check_roadmap.py -- {reason}")
    print("NOT_RUN is not a pass: nothing was compared.")
    if require_api:
        print("FAIL  --require-api was passed; the API is mandatory here")
        return 1
    return 0


def load_items(root):
    """Every roadmap entry, with the file it came from."""
    try:
        import yaml
    except ImportError:
        return None, "PyYAML is not importable"
    out = []
    for path in sorted((root / ".claude" / "roadmap").glob("*.yaml")):
        doc = yaml.safe_load(path.read_text(encoding="utf-8"))
        if not isinstance(doc, dict):
            continue
        for item in doc.get("items") or []:
            if isinstance(item, dict) and item.get("id"):
                item["_file"] = path.name
                out.append(item)
    return out, None


def _git(root, *args):
    """Run git in `root`; return stdout, or None if git failed."""
    try:
        proc = subprocess.run(("git", "-C", str(root)) + args,
                              capture_output=True, text=True, timeout=60,
                              encoding="utf-8")
    except (OSError, subprocess.SubprocessError):
        return None
    return proc.stdout if proc.returncode == 0 else None


def load_items_at_rev(root, rev):
    """`load_items`, but reading the roadmap as of a git revision.

    Returns id -> entry, or None if the revision cannot be read. `_file` is
    dropped: a file rename is not a change to what an entry CLAIMS, and
    including it would make every renamed file look PR-authored.
    """
    try:
        import yaml
    except ImportError:
        return None
    listing = _git(root, "ls-tree", "--name-only", f"{rev}:.claude/roadmap")
    if listing is None:
        return None
    out = {}
    for name in listing.split():
        if not name.endswith(".yaml"):
            continue
        blob = _git(root, "show", f"{rev}:.claude/roadmap/{name}")
        if blob is None:
            return None
        doc = yaml.safe_load(blob)
        if not isinstance(doc, dict):
            continue
        for item in doc.get("items") or []:
            if isinstance(item, dict) and item.get("id"):
                out[item["id"]] = item
    return out


def pr_authored_ids(root, items, base_ref):
    """Entry ids this branch CHANGED relative to where it forked from base_ref.

    RM-07 judges the roadmap against LIVE tracker state, so an entry nobody on
    this branch touched can still start failing here: another pull request
    closes the issue, `main` advances the entry, and every branch that forked
    before that carries the old `status` through no fault of its own. At this
    repository's merge cadence that is the normal state of an open pull
    request, not an exceptional one -- on 2026-09-12 it turned 15 of 18 open
    pull requests red at once, none of which had touched the roadmap.

    The merge base is what separates the two. An entry whose YAML is identical
    at HEAD and at the fork point was not authored by this branch, so a
    disagreement there is `main`'s to fix and `main`'s own CI judges it. An
    entry this branch added or edited is still judged in full -- which is the
    shape both defects in this module's docstring had: #192 and #554 were each
    a change whose OWN entry contradicted the tracker.

    Returns None when the base cannot be resolved, and None means DO NOT SCOPE.
    Narrowing is the only thing this function can do, so losing it has to fail
    towards judging everything; a missing ref must never be a way to be judged
    less.
    """
    base = _git(root, "merge-base", "HEAD", base_ref)
    if not base or not base.strip():
        return None
    was = load_items_at_rev(root, base.strip())
    if was is None:
        return None
    authored = set()
    for e in items:
        before = was.get(e["id"])
        now = {k: v for k, v in e.items() if k != "_file"}
        if before is None or {k: v for k, v in before.items() if k != "_file"} != now:
            authored.add(e["id"])
    return authored


def fetch_issues():
    """number -> {state, parent, milestone, blocked_by} for the whole tracker."""
    try:
        proc = subprocess.run(
            ["gh", "issue", "list", "--repo", REPO, "--state", "all",
             "--limit", "1000", "--json",
             "number,state,parent,milestone,blockedBy,title"],
            capture_output=True, text=True, timeout=180, encoding="utf-8")
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    try:
        raw = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return None, f"gh returned unparseable JSON: {exc}"
    return {
        i["number"]: {
            "state": i["state"],
            "title": i["title"],
            "parent": (i.get("parent") or {}).get("number"),
            "milestone": (i.get("milestone") or {}).get("number"),
            "blocked_by": sorted(n["number"]
                                 for n in (i.get("blockedBy") or {}).get("nodes", [])),
        }
        for i in raw
    }, None


def fetch_open_milestones():
    """Milestone numbers whose milestone is still OPEN."""
    try:
        proc = subprocess.run(
            ["gh", "api", f"repos/{REPO}/milestones?state=all&per_page=100",
             "--jq", ".[] | [.number, .state] | @tsv"],
            capture_output=True, text=True, timeout=120, encoding="utf-8")
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh api milestones exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    open_ms = set()
    for line in proc.stdout.splitlines():
        num, _, state = line.partition("\t")
        if state.strip() == "open":
            open_ms.add(int(num))
    return open_ms, None


def fetch_closing_issues(pr):
    """Issue numbers this pull request will close when it merges.

    GitHub resolves the closing keywords in the body and the commits for us and
    exposes the result as `closingIssuesReferences`, so this does not re-parse
    prose and cannot disagree with what the merge will actually do.
    """
    try:
        proc = subprocess.run(
            ["gh", "pr", "view", str(pr), "--repo", REPO,
             "--json", "closingIssuesReferences",
             "--jq", "[.closingIssuesReferences[].number] | @json"],
            capture_output=True, text=True, timeout=120, encoding="utf-8")
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh pr view exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    try:
        return set(json.loads(proc.stdout.strip() or "[]")), None
    except json.JSONDecodeError as exc:
        return None, f"could not decode closingIssuesReferences: {exc}"


def main(argv):
    require_api = "--require-api" in argv
    scope_to = next((a.partition("=")[2] for a in argv
                     if a.startswith("--scope-to-diff=")), None)
    pr_number = next((a.partition("=")[2] for a in argv
                      if a.startswith("--pr=")), None)
    rest = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(rest[0]).resolve() if rest else pathlib.Path(__file__).resolve().parent.parent

    items, problem = load_items(root)
    if items is None:
        return not_run(problem, require_api)
    if not items:
        print("FAIL  RM-00  no roadmap items found; this check would pass vacuously")
        return 1

    live, problem = fetch_issues()
    if live is None:
        return not_run(problem, require_api)
    open_milestones, problem = fetch_open_milestones()
    if open_milestones is None:
        return not_run(problem, require_api)

    by_id = {i["id"]: i for i in items}
    # None = judge every entry (see pr_authored_ids: narrowing fails towards
    # judging everything, so an unresolvable base cannot buy a lighter check).
    authored = pr_authored_ids(root, items, scope_to) if scope_to else None
    if scope_to and authored is None:
        print(f"note: --scope-to-diff={scope_to} could not be resolved; "
              f"RM-07 is judging every entry")
    failures = 0
    referenced = set()
    for e in items:
        if e.get("gh_issue"):
            referenced.add(e["gh_issue"])
        referenced.update(e.get("gh_sub_issues") or [])

    # RM-01 -----------------------------------------------------------------
    for n in sorted(referenced):
        if n not in live:
            owners = sorted(e["id"] for e in items
                            if e.get("gh_issue") == n or n in (e.get("gh_sub_issues") or []))
            fail("RM-01", f"#{n} is referenced by {', '.join(owners)} but does not exist")
            failures += 1

    # RM-02 -----------------------------------------------------------------
    for e in items:
        if e.get("kind") != "epic" or not e.get("gh_issue"):
            continue
        declared = sorted(e.get("gh_sub_issues") or [])
        actual = sorted(n for n, i in live.items() if i["parent"] == e["gh_issue"])
        for n in sorted(set(actual) - set(declared)):
            fail("RM-02", f"{e['id']}: GitHub parents #{n} to #{e['gh_issue']}, "
                          f"roadmap does not list it -- THE ROADMAP IS STALE")
            failures += 1
        for n in sorted(set(declared) - set(actual)):
            fail("RM-02", f"{e['id']}: roadmap lists #{n}, GitHub does not parent it "
                          f"to #{e['gh_issue']} -- THE TRACKER IS STALE")
            failures += 1

    # RM-03 / RM-04 ---------------------------------------------------------
    for e in items:
        kind = e.get("kind")
        if kind not in LEAF_KINDS or not e.get("gh_issue"):
            continue
        gh = live.get(e["gh_issue"])
        if gh is None:
            continue  # already reported by RM-01
        parent_entry = by_id.get(e.get("parent"))
        if parent_entry is None:
            fail("RM-03" if kind == "deliverable" else "RM-04",
                 f"{e['id']}: parent {e.get('parent')!r} is not an entry in this roadmap")
            failures += 1
            continue
        if kind == "deliverable":
            want = parent_entry.get("gh_issue")
            if gh["parent"] != want:
                fail("RM-03", f"{e['id']}: #{e['gh_issue']} has GitHub parent "
                              f"#{gh['parent']}, entry parent {e['parent']} is #{want}")
                failures += 1
        else:
            if gh["parent"] is not None:
                fail("RM-04", f"{e['id']}: #{e['gh_issue']} is a task but GitHub parents "
                              f"it to #{gh['parent']}; a task is milestone-direct")
                failures += 1
            want_ms = parent_entry.get("gh_milestone")
            if gh["milestone"] != want_ms:
                fail("RM-04", f"{e['id']}: #{e['gh_issue']} is on milestone "
                              f"{gh['milestone']}, entry parent {e['parent']} is "
                              f"milestone {want_ms}")
                failures += 1

    # RM-05 -----------------------------------------------------------------
    for e in items:
        n = e.get("gh_issue")
        if not n or n not in live or live[n]["state"] != "OPEN":
            continue
        declared = sorted(e.get("blocked_by") or [])
        actual = live[n]["blocked_by"]
        if declared != actual:
            fail("RM-05", f"{e['id']}: #{n} blocked_by roadmap={declared} "
                          f"github={actual}")
            failures += 1

    # RM-06 -----------------------------------------------------------------
    owned = {e["gh_milestone"] for e in items
             if e.get("kind") == "milestone" and e.get("gh_milestone")}
    #
    # SCOPED TO WHERE THE ROADMAP CAN STILL LOSE SOMETHING: an issue is only a
    # finding when the issue is open, or its milestone is. A closed issue on a
    # closed milestone is finished work that was never itemized -- it cannot go
    # missing, and flagging it drowns the live gaps. #639 measured the
    # difference: 27 findings before, 1 after, and the 1 was invisible inside
    # the 27.
    known_hit = set()
    for n, i in sorted(live.items()):
        if i["milestone"] not in owned or n in referenced:
            continue
        if i["state"] != "OPEN" and i["milestone"] not in open_milestones:
            continue
        if n in RM06_KNOWN_GAPS:
            known_hit.add(n)
            continue
        fail("RM-06", f"#{n} is on milestone {i['milestone']}, which this roadmap "
                      f"owns, but no entry references it -- {i['title'][:56]}")
        failures += 1

    # Stale entries in the allowlist are themselves a finding: a gap that was
    # closed leaves a number behind that makes the backlog look larger than it
    # is, and the list is supposed to burn down visibly.
    for n in sorted(RM06_KNOWN_GAPS - known_hit):
        fail("RM-06", f"#{n} is in RM06_KNOWN_GAPS but is no longer an unreferenced "
                      f"issue on an owned milestone -- remove it from the list")
        failures += 1

    # The set of issues THIS pull request closes is needed by two rules, so it
    # is fetched once, here, above both of them. RM-08 uses it directly; RM-07
    # uses it to avoid punishing the very thing RM-08 demands (see below).
    closing, closing_problem = (None, None)
    if pr_number:
        closing, closing_problem = fetch_closing_issues(pr_number)

    # RM-07 -----------------------------------------------------------------
    judged = unjudged = 0
    inherited = []
    # Every entry the closing-set rewrite below lets through is RECORDED here
    # and printed with the summary. The rewrite is invisible otherwise: the
    # entry simply stops being judged, and an entry passing `done` against an
    # issue that is still OPEN leaves no trace of why. This module has no quiet
    # mode -- RM-07 already prints its inherited findings for the same reason.
    # RM-08 still judges these entries; the note says which ones RM-07 handed
    # over, so the two rules are legible together.
    exempt = []

    def rm07(entry_id, detail):
        """Fail, unless this branch did not author the entry.

        An inherited disagreement is still PRINTED -- this module does not have
        a quiet mode, and a finding nobody can see is the failure state of a
        reporting gate. It just is not this branch's exit code.
        """
        nonlocal failures
        if authored is not None and entry_id not in authored:
            inherited.append(detail)
            return
        fail("RM-07", detail)
        failures += 1

    for e in items:
        n = e.get("gh_issue")
        if not n or n not in live:
            continue  # RM-01 owns a missing issue
        status = e.get("status")
        gh_state = live[n]["state"]
        # An issue this pull request CLOSES is judged as the merge will leave
        # it, not as it stands mid-review. Without this RM-07 and RM-08
        # contradict each other outright: RM-08 demands the entry be advanced
        # in the closing pull request, RM-07 then sees `done` against an issue
        # that is still OPEN (it closes on merge, not before), and no pull
        # request that closes an issue can be green either way. That is a
        # repository-wide block, and it shipped in #1252 -- the rules were
        # written apart and never run against each other.
        closes_here = bool(closing) and n in closing and gh_state == "OPEN"
        if closes_here:
            gh_state = "CLOSED"
        if status in RM07_DONE_STATUSES:
            judged += 1
            if closes_here:
                # RM-08's required end state, not a disagreement: the merge
                # closes #n and this entry already says so.
                exempt.append(f"{e['id']}: status={status}, #{n} closes on merge")
            elif gh_state == "OPEN":
                rm07(e["id"],
                     f"{e['id']}: roadmap says status={status} but #{n} is "
                     f"OPEN -- either the work is not finished (THE ROADMAP "
                     f"IS STALE) or the issue was never closed (THE TRACKER "
                     f"IS STALE) -- {live[n]['title'][:44]}")
        elif status in RM07_OPEN_STATUSES:
            judged += 1
            if gh_state == "CLOSED":
                rm07(e["id"],
                     f"{e['id']}: #{n} is CLOSED but the roadmap says "
                     f"status={status} -- either the closure was premature "
                     f"(REOPEN IT) or the entry owes an update (ADVANCE THE "
                     f"STATUS) -- {live[n]['title'][:44]}")
        else:
            unjudged += 1

    # RM-08 -----------------------------------------------------------------
    #
    # RM-07 cannot see this one coming. It compares the roadmap against LIVE
    # tracker state, and while a pull request is open the issue it will close
    # is still OPEN -- so `status: blocked` agrees with the tracker, the check
    # passes, the merge closes the issue, and `main` goes red one second later.
    # Three times on 2026-09-12 (#1179 and #1184 by #1204, #1182 by #1250), and
    # each occurrence reddens every open pull request until a human notices.
    #
    # The fix has to run where the author still is, so this asks the question
    # RM-07 structurally cannot: does this pull request close an issue whose
    # entry it does not advance? GitHub resolves the closing keywords itself,
    # so the answer matches what the merge will really do.
    #
    # `pull_request` only. There is no pull request to ask about on `main`, and
    # in the merge queue the closure has effectively already happened -- RM-07
    # judges both of those, as it did before.
    rm08_checked = 0
    if pr_number:
        if closing is None:
            print(f"note: RM-08 could not read closing issues for "
                  f"#{pr_number} ({closing_problem}); RM-07 remains the backstop")
        else:
            by_issue = {e["gh_issue"]: e for e in items if e.get("gh_issue")}
            for n in sorted(closing):
                e = by_issue.get(n)
                if e is None:
                    continue  # no roadmap entry; RM-06 owns that gap
                rm08_checked += 1
                status = e.get("status")
                if status not in RM07_DONE_STATUSES:
                    fail("RM-08",
                         f"{e['id']}: this pull request closes #{n} but leaves "
                         f"its entry at status={status} -- ADVANCE IT IN THIS "
                         f"PULL REQUEST, or `main` goes red the moment this "
                         f"merges and stays red for every open branch")
                    failures += 1

    files = sorted({e["_file"] for e in items})
    print(f"checked {len(items)} entries across {len(files)} file(s): {', '.join(files)}")
    print(f"        {len(referenced)} issue(s) referenced, {len(owned)} milestone(s) owned")
    print(f"        RM-07: {judged} entr{'y' if judged == 1 else 'ies'} judged against "
          f"issue state, {unjudged} with no comparable status")
    if pr_number:
        print(f"        RM-08: {rm08_checked} closing reference(s) checked "
              f"for pull request #{pr_number}")
    if authored is not None:
        print(f"        RM-07: scoped to {len(authored)} entr"
              f"{'y' if len(authored) == 1 else 'ies'} this branch authored "
              f"(base {scope_to})")
    if exempt:
        print(f"        RM-07: {len(exempt)} entr"
              f"{'y' if len(exempt) == 1 else 'ies'} not judged because this "
              f"pull request closes the issue on merge (RM-08 judges those):")
        for detail in exempt:
            print(f"          note  RM-07  {detail}")
    if inherited:
        print(f"        RM-07: {len(inherited)} inherited disagreement(s) NOT "
              f"failed here -- they are `main`'s to fix, and `main`'s own run "
              f"judges them. Listed in full:")
        for detail in inherited:
            print(f"          note  RM-07  {detail}")
    if known_hit:
        print(f"        RM-06: {len(known_hit)} known gap(s) still open "
              f"(this number must go down, never up)")
    if failures:
        print(f"FAIL  {failures} finding(s). Each names which side is stale; "
              f"decide which was right, then fix that side.")
        return 1
    print("ok: roadmap and tracker agree")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main(sys.argv[1:]))
