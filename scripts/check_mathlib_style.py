#!/usr/bin/env python3
"""Fast Mathlib-convention check for a single owner-authored Lean file.

This runs on every agent edit, so it must stay under ~50ms and must never need
Lake, Lean, or the network. It deliberately does *not* re-check anything
`lake exe lint-style` or `lake exe runLinter` already catch in CI; it covers the
gap between an edit landing and CI running for the `DerivedAlgGeo` library.

Two severities:

  ERROR   objectively wrong, no judgement involved. Exits 2 so the PostToolUse
          hook blocks and the agent fixes it before moving on.
  WARN    a heuristic worth a human's attention. Printed, never blocks.

Usage:
    python3 scripts/check_mathlib_style.py FILE [FILE ...]
    python3 scripts/check_mathlib_style.py --hook              # hook JSON on stdin
    python3 scripts/check_mathlib_style.py --diff-only REF F.. # only changed lines
    python3 scripts/check_mathlib_style.py --self-test         # known-answer fixtures
    python3 scripts/check_mathlib_style.py --check-baseline    # ratchet over the library
    python3 scripts/check_mathlib_style.py --relax             # re-record the baseline

`--diff-only` exists because a branch gate and an edit hook are answering
different questions. The hook judges the line you just wrote, so it is strict.
A branch gate that reported every pre-existing violation in a file the branch
happens to touch would turn editing any legacy file into a mandatory refactor
of it -- which `CONTRIBUTING.md` explicitly does not want ("avoid unrelated
refactors in a feature change"), and which stalls an unattended run on debt
that is not its business. Findings are therefore filtered to lines the diff
actually adds or changes.

`scripts/style-baseline.json` answers the same question for the *hook*, which
has no diff to filter by. Switching this checker back on (#1370) exposed 131
pre-existing ERRORs across 76 files, and because the hook judges the whole file
it was handed, every one of those 76 files became un-editable by an agent until
someone refactored it. The baseline enumerates that debt so the hook blocks on
what an edit *adds* and stays quiet about what it inherited -- the
`scripts/nolints.json` and `scripts/warning-baseline.json` pattern, applied here
(#1371).

It records the offending source line rather than its line number, which churns
under every unrelated edit above it -- the reason `check_warnings.py` gives for
keying on the message instead. Unlike that gate it records the text and not only
a count, because a per-edit hook has to name the line to fix, and a count can
only say the file has one too many.

Conventions enforced here are documented in `.claude/references/mathlib-style.md`.
"""

from __future__ import annotations

import functools
import json
import re
import sys
from pathlib import Path

from _output import force_utf8_output

MAX_LINE = 100

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "scripts" / "fixtures" / "mathlib-style"
# Anchored at the repository root, not the working directory: the PostToolUse
# hook runs from wherever the agent's shell happens to be, and a baseline the
# hook cannot find is a hook that blocks on all of it again.
STYLE_BASELINE = ROOT / "scripts" / "style-baseline.json"

# Only owner-authored library source. Vendored Apache source keeps upstream
# style, audit scripts are not library modules, and `.claude/` holds review
# fixtures that were deliberately frozen.
INCLUDED_PREFIXES = ("DerivedAlgGeo/",)
INCLUDED_FILES = ("DerivedAlgGeo.lean",)
EXCLUDED_PARTS = (".lake", "vendor", "scripts", ".claude", "docbuild")

DECL_RE = re.compile(
    r"^(?P<attrs>@\[[^\]]*\]\s*)?"
    r"(?P<kw>theorem|lemma|def|abbrev|structure|class|inductive|instance)\b"
    r"(?P<rest>.*)$"
)
# Declaration kinds Mathlib requires a docstring on, no exceptions.
DOC_REQUIRED = {"def", "abbrev", "structure", "class", "inductive"}
NAME_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_.'₁-₉]*)")
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')

# Primed names Mathlib itself fixes: the field obligations a bundled subobject
# or bundled hom has to discharge, where the prime is part of the required name
# and the unprimed form is the `simp` lemma Mathlib derives from it. The author
# does not choose these, so "say what differs from the unprimed form" is not a
# docstring anyone can write.
MATHLIB_PRIMED = {
    "zero_mem'", "one_mem'", "add_mem'", "mul_mem'", "neg_mem'", "inv_mem'",
    "sub_mem'", "div_mem'", "smul_mem'", "algebraMap_mem'", "mem_carrier'",
    "map_zero'", "map_one'", "map_add'", "map_mul'", "map_smul'", "map_rel'",
    "commutes'", "ext'", "coe_injective'", "toFun_eq_coe'", "nonempty'",
}

# Git writes `<<<<<<< `, `=======`, `>>>>>>> `, and -- under
# `merge.conflictStyle = diff3` -- `||||||| `, each at the very start of a line.
# Seven `<` or seven `>` there are unambiguous: no Lean token and no prose this
# repository writes opens a line that way, so those two are the anchors.
# `=======` is *not* unambiguous -- it is a legal Markdown setext heading
# underline, and the module docstrings here are Markdown -- and seven pipes are
# a marker only in diff3 output. Both are therefore reported only when an anchor
# appears elsewhere in the same file, which is exactly the condition git
# guarantees whenever it writes either of them.
CONFLICT_ANCHOR_RE = re.compile(r"^(?:<{7}|>{7})(?: |$)")
CONFLICT_INNER_RE = re.compile(r"^(?:={7}$|\|{7}(?: |$))")


class Finding:
    def __init__(self, severity: str, line: int, code: str, message: str) -> None:
        self.severity = severity
        self.line = line
        self.code = code
        self.message = message


def in_scope(path: Path) -> bool:
    """Is `path` owner-authored `DerivedAlgGeo` library source?

    Both halves of this test are answered *relative to the repository root*,
    and each half used to be answered against the path as given. That is two
    separate ways for the checker to fall silent, and both were live:

    * An agent session runs in a worktree under `.claude/worktrees/<name>/`,
      and the `PostToolUse` hook is handed an absolute path. So `.claude`
      appeared in `parts`, `EXCLUDED_PARTS` matched it, and every library file
      edited in a worktree was skipped -- on every platform.
    * `INCLUDED_PREFIXES` is written with `/`, but on Windows
      `str(Path("DerivedAlgGeo/Foo.lean"))` is `DerivedAlgGeo\\Foo.lean`, so
      the substring test never matched at all.

    Either one alone makes the hook a no-op, which is the other half of why
    nothing local caught #1359. A path outside the repository keeps the old
    as-given reading.
    """
    if path.suffix != ".lean":
        return False
    try:
        rel = path.resolve().relative_to(ROOT)
    except (ValueError, OSError):
        rel = path
    if any(p in EXCLUDED_PARTS for p in rel.parts):
        return False
    text = rel.as_posix()
    return rel.name in INCLUDED_FILES or any(p in text for p in INCLUDED_PREFIXES)


def strip_string_literals(line: str) -> str:
    """Blank out double-quoted spans so token checks do not fire inside strings."""
    return STRING_RE.sub(lambda m: '"' + " " * (len(m.group(0)) - 2) + '"', line)


def column_in_string(line: str, column: int) -> bool:
    """Does `column` (0-based) fall inside a double-quoted literal on `line`?"""
    return any(m.start() <= column < m.end() for m in STRING_RE.finditer(line))


def code_only(lines: list[str]) -> list[str]:
    """Blank out every block comment, docstring, and line comment.

    Token checks (`sorry`, `λ`, `$`) must not fire on prose: this repository's
    module docstrings discuss `sorry` precisely because it is banned, and a
    checker that cannot tell prose from code would make that undocumentable.
    Nesting is tracked because Lean block comments nest.
    """
    out: list[str] = []
    depth = 0
    for line in lines:
        buf = []
        i = 0
        s = strip_string_literals(line)
        while i < len(s):
            if s.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if s.startswith("-/", i) and depth:
                depth -= 1
                i += 2
                continue
            if not depth and s.startswith("--", i):
                break
            buf.append(" " if depth else s[i])
            i += 1
        out.append("".join(buf))
    return out


def conflict_markers(raw: str, lines: list[str]) -> list[Finding]:
    """Findings for git merge-conflict markers committed into the file.

    Nothing else in `scripts/` catches these. Every structural gate --
    `check_layering.py`, `check_umbrella_coverage.py`,
    `check_source_independence.py`, `check_root_reachability.py` -- reads
    `import` lines and ignores the rest, so a file full of `<<<<<<< HEAD`
    passes all four. On 2026-09-16 a rebase left markers in two files, `git
    add -A` staged them, and the defect surfaced ~13 minutes into CI as
    `unexpected token '<<<'; expected command` (#1359, issue #1315).

    Raw lines, not `code_only`: a conflict inside a docstring is still a
    conflict, and a conflicted file's block-comment nesting is unbalanced
    anyway, so the blanking pass cannot be trusted here.
    """
    # One C-level scan of the whole file keeps the common case -- a file with
    # no conflict in it -- off the per-line path entirely.
    if "<<<<<<<" not in raw and ">>>>>>>" not in raw:
        return []
    text = [ln[:-1] if ln.endswith("\r") else ln for ln in lines]
    hits = {i for i, ln in enumerate(text, start=1) if CONFLICT_ANCHOR_RE.match(ln)}
    if not hits:
        return []
    hits.update(i for i, ln in enumerate(text, start=1) if CONFLICT_INNER_RE.match(ln))
    return [
        Finding(
            "ERROR",
            i,
            "CONFLICT",
            f"Unresolved merge-conflict marker `{elide(text[i - 1])}`; finish the merge.",
        )
        for i in sorted(hits)
    ]


def elide(line: str, limit: int = 48) -> str:
    """Shorten a quoted source line; a rebase marker carries a whole commit subject."""
    return line if len(line) <= limit else line[:limit] + "..."


def check_text(raw: str, path: Path) -> list[Finding]:
    lines = raw.split("\n")

    # A file with conflict markers is not Lean source yet, so every check below
    # would be judging text that does not survive the resolution. Report the
    # markers alone: the only useful next action is to finish the merge.
    if conflicts := conflict_markers(raw, lines):
        return conflicts

    out: list[Finding] = []
    code = code_only(lines)

    # An import-only re-export file needs neither a copyright header nor a full
    # module docstring; Mathlib's own header linter grants the same exemption.
    has_decls = any(DECL_RE.match(c) for c in code)

    # --- whole-file structure -------------------------------------------------
    if has_decls and not raw.startswith("/-\nCopyright "):
        out.append(Finding("ERROR", 1, "HDR", "File must open with a `/-\\nCopyright ...` header block."))

    # The module docstring must be the first command after the imports.
    first_cmd = None
    in_header = False
    for i, line in enumerate(lines):
        s = line.strip()
        if in_header:
            # The copyright block is skipped to its close. It used to be skipped
            # by an allowlist of its prose -- `Copyright`, `Released under`,
            # `Authors` -- so any fourth line fell through and was reported as
            # the first command. `Portions adapted from mattrobball/...` in the
            # vendored attributions did exactly that, five times.
            if s.endswith("-/"):
                in_header = False
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            if s == "/-" or not s.endswith("-/"):
                in_header = True
            continue
        if s == "-/":
            continue
        if s.startswith(("import ", "public import ", "meta import ")) or s == "module":
            continue
        # A file-level `set_option` is a command, but it is one Mathlib writes
        # *before* the module docstring, so it does not answer "is the docstring
        # first". 25 of the 30 MODDOC findings were files that open with
        # `set_option backward.defeqAttrib.useBackward true`.
        if s.startswith("set_option "):
            continue
        first_cmd = (i + 1, s)
        break
    if has_decls and first_cmd and not first_cmd[1].startswith("/-!"):
        out.append(
            Finding(
                "ERROR",
                first_cmd[0],
                "MODDOC",
                "The first command after the imports must be a `/-! ... -/` module docstring "
                "(title, summary, main results, references).",
            )
        )

    # --- per-line -------------------------------------------------------------
    for idx, (line, c) in enumerate(zip(lines, code), start=1):
        if line.endswith("\r"):
            out.append(Finding("ERROR", idx, "WIN", "Windows line ending."))
            line = line[:-1]
        if line != line.rstrip():
            out.append(Finding("ERROR", idx, "TWS", "Trailing whitespace."))
        # Lean import commands cannot be continued onto another line. Mathlib's
        # own long-line linter therefore permits long imports; a deep subject
        # hierarchy such as `CategoryTheory.Triangulated.StabilityCondition`
        # needs the same exception.
        is_import = re.match(r"^\s*(?:(?:public|meta)\s+)?import\s+", c) is not None
        # A line that is only long because the limit lands inside a string
        # literal is not the problem this rule is about. Those are the
        # `(note := "...")` review records, up to 691 characters of deliberate
        # prose; reflowing one means a string gap, which is legal Lean but
        # edits the payload's whitespace for no readability gain. The code on
        # such a line is short. 12 of the 145 LONG findings were these.
        in_string = column_in_string(line, MAX_LINE)
        if len(line) > MAX_LINE and not is_import and not in_string:
            out.append(Finding("ERROR", idx, "LONG", f"Line is {len(line)} chars; Mathlib's limit is {MAX_LINE}."))

        if " ;" in c:
            out.append(Finding("ERROR", idx, "SEM", "Space before `;`."))
        if re.search(r"(?<![A-Za-z0-9_])λ(?![A-Za-z0-9_])", c):
            out.append(Finding("ERROR", idx, "LAM", "Use `fun`, not `λ`."))
        if re.search(r"\s\$\s", c):
            out.append(Finding("ERROR", idx, "DOLLAR", "Use `<|`, not `$`."))
        if re.search(r"\bsorry\b", c):
            out.append(Finding("ERROR", idx, "SORRY", "`sorry` is forbidden in this repository (CLAUDE.md)."))
        if "maxHeartbeats" in c and re.match(r"^\s*set_option", c) and " in" not in c:
            out.append(
                Finding("ERROR", idx, "HEART", "`set_option ... maxHeartbeats` must be scoped with `... in`.")
            )

    # --- declarations ---------------------------------------------------------
    for idx, line in enumerate(lines, start=1):
        m = DECL_RE.match(code[idx - 1])
        if not m:
            continue
        kw = m.group("kw")
        nm = NAME_RE.match(m.group("rest"))
        name = nm.group(1) if nm else "<anonymous>"

        doc = preceding_docstring(lines, idx - 1)
        # `zero_mem'`, `ext'` and friends: Mathlib fixes the name, so neither
        # the ERROR nor the WARN below has anything the author could write.
        explainable_prime = name.endswith("'") and name.split(".")[-1] not in MATHLIB_PRIMED

        if doc is None:
            if kw in DOC_REQUIRED:
                out.append(
                    Finding("ERROR", idx, "DOC", f"`{kw} {name}` has no `/-- ... -/` docstring; Mathlib requires one.")
                )
            elif kw in {"theorem", "lemma"}:
                out.append(
                    Finding("WARN", idx, "DOC", f"`{kw} {name}` has no docstring. Add one if it has mathematical content.")
                )
            if explainable_prime:
                out.append(
                    Finding(
                        "ERROR",
                        idx,
                        "PRIME",
                        f"`{name}` ends in `'` and has no docstring explaining what differs from the unprimed form.",
                    )
                )
        else:
            if explainable_prime and "'" not in doc and "prime" not in doc.lower():
                out.append(
                    Finding(
                        "WARN",
                        idx,
                        "PRIME",
                        f"`{name}` ends in `'`; the docstring should say what differs from the unprimed form.",
                    )
                )
            if restates_the_name(doc, name):
                out.append(
                    Finding(
                        "WARN",
                        idx,
                        "DOCECHO",
                        f"The docstring on `{name}` reads as a translation of its name. Say why the hypothesis "
                        "is needed, what the proof idea is, or where the result sits in the literature.",
                    )
                )

        if kw == "def" and "_" in name.split(".")[-1]:
            out.append(
                Finding("WARN", idx, "DEFNAME", f"`def {name}` should be `lowerCamelCase`, not snake_case.")
            )

    return out


def preceding_docstring(lines: list[str], decl_index: int) -> str | None:
    """Return the `/-- ... -/` docstring immediately above `lines[decl_index]`, if any.

    Attributes may sit between the docstring and the declaration; a blank line
    detaches the docstring, so it is not skipped.

    An attribute can span several lines. This repository's `@[cites ...]`
    carries its `(note := "...")` record on a line of its own, and skipping only
    lines that *start* with `@[` stopped at that continuation, so a documented
    declaration was reported as undocumented -- `def stabilityDist` in
    `.../Metric/Distance/Basic.lean` was the whole of the `DOC` ERROR count.
    A continuation is recognised by its closing `]` and walked back to its
    opener, never across a blank line, so an ordinary `variable [Foo]` above a
    declaration cannot be mistaken for one.
    """
    i = decl_index - 1
    while i >= 0:
        s = lines[i].strip()
        if s.startswith("@["):
            i -= 1
            continue
        if s.endswith("]") and not s.endswith("-/"):
            j = i
            while j >= 0 and lines[j].strip() and not lines[j].strip().startswith("@["):
                j -= 1
            if j < 0 or not lines[j].strip().startswith("@["):
                break
            i = j - 1
            continue
        break
    if i < 0 or not lines[i].strip().endswith("-/"):
        return None
    end = i
    while i >= 0 and "/--" not in lines[i]:
        i -= 1
    if i < 0:
        return None
    return "\n".join(lines[i : end + 1])


_WORDS = {
    "eq": "equal", "ne": "not", "le": "less", "lt": "less", "add": "add", "mul": "multipl",
    "mem": "member", "iff": "if and only if", "comm": "commut", "assoc": "associat",
    "mono": "mono", "inj": "inject", "surj": "surject", "of": "of", "self": "self",
}


def restates_the_name(doc: str, name: str) -> bool:
    """Heuristic: the docstring is a word-for-word English reading of the identifier."""
    body = re.sub(r"/--|-/", " ", doc).strip().lower()
    body = re.sub(r"`[^`]*`", " ", body)
    words = [w for w in re.findall(r"[a-z]+", body) if len(w) > 2]
    if not words or len(words) > 14:
        return False
    parts = [p for p in re.split(r"[._]", name.lower()) if len(p) > 1]
    if len(parts) < 2:
        return False
    hits = 0
    for p in parts:
        stem = _WORDS.get(p, p)
        if any(w.startswith(stem[:4]) or stem.startswith(w[:4]) for w in words):
            hits += 1
    return hits >= max(2, len(parts) - 1)


@functools.lru_cache(maxsize=None)
def renamed_paths(ref: str) -> dict[str, str]:
    """Map each renamed destination to its source path relative to `ref`."""
    import subprocess

    try:
        out = subprocess.run(
            ["git", "diff", "--name-status", "--find-renames=20%", f"{ref}...HEAD"],
            capture_output=True, text=True, check=True, encoding="utf-8",
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return {}

    renames: dict[str, str] = {}
    for line in out.splitlines():
        fields = line.split("\t")
        if len(fields) == 3 and fields[0].startswith("R"):
            renames[fields[2]] = fields[1]
    return renames


def changed_lines(ref: str, path: Path) -> set[int] | None:
    """Line numbers this branch adds or changes in `path`, or None for a new file.

    None means "every line is new", so no filtering is applied.
    """
    import subprocess

    try:
        paths = [str(path)]
        if source := renamed_paths(ref).get(str(path)):
            paths.insert(0, source)
        out = subprocess.run(
            ["git", "diff", "--find-renames=20%", "-U0", f"{ref}...HEAD", "--", *paths],
            capture_output=True, text=True, check=True, encoding="utf-8",
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None

    if "new file mode" in out:
        return None

    lines: set[int] = set()
    for m in re.finditer(r"^@@ -\S+ \+(\d+)(?:,(\d+))? @@", out, re.MULTILINE):
        start = int(m.group(1))
        count = int(m.group(2) or 1)
        lines.update(range(start, start + count))
    return lines


def rel_key(path: Path) -> str:
    """The baseline's key for `path`: repository-relative, forward slashes.

    `in_scope` already resolves against `ROOT` for exactly this reason -- the
    hook is handed an absolute path inside `.claude/worktrees/<name>/`, and a
    key recorded from that path would match in one worktree and nowhere else.
    """
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except (ValueError, OSError):
        return path.as_posix()


def fingerprint(lines: list[str], finding: Finding) -> str:
    """The source line a finding is about, as the baseline records it."""
    if 1 <= finding.line <= len(lines):
        return lines[finding.line - 1].rstrip()
    return ""


@functools.lru_cache(maxsize=1)
def load_style_baseline() -> dict[tuple[str, str, str], int]:
    """`(path, code, source line) -> how many of them this repository carries`."""
    if not STYLE_BASELINE.exists():
        return {}
    try:
        entries = json.loads(STYLE_BASELINE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, ValueError, OSError):
        return {}
    counts: dict[tuple[str, str, str], int] = {}
    for path, code, text, n in entries:
        counts[(path, code, text)] = counts.get((path, code, text), 0) + n
    return counts


def write_style_baseline(counts: dict[tuple[str, str, str], int]) -> None:
    entries = sorted([path, code, text, n] for (path, code, text), n in counts.items())
    STYLE_BASELINE.write_text(
        json.dumps(entries, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def split_baselined(
    path: Path, lines: list[str], findings: list[Finding]
) -> tuple[list[Finding], int]:
    """Partition `findings` into what still blocks and how many the baseline covers.

    Only ERRORs are ever suppressed. A WARN does not block anything, so hiding
    one would cost information and buy nothing.
    """
    baseline = load_style_baseline()
    if not baseline:
        return findings, 0
    key = rel_key(path)
    budget = {k: n for k, n in baseline.items() if k[0] == key}
    if not budget:
        return findings, 0
    kept: list[Finding] = []
    covered = 0
    for f in findings:
        entry = (key, f.code, fingerprint(lines, f))
        if f.severity == "ERROR" and budget.get(entry, 0) > 0:
            budget[entry] -= 1
            covered += 1
            continue
        kept.append(f)
    return kept, covered


def library_files() -> list[Path]:
    """Every in-scope library file, as the whole-library modes read them."""
    files = sorted(ROOT.joinpath("DerivedAlgGeo").rglob("*.lean"))
    files.append(ROOT / "DerivedAlgGeo.lean")
    return [p for p in files if p.exists() and in_scope(p)]


def survey_library() -> dict[tuple[str, str, str], int]:
    """Count every ERROR in the library, keyed as the baseline keys them."""
    counts: dict[tuple[str, str, str], int] = {}
    for p in library_files():
        text = p.read_text(encoding="utf-8")
        lines = text.split("\n")
        for f in check_text(text, p):
            if f.severity != "ERROR":
                continue
            entry = (rel_key(p), f.code, fingerprint(lines, f))
            counts[entry] = counts.get(entry, 0) + 1
    return counts


def check_baseline(relax: bool) -> int:
    """The ratchet: nothing new outside the baseline, and report what it outgrew.

    `--relax` rewrites the file. It only ever *lowers* it: an addition is the
    thing this gate exists to stop, and regenerating past one would be the gate
    marking its own homework.
    """
    current = survey_library()

    if relax and not STYLE_BASELINE.exists():
        # First adoption, and the only time this file is written from a state
        # it does not already dominate. Every later `--relax` may lower it and
        # never raise it, for the reason `check_audit_complete.py` gives about
        # its ceilings: a change that leaves more debt than it found is the
        # thing the ratchet exists to stop.
        write_style_baseline(current)
        print(f"--relax: recorded {sum(current.values())} pre-existing ERROR(s) "
              f"across {len({k[0] for k in current})} file(s) in "
              f"{rel_key(STYLE_BASELINE)}.")
        return 0

    baseline = load_style_baseline()

    if not current and not baseline:
        print("style baseline: nothing recorded and nothing found")
        return 0

    added = {k: n - baseline.get(k, 0) for k, n in current.items()
             if n > baseline.get(k, 0)}
    if added:
        total = sum(added.values())
        print(f"::error::{total} style ERROR(s) are not in {rel_key(STYLE_BASELINE)}. "
              "Fix them; do not regenerate the baseline to make this pass.")
        for (path, code, text), n in sorted(added.items()):
            print(f"  {path} (+{n}) [{code}] {elide(text, 72)}")
        return 1

    removed = {k: baseline[k] - current.get(k, 0) for k in baseline
               if baseline[k] > current.get(k, 0)}
    total_fixed = sum(removed.values())
    print(f"style baseline: {sum(current.values())} ERROR(s) across "
          f"{len({k[0] for k in current})} file(s), all recorded "
          f"(baseline {sum(baseline.values())})")

    if total_fixed and relax:
        write_style_baseline(current)
        print(f"--relax: baseline lowered by {total_fixed}; commit "
              f"{rel_key(STYLE_BASELINE)} with the fix.")
    elif total_fixed:
        print(f"::notice::{total_fixed} baseline finding(s) are gone. Run "
              "`python3 scripts/check_mathlib_style.py --relax` and commit "
              f"{rel_key(STYLE_BASELINE)} so the gate keeps the ground you won.")
    elif relax:
        write_style_baseline(current)
        print(f"--relax: rewrote {rel_key(STYLE_BASELINE)}.")
    return 0


def self_test() -> int:
    """Run the known-answer fixtures under `scripts/fixtures/mathlib-style/`.

    The layout is `<code>/allowed/*.leansrc` and `<code>/forbidden/*.leansrc`,
    where `<code>` is the lowercased finding code under test: every `allowed`
    fixture must produce no finding with that code and every `forbidden`
    fixture must produce at least one, so an edit that silently stops
    rejecting something is caught here instead of by the next regression.

    Only the named code is asserted on, which lets a fixture be about exactly
    one question rather than a fully Mathlib-clean file.

    A fixture is Lean source text but deliberately not a `.lean` file: it must
    reach neither `lake`, `lake exe lint-style`, the declaration sweep, nor
    this checker's own `in_scope`. `scripts/fixtures/layering` keeps its
    hypothetical modules out of the build the same way.
    """
    failures: list[str] = []
    groups = sorted(p for p in FIXTURES.iterdir() if p.is_dir()) if FIXTURES.is_dir() else []
    if not groups:
        print(f"no mathlib-style fixtures found under {FIXTURES}", file=sys.stderr)
        return 1

    checked = 0
    for group in groups:
        code = group.name.upper()
        for verdict in ("allowed", "forbidden"):
            base = group / verdict
            fixtures = sorted(base.glob("*.leansrc")) if base.is_dir() else []
            if not fixtures:
                failures.append(f"no {verdict} fixtures for [{code}] under {base}")
                continue
            for fixture in fixtures:
                checked += 1
                found = [
                    f
                    for f in check_text(fixture.read_text(encoding="utf-8"), fixture)
                    if f.code == code
                ]
                label = fixture.relative_to(ROOT).as_posix()
                if verdict == "forbidden" and not found:
                    failures.append(f"forbidden fixture {label} produced no [{code}] finding")
                if verdict == "allowed" and found:
                    where = ", ".join(f"line {f.line}" for f in found)
                    failures.append(f"allowed fixture {label} was rejected: [{code}] at {where}")

    for failure in failures:
        print(f"mathlib-style fixture: {failure}", file=sys.stderr)
    print(f"mathlib-style fixtures: {checked} checked, {len(failures)} failed")
    return 1 if failures else 0


def report(path: Path, findings: list[Finding]) -> int:
    errors = [f for f in findings if f.severity == "ERROR"]
    warns = [f for f in findings if f.severity == "WARN"]
    for f in sorted(findings, key=lambda f: (f.line, f.severity)):
        print(f"{path}:{f.line}: {f.severity} [{f.code}] {f.message}", file=sys.stderr)
    return 1 if errors else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    if "--check-baseline" in argv or "--relax" in argv:
        return check_baseline(relax="--relax" in argv)

    paths: list[Path]
    hook_mode = "--hook" in argv
    diff_ref: str | None = None
    if "--diff-only" in argv:
        i = argv.index("--diff-only")
        if i + 1 >= len(argv):
            print("--diff-only needs a git ref", file=sys.stderr)
            return 1
        diff_ref = argv[i + 1]
        argv = argv[:i] + argv[i + 2:]
    if hook_mode:
        try:
            payload = json.load(sys.stdin)
        except (json.JSONDecodeError, ValueError):
            return 0
        fp = (payload.get("tool_input") or {}).get("file_path")
        if not fp:
            return 0
        paths = [Path(fp)]
    else:
        paths = [Path(a) for a in argv if not a.startswith("-")]

    if not paths:
        print(__doc__, file=sys.stderr)
        return 0

    bad = 0
    total_warns = 0
    total_covered = 0
    for p in paths:
        if not in_scope(p) or not p.exists():
            continue
        text = p.read_text(encoding="utf-8")
        findings = check_text(text, p)
        # Before the diff filter, so a branch that merely moves a recorded line
        # is not asked to refactor it. The baseline is what this repository has
        # agreed to carry, in every mode that reads a file.
        findings, covered = split_baselined(p, text.split("\n"), findings)
        total_covered += covered
        if diff_ref is not None:
            touched = changed_lines(diff_ref, p)
            if touched is not None:
                findings = [f for f in findings if f.line in touched]
        if hook_mode:
            # An undocumented theorem is backlog, not a defect in this edit.
            # The per-PR review agent reports it; the per-edit hook would only
            # bury the findings that are about the code just written.
            findings = [f for f in findings if not (f.severity == "WARN" and f.code == "DOC")]
        total_warns += sum(1 for f in findings if f.severity == "WARN")
        bad |= report(p, findings)

    if bad:
        print(
            "\nMathlib-convention ERRORs above must be fixed before continuing. "
            "See .claude/references/mathlib-style.md.",
            file=sys.stderr,
        )
        if total_covered:
            print(
                f"({total_covered} further finding(s) in these files are recorded "
                f"in {rel_key(STYLE_BASELINE)} and are not yours to fix. Never add "
                "to it.)",
                file=sys.stderr,
            )
        # Exit 2 is the PostToolUse blocking code: stderr is fed back to the agent.
        return 2 if hook_mode else 1
    if total_warns and hook_mode:
        # Warnings are advisory: surface them without blocking.
        return 0
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main(sys.argv[1:]))
