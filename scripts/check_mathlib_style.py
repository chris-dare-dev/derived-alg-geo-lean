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

`--diff-only` exists because a branch gate and an edit hook are answering
different questions. The hook judges the line you just wrote, so it is strict.
A branch gate that reported every pre-existing violation in a file the branch
happens to touch would turn editing any legacy file into a mandatory refactor
of it -- which `CONTRIBUTING.md` explicitly does not want ("avoid unrelated
refactors in a feature change"), and which stalls an unattended run on debt
that is not its business. Findings are therefore filtered to lines the diff
actually adds or changes.

Conventions enforced here are documented in `.claude/references/mathlib-style.md`.
"""

from __future__ import annotations

import functools
import json
import re
import sys
from pathlib import Path

MAX_LINE = 100

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


class Finding:
    def __init__(self, severity: str, line: int, code: str, message: str) -> None:
        self.severity = severity
        self.line = line
        self.code = code
        self.message = message


def in_scope(path: Path) -> bool:
    if path.suffix != ".lean":
        return False
    parts = path.parts
    if any(p in EXCLUDED_PARTS for p in parts):
        return False
    text = str(path)
    return path.name in INCLUDED_FILES or any(p in text for p in INCLUDED_PREFIXES)


def strip_string_literals(line: str) -> str:
    """Blank out double-quoted spans so token checks do not fire inside strings."""
    return re.sub(r'"(?:[^"\\]|\\.)*"', lambda m: '"' + " " * (len(m.group(0)) - 2) + '"', line)


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


def check_text(raw: str, path: Path) -> list[Finding]:
    out: list[Finding] = []
    lines = raw.split("\n")
    code = code_only(lines)

    # An import-only re-export file needs neither a copyright header nor a full
    # module docstring; Mathlib's own header linter grants the same exemption.
    has_decls = any(DECL_RE.match(c) for c in code)

    # --- whole-file structure -------------------------------------------------
    if has_decls and not raw.startswith("/-\nCopyright "):
        out.append(Finding("ERROR", 1, "HDR", "File must open with a `/-\\nCopyright ...` header block."))

    # The module docstring must be the first command after the imports.
    first_cmd = None
    for i, line in enumerate(lines):
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-") and not s.startswith("/-!"):
            continue  # header block; skipped crudely, good enough for position
        if s.startswith(("import ", "public import ", "meta import ", "module")) or s in {"-/", "module"}:
            continue
        if s.startswith("Copyright") or s.startswith("Released under") or s.startswith("Authors"):
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
        if len(line) > MAX_LINE and not is_import:
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

        if doc is None:
            if kw in DOC_REQUIRED:
                out.append(
                    Finding("ERROR", idx, "DOC", f"`{kw} {name}` has no `/-- ... -/` docstring; Mathlib requires one.")
                )
            elif kw in {"theorem", "lemma"}:
                out.append(
                    Finding("WARN", idx, "DOC", f"`{kw} {name}` has no docstring. Add one if it has mathematical content.")
                )
            if name.endswith("'"):
                out.append(
                    Finding(
                        "ERROR",
                        idx,
                        "PRIME",
                        f"`{name}` ends in `'` and has no docstring explaining what differs from the unprimed form.",
                    )
                )
        else:
            if name.endswith("'") and "'" not in doc and "prime" not in doc.lower():
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
    """Return the `/-- ... -/` docstring immediately above `lines[decl_index]`, if any."""
    i = decl_index - 1
    # Attributes may sit between the docstring and the declaration; a blank line
    # detaches the docstring, so it is not skipped.
    while i >= 0 and lines[i].strip().startswith("@["):
        i -= 1
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


def report(path: Path, findings: list[Finding]) -> int:
    errors = [f for f in findings if f.severity == "ERROR"]
    warns = [f for f in findings if f.severity == "WARN"]
    for f in sorted(findings, key=lambda f: (f.line, f.severity)):
        print(f"{path}:{f.line}: {f.severity} [{f.code}] {f.message}", file=sys.stderr)
    return 1 if errors else 0


def main(argv: list[str]) -> int:
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
    for p in paths:
        if not in_scope(p) or not p.exists():
            continue
        findings = check_text(p.read_text(encoding="utf-8"), p)
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
        # Exit 2 is the PostToolUse blocking code: stderr is fed back to the agent.
        return 2 if hook_mode else 1
    if total_warns and hook_mode:
        # Warnings are advisory: surface them without blocking.
        return 0
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
