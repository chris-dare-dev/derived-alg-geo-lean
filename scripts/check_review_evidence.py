#!/usr/bin/env python3
"""Inventory changed documentation and compile its declaration references.

The inventory is occurrence-complete, not a semantic proof. Non-declaration
classifications belong in the PR draft, with reasons. Probes stay untracked;
durable Lean evidence belongs in Development with sweep/emitter coverage.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

from _output import force_utf8_output
from check_mathlib_style import code_only

RAW_STRING = re.compile(r'r(#+)"')


def prose_only(text: str) -> str:
    """Mask fenced examples while preserving line numbers, including open fences."""
    result = []
    fence = None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^[ \t]*(`{3,}|~{3,})([^\n]*)", line)
        in_fence = fence is not None
        if marker and fence is None:
            if marker[1][0] != "`" or "`" not in marker[2]:
                fence = marker[1]
                in_fence = True
        elif marker and fence is not None:
            if marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
                fence = None
        result.append(("\n" if line.endswith("\n") else "") if in_fence else line)
    return "".join(result)


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], text=True)


def changed_files(base: str) -> list[Path]:
    # Include staged additions and edits made since the last commit. Never walk
    # other worktrees or ignored scratch directories.
    paths = set(git("diff", "--name-only", "-z", f"{base}...HEAD").split("\0"))
    paths.update(git("diff", "--name-only", "-z", "HEAD").split("\0"))
    return sorted(Path(p) for p in paths if p and Path(p).is_file())


def docs(text: str) -> list[tuple[int, str, bool]]:
    """Extract outer Lean doc comments, skipping strings and ordinary comments."""
    found = []
    i = 0
    while i < len(text):
        raw = RAW_STRING.match(text, i)
        if raw:
            end = text.find('"' + raw[1], i + len(raw[0]))
            i = len(text) if end < 0 else end + 1 + len(raw[1])
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            start = i
            is_doc = text.startswith(("/-!", "/--"), i)
            is_module = text.startswith("/-!", i)
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Lean block comment")
            if is_doc:
                found.append((text.count("\n", 0, start) + 1, text[start + 3:i - 2], is_module))
        else:
            i += 1
    return found


def corpus(paths: list[Path], base: str) -> list[tuple[str, int, str, bool]]:
    merge_base = git("merge-base", base, "HEAD").strip()
    result = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        if path.suffix == ".lean" and path.parts[0] not in (".claude", "scripts", ".lake"):
            old = subprocess.run(["git", "show", f"{merge_base}:{path.as_posix()}"],
                                 text=True, capture_output=True)
            def primary_blocks(source: str) -> list[tuple[int, str, bool]]:
                blocks = docs(source)
                primary = next((line for line, _, module in blocks if module), None)
                # Mid-file /-! section notes need no duplicate module header.
                return [(line, body, module and line == primary) for line, body, module in blocks]
            previous = {(body, primary) for _, body, primary in primary_blocks(old.stdout)} if old.returncode == 0 else set()
            current = primary_blocks(text)
            code = "\n".join(code_only(text.splitlines()))
            non_import = any(s.strip() and not re.match(r"^\s*(?:(?:public|meta)\s+)?import\b", s)
                             for s in code.splitlines())
            if not any(primary for _, _, primary in current) and (
                (old.returncode != 0 and non_import) or any(primary for _, primary in previous)
            ):
                result.append((str(path), 1, "", True))
            result.extend((str(path), line, body, primary) for line, body, primary in current
                          if (body, primary) not in previous)
        elif path.suffix == ".md" and path.parts[0] not in (".claude", "openspec"):
            diff = git("diff", "--unified=0", merge_base, "--", str(path))
            touched = set()
            for start, count in re.findall(r"^@@ .*? \+(\d+)(?:,(\d+))? @@", diff, re.M):
                first = max(1, int(start))
                touched.update(range(first, first + max(1, int(count or "1"))))
            # Whole changed sections, not unrelated pre-existing reference debt.
            # Ignore heading-looking text inside fenced examples.
            lines = text.splitlines(keepends=True)
            starts = [0]
            for index, line in enumerate(prose_only(text).splitlines()):
                if index and re.match(r"^#{1,6} ", line):
                    starts.append(index)
            for begin, end in zip(starts, [*starts[1:], len(lines)]):
                if touched.intersection(range(begin + 1, end + 1)):
                    result.append((str(path), begin + 1, "".join(lines[begin:end]), False))
    return result


SECTIONS = ("Main definitions", "Main results", "Implementation notes", "References", "Tags")


def doc_errors(entries: list[tuple[str, int, str, bool]]) -> list[str]:
    errors = []
    for path, line, body, module in entries:
        if not module:
            continue
        if not body.strip():
            errors.append(f"{path}:{line}: missing primary module docstring")
            continue
        body = prose_only(body)
        if not re.search(r"^# \S", body, re.M):
            errors.append(f"{path}:{line}: module docstring lacks a title")
        title = re.search(r"^# [^\n]+\n(.*?)(?=^## |\Z)", body, re.M | re.S)
        if not title or not title[1].strip():
            errors.append(f"{path}:{line}: module docstring needs a summary after its title")
        required = list(SECTIONS)
        if Path(path).is_file():
            code = "\n".join(code_only(Path(path).read_text(encoding="utf-8").splitlines()))
            if re.search(r"^\s*(?:(?:local|scoped)\s+)?(?:notation|infix[lr]?|prefix|postfix)\b", code, re.M):
                required.insert(2, "Notation")
        positions = []
        for section in required:
            names = "(?:Main results|Main statements)" if section == "Main results" else section
            match = re.search(rf"^## {names}\s*\n(.*?)(?=^##? |\Z)", body, re.M | re.S)
            if not match or not match[1].strip():
                errors.append(f"{path}:{line}: module docstring needs nonempty '## {section}'")
            elif match:
                positions.append(match.start())
        if positions != sorted(positions):
            errors.append(f"{path}:{line}: module docstring sections are out of prescribed order")
    return errors


def references(entries: list[tuple[str, int, str, bool]]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for path, line, body, _ in entries:
        body = prose_only(body)
        body = re.sub(r"^## Reference classifications\s*\n.*?(?=^## |\Z)",
                      lambda m: "\n" * m[0].count("\n"), body, flags=re.M | re.S)
        for match in re.finditer(r"(?<!`)`([^`\n]+)`(?!`)", body):
            token = match[1]
            at = line + body.count("\n", 0, match.start())
            result.setdefault(token, []).append(f"{path}:{at}")
    return result


def classifications(draft: str) -> dict[str, str]:
    """Read Token | Kind | Reason under the draft's reference classifications."""
    section = re.search(r"^## Reference classifications\s*\n(.*?)(?=^## |\Z)", prose_only(draft), re.M | re.S)
    result = {}
    if not section:
        return result
    for line in section[1].splitlines():
        cells = [c.strip().strip("`") for c in line.strip().strip("|").split("|")]
        if not line.strip().startswith("|") or cells[0] == "Token" or all(re.fullmatch(r"[-: ]*", c) for c in cells):
            continue
        if len(cells) != 3 or cells[1] not in ("declaration", "parameter", "historical", "path", "code", "formula"):
            raise ValueError(f"malformed reference classification row: {line}")
        token, kind, reason = cells
        if not reason or token in result:
            raise ValueError(f"missing reason or duplicate classification for {token!r}")
        result[token] = kind
    return result


def kind_of(token: str, overrides: dict[str, str]) -> str:
    if token in overrides:
        return overrides[token]
    if not re.search(r"\s", token) and (
        token.endswith((".lean", ".md", ".json", ".py", ".sh", ".yaml", ".toml", ".txt"))
        or re.match(r"^(?:DerivedAlgGeo|Mathlib|scripts|docs|scratch|exe|\.claude)/[\w./-]*$", token)
    ):
        return "path"
    if re.fullmatch(r"(?:[^\W\d]|_)[\w'₀-₉]*(?:\.(?:[^\W\d]|_)[\w'₀-₉]*)*", token):
        return "declaration"
    return "unclassified"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("docs", "inventory", "probe"))
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--draft", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--import", dest="imports", action="append", default=[])
    parser.add_argument("--run", action="store_true", help="compile the generated probe with the developer's lake")
    args = parser.parse_args(argv)
    try:
        paths = changed_files(args.base)
        entries = corpus(paths, args.base)
        draft = args.draft.read_text(encoding="utf-8") if args.draft else ""
        if args.draft:
            entries.append((str(args.draft.resolve()), 1, draft, False))
        errors = doc_errors(entries)
        refs = references(entries)
        overrides = classifications(draft)
        for token in sorted(set(overrides) - set(refs)):
            errors.append(f"stale reference classification: {token!r}")
        if args.mode == "inventory":
            print("| Token | Kind | Occurrences |")
            print("| --- | --- | --- |")
            for token, locations in sorted(refs.items()):
                print(f"| `{token.replace('|', '&#124;')}` | {kind_of(token, overrides)} | {', '.join(locations)} |")
        elif args.mode == "probe":
            if not args.draft or not args.output:
                parser.error("probe requires --draft and --output")
            if subprocess.run(["git", "ls-files", "--error-unmatch", str(args.output)],
                              capture_output=True).returncode == 0:
                errors.append("probe output is tracked; use ignored scratch, or a reviewed Development module")
            names = []
            for token in refs:
                kind = kind_of(token, overrides)
                if kind == "unclassified":
                    errors.append(f"classify {token!r} with a reason in '## Reference classifications'")
                elif kind == "declaration":
                    if not re.fullmatch(r"[\w'.₀-₉]+", token):
                        errors.append(f"unsupported declaration spelling: {token!r}")
                    else:
                        names.append(token)
            imports = sorted(set(args.imports) | {str(p.with_suffix("")).replace("/", ".")
                             for p in paths if p.suffix == ".lean" and p.parts[0] == "DerivedAlgGeo"})
            if not imports and names:
                errors.append("no probe imports; specify the narrow modules with --import")
            if any(not re.fullmatch(r"[\w.]+", m) for m in imports):
                errors.append("invalid probe import")
            if not errors:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text("\n".join([*(f"import {m}" for m in imports), "",
                                       *(f"#check @{n}" for n in sorted(names)), ""]), encoding="utf-8")
                print(f"Reviewed source commit: {git('rev-parse', 'HEAD').strip()}")
                print(f"Reviewed base: {git('rev-parse', args.base).strip()}")
                print(f"Corpus SHA256: {hashlib.sha256(repr(entries).encode()).hexdigest()}")
                print(f"Probe: {args.output}; {len(refs)} tokens; {sum(map(len, refs.values()))} occurrences; {len(names)} declaration checks")
                if args.run:
                    proc = subprocess.run([str(Path.home() / ".elan/bin/lake"), "env", "lean", str(args.output)],
                                          env={**os.environ, "LEAN_NUM_THREADS": "2"})
                    print(f"Reference probe exit: {proc.returncode}")
                    if proc.returncode:
                        return proc.returncode
        for error in errors:
            print(f"FAIL: {error}", file=sys.stderr)
        if errors:
            return 1
        print(f"ok: {len(entries)} documentation blocks checked ({len(paths)} changed files)")
        return 0
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
