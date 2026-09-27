#!/usr/bin/env python3
"""Keep the Codex loop skill discoverable and its project instructions complete."""

from __future__ import annotations

import re
from pathlib import Path

from _output import force_utf8_output


ROOT = Path(__file__).resolve().parent.parent
MAX_PROJECT_DOC_BYTES = 32_768


def valid_frontmatter(contents: str) -> bool:
    """Require a complete named and described Codex skill header."""
    lines = contents.splitlines()
    if not lines or lines[0] != "---":
        return False
    try:
        end = lines.index("---", 1)
    except ValueError:
        return False
    header = lines[1:end]
    names = [line for line in header if re.match(r"name\s*:", line)]
    descriptions = [line for line in header if re.match(r"description\s*:", line)]
    if len(names) != 1 or len(descriptions) != 1:
        return False
    match = re.fullmatch(r"description:\s*(\S.*?)\s*", descriptions[0])
    return (
        bool(re.fullmatch(r"name:\s*run-loop\s*", names[0]))
        and match is not None
        and match[1] not in {"''", '""'}
    )


def main() -> int:
    agents = ROOT / "AGENTS.md"
    size = len(agents.read_bytes())
    if size > MAX_PROJECT_DOC_BYTES:
        print(f"AGENTS.md is {size} bytes; Codex reads at most {MAX_PROJECT_DOC_BYTES}")
        return 1

    entry = ROOT / ".agents/skills/run-loop"
    owner = ROOT / ".claude/skills/run-loop"
    if not entry.is_symlink() or entry.resolve() != owner.resolve():
        print(".agents/skills/run-loop must link to the canonical .claude/skills/run-loop")
        return 1
    skill = entry / "SKILL.md"
    if not skill.is_file() or not valid_frontmatter(skill.read_text(encoding="utf-8")):
        print("Codex run-loop skill is missing or has the wrong front matter")
        return 1

    print(f"Codex entrypoint: AGENTS.md {size}/{MAX_PROJECT_DOC_BYTES} bytes; run-loop linked")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
