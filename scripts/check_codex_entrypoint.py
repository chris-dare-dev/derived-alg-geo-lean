#!/usr/bin/env python3
"""Keep the Codex loop skill discoverable and its project instructions complete."""

from __future__ import annotations

from pathlib import Path

from _output import force_utf8_output


ROOT = Path(__file__).resolve().parent.parent
MAX_PROJECT_DOC_BYTES = 32_768


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
    if not skill.is_file() or not skill.read_text().startswith("---\nname: run-loop\n"):
        print("Codex run-loop skill is missing or has the wrong front matter")
        return 1

    print(f"Codex entrypoint: AGENTS.md {size}/{MAX_PROJECT_DOC_BYTES} bytes; run-loop linked")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
