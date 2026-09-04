#!/usr/bin/env python3
"""Every tracked library module must be reachable by import from the public root.

A module that no umbrella re-exports is still compiled when something imports
it directly, but it is absent from the public API, from the audits that reach
declarations through umbrellas, and from the emission sweep. In CI the
emission-coverage gate reports that after a full build; this check reports it
in seconds, before a push.

The usual cause is a module that shares a name with a directory of its
consequences: `Sites/Descent/StackInGroupoids.lean` declares `StackInGroupoids`
and does not re-export `StackInGroupoids/Morphism.lean`, so the umbrella above
it has to import the children itself. `check_umbrella_coverage.py` deliberately
skips such modules; this check is the other half.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = "DerivedAlgGeo"
SOURCE_ROOT = ROOT / LIBRARY
PUBLIC_ROOT = ROOT / f"{LIBRARY}.lean"
SWEEP_ROOT = ROOT / f"{LIBRARY}Sweep.lean"
IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)"
)


def module_of(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def imports_of(path: pathlib.Path) -> list[str]:
    return [
        m.group(1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if (m := IMPORT.match(line)) and m.group(1).startswith(LIBRARY)
    ]


def main() -> int:
    graph = {module_of(p): imports_of(p) for p in SOURCE_ROOT.rglob("*.lean")}
    roots = [p for p in (PUBLIC_ROOT, SWEEP_ROOT) if p.exists()]
    reachable: set[str] = set()
    stack = [m for p in roots for m in imports_of(p)]
    while stack:
        m = stack.pop()
        if m in reachable:
            continue
        reachable.add(m)
        stack.extend(graph.get(m, ()))
    orphans = sorted(m for m in graph if m not in reachable)
    if orphans:
        print("root reachability failed: modules no umbrella re-exports:")
        for m in orphans:
            print(f"  - {m.replace('.', '/')}.lean")
        print()
        print(
            "Import each from the nearest umbrella. If the parent module shares "
            "a name with the directory, it declares something and is not an "
            "umbrella; the umbrella above it must import the children directly."
        )
        return 1
    print(f"ok: all {len(graph)} library modules are reachable from the public root")
    return 0


if __name__ == "__main__":
    sys.exit(main())
