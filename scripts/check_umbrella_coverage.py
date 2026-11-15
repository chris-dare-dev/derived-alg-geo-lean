#!/usr/bin/env python3
"""Every umbrella re-exports all of its direct children.

The file `Foo.lean` beside a directory `Foo/` is that directory's umbrella,
unless one of `Foo/*.lean` imports it, directly or not. Then Lean's acyclicity
forbids the re-export, `Foo.lean` owns declarations its children build on, and
`check_root_reachability.py` makes sure those children are still reached from
the public root. Nothing lists the owners; the import graph decides. One
umbrella/child boundary is explicit, and the gate pins it exactly.

Imports come from the pinned Lean executable's ``--deps-json --stdin`` header
parser, not a Python approximation of Lean comments, strings, or interpolation.
Only records marked ``isExported`` count: under a ``module`` header a plain
``import`` is available locally but does not re-export the child.
All library modules are parsed in one invocation, and any parser error or
unexpected JSON shape fails the gate. This checks *header imports*, not Lean
elaboration.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
from typing import NamedTuple

from _output import force_utf8_output


ROOT = pathlib.Path(__file__).resolve().parent.parent


# Exact umbrella/child boundary. The top-level AlgebraicGeometry umbrella
# exports this Stability child; the layering gate checks the neutral direction.
EXPLICIT_CHILD_BOUNDARIES = {
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory": {
        "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability",
    },
}
# The omitted child must not enter the neutral umbrella even privately, and
# must still have a public export route through the outer subject umbrella.
STABILITY_EXPORT_ROUTE = (
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory",
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability",
    "DerivedAlgGeo.AlgebraicGeometry",
)


class HeaderImports(NamedTuple):
    all: set[str]
    exported: set[str]


class CoverageError(Exception):
    """A prerequisite to a trustworthy coverage verdict failed."""


def module_name(path: pathlib.Path, root: pathlib.Path = ROOT) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def lean_header_imports(paths: list[pathlib.Path]) -> dict[pathlib.Path, HeaderImports]:
    """Ask pinned Lean to parse every candidate header in a single process."""
    if not paths:
        return {}
    if any("\n" in str(path) or "\r" in str(path) for path in paths):
        raise CoverageError("newline in Lean source path cannot be batched safely")
    try:
        proc = subprocess.run(
            ["lean", "--deps-json", "--stdin"],
            input="\n".join(str(path) for path in paths) + "\n",
            capture_output=True,
            text=True,
            cwd=ROOT,  # elan resolves this repository's pinned lean-toolchain
            timeout=60,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CoverageError(f"pinned Lean header parser could not run: {exc}") from exc
    if proc.returncode != 0 or proc.stderr.strip():
        raise CoverageError(
            f"pinned Lean header parser exited {proc.returncode}: {proc.stderr.strip()}"
        )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise CoverageError(f"pinned Lean header parser returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("imports"), list):
        raise CoverageError("pinned Lean header parser returned no imports result list")
    results = payload["imports"]
    if len(results) != len(paths):
        raise CoverageError(
            f"pinned Lean header parser returned {len(results)} results for {len(paths)} paths"
        )
    imports_by_path: dict[pathlib.Path, HeaderImports] = {}
    for path, entry in zip(paths, results, strict=True):
        if not isinstance(entry, dict) or not isinstance(entry.get("errors"), list):
            raise CoverageError(f"{path}: missing Lean header error list")
        if entry["errors"]:
            raise CoverageError(f"{path}: Lean header errors: {entry['errors']!r}")
        result = entry.get("result")
        if not isinstance(result, dict) or not isinstance(result.get("imports"), list):
            raise CoverageError(f"{path}: missing Lean header result/import list")
        if not isinstance(result.get("isModule"), bool):
            raise CoverageError(f"{path}: malformed Lean header result (isModule)")
        all_modules: set[str] = set()
        exported_modules: set[str] = set()
        for item in result["imports"]:
            if (
                not isinstance(item, dict)
                or not isinstance(item.get("module"), str)
                or not item["module"]
                or not isinstance(item.get("isExported"), bool)
            ):
                raise CoverageError(f"{path}: malformed Lean header import record")
            all_modules.add(item["module"])
            if item["isExported"]:
                exported_modules.add(item["module"])
        imports_by_path[path] = HeaderImports(all_modules, exported_modules)
    return imports_by_path


def direct_children(directory: pathlib.Path, root: pathlib.Path = ROOT) -> dict[str, pathlib.Path]:
    # `Foo/*.lean` includes `Foo/Bar.lean`, the file beside each subdirectory.
    return {module_name(path, root): path for path in sorted(directory.glob("*.lean"))}


def import_closure(imports: dict[str, set[str]]) -> dict[str, set[str]]:
    """Every library module each module reaches through its imports."""
    closure: dict[str, set[str]] = {}
    for start in imports:
        if start in closure:
            continue
        on_path = {start}
        stack = [(start, iter(sorted(imports[start])))]
        while stack:
            module, pending = stack[-1]
            for i in pending:
                if i in imports and i not in closure:
                    if i in on_path:
                        raise CoverageError(f"import cycle through {i}")
                    on_path.add(i)
                    stack.append((i, iter(sorted(imports[i]))))
                    break
            else:
                closure[module] = set().union(
                    *({i} | closure[i] for i in imports[module] if i in imports)
                )
                on_path.discard(module)
                stack.pop()
    return closure


def check_coverage(
    root: pathlib.Path = ROOT,
    child_boundaries: dict[str, set[str]] = EXPLICIT_CHILD_BOUNDARIES,
    export_route: tuple[str, str, str] | None = STABILITY_EXPORT_ROUTE,
) -> tuple[int, list[str]]:
    source_root = root / "DerivedAlgGeo"
    if not source_root.is_dir():
        raise CoverageError(f"missing Lean source root: {source_root}")
    modules = {module_name(path, root): path for path in sorted(source_root.rglob("*.lean"))}
    candidates = {
        name: (path, path.with_suffix(""))
        for name, path in modules.items()
        if path.with_suffix("").is_dir()
    }
    if not candidates:
        raise CoverageError(f"no same-named file/directory candidates below {source_root}")
    headers = lean_header_imports(list(modules.values()))
    imports = {name: headers[path] for name, path in modules.items()}
    closure = import_closure({name: header.all for name, header in imports.items()})
    failures: list[str] = []

    for name, omitted in sorted(child_boundaries.items()):
        if name not in candidates:
            failures.append(f"stale umbrella/child exception: {name} is not a checked umbrella")
            continue
        children = direct_children(candidates[name][1], root)
        for child in sorted(omitted):
            if child not in children:
                failures.append(f"stale umbrella/child exception: {name} / {child}")

    if export_route is not None:
        neutral, child, outer = export_route
        if child_boundaries != {neutral: {child}}:
            failures.append(f"umbrella/child boundary must remain exact: {neutral} / {child}")
        if neutral not in candidates:
            failures.append(f"missing neutral umbrella for boundary: {neutral}")
        elif child in imports[neutral].all:
            failures.append(f"{neutral}: must not import omitted child {child}")
        if outer not in candidates:
            failures.append(f"missing public export umbrella for boundary: {outer}")
        elif child not in imports[outer].exported:
            failures.append(f"{outer}: must publicly re-export omitted child {child}")

    checked = 0
    for name, (umbrella, directory) in sorted(candidates.items()):
        children = direct_children(directory, root)
        if any(name in closure[child] for child in children):
            continue
        checked += 1
        exported = imports[name].exported
        omitted = child_boundaries.get(name, set())
        for child, path in children.items():
            if child not in exported and child not in omitted:
                failures.append(
                    f"{umbrella.relative_to(root)}: does not re-export {path.relative_to(root)}"
                )
    return checked, failures


def main() -> int:
    try:
        checked, failures = check_coverage()
    except CoverageError as exc:
        print(f"umbrella coverage gate failed: {exc}")
        return 1
    if failures:
        print("umbrella coverage gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        print("Import the child from its umbrella.")
        return 1
    print(f"ok: {checked} umbrella(s) re-export their whole directory")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
