#!/usr/bin/env python3
"""Check the neutral derived-category umbrella's complete import closure.

Pinned Lean parses every tracked library header in one ``--deps-json --stdin``
batch. All imports, including private and meta imports, contribute graph edges;
the outer Stability route needs one direct import marked both exported and
non-meta so ordinary downstream declarations can use it. A public meta import
alone is visible only to downstream meta code.
This is a focused architecture check, not general layering or elaboration.
"""

from __future__ import annotations

from collections import deque
from graphlib import CycleError, TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import NamedTuple

from _output import force_utf8_output


ROOT = Path(__file__).resolve().parent.parent
NEUTRAL = "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory"
OUTER = "DerivedAlgGeo.AlgebraicGeometry"
GEOMETRIC_STABILITY = NEUTRAL + ".Stability"
TRIANGULATED_STABILITY = "DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition"
FORBIDDEN = (GEOMETRIC_STABILITY, TRIANGULATED_STABILITY)


class GateError(Exception):
    """The import graph cannot be trusted, so no policy verdict is possible."""


class Header(NamedTuple):
    all_imports: frozenset[str]
    exported_imports: frozenset[str]
    ordinary_exported_imports: frozenset[str]


def module_name(path: Path, root: Path) -> str:
    try:
        return ".".join(path.relative_to(root).with_suffix("").parts)
    except ValueError as exc:
        raise GateError(f"Lean source outside repository root: {path}") from exc


def tracked_sources(root: Path = ROOT) -> list[Path]:
    """Use Git's NUL-delimited index, not a filesystem glob or shell expansion."""
    try:
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", "DerivedAlgGeo"],
            cwd=root,
            capture_output=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"could not enumerate tracked Lean sources: {exc}") from exc
    if proc.returncode != 0 or proc.stderr:
        raise GateError(f"git ls-files failed: {proc.stderr.decode(errors='replace')}")
    if not proc.stdout.endswith(b"\0"):
        raise GateError("git ls-files returned an empty or unterminated path list")
    paths = sorted(
        root / os.fsdecode(raw)
        for raw in proc.stdout.split(b"\0")[:-1]
        if Path(os.fsdecode(raw)).suffix == ".lean"
    )
    if not paths or any(not path.is_file() for path in paths):
        raise GateError("no tracked Lean sources, or a tracked Lean source is missing")
    return paths


def parse_headers(paths: list[Path], *, lean_root: Path = ROOT) -> dict[Path, Header]:
    """Validate every Lean result and import flag before building either graph."""
    if not paths:
        raise GateError("no Lean headers to parse")
    if any("\n" in str(path) or "\r" in str(path) for path in paths):
        raise GateError("newline in Lean source path cannot be batched safely")
    try:
        proc = subprocess.run(
            ["lean", "--deps-json", "--stdin"],
            input="\n".join(str(path) for path in paths) + "\n",
            cwd=lean_root,  # resolve the checked-out lean-toolchain
            capture_output=True,
            text=True,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"pinned Lean header parser could not run: {exc}") from exc
    if proc.returncode != 0 or proc.stderr.strip():
        raise GateError(
            f"pinned Lean header parser exited {proc.returncode}: {proc.stderr.strip()}"
        )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise GateError(f"pinned Lean header parser returned invalid JSON: {exc}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("imports"), list):
        raise GateError("pinned Lean header parser returned no result list")
    results = payload["imports"]
    if len(results) != len(paths):
        raise GateError(f"pinned Lean returned {len(results)} results for {len(paths)} paths")
    headers: dict[Path, Header] = {}
    for path, entry in zip(paths, results, strict=True):
        if not isinstance(entry, dict) or not isinstance(entry.get("errors"), list):
            raise GateError(f"{path}: missing Lean header error list")
        if entry["errors"]:
            raise GateError(f"{path}: Lean header errors: {entry['errors']!r}")
        result = entry.get("result")
        if not isinstance(result, dict) or not isinstance(result.get("imports"), list):
            raise GateError(f"{path}: missing Lean header result/import list")
        if not isinstance(result.get("isModule"), bool):
            raise GateError(f"{path}: malformed Lean header isModule flag")
        all_imports: set[str] = set()
        exported: set[str] = set()
        ordinary_exported: set[str] = set()
        for item in result["imports"]:
            if (
                not isinstance(item, dict)
                or not isinstance(item.get("module"), str)
                or not item["module"]
                or any(not isinstance(item.get(flag), bool)
                       for flag in ("isExported", "isMeta", "importAll"))
            ):
                raise GateError(f"{path}: malformed Lean header import record")
            name = item["module"]
            all_imports.add(name)
            if item["isExported"]:
                exported.add(name)
                if not item["isMeta"]:
                    ordinary_exported.add(name)
        headers[path] = Header(
            frozenset(all_imports), frozenset(exported), frozenset(ordinary_exported)
        )
    return headers


def is_component_of(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + ".")


def check_graph(headers: dict[Path, Header], root: Path) -> list[str]:
    """Use all internal edges for reachability; reject broken graph premises."""
    by_name: dict[str, Header] = {}
    for path, header in headers.items():
        name = module_name(path, root)
        if name in by_name:
            raise GateError(f"duplicate internal module: {name}")
        by_name[name] = header
    for required in (NEUTRAL, OUTER, GEOMETRIC_STABILITY):
        if required not in by_name:
            raise GateError(f"missing required internal module: {required}")
    graph: dict[str, set[str]] = {}
    for name, header in by_name.items():
        for imported in header.all_imports:
            if is_component_of(imported, "DerivedAlgGeo") and imported not in by_name:
                raise GateError(f"{name}: unknown internal import {imported}")
        graph[name] = set(header.all_imports & by_name.keys())
    try:
        TopologicalSorter(graph).prepare()
    except CycleError as exc:
        raise GateError(f"internal import cycle: {exc.args[1]!r}") from exc

    failures: list[str] = []
    if GEOMETRIC_STABILITY not in by_name[OUTER].ordinary_exported_imports:
        failures.append(
            f"{OUTER}: must directly publicly import non-meta {GEOMETRIC_STABILITY}"
        )
    parents: dict[str, str | None] = {NEUTRAL: None}
    queue = deque([NEUTRAL])
    while queue:
        current = queue.popleft()
        for imported in sorted(graph[current]):
            if imported in parents:
                continue
            parents[imported] = current
            if any(is_component_of(imported, prefix) for prefix in FORBIDDEN):
                path = [imported]
                while (parent := parents[path[-1]]) is not None:
                    path.append(parent)
                failures.append("forbidden neutral import path: " + " -> ".join(reversed(path)))
            queue.append(imported)
    return failures


def check_neutrality(root: Path = ROOT, paths: list[Path] | None = None) -> tuple[int, list[str]]:
    sources = tracked_sources(root) if paths is None else paths
    headers = parse_headers(sources)
    return len(headers), check_graph(headers, root)


def main() -> int:
    try:
        count, failures = check_neutrality()
    except GateError as exc:
        print(f"neutral-stability-imports: FAIL CLOSED: {exc}", file=sys.stderr)
        return 1
    for failure in failures:
        print(f"neutral-stability-imports: {failure}", file=sys.stderr)
    if failures:
        return 1
    print(f"ok: neutral Stability import closure ({count} tracked Lean headers)")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    raise SystemExit(main())
