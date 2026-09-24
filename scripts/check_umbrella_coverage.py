#!/usr/bin/env python3
"""Require same-named umbrellas to import every direct child.

Every file beside a same-named directory is an umbrella by default. Genuine
declaration owners (whose children contain consequences, not exports) need an
explicit, source-pinned witness below. A changed owner is reviewed again before
its SHA-256 is updated; the gate never guesses ownership from source regexes.

Imports come from the pinned Lean executable's ``--deps-json --stdin`` header
parser, not a Python approximation of Lean comments, strings, or interpolation.
All candidate paths are parsed in one invocation, and any parser error or
unexpected JSON shape fails the gate. This checks *header imports*, not Lean
elaboration or transitive reachability.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys
from typing import NamedTuple

from _output import force_utf8_output


ROOT = pathlib.Path(__file__).resolve().parent.parent


class OwnerWitness(NamedTuple):
    # One manually reviewed source declaration, plus the complete source digest.
    # The digest makes removal or movement of the declaration fail closed until
    # the exception is re-reviewed. A textual line alone is not a Lean lexer.
    line: int
    declaration: str
    sha256: str


# Complete reviewed exception list at f4c5af5f. Each witness is a code line,
# not doc text. Re-review any changed source before refreshing its digest.
DECLARATION_OWNERS: dict[str, OwnerWitness] = {
    "DerivedAlgGeo.Algebra.Homology.DGCategory.FullSubcategory": OwnerWitness(
        67, "def DGFullSubcategory {C : Type u} (P : C → Prop) : Type u := {X : C // P X}",
        "39c54497bfb0fbf27ed16a96ab4f0b327e1ba9c7b2225eeb7bbc6d841532923e",
    ),
    "DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective": OwnerWitness(
        29, "def boundedAboveProjectiveHomotopy",
        "ea9403b114a6ceb02a0fdefbd57d4d566709302083a158daafe63ad7be730a88",
    ),
    "DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty": OwnerWitness(
        63, "def cohomologyIn (P : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=",
        "f6b638dcf86abf6c283430e653c272d8fd954ab8505861b8e4427c71db040572",
    ),
    "DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor": OwnerWitness(
        52, "noncomputable def Adjunction.mapHomologicalComplex {F : A ⥤ B} {G : B ⥤ A}",
        "1942305c616505a96521329d29eeee59f56a0a997c57cbd7efda11badb5aaf90",
    ),
    "DerivedAlgGeo.Algebra.Homology.DerivedCategory.GrothendieckGroup": OwnerWitness(
        39, "noncomputable abbrev boundedHomologyFunctor (n : ℤ) : Bounded A ⥤ A :=",
        "9512f4eb76fceff99bfa01d62b407c6802d97b44c0978e757173f8c083baf928",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc": OwnerWitness(
        69, "def schemeQuasicoherentCohomology (X : Scheme.{u}) :",
        "086a240909d517ef39778d2849fd19cef4554c7aa24a1e5ce0e156119fe5b461",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Modules.ExteriorPower": OwnerWitness(
        38, "noncomputable def exteriorPower (E : X.Modules) (n : ℕ) : X.Modules :=",
        "462550a756d79d7d97520e2acffdbf5aee863f4e0cb77a1e1f9049028fd493ba",
    ),
    "DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids": OwnerWitness(
        35, "structure StackInGroupoids (C : Type u) [Category.{v} C]",
        "10dd4931c4bf46ca5e21dc4163af721be1befcb17b4399fec3b5fe5e3b74ce72",
    ),
    "DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated": OwnerWitness(
        62, "inductive coprodClosure (P : ObjectProperty C) : ObjectProperty C",
        "09b4648348ccee0833f209cb4851ab7ef690c0e81c22f669d887b5814983ff19",
    ),
    "DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing": OwnerWitness(
        37, "structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)",
        "682eed28ebde9ebd721e1a5c83ea380a714c635843a8bf6bf475d6c99ebb6ad8",
    ),
    "DerivedAlgGeo.Topology.Sheaves.ModuleTensor": OwnerWitness(
        29, "lemma W_whiskerLeft_of_isIso_stalk",
        "6846f0bd32b52ebcf58062b76a92ae891d9149e8cfaf4b8595baa364dc8c0e3d",
    ),
}

# Exact umbrella/child boundary. The top-level AlgebraicGeometry umbrella
# exports this Stability child; the layering gate checks the neutral direction.
EXPLICIT_CHILD_BOUNDARIES = {
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory": {
        "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability",
    },
}


class CoverageError(Exception):
    """A prerequisite to a trustworthy coverage verdict failed."""


def module_name(path: pathlib.Path, root: pathlib.Path = ROOT) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def lean_header_imports(paths: list[pathlib.Path]) -> dict[pathlib.Path, set[str]]:
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
    imports_by_path: dict[pathlib.Path, set[str]] = {}
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
        modules: set[str] = set()
        for item in result["imports"]:
            if (
                not isinstance(item, dict)
                or not isinstance(item.get("module"), str)
                or not item["module"]
            ):
                raise CoverageError(f"{path}: malformed Lean header import record")
            modules.add(item["module"])
        imports_by_path[path] = modules
    return imports_by_path


def check_coverage(
    root: pathlib.Path = ROOT,
    owners: dict[str, OwnerWitness] = DECLARATION_OWNERS,
    child_boundaries: dict[str, set[str]] = EXPLICIT_CHILD_BOUNDARIES,
) -> tuple[int, list[str]]:
    source_root = root / "DerivedAlgGeo"
    if not source_root.is_dir():
        raise CoverageError(f"missing Lean source root: {source_root}")
    candidates = {
        module_name(umbrella, root): (umbrella, directory)
        for directory in source_root.rglob("*")
        if directory.is_dir()
        for umbrella in [directory.with_suffix(".lean")]
        if umbrella.is_file()
    }
    if not candidates:
        raise CoverageError(f"no same-named file/directory candidates below {source_root}")
    failures: list[str] = []
    for name, witness in sorted(owners.items()):
        if name not in candidates:
            failures.append(f"stale declaration-owner exception: {name} has no sibling directory")
            continue
        path = candidates[name][0]
        source = path.read_bytes()
        try:
            lines = source.decode("utf-8").splitlines()
        except UnicodeDecodeError as exc:
            raise CoverageError(f"{path}: invalid UTF-8 in declaration owner") from exc
        if not 1 <= witness.line <= len(lines) or lines[witness.line - 1] != witness.declaration:
            failures.append(f"{path.relative_to(root)}: declaration-owner witness line changed")
        if hashlib.sha256(source).hexdigest() != witness.sha256:
            failures.append(f"{path.relative_to(root)}: declaration-owner digest changed; re-review")

    for name, omitted in sorted(child_boundaries.items()):
        if name not in candidates or name in owners:
            failures.append(f"stale umbrella/child exception: {name} is not a checked umbrella")
            continue
        directory = candidates[name][1]
        direct = {module_name(path, root) for path in directory.glob("*.lean")}
        direct.update(
            module_name(sub.with_suffix(".lean"), root)
            for sub in directory.iterdir()
            if sub.is_dir() and sub.with_suffix(".lean").is_file()
        )
        for child in sorted(omitted):
            if child not in direct:
                failures.append(f"stale umbrella/child exception: {name} / {child}")

    imports = lean_header_imports([pair[0] for _, pair in sorted(candidates.items())])
    checked = 0
    for name, (umbrella, directory) in sorted(candidates.items()):
        if name in owners:
            continue
        checked += 1
        declared = imports[umbrella]
        omitted = child_boundaries.get(name, set())
        # Direct children only. A file beside a same-named directory is
        # reached by both loops, so deduplicate its missing-import message.
        children = {module_name(path, root): path for path in directory.glob("*.lean")}
        children.update(
            (module_name(sub.with_suffix(".lean"), root), sub.with_suffix(".lean"))
            for sub in directory.iterdir()
            if sub.is_dir() and sub.with_suffix(".lean").is_file()
        )
        for child, path in sorted(children.items()):
            if child not in declared and child not in omitted:
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
        print("Add the child import, or explicitly review a genuine declaration owner.")
        return 1
    print(f"ok: {checked} umbrella(s) re-export their whole directory")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
