#!/usr/bin/env python3
"""Prevent stable family APIs from regressing to theorem-specific coherence.

The narrow classes remain source-compatible views of the coherent roots, but
new consumers must depend on `HasCoherentDerivedTensor` and
`HasMonoidalDerivedPullback`. This gate rejects legacy capability assumptions
outside the two compatibility declarations that define the old pulled-unit
views. Geometric family implementations are owned by AlgebraicGeometry.
"""

from __future__ import annotations

import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = ROOT / "DerivedAlgGeo"
GEOMETRIC_FOURIER_MUKAI = (
    "DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/FourierMukai"
)
STABILITY_FOURIER_MUKAI = (
    "DerivedAlgGeo/AlgebraicGeometry/StabilityCondition/FourierMukai"
)

# Class-name tokens, not binder substrings: `[i : HasDerivedTensorAssoc D]`, a
# qualified name, or a line-wrapped binder must all count. The 2026-08-18
# adversarial review demonstrated that the previous literal `[Has... ` match
# was evadable by exactly those forms, and that scanning only the geometric
# families subtree left every other directory free to consume the legacy
# classes unchecked.
LEGACY_CLASSES = re.compile(
    r"\b(HasDerivedTensorAssoc|HasDerivedPullbackTensor|"
    r"HasUnitPullbackRightUnitor|HasUnitPullbackLeftUnitor)\b"
)

# The only modules allowed to mention the legacy classes: the two that define
# them and derive their one-way views from the coherent roots.
LEGACY_DEFINING = {
    f"{GEOMETRIC_FOURIER_MUKAI}/KernelConvolution.lean",
    f"{STABILITY_FOURIER_MUKAI}/KernelUnitConvolution.lean",
}

TENSOR_UNIT = re.compile(r"\bHasTensorUnit\b")
TENSOR_UNIT_BINDER = re.compile(r"\[\s*(?:\w+\s*:\s*)?HasTensorUnit\b")
TENSOR_UNIT_DEFINING = f"{STABILITY_FOURIER_MUKAI}/KernelUnit.lean"
TENSOR_UNIT_COMPAT = f"{STABILITY_FOURIER_MUKAI}/KernelUnitConvolution.lean"


def main() -> int:
    failures: list[str] = []
    unit_compatibility_lines = 0

    for path in sorted(LIBRARY.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = LEGACY_CLASSES.search(line)
            if match and rel not in LEGACY_DEFINING:
                failures.append(
                    f"{rel}:{line_number}: legacy coherence class "
                    f"{match.group(1)} outside its defining module; depend on "
                    "HasCoherentDerivedTensor / HasMonoidalDerivedPullback"
                )

            if not TENSOR_UNIT.search(line):
                continue
            if rel == TENSOR_UNIT_DEFINING:
                if TENSOR_UNIT_BINDER.search(line):
                    failures.append(
                        f"{rel}:{line_number}: tensor-unit binder in the "
                        "defining module"
                    )
                continue
            if rel == TENSOR_UNIT_COMPAT:
                if TENSOR_UNIT_BINDER.search(line):
                    unit_compatibility_lines += 1
                continue
            failures.append(
                f"{rel}:{line_number}: legacy tensor-unit assumption outside "
                "its defining and compatibility modules"
            )

    if unit_compatibility_lines != 2:
        failures.append(
            "expected exactly two pulled-unit compatibility binders in "
            f"{TENSOR_UNIT_COMPAT}; found {unit_compatibility_lines}"
        )

    if failures:
        print("coherent-families gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        "ok: stable family consumers use coherent tensor and monoidal "
        "pullback roots"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
