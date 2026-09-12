#!/usr/bin/env python3
"""Keep numerical presentations explicit instead of typeclass-selected.

Numerical intersection rings and numerical varieties are choices of data: two
presentations may legitimately use the same carrier types.  Selecting either
one through typeclass inference makes that choice global and reintroduces the
instance ambiguity removed by issue #602.  This source gate protects the
boundary independently of whether today's examples happen to trigger an
ambiguity during elaboration.
"""

from __future__ import annotations

import pathlib
import re
import sys

from _output import force_utf8_output


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "DerivedAlgGeo"
DATA_NAMES = (
    "NumericalRingData",
    "NumericalVarietyData",
    "NumericalRingDualData",
)
DATA_NAME = "(?:" + "|".join(DATA_NAMES) + ")"


def code_without_comments_or_strings(source: str) -> str:
    """Replace Lean comments and strings by spaces while preserving newlines."""

    result: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                block_depth += 1
                result.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue

        if in_string:
            if source[i] == "\\" and i + 1 < len(source):
                result.extend("  ")
                i += 2
            elif source[i] == '"':
                in_string = False
                result.append(" ")
                i += 1
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
            continue

        if source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                result.append(" ")
                i += 1
        elif source.startswith("/-", i):
            block_depth = 1
            result.extend("  ")
            i += 2
        elif source[i] == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


FORBIDDEN = (
    (
        re.compile(rf"\bclass\s+{DATA_NAME}\b"),
        "numerical presentation declared as a class",
    ),
    (
        re.compile(
            rf"\[\s*(?:[A-Za-z_][\w']*\s*:\s*)?{DATA_NAME}\b(?!\.)"
        ),
        "numerical presentation requested through a typeclass binder",
    ),
    (
        re.compile(rf"\bletI\b[^\n]{{0,240}}:\s*{DATA_NAME}\b"),
        "local instance selects numerical presentation data",
    ),
    (
        re.compile(rf"\binstance\b[^\n]{{0,240}}:\s*{DATA_NAME}\b"),
        "global instance selects numerical presentation data",
    ),
)


def main() -> int:
    failures: list[str] = []
    combined = ""

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        source = path.read_text(encoding="utf-8")
        code = code_without_comments_or_strings(source)
        combined += code
        for pattern, message in FORBIDDEN:
            for match in pattern.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: {message}"
                )

    required = {
        "structure NumericalRingData": "explicit numerical-ring data structure",
        "structure NumericalVarietyData": "explicit numerical-variety data structure",
        "structure SatisfiesHRR": "separate proposition-valued HRR witness",
        "k3AndAbelianPresentations": "same-carrier coexistence regression example",
    }
    for marker, description in required.items():
        if marker not in combined:
            failures.append(f"missing {description}: expected `{marker}`")

    if failures:
        print("explicit-numerical-data gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        "ok: numerical presentations are explicit data and same-carrier "
        "presentations coexist"
    )
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
