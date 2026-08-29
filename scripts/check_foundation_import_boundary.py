#!/usr/bin/env python3
"""Keep the StabilityCondition Foundation umbrella out of implementation modules."""

from __future__ import annotations

import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "DerivedAlgGeo"
UMBRELLA = (
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation"
)
ALLOWED_IMPORTERS = {
    pathlib.Path(
        "DerivedAlgGeo/CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition.lean"
    ),
}
IMPORT = re.compile(r"^\s*import\s+(\S+)")


def main() -> int:
    failures: list[str] = []
    allowed_uses = 0

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        relative = path.relative_to(ROOT)
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = IMPORT.match(line)
            if match is None or match.group(1) != UMBRELLA:
                continue
            if relative in ALLOWED_IMPORTERS:
                allowed_uses += 1
                continue
            failures.append(
                f"{relative}:{line_number}: imports the downstream Foundation "
                "umbrella; import the narrow owning module instead (for example "
                "the weak parent Foundation.Slicing or "
                "Foundation.IntervalCategory, the strong child "
                "Foundation.PreStabilityCondition or "
                "Foundation.StabilityCondition, or a narrow "
                "Foundation.StabilityFunction leaf)"
            )

    if failures:
        print("stability-condition Foundation import boundary failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    if allowed_uses != len(ALLOWED_IMPORTERS):
        print(
            "stability-condition Foundation import boundary failed: expected "
            f"{len(ALLOWED_IMPORTERS)} downstream umbrella import, found "
            f"{allowed_uses}"
        )
        return 1

    print(
        "ok: no StabilityCondition implementation module imports the "
        "Foundation umbrella"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
