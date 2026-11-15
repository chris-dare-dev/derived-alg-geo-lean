/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import MathFormalContract

/-!
# The restate producer, pointed at this repository's combined library

`lake env lean --run exe/Restate.lean --plan attest/restate-plan.json --out
attest/restate.json` reads the work-list `mfc restate-plan` derives from
`attest/review.yaml`, elaborates each reviewed statement in the CURRENT
environment, and asks `isDefEq` against the declaration's type now.

## Main definitions

* `main` — `MathFormalContract.restateMainForRoots` with `DerivedAlgGeoSweep` as
  the imported root and `DerivedAlgGeo` as an additional scope root.

## Main results

None proved here. `main` exits 0 whatever the outcomes: it writes the record,
and `mfc restate-check` is the gate that reads it. Only `restated` carries a
review into a new environment: for `changed` or `not_checkable`, `C-10` fails.

## Implementation notes

### Why restate at all

`env_digest` hashes every package revision, so one dependency bump rotates it
while the mathematics sits still, and `C-10` then reports every human review as
belonging to another environment. Without a restatement each bump would cost a
re-read of every review.

### Roots

Same roots as `exe/Emit.lean`, and for the same reason: the reviewed
declarations live under `DerivedAlgGeo`, while `DerivedAlgGeoSweep` is the
umbrella. Importing one and not the other would put a reviewed declaration
outside the environment, and `restateOne` would return `not_checkable` —
"declaration is not in this environment" — which carries nothing forward and
looks like a tooling failure rather than a scope mistake.

### Renames

A reviewed statement names declarations as they are now, and the environment
holds no aliases for older names. A rename that changes one of those names edits
the recorded statement and its `decl` in the same change; `restated` is then the
evidence that only the name moved.

## References

* `MathFormalContract.restateMainForRoots` and `MathFormalContract.restateOne`.

## Tags

restate, human review, isDefEq, review.yaml
-/

def main (args : List String) : IO UInt32 :=
  MathFormalContract.restateMainForRoots
    (rootLib := `DerivedAlgGeoSweep)
    (additionalRoots := [`DerivedAlgGeo])
    args
