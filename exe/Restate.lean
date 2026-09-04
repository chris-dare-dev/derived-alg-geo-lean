/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import MathFormalContract
import RestateHistoricalNames

/-!
# The restate producer, pointed at this repository's combined library

`lake env lean --run exe/Restate.lean --plan attest/restate-plan.json --out
attest/restate.json` reads the work-list `mfc restate-plan` derives from
`attest/review.yaml`, elaborates each reviewed statement in the CURRENT
environment, and asks `isDefEq` against the declaration's type now.

It exists because `env_digest` hashes every package revision, so one dependency
bump rotates it while the mathematics sits still — and `C-10` then reports
every human review as belonging to another environment. That is not
hypothetical here: it happened to this repository's first review, hours after
it was written, and the recovery without this file is a re-read per review per
bump at roughly two hours each.

Same roots as `exe/Emit.lean`, and for the same reason: the reviewed
declarations live under `DerivedAlgGeo`, while `DerivedAlgGeoSweep` is the
umbrella. Importing one and not the other would put a reviewed declaration
outside the environment, and `restateOne` would return `not_checkable` —
"declaration is not in this environment" — which carries nothing forward and
looks like a tooling failure rather than a scope mistake.

`RestateHistoricalNames` is executable-only support for immutable review
payloads that contain names retired from the public library. It is imported by
this producer and added to the restatement environment, but it is intentionally
unreachable from both library roots and therefore absent from emitted
declarations.

Exit 0 whatever the outcomes. This writes the record; `mfc restate-check` is
the gate that reads it.
-/

def main (args : List String) : IO UInt32 :=
  MathFormalContract.restateMainForRoots
    (rootLib := `DerivedAlgGeoSweep)
    (additionalRoots := [`DerivedAlgGeo, `RestateHistoricalNames])
    args
