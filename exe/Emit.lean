/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeoSweep
import MathFormalContract

/-!
# The emitter, pointed at this repository's combined library

`lake env lean --run exe/Emit.lean --out attest/lean-emission.json` imports
`DerivedAlgGeoSweep`, sweeps `Environment.constants` and calls
`Lean.collectAxioms` on every in-scope constant, private and auto-generated ones
included. It never parses Lean source, so
`set_option maxHeartbeats 400000 in theorem sneaky : False := by sorry` has no
text to hide in.

## Main definitions

* `main` — `MathFormalContract.emitMainForRoots` with `DerivedAlgGeoSweep` as the
  imported root, `DerivedAlgGeo` as an additional scope root, and the library's
  `leanOptions`.

## Main results

None proved here. The emission is the repository's axiom audit: `main` returns
non-zero when any constant's axiom closure contains `sorryAx`, and writes the
artifact either way, because the record is most useful exactly when the build
is not clean. `scripts/check_emission_coverage.py` then reads the artifact and
fails on any axiom outside `propext`, `Classical.choice` and `Quot.sound`. No
file lists declarations by hand, so none can fall behind the source.

## Implementation notes

### Coverage

`rootLib` is what `emitToFileForRootsImpl` imports; `additionalRoots` only
widens the scope filter over what that import brought in. `DerivedAlgGeoSweep`
exists to import every tracked module, and `scripts/check_emission_coverage.py`
fails when a tracked module is missing from the emission.

The one file no emission can cover is this one: a `lean_exe` root is not a
library module and cannot appear in the environment built from its own imports.
CI elaborates `exe/*.lean` separately and refuses `declaration uses 'sorry'`.

### Interpreted, not linked

CI runs the emitter through the interpreter, which needs no native link of a
Mathlib-sized environment. `lake build emit` in the cache-warm workflow keeps
proving that the executable still links.

### `leanOptions` is declared here, not observed

Elaboration options are compile flags and are not recorded in the `.olean`, so
the emitter cannot read them back out of the environment; reporting the process
defaults would make the artifact claim a setting the build did not use.

It must therefore mirror the `[leanOptions]` block of `lakefile.toml`
**character for character**, and `mfc lint` fails a mismatch. If you change one,
change the other in the same commit.

## References

* `MathFormalContract.emitMainForRoots` and Lean's `Lean.collectAxioms`.

## Tags

axiom audit, emission, collectAxioms, sorry
-/

def main (args : List String) : IO UInt32 :=
  MathFormalContract.emitMainForRoots
    (rootLib := `DerivedAlgGeoSweep)
    (additionalRoots := [`DerivedAlgGeo])
    (leanOptions := [("autoImplicit", .bool false),
                     ("relaxedAutoImplicit", .bool false)])
    args
