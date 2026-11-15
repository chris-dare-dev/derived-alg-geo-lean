import DerivedAlgGeoSweep
import Lean.Elab.Command

/-!
Invariant: no constant of any `DerivedAlgGeo` module depends on an axiom other
than `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorry`
(`sorryAx`), a declared `axiom` and `native_decide` (`Lean.ofReduceBool`).

Run: `lake env lean scripts/AxiomAudit.lean`. It fails with one line per
offending constant.

It reads the compiled environment, so no syntax can hide a `sorry` from it, and
every constant counts: private, auto-generated and instance declarations
included. `DerivedAlgGeoSweep` imports every library module, and
`scripts/check_root_reachability.py` fails when one is left out, so the sweep
cannot shrink without notice. An empty sweep fails too.

`collectAxioms` reads each imported constant's axioms from its `.olean`, where
the build stored them, so the audit costs a lookup per constant.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules : Nat := 0
  let mut constants : Nat := 0
  let mut offending : Array MessageData := #[]
  for i in [0:env.header.moduleNames.size] do
    unless (`DerivedAlgGeo).isPrefixOf env.header.moduleNames[i]! do continue
    modules := modules + 1
    for c in env.header.moduleData[i]!.constNames do
      constants := constants + 1
      let extra := (← collectAxioms c).filter (!allowed.contains ·)
      unless extra.isEmpty do
        offending := offending.push m!"{c} depends on {extra}"
  if constants == 0 then
    throwError "no constant of a DerivedAlgGeo module is in the environment"
  unless offending.isEmpty do
    throwError m!"{offending.size} constants depend on an axiom outside propext, \
      Classical.choice and Quot.sound:\n{MessageData.joinSep offending.toList "\n"}"
  logInfo m!"{constants} constants in {modules} modules depend only on propext, \
    Classical.choice and Quot.sound"
