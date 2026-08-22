/-
Print every public declaration of the owner-authored libraries, one per line, as
`<library>\t<name>`.

The subsystem audits are hand-maintained lists, and `check_audit.py` compares
what a run printed against what the file commanded -- so a listed name that
disappears breaks the build, and a new declaration nobody listed is invisible.
`scripts/check_audit_complete.py` closes the other direction by diffing this
sweep against the lists.

Run: `lake env lean scripts/EnumDecls.lean`

Auto-generated constructions are filtered here rather than in the consumer,
because the environment is where the information lives: `.casesOn`, `.recOn`,
`.noConfusion`, `.injEq`, and the `match_`/`proof_` internals are produced by
declaring an inductive or by tactic elaboration, and no audit should list them.
-/
import DerivedAlgGeo
import DerivedAlgGeo.Development
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold

open Lean

/-- Suffixes Lean generates on the author's behalf. -/
private def autoSuffixes : List String :=
  [".casesOn", ".recOn", ".rec", ".brecOn", ".below", ".ibelow", ".binductionOn",
   ".noConfusion", ".noConfusionType", ".ctorIdx", ".toCtorIdx", ".sizeOf",
   ".injEq", ".mk", ".ofNat", ".eq_def", ".induct"]

/-- Is this a name a human wrote, rather than one elaboration produced? -/
private def isAuthored (n : Name) : Bool := Id.run do
  let s := n.toString
  if autoSuffixes.any (fun suf => s.endsWith suf) then return false
  -- `_proof_1`, `match_2`, `eq_3`, and the `._` internals.
  if (s.splitOn "._").length > 1 then return false
  if (s.splitOn "proof_").length > 1 then return false
  if (s.splitOn "match_").length > 1 then return false
  -- Equation lemmas: `prodD.eq_1`, `foo.eq_2`, … Missing these was what made a
  -- complete dg-category audit look like it was one declaration short.
  if (s.splitOn ".eq_").length > 1 then return false
  return true

/-- The mathematical subsystem owning a module under the unified source root.

`none` for a module under `DerivedAlgGeo` does **not** mean "skip quietly": the
sweep emits such modules under the `Unclassified` sentinel and
`scripts/check_audit_complete.py` fails on any of them. Before #508 `none`
meant invisible — a new source directory's declarations were neither counted
as public nor reported as missing, so the audit-complete gate passed
vacuously. Adding a directory now means adding a branch here, and forgetting
is a red gate rather than a silent hole. Modules outside `DerivedAlgGeo`
(Mathlib and the other dependencies) are still skipped: they are not this
repository's to audit. -/
private def libraryOf (m : Name) : Option String :=
  let dg := `DerivedAlgGeo.CategoryTheory.DGCategory
  let triangulated := `DerivedAlgGeo.CategoryTheory.Triangulated
  let constantSheafPullback := `DerivedAlgGeo.CategoryTheory.ConstantSheafPullback
  let extDimensionShift := `DerivedAlgGeo.CategoryTheory.ExtDimensionShift
  let equivalenceTransport := `DerivedAlgGeo.CategoryTheory.EquivalenceTransport
  let pseudofunctorObjectProperty :=
    `DerivedAlgGeo.CategoryTheory.PseudofunctorObjectProperty
  let linearAlgebra := `DerivedAlgGeo.LinearAlgebra
  let algebraicGeometry := `DerivedAlgGeo.AlgebraicGeometry
  let algebra := `DerivedAlgGeo.Algebra
  let topology := `DerivedAlgGeo.Topology
  let development := `DerivedAlgGeo.Development
  if m == dg || dg.isPrefixOf m then some "DGCategory"
  else if m == triangulated || triangulated.isPrefixOf m ||
      m == constantSheafPullback || constantSheafPullback.isPrefixOf m ||
      m == extDimensionShift || extDimensionShift.isPrefixOf m ||
      m == equivalenceTransport || equivalenceTransport.isPrefixOf m ||
      m == pseudofunctorObjectProperty ||
        pseudofunctorObjectProperty.isPrefixOf m ||
      m == linearAlgebra || linearAlgebra.isPrefixOf m then
    some "StabilityCondition"
  else if m == algebraicGeometry || algebraicGeometry.isPrefixOf m ||
      m == algebra || algebra.isPrefixOf m || m == topology || topology.isPrefixOf m ||
      m == development || development.isPrefixOf m then
    some "AlgebraicGeometry"
  else none

run_cmd do
  let env ← Lean.getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || !isAuthored n then continue
    unless ci.isTheorem || ci.isDefinition || ci.isInductive || ci.isCtor do continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      match libraryOf m with
      | some lib => rows := rows.push s!"{lib}\t{n}"
      | none =>
        -- A declaration under the source root whose module no prefix claims.
        -- Emit the MODULE under a sentinel so the checker can fail loudly
        -- naming it; anything outside `DerivedAlgGeo` is a dependency's and
        -- stays out of the sweep.
        if (`DerivedAlgGeo).isPrefixOf m then
          rows := rows.push s!"Unclassified\t{m}"
    | none => pure ()
  for r in rows.qsort (· < ·) do
    IO.println r
