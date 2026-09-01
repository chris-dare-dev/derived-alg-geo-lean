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

Deprecated declarations are excluded for the same ownership reason: they are
compatibility spellings, not canonical public API. A compatibility module that
contains any non-deprecated authored declaration still falls through to the
`Unclassified` sentinel and fails the audit-completeness gate.
-/
import DerivedAlgGeo
import DerivedAlgGeo.Development
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold

open Lean

/-- Suffixes Lean generates on the author's behalf.

`.congr_simp` joined this list on 2026-08-26. Lean generates a structure's
congruence lemma on first use and attributes it to the module that triggered it,
which is whichever module in the build happens to mention the structure first --
not the module that declared it, and never a module the author wrote it in. Two
such lemmas for Mathlib's `ShortComplex` landed in
`CategoryTheory/Abelian/WeakSerre.lean` (#721) purely because it is the first module
to `rw` with one, and the ratchet counted them as that file's unaudited public
declarations. They are the same class of artifact as `.injEq` and
`.noConfusion`, which have always been filtered here. -/
private def autoSuffixes : List String :=
  [".casesOn", ".recOn", ".rec", ".brecOn", ".below", ".ibelow", ".binductionOn",
   ".noConfusion", ".noConfusionType", ".ctorIdx", ".toCtorIdx", ".sizeOf",
   ".injEq", ".mk", ".ofNat", ".eq_def", ".induct", ".congr_simp"]

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
vacuously. Modules outside `DerivedAlgGeo` (Mathlib and the other
dependencies) are still skipped: they are not this repository's to audit.

WHY `CategoryTheory` ROUTES BY SUBTREE RATHER THAN BY NAME. This used to
enumerate every top-level module under `DerivedAlgGeo.CategoryTheory`
individually, so adding one — a file or a directory — meant editing this file.
That is a trust-surface path, so every such pull request tripped the trust
guard and waited on a `trust-reviewed` label. The work being gated was the
routine addition of a module, and #727 and #730 each spent a review cycle on a
one-line `let`. A gate that fires on routine work is a gate that stops being
read, which is the same reasoning that excluded the audit record slices from
the guard.

Routing the whole subtree keeps every protection. A new module is now counted
automatically, so its unaudited declarations raise `missing` and fail
`check_audit_complete.py` on both the ceiling and the absent-from-baseline
identity check. A genuinely new top-level subject — `DerivedAlgGeo.Foo` —
still falls through to `none`, lands under `Unclassified`, and still fails,
which is the case that deserves a human decision. Only the forced edit is
gone. -/
private def libraryOf (m : Name) : Option String :=
  let dg := `DerivedAlgGeo.CategoryTheory.Enriched.DGCategory
  let dgEnhancement := `DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement
  let categoryTheory := `DerivedAlgGeo.CategoryTheory
  let linearAlgebra := `DerivedAlgGeo.LinearAlgebra
  let algebraicGeometry := `DerivedAlgGeo.AlgebraicGeometry
  let algebra := `DerivedAlgGeo.Algebra
  let topology := `DerivedAlgGeo.Topology
  let development := `DerivedAlgGeo.Development
  -- Both dg subtrees precede the generic `CategoryTheory` route.
  if m == dg || dg.isPrefixOf m ||
      m == dgEnhancement || dgEnhancement.isPrefixOf m then
    some "DGCategory"
  else if m == categoryTheory || categoryTheory.isPrefixOf m ||
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
    if n.isInternal || !isAuthored n || Linter.isDeprecated env n then continue
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
