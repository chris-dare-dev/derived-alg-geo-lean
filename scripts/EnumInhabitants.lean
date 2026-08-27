/-
Print, for every structure and class this repository declares, how many terms of
that type it also declares. Two row shapes, tab-separated:

    structure   <module>            <name>
    inhabitant  <structureName>     <declName>

Run: `lake env lean scripts/EnumInhabitants.lean`

## Why the environment, and not a grep

The question "how many things instantiate `S`" cannot be answered from source
text. A first attempt counted every signature mentioning `S` after a colon,
which reports `def IsPositive (D : ClassDatum O G) : Prop` as an instantiation
of `ClassDatum`. That is a *consumer*: it takes one as a parameter. Producers
and consumers are indistinguishable by position in the text and trivially
distinguishable in the elaborated environment.

An inhabitant is a declaration whose type, after stripping every leading `∀`,
has `S` as the head of its conclusion:

    abelianDatum : ClassDatum A (K₀Ab A)          -- conclusion head `ClassDatum`
    IsPositive   : ClassDatum O G → … → Prop      -- conclusion head `Prop`

The same test also disposes of type synonyms for free. `abbrev StabilityFunction
:= StabilityFunctionOn (abelianDatum A)` has type `Type _`, so its conclusion
head is a sort, and it is not counted as a term of `StabilityFunctionOn` --
which is right, because it is another name for the type rather than a thing of
it.

Projections come out correct without special handling: `S.field : S → F` has
conclusion head `F`. Constructors do not, so `.mk` is filtered with the other
generated suffixes, exactly as `EnumDecls.lean` filters them.
-/
import DerivedAlgGeo
import DerivedAlgGeo.Development

open Lean

/-- Suffixes Lean generates on the author's behalf; see `EnumDecls.lean`, whose
list this mirrors. `.mk` matters most here: a constructor's conclusion IS its
structure, so leaving it in would give every structure a free inhabitant. -/
private def autoSuffixes : List String :=
  [".casesOn", ".recOn", ".rec", ".brecOn", ".below", ".ibelow", ".binductionOn",
   ".noConfusion", ".noConfusionType", ".ctorIdx", ".toCtorIdx", ".sizeOf",
   ".injEq", ".mk", ".ofNat", ".eq_def", ".induct", ".congr_simp"]

private def isAuthored (n : Name) : Bool := Id.run do
  let s := n.toString
  if autoSuffixes.any (fun suf => s.endsWith suf) then return false
  if (s.splitOn "._").length > 1 then return false
  if (s.splitOn "proof_").length > 1 then return false
  if (s.splitOn "match_").length > 1 then return false
  if (s.splitOn ".eq_").length > 1 then return false
  return true

/-- The head constant of a type's conclusion, with every leading binder
stripped. This is the whole of the producer/consumer distinction. -/
private partial def conclusionHead : Expr → Option Name
  | .forallE _ _ body _ => conclusionHead body
  | e => e.getAppFn.constName?

run_cmd do
  let env ← Lean.getEnv
  let ours := `DerivedAlgGeo
  let mut structures : Std.HashSet Name := {}
  let mut rows : Array String := #[]

  -- Pass one: the structures and classes this repository declares.
  for (n, ci) in env.constants.toList do
    if n.isInternal || !isAuthored n then continue
    unless ci.isInductive do continue
    unless isStructure env n do continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if ours.isPrefixOf m then
        structures := structures.insert n
        rows := rows.push s!"structure\t{m}\t{n}"
    | none => pure ()

  -- Pass two: terms whose conclusion is one of them, wherever they live. An
  -- instantiation in `AlgebraicGeometry` counts for a structure declared in
  -- `CategoryTheory`; that is the direction the whole question is about.
  for (n, ci) in env.constants.toList do
    if n.isInternal || !isAuthored n then continue
    -- Definitions AND theorems. An instance of a `Prop`-valued class is a
    -- proof, so it is a theorem: scanning definitions only reported
    -- `QuasiAbelian` as uninhabited when `Slicing.intervalCat_quasiAbelian`
    -- inhabits it. That miss is the reason this file exists rather than a grep,
    -- and it would have been invisible without checking a case whose answer was
    -- known in advance.
    unless ci.isDefinition || ci.isTheorem do continue
    -- A projection whose field type is itself a structure produces a term of
    -- that structure, but Lean wrote it, not the author.
    if (env.getProjectionFnInfo? n).isSome then continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      unless ours.isPrefixOf m do continue
      match conclusionHead ci.type with
      | some head => if structures.contains head then rows := rows.push s!"inhabitant\t{head}\t{n}"
      | none => pure ()
    | none => pure ()

  for r in rows.qsort (· < ·) do
    IO.println r
