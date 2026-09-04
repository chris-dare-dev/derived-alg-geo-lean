/-
Environment census of the stability-condition subsystem, run through the interpreter.

Run: `lake env lean scripts/StabilityConditionCensus.lean`

It exists to keep `scripts/StabilityConditionAudit.lean`'s docstring honest. That comment states
how much of the library the hand-maintained audit actually covers, and every
number in it had gone stale twice; the fix is a command that reproduces them
rather than a figure someone adjusts.

Why this and not `lake exe emit`: `exe/Emit.lean` documents that it cannot be
LINKED on Windows (`supportInterpreter` pushes the PE export table past 65535
symbols). `lake env lean` runs the same sweep through the interpreter without
linking anything, so the environment-level count IS available on this platform.

This is a script, NOT a gate and NOT a build target. `lean_lib "StabilityConditionAudit"`
roots at `StabilityConditionAudit`, so a sibling file in `scripts/` is not swept into it. It reports the
shortfall; it does not fail on one.

Ordering note: `isPrivateName` must be tested BEFORE `Name.isInternal`. Lean
mangles a private name to `_private.<Module>.<hash>.<Name>`, whose first
component starts with `_`, so `isInternal` swallows every private declaration
and reports zero of them. The generated-name test therefore runs on the
DEMANGLED user name, not on the raw one.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability
import DerivedAlgGeo.AlgebraicGeometry.Moduli
import DerivedAlgGeo.LinearAlgebra.Lattice

open Lean

/-- Compiler-generated companions: recursors, constructors, `casesOn`, matchers,
equation lemmas, and internal names. Run on the DEMANGLED name. -/
def isGenerated (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  match ci with
  | .ctorInfo _ | .recInfo _ => true
  | _ =>
    n.isInternal
    || isAuxRecursor env n
    || isNoConfusion env n
    || isRecCore env n
    -- `<Struct>.mk.inj`, emitted for every structure
    || (match n with
        | .str (.str _ "mk") "inj" => true
        | _ => false)
    || (match n with
        | .str _ s =>
          s ∈ ["recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
               "ndrec", "ndrecOn", "noConfusionType", "injEq", "sizeOf_spec",
               "toCtorIdx", "eq_def", "eq_1", "eq_2", "eq_3", "sizeOf_inst",
               -- Added 2026-08-07. Each of these families was verified to
               -- occur zero times in the stability-condition source, so they are
               -- emitted, not written:
               --   ctorIdx     one per structure
               --   congr_simp  congruence lemma for a def
               --   ext_iff     from `@[ext] theorem ext` (the ext IS written)
               --   ext'_iff    from `@[ext] theorem ext'` (the ext' IS written)
               "ctorIdx", "congr_simp", "ext_iff", "ext'_iff"]
          || "match_".isPrefixOf s || "proof_".isPrefixOf s
          -- Heterogeneous congruence companions generated for dependent defs.
          -- `rg 'hcongr_' DerivedAlgGeo/CategoryTheory/Triangulated` is empty.
          || "hcongr_".isPrefixOf s
        | _ => true)

/-- `A.f` is a structure field projection iff `A` is a structure with field `f`.
These are emitted by the `structure` command, so they are not declarations
anyone wrote a name for, and listing them in a hand-maintained audit would be
noise rather than coverage. -/
def isProjection (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p f => isStructure env p && (getStructureFields env p).contains (Name.mkSimple f)
  | _ => false

/-- Whitespace trim that does not depend on `String.trim`, which is mid-
deprecation at this toolchain and returns `String` in one position and
`String.Slice` in another. Also strips `\r`, which matters: the checkout has
Windows line endings. -/
def myTrim (s : String) : String :=
  let ws (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'
  (s.toList.dropWhile ws |>.reverse.dropWhile ws |>.reverse).asString

/-- Every suffix of a name, longest first: the forms under which an importing
module with the relevant subject namespaces open could legally refer to it. -/
partial def suffixes (n : Name) : List String :=
  let full := n.toString
  let parts := full.splitOn "."
  let rec go (ps : List String) (acc : List String) : List String :=
    match ps with
    | [] => acc
    | _ :: rest => go rest (acc ++ [".".intercalate ps])
  go parts []

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let roots := #[`DerivedAlgGeo.CategoryTheory.Triangulated,
    `DerivedAlgGeo.LinearAlgebra]

  -- names scripts/StabilityConditionAudit.lean actually gates
  let auditSrc ← IO.FS.readFile "scripts/StabilityConditionAudit.lean"
  let auditNames : List String :=
    auditSrc.splitOn "\n" |>.filterMap fun ln =>
      -- tokenise rather than `String.drop`, which returns a `String.Slice` here
      let toks := (myTrim ln).splitOn " " |>.filter (· != "")
      match toks with
      | "#print" :: "axioms" :: nm :: _ => some (myTrim nm)
      | _ => none
  let auditSet : Std.HashSet String := auditNames.foldl (·.insert ·) {}

  let mut nMods := 0
  let mut raw := 0
  let mut authored := 0
  let mut priv := 0
  let mut thms := 0
  let mut nonThms := 0
  let mut uncovered : Array Name := #[]
  let mut privThms := 0
  let mut projGap := 0
  let mut gatedThms := 0
  let mut gatedDefs := 0
  let mut gatedStructs := 0
  for i in [0 : mods.size] do
    let m := mods[i]!
    unless roots.any (fun root => m == root || root.isPrefixOf m) do continue
    nMods := nMods + 1
    for n in data[i]!.constNames do
      let some ci := env.find? n | continue
      raw := raw + 1
      let isPriv := isPrivateName n
      let user := (privateToUserName? n).getD n
      if isGenerated env user ci then continue
      authored := authored + 1
      if isPriv then
        priv := priv + 1
        if ci matches .thmInfo _ then privThms := privThms + 1
      else
        match ci with
        | .thmInfo _ => thms := thms + 1
        | _          => nonThms := nonThms + 1
        -- covered iff SOME legal suffix of the name is named in Audit.lean
        if (suffixes n).any (auditSet.contains ·) then
          -- the split the docstring's claim about `#print axioms` rests on:
          -- for a construction, a clean line says nothing about a proposition
          if ci matches .thmInfo _ then gatedThms := gatedThms + 1
          else if isStructure env n then gatedStructs := gatedStructs + 1
          else gatedDefs := gatedDefs + 1
        else if isProjection env n then
          projGap := projGap + 1
        else
          uncovered := uncovered.push n

  logInfo s!"stability-condition modules      : {nMods}"
  logInfo s!"constants (raw, incl. generated) : {raw}"
  logInfo s!"AUTHORED declarations            : {authored}"
  logInfo s!"  private (Audit cannot name)    : {priv}   (of which theorems: {privThms})"
  logInfo s!"  public theorems (.thmInfo)     : {thms}"
  logInfo s!"  public non-theorems            : {nonThms}"
  logInfo s!"Audit.lean `#print axioms` lines : {auditNames.length}"
  logInfo s!"  of the gated: theorems         : {gatedThms}"
  logInfo s!"  of the gated: structures       : {gatedStructs}"
  logInfo s!"  of the gated: other non-thms   : {gatedDefs}"
  logInfo s!"  of the gated: NOT theorems     : {gatedStructs + gatedDefs}"
  logInfo s!"ungated, structure projections   : {projGap}  (noise, not a real gap)"
  logInfo s!"PUBLIC declarations NOT gated    : {uncovered.size}  (the real gap)"
  -- group the gap by module
  let mut byMod : Std.HashMap Name Nat := {}
  for n in uncovered do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      byMod := byMod.insert m (byMod.getD m 0 + 1)
  for (m, c) in byMod.toList.toArray.qsort (fun a b => a.2 > b.2) do
    logInfo s!"    {c}  {m}"
