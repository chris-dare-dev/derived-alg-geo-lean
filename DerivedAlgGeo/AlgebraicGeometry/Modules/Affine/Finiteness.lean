/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Gluing
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Over
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finiteness from the affine comparison

The affine comparison identifies a quasi-coherent module on `Spec R` with the tilde of its
global sections.  This file supplies the finiteness consequences needed by coherent sheaves:
a finite family of generators on an affine scheme gives finite global sections, and finiteness
can then be checked on a finite basic-open cover.

## Main results

* `Scheme.Modules.exists_basicOpen_finiteGenerating_cover` refines finite-type data to basic
  opens whose defining elements span the unit ideal;
* `Scheme.Modules.moduleFinite_globalSections_of_isFiniteType` patches the resulting finite
  localized modules;
* `Scheme.Modules.moduleFinite_globalSections` specializes the result to finite presentation.
-/

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

local instance (U : TopologicalSpace.Opens (Spec R)) : HasBinaryProducts (Over U) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- Finite generating sections transported across an equality of opens remain finite. -/
private lemma generatingSections_isFiniteType_cast {M : (Spec R).Modules}
    {U V : (Spec R).Opens} (h : U = V) (σ : (M.over U).GeneratingSections)
    [GeneratingSections.IsFiniteType.{u, u, u} σ] :
    (h ▸ σ).IsFiniteType := by
  subst V
  infer_instance

/-- Generating sections on `D(g)` transport to generating sections on `Spec R[1/g]`. -/
noncomputable def GeneratingSections.restrictBasicOpen (M : (Spec R).Modules) (g : R)
    (σ : (M.over (PrimeSpectrum.basicOpen g)).GeneratingSections) :
    (M.restrict (basicOpenSpecMap g)).GeneratingSections :=
  let h := basicOpenSpecMap_opensRange (R := R) g
  let σ' : (M.over (basicOpenSpecMap g).opensRange).GeneratingSections := h.symm ▸ σ
  σ'.map (basicOpenSpecMap g).opensRangeModulesEquivalence.inverse
    (basicOpenSpecMap g).opensRangeModulesEquivalenceInverseUnitIso.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Restriction from a basic open to its affine spectrum preserves finite generation. -/
instance GeneratingSections.isFiniteType_restrictBasicOpen (M : (Spec R).Modules) (g : R)
    (σ : (M.over (PrimeSpectrum.basicOpen g)).GeneratingSections)
    [GeneratingSections.IsFiniteType.{u, u, u} σ] :
    (GeneratingSections.restrictBasicOpen M g σ).IsFiniteType := by
  let h := basicOpenSpecMap_opensRange (R := R) g
  let σ' : (M.over (basicOpenSpecMap g).opensRange).GeneratingSections := h.symm ▸ σ
  letI hσ' : σ'.IsFiniteType := generatingSections_isFiniteType_cast h.symm σ
  change (σ'.map (basicOpenSpecMap g).opensRangeModulesEquivalence.inverse
    (basicOpenSpecMap g).opensRangeModulesEquivalenceInverseUnitIso.symm).IsFiniteType
  show GeneratingSections.IsFiniteType.{u, u, u} _
  constructor
  change Finite σ'.I
  exact hσ'.finite

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Quasi-coherent presentation data transports from `Spec R` to the affine scheme
corresponding to `D(g)`. Keeping this transport behind an opaque definition prevents later
callers from repeatedly normalizing the two nested site equivalences. -/
noncomputable def QuasicoherentData.restrictBasicOpen (M : (Spec R).Modules) (g : R)
    (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    SheafOfModules.QuasicoherentData.{u, u, u, u}
      (M.restrict (basicOpenSpecMap g)) :=
  (basicOpenSpecMap g).restrictQuasicoherentData M
    (q.over (basicOpenSpecMap g).opensRange)

set_option maxHeartbeats 1600000 in
/-- The affine comparison for the restriction to `D(g)`, built from explicit quasi-coherent
data on the original affine scheme. -/
theorem isIso_fromTildeΓ_restrictBasicOpen_of_quasicoherentData
    (M : (Spec R).Modules) (g : R)
    (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    IsIso (Scheme.Modules.fromTildeΓ (R := .of (Localization.Away g))
      (M.restrict (basicOpenSpecMap g))) :=
  isIso_fromTildeΓ_of_quasicoherentData _
    (QuasicoherentData.restrictBasicOpen M g q)

/-- A finite family of global generators gives finitely generated global sections whenever the
affine comparison map is an isomorphism. -/
theorem moduleFinite_globalSections_of_generatingSections (M : (Spec R).Modules)
    (σ : M.GeneratingSections)
    [GeneratingSections.IsFiniteType.{u, u, u} σ] [IsIso M.fromTildeΓ] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  let F : (Spec R).Modules :=
    SheafOfModules.free.{u} (R := (Spec R).ringCatSheaf) σ.I
  let p : F ⟶ M := σ.π
  let h := moduleSpecΓFunctor.map p
  letI hM : IsIso M.fromTildeΓ := inferInstance
  letI hF : IsIso F.fromTildeΓ := by
    exact isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeFinsupp σ.I⟩⟩
  letI hp : Epi p := by
    dsimp only [p]
    exact σ.epi
  haveI : Epi ((tilde.functor R).map h) := by
    letI hcomp : Epi ((tilde.functor R).map h ≫ M.fromTildeΓ) := by
      have hnat :
          (tilde.functor R).map h ≫ M.fromTildeΓ = F.fromTildeΓ ≫ p := by
        have hnat := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality p
        change (tilde.functor R).map (moduleSpecΓFunctor.map p) ≫ M.fromTildeΓ =
          F.fromTildeΓ ≫ p at hnat
        simpa only [h] using hnat
      rw [hnat]
      exact epi_comp' hF.epi_of_iso hp
    exact (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ hM).mp hcomp
  haveI : Epi h := (tilde.functor R).epi_of_epi_map (f := h) inferInstance
  let e : ModuleCat.of R (σ.I →₀ R) ≅ moduleSpecΓFunctor.obj F :=
    tilde.isoTop (ModuleCat.of R (σ.I →₀ R)) ≪≫
      moduleSpecΓFunctor.mapIso (tildeFinsupp σ.I)
  haveI : Module.Finite R (moduleSpecΓFunctor.obj F) :=
    Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.of_surjective h.hom ((ModuleCat.epi_iff_surjective h).mp inferInstance)

/-- **The map out of a free sheaf that a chosen spanning family provides.**

Transport across `tildeFinsupp`, apply `tilde` to `Finsupp.linearCombination`, and land through the
affine comparison.

`M.fromTildeΓ` is composed with, not inverted, so the map exists for any `M`. It is
`epi_freeEpiOfSpan` that needs `[IsIso M.fromTildeΓ]`, and it takes it there. -/
noncomputable def freeEpiOfSpan (M : (Spec R).Modules)
    (s : Set (moduleSpecΓFunctor.obj M)) :
    SheafOfModules.free.{u} s ⟶ M :=
  (tildeFinsupp s).inv ≫
    (tilde.functor R).map
      (ModuleCat.ofHom (Finsupp.linearCombination R ((↑) : s → moduleSpecΓFunctor.obj M))) ≫
    M.fromTildeΓ

set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **It is an epimorphism exactly when the chosen family spans.**

`tilde` is a left adjoint (`tilde.adjunction`), so it preserves colimits and hence epimorphisms;
`Finsupp.linearCombination` is surjective precisely when the span is everything
(`Finsupp.range_linearCombination`); and the two outer maps are isomorphisms.

Two elaboration hazards, both paid for once:

1. **Keep `PreservesEpimorphisms` inside the `have`.** Left in context as a local instance it
   makes every later instance search diverge, and the resulting heartbeat timeout is *reported* as
   an ordinary "failed to synthesize", which reads like a missing instance rather than a budget.
2. **`backward.isDefEq.respectTransparency false` is required**, as elsewhere in this repository:
   without it the goal after the first rewrite is "not type-correct under the `instances`
   transparency level" and `Iso.hom_inv_id_assoc` silently fails to match. -/
theorem epi_freeEpiOfSpan (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (s : Set (moduleSpecΓFunctor.obj M)) (hs : Submodule.span R s = ⊤) :
    Epi (freeEpiOfSpan M s) := by
  haveI hmap : Epi ((tilde.functor R).map (ModuleCat.ofHom
      (Finsupp.linearCombination R ((↑) : s → moduleSpecΓFunctor.obj M)))) := by
    haveI : (tilde.functor R).PreservesEpimorphisms := by
      haveI := (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
      infer_instance
    haveI : Epi (ModuleCat.ofHom
        (Finsupp.linearCombination R ((↑) : s → moduleSpecΓFunctor.obj M))) := by
      rw [ModuleCat.epi_iff_surjective]
      simp only [ModuleCat.hom_ofHom]
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      simpa using hs
    infer_instance
  haveI hfrom : Epi M.fromTildeΓ := inferInstance
  haveI hq : Epi ((tilde.functor R).map (ModuleCat.ofHom
      (Finsupp.linearCombination R ((↑) : s → moduleSpecΓFunctor.obj M))) ≫ M.fromTildeΓ) :=
    epi_comp _ _
  have hfac : (tildeFinsupp (R := R) s).hom ≫ freeEpiOfSpan M s
      = (tilde.functor R).map (ModuleCat.ofHom
        (Finsupp.linearCombination R ((↑) : s → moduleSpecΓFunctor.obj M))) ≫ M.fromTildeΓ := by
    show (tildeFinsupp (R := R) s).hom ≫ (tildeFinsupp (R := R) s).inv ≫ _ = _
    rw [Iso.hom_inv_id_assoc]
  haveI : Epi ((tildeFinsupp (R := R) s).hom ≫ freeEpiOfSpan M s) := hfac ▸ hq
  exact epi_of_epi (tildeFinsupp (R := R) s).hom _

/-- **A finite module of global sections gives a finite free epimorphism.**

The converse of `moduleFinite_globalSections_of_generatingSections`, and the direction Serre's
global generation needs: paired with `GeneratingSections.ofFreeEpi` it turns `Module.Finite` of the
global sections into an `M.GeneratingSections`, closing the loop between the two.

The index type is a `Finset` of the global sections, so its finiteness is definitional rather than
transported. -/
theorem exists_finite_free_epi_of_moduleFinite (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    [Module.Finite R (moduleSpecΓFunctor.obj M)] :
    ∃ (I : Type u) (_ : Finite I) (p : SheafOfModules.free.{u} I ⟶ M), Epi p := by
  obtain ⟨t, ht⟩ :=
    (Module.finite_def.mp inferInstance :
      (⊤ : Submodule R (moduleSpecΓFunctor.obj M)).FG)
  exact ⟨(t : Set (moduleSpecΓFunctor.obj M)), inferInstance,
    freeEpiOfSpan M _, epi_freeEpiOfSpan M _ ht⟩

/-- A finite global presentation on an affine scheme gives finitely generated global sections. -/
theorem moduleFinite_globalSections_of_presentation (M : (Spec R).Modules)
    (P : M.Presentation) [Presentation.IsFinite.{u, u, u} P] :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  letI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_presentation M P
  exact moduleFinite_globalSections_of_generatingSections M P.generators

set_option maxHeartbeats 1600000 in
/-- A finite-type module sheaf on `Spec R` has finite generating families on a basic-open
cover whose defining elements generate the unit ideal. -/
theorem exists_basicOpen_finiteGenerating_cover (M : (Spec R).Modules)
    (hM : SheafOfModules.IsFiniteType.{u, u, u} M) :
    ∃ (I : Type u) (g : I → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ σ : (M.over (PrimeSpectrum.basicOpen (g i))).GeneratingSections,
        GeneratingSections.IsFiniteType.{u, u, u} σ := by
  obtain ⟨q, hq⟩ := hM.exists_localGeneratorsData
  letI := hq
  let I := Σ i : q.I, {g : R // PrimeSpectrum.basicOpen g ≤ q.X i}
  let g : I → R := fun i ↦ i.2.1
  refine ⟨I, g, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    constructor
    · intro
      trivial
    intro hx
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by simp)
    obtain ⟨i, ⟨k⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
    have hxXi : x ∈ q.X i := k.le hxU
    obtain ⟨V, ⟨_, ⟨a, rfl⟩, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxXi (q.X i).2
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨a, hV⟩⟩, hxV⟩
  · rintro ⟨i, a, ha⟩
    let W : Over (q.X i) := Over.mk (homOfLE ha)
    let σ := (q.generators i).over W
    haveI hσi : (q.generators i).IsFiniteType := hq.isFiniteType i
    haveI hσ : σ.IsFiniteType := GeneratingSections.isFiniteType_over (q.generators i) W
    exact ⟨σ, hσ⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- A quasi-coherent finite-type module sheaf on an affine scheme has finitely generated global
sections. This is the finite-generation corollary of the affine comparison. -/
theorem moduleFinite_globalSections_of_isFiniteType (M : (Spec R).Modules)
    [M.IsQuasicoherent] (hM : SheafOfModules.IsFiniteType.{u, u, u} M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  classical
  obtain ⟨I, g, hg, hσ⟩ := M.exists_basicOpen_finiteGenerating_cover hM
  obtain ⟨q⟩ :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  let N (x : Set.range g) := M.restrict (basicOpenSpecMap x.1)
  let L (x : Set.range g) :=
    moduleSpecΓFunctor (R := .of (Localization.Away x.1)).obj (N x)
  letI (x : Set.range g) : Module R (L x) :=
    Module.compHom (L x) (algebraMap R (Localization.Away x.1))
  letI (x : Set.range g) : IsScalarTower R (Localization.Away x.1) (L x) :=
    .of_algebraMap_smul fun _ _ => rfl
  let e (x : Set.range g) :
      L x ≃ₗ[R]
        (modulesSpecToSheaf.obj M).presheaf.obj
          (op (PrimeSpectrum.basicOpen x.1)) :=
    M.restrictBasicOpenTopLinearEquiv x.1
  let f (x : Set.range g) : moduleSpecΓFunctor.obj M →ₗ[R] L x :=
    (e x).symm.toLinearMap ∘ₗ (M.basicOpenRestriction x.1).hom
  letI (x : Set.range g) :
      IsLocalizedModule (Submonoid.powers x.1) (f x) := by
    letI hloc : IsLocalizedModule (Submonoid.powers x.1)
        (M.basicOpenRestriction x.1).hom :=
      M.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent x.1
    exact IsLocalizedModule.of_linearEquiv (Submonoid.powers x.1)
      (M.basicOpenRestriction x.1).hom (e x).symm
  have hfinite (x : Set.range g) :
      Module.Finite (Localization.Away x.1) (L x) := by
    let i : I := x.2.choose
    have hi : g i = x.1 := x.2.choose_spec
    obtain ⟨σ, hσfinite⟩ := hσ i
    letI hσi : GeneratingSections.IsFiniteType.{u, u, u} σ := hσfinite
    let hopen : PrimeSpectrum.basicOpen (g i) = PrimeSpectrum.basicOpen x.1 :=
      congrArg PrimeSpectrum.basicOpen hi
    let σx : (M.over (PrimeSpectrum.basicOpen x.1)).GeneratingSections := hopen ▸ σ
    letI hσx : GeneratingSections.IsFiniteType.{u, u, u} σx :=
      generatingSections_isFiniteType_cast hopen σ
    let σN := GeneratingSections.restrictBasicOpen M x.1 σx
    letI hσN : GeneratingSections.IsFiniteType.{u, u, u} σN :=
      @GeneratingSections.isFiniteType_restrictBasicOpen R M x.1 σx hσx
    letI hN : IsIso (Scheme.Modules.fromTildeΓ
        (R := .of (Localization.Away x.1)) (N x)) :=
      isIso_fromTildeΓ_restrictBasicOpen_of_quasicoherentData M x.1 q
    exact @moduleFinite_globalSections_of_generatingSections
      (.of (Localization.Away x.1)) (N x) σN hσN hN
  exact Module.Finite.of_localizationSpan' (Set.range g) hg f hfinite

/-- A finitely presented module sheaf on an affine scheme has finitely generated global
sections. -/
theorem moduleFinite_globalSections (M : (Spec R).Modules)
    (hM : SheafOfModules.IsFinitePresentation.{u, u, u} M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  letI hM' : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  exact moduleFinite_globalSections_of_isFiniteType M inferInstance

end AlgebraicGeometry.Scheme.Modules
