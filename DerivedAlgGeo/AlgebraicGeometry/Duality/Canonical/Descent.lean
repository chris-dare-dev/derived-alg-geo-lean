/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Duality.Canonical.Differentials
import DerivedAlgGeo.AlgebraicGeometry.Divisors.LineBundleDual
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Invertible
import DerivedAlgGeo.Topology.Category.TopCat.Opens.CoversTop

/-!
# Fixed-rank descent for the relative cotangent sheaf

This file carries the affine Kähler calculation through sheafification. A standard-smooth chart
supplies a basis of the objectwise differential module; localization on principal opens proves
that the basis morphism is locally bijective, hence its sheafification is an isomorphism. These
chart isomorphisms assemble into fixed-rank locally-free data for the cotangent sheaf.
-/

universe u v w t

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- A cover on which a module sheaf is explicitly trivial of fixed rank `n`. -/
structure FixedRankTrivializations (E : X.Modules) (n : ℕ) where
  /-- Indexing type of the chosen cover. -/
  I : Type u
  /-- Opens in the trivializing cover. -/
  chartOpen : I → X.Opens
  /-- The chosen opens cover the scheme. -/
  coversTop : (_root_.Opens.grothendieckTopology X).CoversTop chartOpen
  /-- A rank-`n` free trivialization on every cover member. -/
  trivialization : ∀ i,
    SheafOfModules.free (R := X.ringCatSheaf.over (chartOpen i))
        (ULift.{u} (Fin n)) ≅
      E.over (chartOpen i)

namespace FixedRankTrivializations

variable {E : X.Modules} {n : ℕ}

/-- The local generating sections induced by the chosen free trivializations. -/
noncomputable def localGenerators (T : FixedRankTrivializations E n) :
    SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from E) where
  I := T.I
  X := T.chartOpen
  coversTop := T.coversTop
  generators i :=
    { I := ULift.{u} (Fin n)
      s := (E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }

/-- The induced local generators are bases rather than merely epimorphic generating families. -/
theorem localGenerators_isLocallyFreeData (T : FixedRankTrivializations E n) :
    T.localGenerators.IsLocallyFreeData := by
  constructor
  intro i
  change IsIso ((E.over (T.chartOpen i)).freeHomEquiv.symm
    ((E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

/-- Explicit rank-`n` trivializations produce fixed-rank locally-free data. -/
noncomputable def finiteLocallyFree (T : FixedRankTrivializations E n) :
    FiniteLocallyFreeData E n where
  localGenerators := T.localGenerators
  isLocallyFreeData := T.localGenerators_isLocallyFreeData
  rankEquiv _ := ⟨Equiv.ulift⟩

/-- The determinant trivialization induced on each member of the fixed-rank atlas. -/
noncomputable def topExteriorTrivialization (T : FixedRankTrivializations E n) (i : T.I) :
    SheafOfModules.unit (X.ringCatSheaf.over (T.chartOpen i)) ≅
      (exteriorPower E n).over (T.chartOpen i) :=
  (exteriorPowerOverIso E (T.chartOpen i) n ≪≫
    exteriorPowerOverMapIsoOfIso (T.chartOpen i) (T.trivialization i).symm n ≪≫
    topExteriorFreeOverIso (T.chartOpen i) n).symm

/-- The top exterior power of an explicitly fixed-rank locally-free sheaf is invertible. -/
theorem topExteriorPower_isInvertible (T : FixedRankTrivializations E n) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from exteriorPower E n) :=
  SheafOfModules.IsInvertible.of_trivializations
    (R := X.ringCatSheaf) (I := T.I) T.chartOpen T.coversTop
      T.topExteriorTrivialization

/-- Fixed-rank trivializations canonically package the constructed top exterior power as an
explicit line bundle with its sheafified-dual tensor inverse. -/
noncomputable def exteriorDeterminantData (T : FixedRankTrivializations E n) :
    ExteriorDeterminantData E := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from exteriorPower E n) :=
    T.topExteriorPower_isInvertible
  exact
    { rank := n
      finiteLocallyFree := T.finiteLocallyFree
      topExteriorPower := LineBundleData.ofIsInvertible (exteriorPower E n)
      topExteriorPowerIso := Iso.refl _ }

/-- The determinant package underlying `exteriorDeterminantData`. -/
noncomputable def determinantData (T : FixedRankTrivializations E n) :
    DeterminantData E :=
  T.exteriorDeterminantData.determinantData

/-- In particular, an explicitly rank-`n`-trivialized sheaf is locally free. -/
theorem isLocallyFree (T : FixedRankTrivializations E n) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from E) :=
  T.finiteLocallyFree.isLocallyFree

end FixedRankTrivializations

end

end Scheme.Modules

namespace Variety

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- A standard-smooth affine chart of relative dimension `n` around a point. -/
structure SmoothChart (n : ℕ) (x : X) where
  target : (Spec (CommRingCat.of k)).Opens
  targetAffine : IsAffineOpen target
  source : X.Opens
  sourceAffine : IsAffineOpen source
  mem_source : x ∈ source
  source_le_preimage : source ≤ (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ target
  standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((X ↘ Spec (CommRingCat.of k)).appLE target source source_le_preimage).hom

namespace SmoothChart

/-- Choose the standard-smooth chart supplied at a point by smooth pure relative dimension. -/
noncomputable def ofSmooth {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) (x : X) :
    SmoothChart k X n x :=
  Classical.choice (show Nonempty (SmoothChart k X n x) from by
    obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
      h.exists_isStandardSmoothOfRelativeDimension x
    exact ⟨
      { target := U
        targetAffine := hU
        source := V
        sourceAffine := hV
        mem_source := hx
        source_le_preimage := e
        standardSmooth := hstd }⟩)

end SmoothChart

private lemma locallyBijective_over_of_pointwise_iso
    {S : Type u} [TopologicalSpace S] {U : Opens S}
    {D : Type v} [Category.{w} D] {FD : D → D → Type*} {CD : D → Type t}
    [∀ A B, FunLike (FD A B) (CD A) (CD B)]
    [ConcreteCategory.{t} D FD]
    {P Q : Functor (Over U)ᵒᵖ D} (p : P ⟶ Q)
    (h : ∀ (Y : Over U) (x : S), x ∈ Y.left →
      ∃ (Z : Over U) (_g : Z ⟶ Y), x ∈ Z.left ∧ IsIso (p.app (Opposite.op Z))) :
    Presheaf.IsLocallyInjective
        ((_root_.Opens.grothendieckTopology S).over U) p ∧
      Presheaf.IsLocallySurjective
        ((_root_.Opens.grothendieckTopology S).over U) p := by
  constructor
  · constructor
    intro Y a b hab
    rw [GrothendieckTopology.mem_over_iff]
    rw [_root_.Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨Z, g, hxZ, hg⟩ := h Y.unop x hx
    refine ⟨Z.left, g.left, ?_, hxZ⟩
    rw [Sieve.overEquiv_iff]
    change P.map (Over.homMk g.left (Over.w g)).op a =
      P.map (Over.homMk g.left (Over.w g)).op b
    have heq : Over.homMk g.left (Over.w g) = g := by ext; rfl
    rw [heq]
    apply (ConcreteCategory.bijective_of_isIso (p.app (Opposite.op Z))).1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hab]
  · constructor
    intro Y s
    rw [GrothendieckTopology.mem_over_iff]
    rw [_root_.Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨Z, g, hxZ, hg⟩ := h Y x hx
    refine ⟨Z.left, g.left, ?_, hxZ⟩
    rw [Sieve.overEquiv_iff]
    obtain ⟨t, ht⟩ :=
      (ConcreteCategory.bijective_of_isIso (p.app (Opposite.op Z))).2 (Q.map g.op s)
    exact ⟨t, ht⟩

omit [IsVariety k X] in
/-- The ring map on a standard-smooth chart is standard smooth after identifying the unique
affine open of `Spec k` containing the image point with the whole spectrum. -/
lemma SmoothChart.standardSmooth_baseField {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source)).hom := by
  rcases C with ⟨target, targetAffine, source, sourceAffine, hx, hle, hstd⟩
  dsimp only [SmoothChart.source, SmoothChart.target] at *
  have htarget : target = ⊤ := by
    apply top_unique
    intro y _hy
    have hxT : (X ↘ Spec (CommRingCat.of k)) x ∈ target := hle hx
    simpa [Subsingleton.elim y ((X ↘ Spec (CommRingCat.of k)) x)] using hxT
  subst target
  apply RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hstd

private noncomputable def SmoothChart.differentialBasis {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    Module.Basis (Fin n) Γ(X, C.source)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source))) := by
  letI : Nonempty C.source := ⟨⟨x, C.mem_source⟩⟩
  letI : Nontrivial Γ(X, C.source) :=
    Scheme.component_nontrivial X C.source
  letI : Module.Free Γ(X, C.source)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source))) :=
    relativeDifferentialsPresheaf_obj_free k X (Opposite.op C.source) n
      (C.standardSmooth_baseField k X)
  have hrank := relativeDifferentialsPresheaf_obj_rank k X (Opposite.op C.source) n
    (C.standardSmooth_baseField k X)
  letI : Module.Finite Γ(X, C.source)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source))) := by
    exact Module.rank_lt_aleph0_iff.mp (by
      rw [hrank]
      exact Cardinal.natCast_lt_aleph0)
  exact Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)

private noncomputable def SmoothChart.differentialBasisULift
    {n : ℕ} {x : X} (C : SmoothChart k X n x) :
    Module.Basis (ULift.{u} (Fin n)) Γ(X, C.source)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source))) :=
  (C.differentialBasis k X).reindex Equiv.ulift.symm

private noncomputable abbrev chartDifferentialsPresheaf {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    PresheafOfModules (X.ringCatSheaf.over C.source).obj :=
  (PresheafOfModules.pushforward
    (𝟙 (X.ringCatSheaf.over C.source).obj)).obj
      (relativeDifferentialsPresheaf k X)

set_option maxHeartbeats 800000 in
private noncomputable def restrictionFamily {U : X.Opens}
    {I : Type u}
    (P : PresheafOfModules (X.ringCatSheaf.over U).obj)
    (b : I → P.obj (Opposite.op (Over.mk (𝟙 U)))) :
    (Functor.const (Over U)ᵒᵖ).obj I ⟶ P.presheaf ⋙ forget _ where
  app Y := ↾fun i ↦
    P.map (show (Y.unop ⟶ Over.mk (𝟙 U)) from
      Over.homMk Y.unop.hom).op (b i)
  naturality Y Z f := by
    ext i
    let hY : Y.unop ⟶ Over.mk (𝟙 U) := Over.homMk Y.unop.hom
    let hZ : Z.unop ⟶ Over.mk (𝟙 U) := Over.homMk Z.unop.hom
    change P.map hZ.op (b i) = P.map f (P.map hY.op (b i))
    have hh : hY.op ≫ f = hZ.op := by
      apply Quiver.Hom.unop_inj
      ext
      rfl
    rw [← hh, P.map_comp]
    rfl

private noncomputable def chartBasisFamily {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    (Functor.const (Over C.source)ᵒᵖ).obj (ULift.{u} (Fin n)) ⟶
      (chartDifferentialsPresheaf k X C).presheaf ⋙ forget _ :=
  restrictionFamily X (chartDifferentialsPresheaf k X C) (C.differentialBasisULift k X)

private noncomputable def chartBasisHom {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    PresheafOfModules.freeObj
        ((Functor.const (Over C.source)ᵒᵖ).obj (ULift.{u} (Fin n))) ⟶
      chartDifferentialsPresheaf k X C :=
  PresheafOfModules.freeObjDesc (chartBasisFamily k X C)

private def chartBasicOpen {n : ℕ} {x : X}
    (C : SmoothChart k X n x) (f : Γ(X, C.source)) : Over C.source :=
  Over.mk (homOfLE (X.basicOpen_le f))

set_option maxHeartbeats 1600000 in
private lemma chartBasisHom_app_basicOpen_isIso {n : ℕ} {x : X}
    (C : SmoothChart k X n x) (f : Γ(X, C.source)) :
    IsIso ((chartBasisHom k X C).app (Opposite.op (chartBasicOpen k X C f))) := by
  let R := Γ(X, C.source)
  let T := Γ(X, X.basicOpen f)
  let A := CommRingCat.KaehlerDifferential
    ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source))
  let Aₛ := CommRingCat.KaehlerDifferential
    ((baseFieldToStructurePresheaf k X).app (Opposite.op (X.basicOpen f)))
  let res : R →+* T :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  letI : Algebra k R :=
    ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source)).hom.toAlgebra
  letI : Algebra k T :=
    ((baseFieldToStructurePresheaf k X).app
      (Opposite.op (X.basicOpen f))).hom.toAlgebra
  letI : Algebra R T := res.toAlgebra
  have hcomp : res.comp
      ((baseFieldToStructurePresheaf k X).app (Opposite.op C.source)).hom =
      ((baseFieldToStructurePresheaf k X).app
        (Opposite.op (X.basicOpen f))).hom := by
    have hnat := (baseFieldToStructurePresheaf k X).naturality
      (homOfLE (X.basicOpen_le f)).op
    exact congrArg CommRingCat.Hom.hom hnat.symm
  letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' hcomp.symm
  letI : IsLocalization.Away f T := C.sourceAffine.isLocalization_basicOpen f
  letI : Module R Aₛ := Module.compHom Aₛ (algebraMap R T)
  letI : IsScalarTower R T Aₛ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let diffMap : A →ₗ[R] Aₛ := _root_.KaehlerDifferential.map k k R T
  haveI hloc : IsLocalizedModule (Submonoid.powers f) diffMap := by
    exact KaehlerDifferential.isLocalizedModule_map k R T (Submonoid.powers f)
  let bₛ : Module.Basis (ULift.{u} (Fin n)) T Aₛ :=
    (C.differentialBasisULift k X).ofIsLocalizedModule T
      (Submonoid.powers f) diffMap
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective
    ((chartBasisHom k X C).app (Opposite.op (chartBasicOpen k X C f))).hom
  have heq : ((chartBasisHom k X C).app
      (Opposite.op (chartBasicOpen k X C f))).hom = bₛ.repr.symm.toLinearMap := by
    let eHom : (ModuleCat.free T).obj (ULift.{u} (Fin n)) ⟶
        ModuleCat.of T Aₛ := ModuleCat.ofHom bₛ.repr.symm.toLinearMap
    have heq' : (chartBasisHom k X C).app
        (Opposite.op (chartBasicOpen k X C f)) = eHom := by
      apply ModuleCat.free_hom_ext
      intro i
      dsimp only [chartBasisHom]
      rw [PresheafOfModules.freeObjDesc_app, ModuleCat.freeDesc_apply]
      dsimp only [chartBasisFamily, restrictionFamily, chartBasicOpen, eHom,
        ModuleCat.ofHom]
      change _ = bₛ.repr.symm (Finsupp.single i 1)
      rw [Module.Basis.repr_symm_single_one,
        Module.Basis.ofIsLocalizedModule_apply]
      rfl
    exact congrArg ModuleCat.Hom.hom heq'
  rw [heq]
  exact bₛ.repr.symm.bijective

private lemma chartBasisHom_mem_W {n : ℕ} {x : X}
    (C : SmoothChart k X n x) :
    ((_root_.Opens.grothendieckTopology X).over C.source).W
      ((PresheafOfModules.toPresheaf _).map (chartBasisHom k X C)) := by
  let p := (PresheafOfModules.toPresheaf _).map (chartBasisHom k X C)
  have hlocal : ∀ (Y : Over C.source) (y : X), y ∈ Y.left →
      ∃ (Z : Over C.source) (g : Z ⟶ Y), y ∈ Z.left ∧
        IsIso (p.app (Opposite.op Z)) := by
    intro Y y hy
    obtain ⟨f, hf, hyf⟩ := C.sourceAffine.exists_basicOpen_le
      (⟨y, hy⟩ : Y.left) (leOfHom Y.hom hy)
    let Z := chartBasicOpen k X C f
    let g : Z ⟶ Y := Over.homMk (homOfLE hf)
    haveI : IsIso ((chartBasisHom k X C).app (Opposite.op Z)) :=
      chartBasisHom_app_basicOpen_isIso k X C f
    haveI : IsIso (p.app (Opposite.op Z)) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso
        ((chartBasisHom k X C).app (Opposite.op Z))
    exact ⟨Z, g, hyf, inferInstance⟩
  obtain ⟨hinj, hsurj⟩ := locallyBijective_over_of_pointwise_iso p hlocal
  letI : Presheaf.IsLocallyInjective
      ((_root_.Opens.grothendieckTopology X).over C.source) p := hinj
  letI : Presheaf.IsLocallySurjective
      ((_root_.Opens.grothendieckTopology X).over C.source) p := hsurj
  exact ((_root_.Opens.grothendieckTopology X).over C.source)
    |>.W_of_isLocallyBijective p

private def familyOfSections {U : X.Opens} {I : Type u}
    (M : SheafOfModules (X.ringCatSheaf.over U))
    (s : I → M.sections) :
    (Functor.const (Over U)ᵒᵖ).obj I ⟶ M.val.presheaf ⋙ forget _ where
  app Y := ↾fun i ↦ (s i).val Y
  naturality Y Z f := by
    ext i
    exact (PresheafOfModules.sections_property (s i) f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
private noncomputable def freeObjGeneratorSection
    {C₀ : Type u} [Category.{u} C₀]
    {R₀ : Functor C₀ᵒᵖ RingCat.{u}} (I : Type u) (i : I) :
    (PresheafOfModules.freeObj
      (R := R₀) ((Functor.const C₀ᵒᵖ).obj I)).sections :=
  PresheafOfModules.sectionsMk (fun Y ↦ ModuleCat.freeMk
    (Eq.mpr (Functor.const_obj_obj C₀ᵒᵖ I Y) i)) (by
    intro Y Z f
    rw [PresheafOfModules.freeObj_map]
    simpa using! (ModuleCat.freeDesc_apply
      (f := ↾fun x ↦ ModuleCat.freeMk
        (((Functor.const C₀ᵒᵖ).obj I).map f x))
      (Eq.mpr (Functor.const_obj_obj C₀ᵒᵖ I Y) i)))

set_option maxHeartbeats 1600000 in
private noncomputable def freeSheafIsoAssociatedFree
    {U : X.Opens} (I : Type u) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      (PresheafOfModules.sheafification
        (𝟙 (X.ringCatSheaf.over U).obj)).obj
          (PresheafOfModules.freeObj
            ((Functor.const (Over U)ᵒᵖ).obj I)) := by
  let P := PresheafOfModules.freeObj
    (R := (X.ringCatSheaf.over U).obj)
    ((Functor.const (Over U)ᵒᵖ).obj I)
  let a := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let A := a.obj P
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)).unit.app P
  let e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ A :=
    (SheafOfModules.freeHomEquiv A).symm (fun i ↦
      PresheafOfModules.sectionsMap eta (freeObjGeneratorSection I i))
  let q : P ⟶ (SheafOfModules.free
      (R := X.ringCatSheaf.over U) I).val :=
    PresheafOfModules.freeObjDesc
      (familyOfSections X _ (fun i ↦ SheafOfModules.freeSection i))
  let d : A ⟶ SheafOfModules.free
      (R := X.ringCatSheaf.over U) I :=
    (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (X.ringCatSheaf.over U).obj)).symm q
  refine ⟨e, d, ?_, ?_⟩
  · apply (SheafOfModules.freeHomEquiv
      (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).injective
    funext i
    rw [SheafOfModules.freeHomEquiv_comp_apply]
    dsimp only [e]
    rw [Equiv.apply_symm_apply]
    change PresheafOfModules.sectionsMap d.val
        (PresheafOfModules.sectionsMap eta (freeObjGeneratorSection I i)) =
      SheafOfModules.freeSection i
    rw [← PresheafOfModules.sectionsMap_comp]
    have hd : eta ≫ d.val = q := by
      change (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (X.ringCatSheaf.over U).obj)) d = q
      exact Equiv.apply_symm_apply _ _
    have hmap := congrArg
      (fun m ↦ PresheafOfModules.sectionsMap m
        (freeObjGeneratorSection I i)) hd
    exact hmap.trans (by
      apply PresheafOfModules.sections_ext
      intro Y
      change q.app Y ((freeObjGeneratorSection I i).val Y) =
        (SheafOfModules.freeSection i).val Y
      change q.app Y (ModuleCat.freeMk
          (Eq.mpr (Functor.const_obj_obj (Over U)ᵒᵖ I Y) i)) =
        (SheafOfModules.freeSection i).val Y
      dsimp only [q]
      rw [PresheafOfModules.freeObjDesc_app]
      exact (ModuleCat.freeDesc_apply
        (f := (familyOfSections X
          (SheafOfModules.free (R := X.ringCatSheaf.over U) I)
          (fun i ↦ SheafOfModules.freeSection i)).app Y)
        (Eq.mpr (Functor.const_obj_obj (Over U)ᵒᵖ I Y) i)))
  · apply (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (X.ringCatSheaf.over U).obj)).injective
    have hd : eta ≫ d.val = q := by
      change (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (X.ringCatSheaf.over U).obj)) d = q
      exact Equiv.apply_symm_apply _ _
    have hqe : q ≫ e.val = eta := by
      apply PresheafOfModules.hom_ext
      intro Y
      apply ModuleCat.free_hom_ext
      intro i
      change I at i
      rw [PresheafOfModules.comp_app]
      change e.val.app Y (q.app Y (ModuleCat.freeMk i)) =
        eta.app Y (ModuleCat.freeMk i)
      dsimp only [q]
      rw [PresheafOfModules.freeObjDesc_app]
      calc
        e.val.app Y
            (ModuleCat.freeDesc
              ((familyOfSections X
                (SheafOfModules.free
                  (R := X.ringCatSheaf.over U) I)
                (fun i ↦ SheafOfModules.freeSection i)).app Y)
              (ModuleCat.freeMk i)) =
            e.val.app Y ((SheafOfModules.freeSection i).val Y) := by
              congr 1
              exact ModuleCat.freeDesc_apply _ _
        _ = eta.app Y (ModuleCat.freeMk i) := by
          have he := congrArg (fun s ↦ s.val Y)
            (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
              (M := A)
              (fun i ↦ PresheafOfModules.sectionsMap eta
                (freeObjGeneratorSection I i)) i)
          dsimp only [e] at he ⊢
          convert he using 1 <;> rfl
    have hmain : eta ≫ (d.val ≫ e.val) = eta := by
      exact (Category.assoc eta d.val e.val).symm.trans
        ((congrArg (fun m ↦ m ≫ e.val) hd).trans hqe)
    change eta ≫ (d ≫ e).val = eta
    change eta ≫ (d.val ≫ e.val) = eta
    exact hmain

private lemma isIso_sheafification_map_chartBasisHom {n : ℕ}
    {x : X} (C : SmoothChart k X n x) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over C.source).obj)).map
        (chartBasisHom k X C)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over C.source).obj))
    (((_root_.Opens.grothendieckTopology X).over C.source).W.inverseImage
      (PresheafOfModules.toPresheaf
        (X.ringCatSheaf.over C.source).obj))
  exact chartBasisHom_mem_W k X C

/-- On a standard-smooth affine chart of relative dimension `n`, the relative cotangent
sheaf is the free sheaf of rank `n`. -/
noncomputable def relativeDifferentialsChartIso {n : ℕ}
    {x : X} (C : SmoothChart k X n x) :
    SheafOfModules.free
        (R := X.ringCatSheaf.over C.source)
        (ULift.{u} (Fin n)) ≅
      (relativeDifferentials k X).over C.source :=
  freeSheafIsoAssociatedFree X (ULift.{u} (Fin n)) ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification
        (𝟙 (X.ringCatSheaf.over C.source).obj)).map
          (chartBasisHom k X C))
      (isIso_sheafification_map_chartBasisHom k X C) ≪≫
    @asIso _ _ _ _
      (Scheme.Modules.overSheafificationComparison
        (relativeDifferentialsPresheaf k X) C.source)
      (Scheme.Modules.isIso_overSheafificationComparison _ _)

/-- Rank-`n` cotangent trivializations on the canonical standard-smooth chart cover. -/
structure SmoothCotangentTrivializations {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) where
  trivialization : ∀ x : X,
    SheafOfModules.free
        (R := X.ringCatSheaf.over ((SmoothChart.ofSmooth k X h x).source))
        (ULift.{u} (Fin n)) ≅
      (relativeDifferentials k X).over ((SmoothChart.ofSmooth k X h x).source)

namespace SmoothCotangentTrivializations

variable {k} {X} {n : ℕ} {h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))}

/-- Smoothness of pure relative dimension canonically supplies the cotangent chart
trivializations. -/
noncomputable def ofSmooth : SmoothCotangentTrivializations k X h where
  trivialization x :=
    relativeDifferentialsChartIso k X (SmoothChart.ofSmooth k X h x)

omit [IsVariety k X] in
/-- The source opens of the chosen smooth charts cover the variety. -/
theorem chartSources_coversTop (_T : SmoothCotangentTrivializations k X h) :
    (_root_.Opens.grothendieckTopology X).CoversTop
      (fun x : X ↦ (SmoothChart.ofSmooth k X h x).source) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr
    ⟨x, (SmoothChart.ofSmooth k X h x).mem_source⟩

/-- Package the smooth-chart comparisons as fixed-rank trivializations of `Ω¹_{X/k}`. -/
noncomputable def fixedRankTrivializations (T : SmoothCotangentTrivializations k X h) :
    Scheme.Modules.FixedRankTrivializations (relativeDifferentials k X) n where
  I := X
  chartOpen x := (SmoothChart.ofSmooth k X h x).source
  coversTop := T.chartSources_coversTop
  trivialization := T.trivialization

/-- The chartwise sheafification comparisons globalize to fixed-rank locally-free cotangent
data. -/
noncomputable def finiteLocallyFree (T : SmoothCotangentTrivializations k X h) :
    Scheme.Modules.FiniteLocallyFreeData (relativeDifferentials k X) n :=
  T.fixedRankTrivializations.finiteLocallyFree

omit [IsVariety k X] in
/-- The constructed relative cotangent sheaf is locally free once the chart comparisons are
supplied. -/
theorem relativeDifferentials_isLocallyFree (T : SmoothCotangentTrivializations k X h) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from relativeDifferentials k X) :=
  T.finiteLocallyFree.isLocallyFree

end SmoothCotangentTrivializations

/-- The relative cotangent sheaf of a smooth pure-dimensional variety is finite locally free of
the relative dimension. -/
noncomputable def relativeDifferentialsFiniteLocallyFree {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    Scheme.Modules.FiniteLocallyFreeData (relativeDifferentials k X) n :=
  (SmoothCotangentTrivializations.ofSmooth (X := X) (h := h)).finiteLocallyFree

/-- The relative cotangent sheaf of a smooth pure-dimensional variety is locally free. -/
theorem relativeDifferentials_isLocallyFree_of_smooth {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from relativeDifferentials k X) :=
  (relativeDifferentialsFiniteLocallyFree k X h).isLocallyFree

/-- Smooth pure relative dimension supplies determinant descent for the relative cotangent
sheaf, including the constructed top exterior power and its explicit tensor inverse. -/
noncomputable def relativeDifferentialsExteriorDeterminantData {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    Scheme.Modules.ExteriorDeterminantData (relativeDifferentials k X) :=
  (SmoothCotangentTrivializations.ofSmooth (X := X) (h := h))
    |>.fixedRankTrivializations.exteriorDeterminantData

/-- The determinant data underlying `relativeDifferentialsExteriorDeterminantData`. -/
noncomputable def relativeDifferentialsDeterminantData {n : ℕ}
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    Scheme.Modules.DeterminantData (relativeDifferentials k X) :=
  (relativeDifferentialsExteriorDeterminantData k X h).determinantData

end Variety

namespace SmoothProperVariety

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsSmoothProperVariety k X] {n : ℕ}

namespace CanonicalSheafData

/-- The automatic canonical-sheaf package of a smooth proper variety of pure relative
dimension `n`. -/
noncomputable def ofSmoothRelativeDifferentials
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    CanonicalSheafData k X n :=
  ofRelativeDifferentials h
    (Variety.relativeDifferentialsDeterminantData k X h) rfl

@[simp]
theorem ofSmoothRelativeDifferentials_cotangent
    (h : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of k))) :
    (ofSmoothRelativeDifferentials h).cotangent =
      Variety.relativeDifferentials k X :=
  rfl

end CanonicalSheafData

end SmoothProperVariety

end AlgebraicGeometry
