/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.ChangeOfRings
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Invertible
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Twisting sheaves along `Proj.map`

Let `ψ : 𝒜 →+*ᵍ ℬ` be a graded ring map with `ℬ₊ ≤ √(ψ(𝒜₊))`, so that Mathlib's
`Proj.map ψ : Proj ℬ ⟶ Proj 𝒜` is defined. A semilinear map of graded modules `g : M → N` over
`ψ` induces `M̃ ⟶ (Proj.map ψ)_* Ñ`, fibrewise `m / s ↦ g m / ψ s`. For the twisting sheaves its
adjoint is the comparison

    θ : (Proj.map ψ)^* 𝒪_{Proj 𝒜}(d) ⟶ 𝒪_{Proj ℬ}(d)

of Stacks 01MY, and it is an isomorphism once `𝒜` is generated in degree one over `𝒜 0`.

## Main definitions

* `AlgebraicGeometry.Proj.associatedSheafMapOfRingHom`: `M̃ ⟶ (Proj.map ψ)_* Ñ`.
* `AlgebraicGeometry.Proj.twistingSheafMapOfRingHom`: its case `𝒪(d) ⟶ (Proj.map ψ)_* 𝒪(d)`.
* `AlgebraicGeometry.Proj.mapPullbackTwistingSheaf`: the adjoint
  `θ : (Proj.map ψ)^* 𝒪(d) ⟶ 𝒪(d)`.
* `AlgebraicGeometry.Proj.mapPullbackTwistingSheafIso`: `θ` as an isomorphism, for `𝒜` generated
  in degree one.

## Main results

* `AlgebraicGeometry.Proj.mapPullbackTwistingSheaf_app_unit`: `θ` sends the pullback of a section
  `s` to the image of `s` under `a / t ↦ ψ a / ψ t`.
* `AlgebraicGeometry.Proj.isIso_mapPullbackTwistingSheaf`: `θ` is an isomorphism when `𝒜` is
  generated in degree one over `𝒜 0`.

## Implementation notes

The isomorphism is checked on the preimages `D₊(ψ f)` of the degree-one charts `D₊(f)`, which
cover `Proj ℬ`. There `𝒪(d)` is trivialized by `f^{d⁺} / f^{d⁻}` on `Proj 𝒜` and by its image
`(ψ f)^{d⁺} / (ψ f)^{d⁻}` on `Proj ℬ`, and `θ` sends the pullback of the first to the second. So
`θ` is a split epimorphism between two modules isomorphic to the unit; the endomorphisms of the
unit commute, being multiplications by sections of the structure sheaf, so `θ` is an
isomorphism there. Local bijectivity on a cover then makes it one globally.

Nothing here is specific to base change or to projective space: for the base change
`𝒜 → S ⊗[R] 𝒜` of `Proj.isPullback_map_baseChange` and for `ℤ[n] → R[n]` this is the `θ` of
Stacks 01N2, and the same map along a surjective graded ring map is the `θ` of Stacks 01N0/01N1.

## References

* [Stacks, Lemma 27.11.1 (Tag 01MY)](https://stacks.math.columbia.edu/tag/01MY).
* [Stacks, Lemma 27.11.5 (Tag 01N1)](https://stacks.math.columbia.edu/tag/01N1).
* [Stacks, Lemma 27.11.6 (Tag 01N2)](https://stacks.math.columbia.edu/tag/01N2).

## Tags

Proj, twisting sheaf, pullback, functoriality, graded ring map
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A B M N σA σB σM σN : Type u}
variable [CommRing A] [CommRing B] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [SetLike σA A] [AddSubgroupClass σA A] [SetLike σB B] [AddSubgroupClass σB B]
variable [SetLike σM M] [AddSubgroupClass σM M] [SetLike σN N] [AddSubgroupClass σN N]
variable {𝒜 : ℕ → σA} {ℬ : ℕ → σB} (𝓜 : ℕ → σM) (𝓝 : ℕ → σN)
variable [GradedRing 𝒜] [GradedRing ℬ] [SetLike.GradedSMul 𝒜 𝓜] [SetLike.GradedSMul ℬ 𝓝]
variable (ψ : 𝒜 →+*ᵍ ℬ)
  (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
variable (g : M →ₛₗ[ψ.toRingHom] N) (hg : ∀ i (m : M), m ∈ 𝓜 i → g m ∈ 𝓝 i)

lemma primeCompl_comap_le (y : ProjectiveSpectrum ℬ) :
    (ProjectiveSpectrum.comap ψ hψ y).asHomogeneousIdeal.toIdeal.primeCompl ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl.comap ψ :=
  fun _ h ↦ h

/-- The fibre at `y ∈ Proj ℬ` of the map `M̃ → (Proj.map ψ)_* Ñ`: `m / s ↦ g m / ψ s`. -/
def fiberMapOfRingHom (y : ProjectiveSpectrum ℬ) :
    Fiber 𝒜 𝓜 (ProjectiveSpectrum.comap ψ hψ y) →+ Fiber ℬ 𝓝 y :=
  DegreeZeroLocalization.mapOfRingHom ψ g (primeCompl_comap_le ψ hψ y) hg

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A locally fractional section of `M̃` over `U` gives one of `Ñ` over the preimage of `U`. -/
def sectionMapOfRingHom (U : Opens (ProjectiveSpectrum.top 𝒜))
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) :
    (associatedSheafInType ℬ 𝓝).1.obj (op ((map ψ hψ) ⁻¹ᵁ U)) := by
  refine ⟨fun y ↦ fiberMapOfRingHom 𝓜 𝓝 ψ hψ g hg y.1 (s.1 ⟨_, y.2⟩), ?_⟩
  intro y
  obtain ⟨V, hyV, i, d, r, t, ht, e⟩ := s.2 ⟨_, y.2⟩
  refine ⟨(map ψ hψ) ⁻¹ᵁ V, hyV, homOfLE fun z hz ↦ (leOfHom i) hz, d,
    ⟨g r, hg d r r.2⟩, ⟨ψ t, ψ.map_mem t.2⟩, fun z ↦ ht ⟨_, z.2⟩, fun z ↦ ?_⟩
  exact (congrArg (fiberMapOfRingHom 𝓜 𝓝 ψ hψ g hg z.1) (e ⟨_, z.2⟩)).trans
    (DegreeZeroLocalization.mapOfRingHom_mk ψ g _ hg _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem sectionMapOfRingHom_apply (U : Opens (ProjectiveSpectrum.top 𝒜))
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) (y : (map ψ hψ) ⁻¹ᵁ U) :
    (sectionMapOfRingHom 𝓜 𝓝 ψ hψ g hg U s).1 y =
      fiberMapOfRingHom 𝓜 𝓝 ψ hψ g hg y.1 (s.1 ⟨_, y.2⟩) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The map `M̃ ⟶ (Proj.map ψ)_* Ñ` of presheaves of modules, fibrewise `m / s ↦ g m / ψ s`. -/
def associatedPresheafMapOfRingHom :
    associatedPresheaf 𝒜 𝓜 ⟶
      ((Scheme.Modules.pushforward (map ψ hψ)).obj (associatedSheaf ℬ 𝓝)).val where
  app U := ModuleCat.homMk
    (AddCommGrpCat.ofHom
      { toFun := fun s ↦ sectionMapOfRingHom 𝓜 𝓝 ψ hψ g hg U.unop s
        map_zero' := by
          apply section_ext
          funext y
          exact map_zero (fiberMapOfRingHom 𝓜 𝓝 ψ hψ g hg y.1)
        map_add' := fun s t ↦ by
          apply section_ext
          funext y
          exact map_add (fiberMapOfRingHom 𝓜 𝓝 ψ hψ g hg y.1) _ _ })
    (fun r ↦ by
      ext s
      apply section_ext
      funext y
      exact (DegreeZeroLocalization.mapOfRingHom_smul ψ g _ hg
        (AlgebraicGeometry.openToLocalization 𝒜 U.unop _ y.2 r) (s.1 ⟨_, y.2⟩)).symm)
  naturality := by
    intro U V i
    ext s
    apply section_ext
    funext y
    rfl

/-- The map `M̃ ⟶ (Proj.map ψ)_* Ñ`, fibrewise `m / s ↦ g m / ψ s`. -/
def associatedSheafMapOfRingHom :
    associatedSheaf 𝒜 𝓜 ⟶ (Scheme.Modules.pushforward (map ψ hψ)).obj (associatedSheaf ℬ 𝓝) :=
  (Scheme.Modules.toPresheafOfModules (AlgebraicGeometry.Proj 𝒜)).preimage
    (associatedPresheafMapOfRingHom 𝓜 𝓝 ψ hψ g hg)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem associatedSheafMapOfRingHom_app (U : Opens (ProjectiveSpectrum.top 𝒜))
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) :
    ((associatedSheafMapOfRingHom 𝓜 𝓝 ψ hψ g hg).app U s :
        (associatedSheafInType ℬ 𝓝).1.obj (op ((map ψ hψ) ⁻¹ᵁ U))) =
      sectionMapOfRingHom 𝓜 𝓝 ψ hψ g hg U s := by
  change ((((Scheme.Modules.toPresheafOfModules (AlgebraicGeometry.Proj 𝒜)).map
    (associatedSheafMapOfRingHom 𝓜 𝓝 ψ hψ g hg)).app (op U)) s :
      (associatedSheafInType ℬ 𝓝).1.obj (op ((map ψ hψ) ⁻¹ᵁ U))) = _
  rw [associatedSheafMapOfRingHom, CategoryTheory.Functor.map_preimage]
  rfl

/-! ## The comparison `θ` for twisting sheaves -/

section TwistingSheaf

variable {𝓜 𝓝 g hg}

omit [GradedRing 𝒜] [GradedRing ℬ] in
lemma map_mem_intShift (d : ℤ) (i : ℕ) (a : A) (ha : a ∈ intShift 𝒜 d i) :
    ψ a ∈ intShift ℬ d i := by
  simp only [intShift_apply, mem_intShiftPiece] at ha ⊢
  rcases ha with rfl | ⟨k, hk, ha⟩
  · exact Or.inl (map_zero ψ)
  · exact Or.inr ⟨k, hk, ψ.map_mem ha⟩

/-- `𝒪(d) ⟶ (Proj.map ψ)_* 𝒪(d)`, fibrewise `a / s ↦ ψ a / ψ s`. -/
def twistingSheafMapOfRingHom (d : ℤ) :
    twistingSheaf 𝒜 d ⟶ (Scheme.Modules.pushforward (map ψ hψ)).obj (twistingSheaf ℬ d) :=
  associatedSheafMapOfRingHom (intShift 𝒜 d) (intShift ℬ d) ψ hψ ψ.toRingHom.toSemilinearMap
    (map_mem_intShift ψ d)

/-- **The comparison `θ : (Proj.map ψ)^* 𝒪(d) ⟶ 𝒪(d)`** (Stacks 01MY), adjoint to
`twistingSheafMapOfRingHom`. It is an isomorphism once `𝒜` is generated in degree one
(`isIso_mapPullbackTwistingSheaf`), and not in general. -/
def mapPullbackTwistingSheaf (d : ℤ) :
    (Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d) ⟶ twistingSheaf ℬ d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).homEquiv _ _).symm
    (twistingSheafMapOfRingHom ψ hψ d)

/-- `θ` sends the pullback of a section `s` of `𝒪(d)` to `s` pushed through `a / t ↦ ψ a / ψ t`. -/
theorem mapPullbackTwistingSheaf_app_unit (d : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (s : Γ(twistingSheaf 𝒜 d, U)) :
    (mapPullbackTwistingSheaf ψ hψ d).app ((map ψ hψ) ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).unit.app
          (twistingSheaf 𝒜 d)).app U) s) =
      (twistingSheafMapOfRingHom ψ hψ d).app U s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).homEquiv _ _
    ).apply_symm_apply (twistingSheafMapOfRingHom ψ hψ d)
  rw [Adjunction.homEquiv_unit] at h
  rw [← h]
  rfl

end TwistingSheaf

/-! ## Trivializations on degree-one charts, on sections -/

section Trivialization

variable (𝒜)

/-- `𝒪(d)` is trivial over any open inside a degree-one chart `D₊(f)`. -/
private def twistingSheafOverUnitIsoOfLE {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {V : (AlgebraicGeometry.Proj 𝒜).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    SheafOfModules.unit ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.over V) ≅
      (show SheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf from
        twistingSheaf 𝒜 d).over V :=
  Iso.refl _ ≪≫
    ((SheafOfModules.overFunctor _ V).mapIso (associatedSheafSelfIso 𝒜)).symm ≪≫
      ((SheafOfModules.overFunctor _ V).mapIso (intShiftZeroIso 𝒜)).symm ≪≫
        (intShiftOverIso 𝒜 hf d hV).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The generator of `𝒪(d)` over `V ⊆ D₊(f)` is `f^{d⁺} / f^{d⁻}` at every point. -/
private lemma twistingSheafOverUnitIsoOfLE_hom_one {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {V : (AlgebraicGeometry.Proj 𝒜).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (x : V) :
    ((((twistingSheafOverUnitIsoOfLE 𝒜 hf d hV).hom.val.app (op (Over.mk (𝟙 V)))
        (1 : ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.over V).obj.obj (op (Over.mk (𝟙 V)))) :
        (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op V)).1 x :
          Fiber 𝒜 (intShift 𝒜 d) x.1) :
            LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) =
      LocalizedModule.mk (f ^ d.toNat)
        ⟨f ^ (-d).toNat, (x.1.asHomogeneousIdeal.toIdeal.primeCompl).pow_mem (hV x.2) _⟩ := by
  simp only [twistingSheafOverUnitIsoOfLE, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    Functor.mapIso_inv, Category.id_comp, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  have hc : ∀ s, ((((ConcreteCategory.hom
      ((intShiftOverIso 𝒜 hf d hV).inv.val.app (op (Over.mk (𝟙 V))))) s :
        (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op V)).1 x :
          Fiber 𝒜 (intShift 𝒜 d) x.1) :
            LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) =
      Localization.mk (f ^ d.toNat)
        ⟨f ^ (-d).toNat, (x.1.asHomogeneousIdeal.toIdeal.primeCompl).pow_mem (hV x.2) _⟩ •
        (((s : (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op V)).1 x :
          Fiber 𝒜 (intShift 𝒜 0) x.1) : LocalizedModule _ A) :=
    fun _ ↦ rfl
  have hzero : ∀ s, ((((ConcreteCategory.hom
      (((SheafOfModules.overFunctor _ V).map (intShiftZeroIso 𝒜).inv).val.app
        (op (Over.mk (𝟙 V))))) s : (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op V)).1 x :
          Fiber 𝒜 (intShift 𝒜 0) x.1) :
            LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) =
      (((s : (associatedSheafInType 𝒜 𝒜).1.obj (op V)).1 x : Fiber 𝒜 𝒜 x.1) :
        LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) := by
    intro s
    change (((associatedMap (𝓜 := 𝒜) 𝒜 (intShift 𝒜 0)
      (identityGradedMap (𝓜 := 𝒜) (intShift 𝒜 0)
        fun i m hm => (mem_intShift_zero_iff 𝒜 i m).mpr hm)).app V s).1 x :
          LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) = _
    rw [associatedMap_app_apply]
    obtain ⟨c, hc⟩ := DegreeZeroLocalization.mk_surjective (s.1 x)
    rw [← hc, GradedLinearMap.map_mk]
    rfl
  have hself : ((((ConcreteCategory.hom
      (((SheafOfModules.overFunctor _ V).map (associatedSheafSelfIso 𝒜).inv).val.app
        (op (Over.mk (𝟙 V)))))
        (1 : ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.over V).obj.obj (op (Over.mk (𝟙 V)))) :
          (associatedSheafInType 𝒜 𝒜).1.obj (op V)).1 x : Fiber 𝒜 𝒜 x.1) :
            LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) =
      LocalizedModule.mk 1 1 := by
    change ((((ConcreteCategory.hom ((associatedSheafSelfIso 𝒜).inv.val.app (op V)))
      (1 : (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.obj (op V)) :
        (associatedSheafInType 𝒜 𝒜).1.obj (op V)).1 x : Fiber 𝒜 𝒜 x.1) :
          LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) = _
    rw [show (associatedSheafSelfIso 𝒜).inv.val = (associatedPresheafSelfIso 𝒜).inv from
      (SheafOfModules.fullyFaithfulForget (AlgebraicGeometry.Proj 𝒜).ringCatSheaf).map_preimage
        (X := SheafOfModules.unit _) (Y := associatedSheaf 𝒜 𝒜) (associatedPresheafSelfIso 𝒜).inv]
    change (((selfFiberLinearEquiv 𝒜 x.1).symm (HomogeneousLocalization.mk 1) : Fiber 𝒜 𝒜 x.1) :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl A) = _
    rw [selfFiberLinearEquiv_symm_apply_mk, DegreeZeroLocalization.coe_mk,
      NumDenSameDeg.embedding]
    rfl
  refine (hc _).trans ((congrArg (fun z ↦ Localization.mk (f ^ d.toNat)
    ⟨f ^ (-d).toNat, (x.1.asHomogeneousIdeal.toIdeal.primeCompl).pow_mem (hV x.2) _⟩ • z)
      ((hzero _).trans hself)).trans ?_)
  rw [LocalizedModule.mk_smul_mk, smul_eq_mul, mul_one, mul_one]

end Trivialization

/-! ## `θ` is an isomorphism on degree-one charts -/

section Chart

/-- An endomorphism of the unit module, evaluated on a section of the structure sheaf. -/
private def unitEndApp {Y : Scheme.{u}} {W : Y.Opens}
    (φ : SheafOfModules.unit (Y.ringCatSheaf.over W) ⟶
      SheafOfModules.unit (Y.ringCatSheaf.over W)) (j : (Over W)ᵒᵖ)
    (a : (Y.ringCatSheaf.over W).obj.obj j) : (Y.ringCatSheaf.over W).obj.obj j :=
  φ.val.app j a

private lemma unitEndApp_eq {Y : Scheme.{u}} {W : Y.Opens}
    (φ : SheafOfModules.unit (Y.ringCatSheaf.over W) ⟶
      SheafOfModules.unit (Y.ringCatSheaf.over W)) (j : (Over W)ᵒᵖ)
    (a : (Y.ringCatSheaf.over W).obj.obj j) :
    unitEndApp φ j a = a * unitEndApp φ j 1 :=
  calc unitEndApp φ j a = unitEndApp φ j (a * 1) := by rw [mul_one]
    _ = a * unitEndApp φ j 1 :=
      (φ.val.app j).hom.map_smul a (1 : (Y.ringCatSheaf.over W).obj.obj j)

/-- Endomorphisms of the unit module over an open of a scheme commute: each is multiplication by
a section of the commutative structure sheaf. -/
private lemma unit_endo_comm {Y : Scheme.{u}} {W : Y.Opens}
    (u v : SheafOfModules.unit (Y.ringCatSheaf.over W) ⟶
      SheafOfModules.unit (Y.ringCatSheaf.over W)) :
    u ≫ v = v ≫ u := by
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext j
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  change unitEndApp v j (unitEndApp u j 1) = unitEndApp u j (unitEndApp v j 1)
  rw [unitEndApp_eq v j (unitEndApp u j 1), unitEndApp_eq u j (unitEndApp v j 1)]
  exact mul_comm (G := Γ(Y, j.unop.left)) _ _

/-- A section of a module over the slice of an open `W` is determined by its value on `W`. -/
private lemma sections_ext_top {Y : Scheme.{u}} {W : Y.Opens}
    {M : SheafOfModules (Y.ringCatSheaf.over W)} (s t : M.sections)
    (h : s.val (op (Over.mk (𝟙 W))) = t.val (op (Over.mk (𝟙 W)))) : s = t := by
  apply Subtype.ext
  funext j
  let g : op (Over.mk (𝟙 W)) ⟶ j := (Over.homMk j.unop.hom : j.unop ⟶ Over.mk (𝟙 W)).op
  rw [← s.property g, ← t.property g, h]

variable {f : A} (hf : f ∈ 𝒜 1) (d : ℤ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
  (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)

/-- The generator `f^{d⁺} / f^{d⁻}` of `𝒪(d)` over `U ⊆ D₊(f)`. -/
private def chartGenerator : Γ(twistingSheaf 𝒜 d, U) :=
  (twistingSheafOverUnitIsoOfLE 𝒜 hf d hU).hom.val.app (op (Over.mk (𝟙 U)))
    (1 : ((AlgebraicGeometry.Proj 𝒜).ringCatSheaf.over U).obj.obj (op (Over.mk (𝟙 U))))

/-- The pullback of `chartGenerator` along `Proj.map ψ`, restricted to every open of
`(Proj.map ψ)⁻¹ U`. -/
private def pullbackChartGenerator :
    (((Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d)).over
      ((map ψ hψ) ⁻¹ᵁ U)).sections where
  val j := ((Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d)).presheaf.map
    j.unop.hom.op ((((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).unit.app
      (twistingSheaf 𝒜 d)).app U) (chartGenerator hf d hU))
  property {j j'} g := by
    change ((Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d)).presheaf.map _
      (((Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d)).presheaf.map _ _) = _
    erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `θ` sends the pulled-back generator of `𝒪(d)` to the generator of `𝒪(d)` on `Proj ℬ`. -/
private lemma mapPullbackTwistingSheaf_pullbackChartGenerator :
    (mapPullbackTwistingSheaf ψ hψ d).app ((map ψ hψ) ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).unit.app
          (twistingSheaf 𝒜 d)).app U) (chartGenerator hf d hU)) =
      chartGenerator (ψ.map_mem hf) d (U := (map ψ hψ) ⁻¹ᵁ U) (fun _ hy ↦ hU hy) := by
  rw [mapPullbackTwistingSheaf_app_unit, twistingSheafMapOfRingHom]
  refine (associatedSheafMapOfRingHom_app (intShift 𝒜 d) (intShift ℬ d) ψ hψ _ _ U _).trans ?_
  apply section_ext
  funext y
  apply DegreeZeroLocalization.ext
  rw [sectionMapOfRingHom_apply]
  refine (congrArg (localizedMapOfRingHom ψ ψ.toRingHom.toSemilinearMap
    (primeCompl_comap_le ψ hψ y.1))
      (twistingSheafOverUnitIsoOfLE_hom_one 𝒜 hf d hU ⟨_, y.2⟩)).trans ?_
  refine Eq.trans ?_ (twistingSheafOverUnitIsoOfLE_hom_one ℬ (ψ.map_mem hf) d _ y).symm
  rw [localizedMapOfRingHom_mk]
  simp only [RingHom.coe_toSemilinearMap, GradedRingHom.coe_toRingHom, map_pow]

include hf hU in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `θ` is an isomorphism over the preimage of an open inside a degree-one chart: it is a split
epimorphism there, between two modules isomorphic to the unit, whose endomorphisms commute. -/
private lemma isIso_over_mapPullbackTwistingSheaf :
    IsIso ((SheafOfModules.overFunctor _ ((map ψ hψ) ⁻¹ᵁ U)).map
      (mapPullbackTwistingSheaf ψ hψ d)) := by
  have hW : (map ψ hψ) ⁻¹ᵁ U ≤ ProjectiveSpectrum.basicOpen ℬ (ψ f) := fun _ hy ↦ hU hy
  let E₁ := Scheme.Modules.pullbackTrivializationOver (map ψ hψ) (twistingSheaf 𝒜 d) U
    (twistingSheafOverUnitIsoOfLE 𝒜 hf d hU)
  let E₂ := twistingSheafOverUnitIsoOfLE ℬ (ψ.map_mem hf) d hW
  let θW := (SheafOfModules.overFunctor _ ((map ψ hψ) ⁻¹ᵁ U)).map
    (mapPullbackTwistingSheaf ψ hψ d)
  let τ := (SheafOfModules.unitHomEquiv _).symm (pullbackChartGenerator ψ hψ hf d hU)
  have hT : (pullbackChartGenerator ψ hψ hf d hU).val (op (Over.mk (𝟙 _))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (map ψ hψ)).unit.app
        (twistingSheaf 𝒜 d)).app U) (chartGenerator hf d hU) := by
    change ((Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d)).presheaf.map
      (𝟙 _) _ = _
    erw [CategoryTheory.Functor.map_id]
    rfl
  have key : τ ≫ θW = E₂.hom := by
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply sections_ext_top
    rw [SheafOfModules.unitHomEquiv_apply_coe]
    change θW.val.app _ ((pullbackChartGenerator ψ hψ hf d hU).val _) = _
    rw [hT]
    exact mapPullbackTwistingSheaf_pullbackChartGenerator ψ hψ hf d hU
  let u := E₁.hom ≫ θW ≫ E₂.inv
  let v := τ ≫ E₁.inv
  have hvu : v ≫ u = 𝟙 _ := by
    simp only [u, v, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% key, Iso.hom_inv_id]
  have huv : u ≫ v = 𝟙 _ := (unit_endo_comm u v).trans hvu
  have : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hθ : θW = E₁.inv ≫ u ≫ E₂.hom := by simp [u]
  change IsIso θW
  rw [hθ]
  infer_instance

end Chart

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **`θ` is an isomorphism** as soon as `𝒜` is generated in degree one over `𝒜 0` (Stacks 01MY,
01N1): on each preimage of a degree-one chart it is, and those preimages cover `Proj ℬ`.

The degree-one hypothesis is needed: for `A = k[x²] ⊆ k[x]` the twisting sheaf `𝒪(1)` of
`Proj A` is zero while that of `Proj k[x]` is not. -/
theorem isIso_mapPullbackTwistingSheaf {I : Type u} (g : I → 𝒜 1)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) (d : ℤ) :
    IsIso (mapPullbackTwistingSheaf ψ hψ d) := by
  let V : I → (AlgebraicGeometry.Proj ℬ).Opens := fun i ↦
    (map ψ hψ) ⁻¹ᵁ (standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange
  have hV : (Opens.grothendieckTopology (AlgebraicGeometry.Proj ℬ)).CoversTop V :=
    (map ψ hψ).coversTop_preimage (degreeOneCharts_coversTop 𝒜 g hg)
  have hloc (i : I) : IsIso (Functor.whiskerLeft (Over.forget (V i)).op
      ((SheafOfModules.toSheaf _).map (mapPullbackTwistingSheaf ψ hψ d)).hom) := by
    have := isIso_over_mapPullbackTwistingSheaf ψ hψ (g i).2 d
      (standardAway_degreeOne_opensRange_le 𝒜 (g i))
    exact (inferInstance : IsIso ((SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _).map
      ((SheafOfModules.overFunctor _ (V i)).map (mapPullbackTwistingSheaf ψ hψ d))))
  have : IsIso ((SheafOfModules.toSheaf _).map (mapPullbackTwistingSheaf ψ hψ d)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨Presheaf.isLocallyInjective_of_coversTop _ V hV fun _ ↦ inferInstance,
        Presheaf.isLocallySurjective_of_coversTop _ V hV fun _ ↦ inferInstance⟩
  rw [← isIso_iff_of_reflects_iso _ (Scheme.Modules.toPresheaf _)]
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map
    ((SheafOfModules.toSheaf _).map (mapPullbackTwistingSheaf ψ hψ d))))

/-- **`θ` as an isomorphism `(Proj.map ψ)^* 𝒪(d) ≅ 𝒪(d)`**, for `𝒜` generated in degree one. -/
def mapPullbackTwistingSheafIso {I : Type u} (g : I → 𝒜 1)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) (d : ℤ) :
    (Scheme.Modules.pullback (map ψ hψ)).obj (twistingSheaf 𝒜 d) ≅ twistingSheaf ℬ d :=
  haveI := isIso_mapPullbackTwistingSheaf ψ hψ g hg d
  asIso (mapPullbackTwistingSheaf ψ hψ d)

@[simp]
lemma mapPullbackTwistingSheafIso_hom {I : Type u} (g : I → 𝒜 1)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) (d : ℤ) :
    (mapPullbackTwistingSheafIso ψ hψ g hg d).hom = mapPullbackTwistingSheaf ψ hψ d :=
  rfl

end AlgebraicGeometry.Proj
