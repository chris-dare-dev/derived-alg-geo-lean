/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.MayerVietoris

/-!
# The Mayer–Vietoris sequence of morphisms

Applying `Hom(-, F)` to the Mayer–Vietoris triangle of `E` and using the adjunction `j_! ⊣ j^*`
gives the exact sequence
`⋯ ⟶ Hom(E|_{U∩V}⟦1⟧, F|_{U∩V}) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) × Hom(E|_V, F|_V)
  ⟶ Hom(E|_{U∩V}, F|_{U∩V})`
(Stacks Tag 08BW), where the first map is the connecting map, the second restricts to the two
opens, and the third is the difference of the two restrictions to the intersection.

## Main definitions

* `AlgebraicGeometry.Scheme.mvRes`: restriction of a morphism to the two opens.
* `AlgebraicGeometry.Scheme.mvDiff`: the difference of the restrictions to the intersection.
* `AlgebraicGeometry.Scheme.mvConnect`: the connecting map from
  `Hom(E|_{U∩V}⟦1⟧, F|_{U∩V})`.

## Main results

* `AlgebraicGeometry.Scheme.mvRes_exact_mvDiff`: exactness at
  `Hom(E|_U, F|_U) × Hom(E|_V, F|_V)`.
* `AlgebraicGeometry.Scheme.mvConnect_exact_mvRes`: exactness at `Hom(E, F)`.

## Implementation notes

The statements are for a pullback square of open immersions through the intersection, and
the isomorphisms `cU` and `cV` express the composite restrictions as restriction to the
intersection. `mvDiff` uses them to compare the two restrictions. The proofs are the
exactness of `Hom(-, F)` on a distinguished triangle, with the adjunction used to identify the
maps out of `j_! j^* E`.

## References

* Stacks Project, Tag 08BW.

## Tags

derived category, Mayer–Vietoris, extension by zero, open cover
-/

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits Pretriangulated
open AlgebraicGeometry.DerivedCategory

noncomputable section

variable {Y : Scheme.{u}} {U V : Y.Opens} {W : Scheme.{u}} {kU : W ⟶ U} {kV : W ⟶ V} {w : W ⟶ Y}
  [IsOpenImmersion kU] [IsOpenImmersion kV] [IsOpenImmersion w]

/-- Restriction of morphisms to the two opens. -/
def mvRes (U V : Y.Opens) (E F : SchemeDerivedCategory Y) :
    (E ⟶ F) →+ (((derivedRestrict U.ι).obj E ⟶ (derivedRestrict U.ι).obj F) ×
      ((derivedRestrict V.ι).obj E ⟶ (derivedRestrict V.ι).obj F)) :=
  AddMonoidHom.prod (Functor.mapAddHom (derivedRestrict U.ι))
    (Functor.mapAddHom (derivedRestrict V.ι))

/-- The difference of the two restrictions to the intersection, compared through the
isomorphisms `cU` and `cV`. -/
def mvDiff (cU : derivedRestrict U.ι ⋙ derivedRestrict kU ≅ derivedRestrict w)
    (cV : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
    (E F : SchemeDerivedCategory Y) :
    (((derivedRestrict U.ι).obj E ⟶ (derivedRestrict U.ι).obj F) ×
      ((derivedRestrict V.ι).obj E ⟶ (derivedRestrict V.ι).obj F)) →+
      ((derivedRestrict w).obj E ⟶ (derivedRestrict w).obj F) where
  toFun p := (cU.inv.app E ≫ (derivedRestrict kU).map p.1 ≫ cU.hom.app F) -
    (cV.inv.app E ≫ (derivedRestrict kV).map p.2 ≫ cV.hom.app F)
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]
    abel

section

variable (cU : derivedRestrict U.ι ⋙ derivedRestrict kU ≅ derivedRestrict w)
  (cV : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
  (E F : SchemeDerivedCategory Y)

lemma mvDiff_mvRes (φ : E ⟶ F) : mvDiff cU cV E F (mvRes U V E F φ) = 0 := by
  have e1 : cU.inv.app E ≫ (derivedRestrict kU).map ((derivedRestrict U.ι).map φ) ≫
      cU.hom.app F = (derivedRestrict w).map φ := by
    have := cU.hom.naturality φ
    rw [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  have e2 : cV.inv.app E ≫ (derivedRestrict kV).map ((derivedRestrict V.ι).map φ) ≫
      cV.hom.app F = (derivedRestrict w).map φ := by
    have := cV.hom.naturality φ
    rw [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  change (cU.inv.app E ≫ (derivedRestrict kU).map ((derivedRestrict U.ι).map φ) ≫
      cU.hom.app F) -
    (cV.inv.app E ≫ (derivedRestrict kV).map ((derivedRestrict V.ι).map φ) ≫ cV.hom.app F) = 0
  rw [e1, e2, sub_self]

end

lemma counit_comp_eq {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E F : SchemeDerivedCategory Y} (φ : E ⟶ F) :
    (derivedExtendByZeroAdjunction f).counit.app E ≫ φ =
      ((derivedExtendByZeroAdjunction f).homEquiv _ _).symm ((derivedRestrict f).map φ) := by
  rw [Adjunction.homEquiv_counit]
  exact ((derivedExtendByZeroAdjunction f).counit.naturality φ).symm

/-- A morphism restricts to zero on an open if and only if it is killed by the counit. -/
lemma restrict_map_eq_zero_iff {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E F : SchemeDerivedCategory Y} (φ : E ⟶ F) :
    (derivedRestrict f).map φ = 0 ↔ (derivedExtendByZeroAdjunction f).counit.app E ≫ φ = 0 := by
  rw [counit_comp_eq]
  constructor
  · intro h
    rw [h]
    simp [Adjunction.homEquiv_counit]
  · intro h
    have := congrArg ((derivedExtendByZeroAdjunction f).homEquiv _ _) h
    rw [Equiv.apply_symm_apply] at this
    rw [this, Adjunction.homEquiv_unit]
    simp

/-- A morphism restricts to zero on both opens if and only if it is killed by the second map of
the Mayer–Vietoris triangle. -/
lemma mvRes_eq_zero_iff {E F : SchemeDerivedCategory Y} (φ : E ⟶ F) :
    mvRes U V E F φ = 0 ↔ mvSecond U V E ≫ φ = 0 := by
  rw [mvSecond, mvRes]
  simp only [AddMonoidHom.prod_apply, Functor.mapAddHom_apply, Prod.mk_eq_zero]
  rw [restrict_map_eq_zero_iff, restrict_map_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    apply biprod.hom_ext'
    · simpa using h1
    · simpa using h2
  · intro h
    constructor
    · simpa using congrArg (fun f => biprod.inl ≫ f) h
    · simpa using congrArg (fun f => biprod.inr ≫ f) h

private lemma homEquiv_sub {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [G.Additive] (adj : F ⊣ G) {X : C} {Z : D} (f g : F.obj X ⟶ Z) :
    adj.homEquiv X Z (f - g) = adj.homEquiv X Z f - adj.homEquiv X Z g := by
  simp [Adjunction.homEquiv_unit]

section

variable (cU : derivedRestrict U.ι ⋙ derivedRestrict kU ≅ derivedRestrict w)
  (cV : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
  (hP : IsPullback kU kV U.ι V.ι) (hUV : U ⊔ V = ⊤) (E F : SchemeDerivedCategory Y)

include hP hUV

/-- The Mayer–Vietoris sequence of morphisms is exact at
`Hom(E|_U, F|_U) × Hom(E|_V, F|_V)`: a pair of morphisms that agree on the intersection is the
restriction of a morphism `E ⟶ F`. -/
theorem mvRes_exact_mvDiff : Function.Exact (mvRes U V E F) (mvDiff cU cV E F) := by
  intro p
  constructor
  · intro hp
    let h : (derivedExtendByZero U.ι).obj ((derivedRestrict U.ι).obj E) ⊞
        (derivedExtendByZero V.ι).obj ((derivedRestrict V.ι).obj E) ⟶ F :=
      biprod.desc (((derivedExtendByZeroAdjunction U.ι).homEquiv _ _).symm p.1)
        (((derivedExtendByZeroAdjunction V.ι).homEquiv _ _).symm p.2)
    have hh : mvFirst cU cV E ≫ h = 0 := by
      have e : mvFirst cU cV E ≫ h = thetaApp cU E ≫
          ((derivedExtendByZeroAdjunction U.ι).homEquiv _ _).symm p.1 -
          thetaApp cV E ≫ ((derivedExtendByZeroAdjunction V.ι).homEquiv _ _).symm p.2 := by
        simp [mvFirst, h, sub_eq_add_neg]
      have h0 : (derivedExtendByZeroAdjunction w).homEquiv ((derivedRestrict w).obj E) F
          (0 : (derivedExtendByZero w).obj ((derivedRestrict w).obj E) ⟶ F) = 0 := by
        simp [Adjunction.homEquiv_unit]
      apply ((derivedExtendByZeroAdjunction w).homEquiv _ _).injective
      rw [e, homEquiv_sub, homEquiv_thetaApp, homEquiv_thetaApp, h0]
      simpa [mvDiff] using hp
    obtain ⟨φ₀, hφ₀⟩ := Triangle.yoneda_exact₂ _
      (mayerVietorisTriangleOfSquare_distinguished cU cV hP hUV E) h hh
    obtain ⟨φ, hφ⟩ : ∃ φ : E ⟶ F, mvSecond U V E ≫ φ = h := ⟨φ₀, hφ₀.symm⟩
    refine ⟨φ, ?_⟩
    have h1 : (derivedExtendByZeroAdjunction U.ι).counit.app E ≫ φ =
        ((derivedExtendByZeroAdjunction U.ι).homEquiv _ _).symm p.1 := by
      have := congrArg (fun f => biprod.inl ≫ f) hφ
      simp only [h, mvSecond, ← Category.assoc, biprod.inl_desc] at this
      exact this
    have h2 : (derivedExtendByZeroAdjunction V.ι).counit.app E ≫ φ =
        ((derivedExtendByZeroAdjunction V.ι).homEquiv _ _).symm p.2 := by
      have := congrArg (fun f => biprod.inr ≫ f) hφ
      simp only [h, mvSecond, ← Category.assoc, biprod.inr_desc] at this
      exact this
    rw [counit_comp_eq] at h1 h2
    exact Prod.ext (Equiv.injective _ h1) (Equiv.injective _ h2)
  · rintro ⟨φ, rfl⟩
    exact mvDiff_mvRes cU cV E F φ

/-- The third map of the Mayer–Vietoris triangle. -/
def mvDelta : E ⟶ ((derivedExtendByZero w).obj ((derivedRestrict w).obj E))⟦(1 : ℤ)⟧ :=
  (mayerVietorisTriangleOfSquare cU cV hP hUV E).mor₃

/-- The connecting map from the negative `Ext` group
`Hom(E|_{U∩V}⟦1⟧, F|_{U∩V})` on the intersection to `Hom(E, F)`. -/
def mvConnect :
    ((((derivedRestrict w).obj E)⟦(1 : ℤ)⟧ ⟶ (derivedRestrict w).obj F)) →+ (E ⟶ F) where
  toFun ψ := mvDelta cU cV hP hUV E ≫
    ((derivedExtendByZero w).commShiftIso (1 : ℤ)).inv.app ((derivedRestrict w).obj E) ≫
      ((derivedExtendByZeroAdjunction w).homEquiv _ _).symm ψ
  map_zero' := by simp [Adjunction.homEquiv_counit]
  map_add' ψ ψ' := by simp [Adjunction.homEquiv_counit]

/-- The Mayer–Vietoris sequence of morphisms is exact at `Hom(E, F)`: a morphism that restricts
to zero on `U` and on `V` comes from the negative `Ext` group of the intersection. -/
theorem mvConnect_exact_mvRes :
    Function.Exact (mvConnect cU cV hP hUV E F) (mvRes U V E F) := by
  intro φ
  have hT := mayerVietorisTriangleOfSquare_distinguished cU cV hP hUV E
  constructor
  · intro hφ
    have h0 : (mayerVietorisTriangleOfSquare cU cV hP hUV E).mor₂ ≫ φ = 0 :=
      (mvRes_eq_zero_iff φ).1 hφ
    obtain ⟨g, hg⟩ : ∃ g : ((derivedExtendByZero w).obj ((derivedRestrict w).obj E))⟦(1 : ℤ)⟧ ⟶ F,
        φ = mvDelta cU cV hP hUV E ≫ g := Triangle.yoneda_exact₃ _ hT φ h0
    refine ⟨((derivedExtendByZeroAdjunction w).homEquiv _ _)
      (((derivedExtendByZero w).commShiftIso (1 : ℤ)).hom.app ((derivedRestrict w).obj E) ≫ g),
      ?_⟩
    simp only [mvConnect, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply]
    erw [Iso.inv_hom_id_app_assoc]
    exact hg.symm
  · rintro ⟨ψ, rfl⟩
    rw [mvRes_eq_zero_iff]
    simp only [mvConnect, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have h0 : mvSecond U V E ≫ mvDelta cU cV hP hUV E = 0 := comp_distTriang_mor_zero₂₃ _ hT
    rw [reassoc_of% h0, zero_comp]

end

section Opens

variable (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (E F : SchemeDerivedCategory Y)

include hUV

/-- **The Mayer–Vietoris sequence of morphisms** (Stacks Tag 08BW), exact at
`Hom(E|_U, F|_U) × Hom(E|_V, F|_V)`, for `Y = U ∪ V`. -/
theorem mayerVietoris_exact_mvRes_mvDiff :
    Function.Exact (mvRes U V E F)
      (mvDiff (restrictCompInfLeft U V) (restrictCompInfRight U V) E F) :=
  mvRes_exact_mvDiff _ _ (isPullback_opens_inf U V) hUV E F

/-- **The Mayer–Vietoris sequence of morphisms** (Stacks Tag 08BW), exact at `Hom(E, F)`, for
`Y = U ∪ V`. -/
theorem mayerVietoris_exact_mvConnect_mvRes :
    Function.Exact
      (mvConnect (restrictCompInfLeft U V) (restrictCompInfRight U V)
        (isPullback_opens_inf U V) hUV E F) (mvRes U V E F) :=
  mvConnect_exact_mvRes _ _ _ _ E F

end Opens

end

end AlgebraicGeometry.Scheme
