/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearCopower
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Linear

/-!
# Functoriality of scalar-linear dg copowers

A degree-`p` element of `HomComplex.Cochain K L p` induces a degree-`p`
morphism between any chosen scalar-linear copowers of a fixed dg object `X`:
compose the cochain with the target universal chain map, then apply the source
representing inverse.  This construction is linear, commutes with
differentials, and preserves graded composition strictly.

Consequently, when all scalar-linear copowers exist, the selected objects form
a linear dg functor `C^dg(ModuleCat k) ⟶ C`.  At witness level,
homotopy-equivalent coefficient complexes induce isomorphic copowers in `H⁰`.
The specialized comparison through Mathlib's homotopy category lives with the
`H⁰(C^dg)` enhancement seam.

This is homotopy invariance, not quasi-isomorphism invariance.  No boundedness,
finite-dimensionality, shift decomposition, Euler-class formula, cone
preservation, or concrete copower instance is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace IsLinearCopowerOf

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {K L M : CochainComplex (ModuleCat.{v} k) ℤ}
  {X ZK ZL ZM : C}

/-- The representing map from a linear copower is a morphism of Hom-complexes. -/
lemma linearCopowerCochain_d
    (tK : IsLinearCopowerOf k K X ZK) (W : C) (p q : ℤ)
    (f : (dgHom ZK W).X p) :
    CochainComplex.HomComplex.δ p q
        (linearCopowerCochain k tK.univ p f) =
      linearCopowerCochain k tK.univ q
        (((dgHom ZK W).d p q).hom f) := by
  change CochainComplex.HomComplex.δ p q
      ((CochainComplex.HomComplex.Cochain.ofHom tK.univ).comp
        (DGLinear.postcompCochain k X p f) (zero_add p)) = _
  rw [CochainComplex.HomComplex.δ_ofHom_comp,
    DGLinear.postcompCochain_d]
  rfl

/-- The universal property as an isomorphism of Hom-complexes.  This packages
all degrees and the compatibility with differentials in one categorical
interface. -/
noncomputable def homComplexIso (tK : IsLinearCopowerOf k K X ZK) (W : C) :
    DGLinear.homComplex k ZK W ≅
      DGLinear.homComplex (C := Cdg (ModuleCat.{v} k)) k
        (show Cdg (ModuleCat.{v} k) from K)
        (show Cdg (ModuleCat.{v} k) from DGLinear.homComplex k X W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (tK.cochainLinearEquiv W p).toModuleIso) (by
      intro p q _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact tK.linearCopowerCochain_d W p q f)

lemma homComplexIso_hom_f_apply
    (tK : IsLinearCopowerOf k K X ZK) (W : C) (p : ℤ)
    (f : (dgHom ZK W).X p) :
    ((tK.homComplexIso W).hom.f p).hom f =
      linearCopowerCochain k tK.univ p f := rfl

lemma homComplexIso_inv_f_apply
    (tK : IsLinearCopowerOf k K X ZK) (W : C) (p : ℤ)
    (γ : CochainComplex.HomComplex.Cochain K
      (DGLinear.homComplex k X W) p) :
    ((tK.homComplexIso W).inv.f p).hom γ = tK.lift p γ := rfl

/-- The representing inverse intertwines Mathlib's Hom-complex differential
with the dg differential. -/
lemma lift_d (tK : IsLinearCopowerOf k K X ZK) {W : C} (p q : ℤ)
    (γ : CochainComplex.HomComplex.Cochain
      K (DGLinear.homComplex k X W) p) :
    tK.lift q (CochainComplex.HomComplex.δ p q γ) =
      ((dgHom ZK W).d p q).hom (tK.lift p γ) := by
  apply (tK.cochainLinearEquiv W q).injective
  change (tK.cochainLinearEquiv W q)
      ((tK.cochainLinearEquiv W q).symm
        (CochainComplex.HomComplex.δ p q γ)) =
    (tK.cochainLinearEquiv W q)
      (((dgHom ZK W).d p q).hom
        ((tK.cochainLinearEquiv W p).symm γ))
  rw [(tK.cochainLinearEquiv W q).apply_symm_apply]
  change CochainComplex.HomComplex.δ p q γ =
    linearCopowerCochain k tK.univ q
      (((dgHom ZK W).d p q).hom
        ((tK.cochainLinearEquiv W p).symm γ))
  rw [← tK.linearCopowerCochain_d W p q]
  have h := (tK.cochainLinearEquiv W p).apply_symm_apply γ
  change linearCopowerCochain k tK.univ p
    ((tK.cochainLinearEquiv W p).symm γ) = γ at h
  rw [h]

/-- A homogeneous cochain between coefficient complexes induces a homogeneous
morphism between their scalar-linear copowers. -/
noncomputable def coefficientMap
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (p : ℤ) :
    CochainComplex.HomComplex.Cochain K L p →ₗ[k] (dgHom ZK ZL).X p where
  toFun γ := tK.lift p (γ.comp
    (CochainComplex.HomComplex.Cochain.ofHom tL.univ) (add_zero p))
  map_add' γ γ' := by
    rw [CochainComplex.HomComplex.Cochain.add_comp, tK.lift_add]
  map_smul' c γ := by
    rw [CochainComplex.HomComplex.Cochain.smul_comp, tK.lift_smul]
    rfl

@[simp]
lemma univ_comp_coefficientMap
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (p : ℤ)
    (γ : CochainComplex.HomComplex.Cochain K L p)
    (i j : ℤ) (hij : i + p = j) (x : K.X i) :
    dgComp i p j hij (tK.univ.f i x) (tK.coefficientMap tL p γ) =
      tL.univ.f j ((γ.v i j hij).hom x) := by
  change dgComp i p j hij (tK.univ.f i x)
      (tK.lift p (γ.comp
        (CochainComplex.HomComplex.Cochain.ofHom tL.univ) (add_zero p))) = _
  rw [tK.univ_comp_lift,
    CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  rfl

/-- The homogeneous cochain action intertwines Mathlib's Hom-complex
differential with the dg differential. -/
lemma coefficientMap_d
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (p q : ℤ)
    (γ : CochainComplex.HomComplex.Cochain K L p) :
    tK.coefficientMap tL q (CochainComplex.HomComplex.δ p q γ) =
      ((dgHom ZK ZL).d p q).hom (tK.coefficientMap tL p γ) := by
  change tK.lift q
      ((CochainComplex.HomComplex.δ p q γ).comp
        (CochainComplex.HomComplex.Cochain.ofHom tL.univ) (add_zero q)) =
    ((dgHom ZK ZL).d p q).hom
      (tK.lift p (γ.comp
        (CochainComplex.HomComplex.Cochain.ofHom tL.univ) (add_zero p)))
  rw [← tK.lift_d p q (γ.comp
    (CochainComplex.HomComplex.Cochain.ofHom tL.univ) (add_zero p))]
  apply congrArg (tK.lift q)
  by_cases hpq : p + 1 = q
  · rw [CochainComplex.HomComplex.δ_comp_zero_cochain γ
      (CochainComplex.HomComplex.Cochain.ofHom tL.univ) q hpq,
      CochainComplex.HomComplex.δ_ofHom, CochainComplex.HomComplex.Cochain.comp_zero,
      zero_add]
  · rw [CochainComplex.HomComplex.δ_shape p q hpq,
      CochainComplex.HomComplex.δ_shape p q hpq,
      CochainComplex.HomComplex.Cochain.zero_comp]

/-- Homogeneous coefficient cochains compose strictly after passage to their
scalar-linear copowers. -/
lemma coefficientMap_comp
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL)
    (tM : IsLinearCopowerOf k M X ZM)
    (p q r : ℤ) (h : p + q = r)
    (γ : CochainComplex.HomComplex.Cochain K L p)
    (η : CochainComplex.HomComplex.Cochain L M q) :
    dgComp p q r h (tK.coefficientMap tL p γ) (tL.coefficientMap tM q η) =
      tK.coefficientMap tM r (γ.comp η h) := by
  refine tK.lift_unique (fun i j hij x => ?_)
  rw [← dgComp_assoc i p q (i + p) r j rfl h (by omega),
    tK.univ_comp_coefficientMap tL, tL.univ_comp_coefficientMap tM,
    tK.univ_comp_coefficientMap tM,
    CochainComplex.HomComplex.Cochain.comp_v γ η h i (i + p) j rfl (by omega)]
  rfl

/-- The identity cochain induces the dg identity when the same copower witness
is used at both ends. -/
@[simp]
lemma coefficientMap_id (tK : IsLinearCopowerOf k K X ZK) :
    tK.coefficientMap tK 0
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K)) = dgId ZK := by
  refine tK.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [tK.univ_comp_coefficientMap tK,
    CochainComplex.HomComplex.Cochain.ofHom_v, dgComp_id]
  rfl

/-- Between two choices for the same coefficient complex, the lifted identity
is the existing canonical comparison. -/
lemma coefficientMap_id_eq_compare
    (tK : IsLinearCopowerOf k K X ZK)
    (tK' : IsLinearCopowerOf k K X ZL) :
    tK.coefficientMap tK' 0
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K)) = tK.compare tK' := by
  refine tK.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [tK.univ_comp_coefficientMap tK', tK.univ_comp_compare tK',
    CochainComplex.HomComplex.Cochain.ofHom_v]
  rfl

/-- A chain map between coefficient complexes induces a degree-zero dg
morphism between their scalar-linear copowers. -/
noncomputable def coefficientMapOfHom
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) :
    (K ⟶ L) →ₗ[k] (dgHom ZK ZL).X 0 where
  toFun f := tK.coefficientMap tL 0
    (CochainComplex.HomComplex.Cochain.ofHom f)
  map_add' f f' := by
    rw [CochainComplex.HomComplex.Cochain.ofHom_add, map_add]
  map_smul' c f := by
    rw [show CochainComplex.HomComplex.Cochain.ofHom (c • f) =
        c • CochainComplex.HomComplex.Cochain.ofHom f by
      apply CochainComplex.HomComplex.Cochain.ext₀
      intro i
      rw [CochainComplex.HomComplex.Cochain.ofHom_v,
        CochainComplex.HomComplex.Cochain.smul_v,
        CochainComplex.HomComplex.Cochain.ofHom_v]
      rfl,
      map_smul]
    rfl

@[simp]
lemma univ_comp_coefficientMapOfHom
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (f : K ⟶ L)
    (i : ℤ) (x : K.X i) :
    dgComp i 0 i (by omega) (tK.univ.f i x) (tK.coefficientMapOfHom tL f) =
      tL.univ.f i (f.f i x) := by
  change dgComp i 0 i (by omega) (tK.univ.f i x)
      (tK.coefficientMap tL 0
        (CochainComplex.HomComplex.Cochain.ofHom f)) = _
  rw [tK.univ_comp_coefficientMap tL,
    CochainComplex.HomComplex.Cochain.ofHom_v]

/-- Coefficient chain maps induce closed degree-zero dg morphisms. -/
lemma coefficientMapOfHom_mem_cocycles
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (f : K ⟶ L) :
    tK.coefficientMapOfHom tL f ∈ cocycles ZK ZL := by
  rw [mem_cocycles_iff]
  change ((dgHom ZK ZL).d 0 1).hom
      (tK.coefficientMap tL 0
        (CochainComplex.HomComplex.Cochain.ofHom f)) = 0
  rw [← tK.coefficientMap_d tL 0 1
    (CochainComplex.HomComplex.Cochain.ofHom f),
    CochainComplex.HomComplex.δ_ofHom, map_zero]

/-- The identity coefficient map is the canonical comparison between two
choices for the same linear copower. -/
lemma coefficientMapOfHom_id_eq_compare
    (tK : IsLinearCopowerOf k K X ZK)
    (tK' : IsLinearCopowerOf k K X ZL) :
    tK.coefficientMapOfHom tK' (𝟙 K) = tK.compare tK' := by
  change tK.coefficientMap tK' 0
    (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K)) = tK.compare tK'
  exact tK.coefficientMap_id_eq_compare tK'

/-- Coefficient chain maps compose strictly after passage to linear
copowers. -/
lemma coefficientMapOfHom_comp
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL)
    (tM : IsLinearCopowerOf k M X ZM) (f : K ⟶ L) (g : L ⟶ M) :
    dgComp 0 0 0 (by omega) (tK.coefficientMapOfHom tL f)
        (tL.coefficientMapOfHom tM g) =
      tK.coefficientMapOfHom tM (f ≫ g) := by
  change dgComp 0 0 0 (by omega)
      (tK.coefficientMap tL 0 (CochainComplex.HomComplex.Cochain.ofHom f))
      (tL.coefficientMap tM 0 (CochainComplex.HomComplex.Cochain.ofHom g)) =
    tK.coefficientMap tM 0
      (CochainComplex.HomComplex.Cochain.ofHom (f ≫ g))
  rw [tK.coefficientMap_comp tL tM 0 0 0 (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_comp]

/-- Homotopic coefficient chain maps induce dg morphisms whose difference is
a coboundary. -/
lemma coefficientMapOfHom_sub_mem_coboundaries
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) {f g : K ⟶ L}
    (h : Homotopy f g) :
    tK.coefficientMapOfHom tL f - tK.coefficientMapOfHom tL g ∈
      coboundaries ZK ZL := by
  change tK.coefficientMap tL 0
      (CochainComplex.HomComplex.Cochain.ofHom f) -
    tK.coefficientMap tL 0
      (CochainComplex.HomComplex.Cochain.ofHom g) ∈ coboundaries ZK ZL
  refine ⟨tK.coefficientMap tL (-1)
    (CochainComplex.HomComplex.Cochain.ofHomotopy h), ?_⟩
  rw [← tK.coefficientMap_d tL (-1) 0
      (CochainComplex.HomComplex.Cochain.ofHomotopy h),
    CochainComplex.HomComplex.δ_ofHomotopy, map_sub]

/-- The `H⁰` morphism induced by a coefficient chain map. -/
noncomputable def coefficientHom
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (f : K ⟶ L) :
    (show H0 C from ZK) ⟶ (show H0 C from ZL) :=
  H0.homMk ⟨tK.coefficientMapOfHom tL f, tK.coefficientMapOfHom_mem_cocycles tL f⟩

/-- Homotopic coefficient chain maps induce equal morphisms in `H⁰ C`. -/
lemma coefficientHom_eq_of_homotopy
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) {f g : K ⟶ L}
    (h : Homotopy f g) :
    tK.coefficientHom tL f = tK.coefficientHom tL g :=
  H0.homMk_eq_homMk (tK.coefficientMapOfHom_sub_mem_coboundaries tL h)

/-- The coefficient action preserves identities in `H⁰ C`. -/
@[simp]
lemma coefficientHom_id (tK : IsLinearCopowerOf k K X ZK) :
    tK.coefficientHom tK (𝟙 K) = 𝟙 (show H0 C from ZK) := by
  calc
    tK.coefficientHom tK (𝟙 K) =
        H0.homMk (⟨dgId ZK, dgId_cocycle ZK⟩ : cocycles ZK ZK) := by
      apply congrArg H0.homMk
      apply Subtype.ext
      change tK.coefficientMap tK 0
        (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K)) = dgId ZK
      exact tK.coefficientMap_id
    _ = 𝟙 (show H0 C from ZK) := H0.homMk_id ZK

/-- The coefficient action preserves composition in `H⁰ C`. -/
lemma coefficientHom_comp
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL)
    (tM : IsLinearCopowerOf k M X ZM) (f : K ⟶ L) (g : L ⟶ M) :
    tK.coefficientHom tL f ≫ tL.coefficientHom tM g =
      tK.coefficientHom tM (f ≫ g) := by
  rw [coefficientHom, coefficientHom, H0.homMk_comp]
  apply congrArg H0.homMk
  apply Subtype.ext
  exact tK.coefficientMapOfHom_comp tL tM f g

/-- A homotopy equivalence of coefficient complexes induces an isomorphism
between any witnessed scalar-linear copowers in `H⁰ C`. -/
noncomputable def homotopyEquivIso
    (tK : IsLinearCopowerOf k K X ZK)
    (tL : IsLinearCopowerOf k L X ZL) (e : HomotopyEquiv K L) :
    (show H0 C from ZK) ≅ (show H0 C from ZL) where
  hom := tK.coefficientHom tL e.hom
  inv := tL.coefficientHom tK e.inv
  hom_inv_id := by
    rw [tK.coefficientHom_comp tL tK]
    exact (tK.coefficientHom_eq_of_homotopy tK e.homotopyHomInvId).trans
      tK.coefficientHom_id
  inv_hom_id := by
    rw [tL.coefficientHom_comp tK tL]
    exact (tL.coefficientHom_eq_of_homotopy tL e.homotopyInvHomId).trans
      tL.coefficientHom_id

end IsLinearCopowerOf

section Selected

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HasLinearCopowers k C]

/-- For a fixed dg object, selected scalar-linear copowers form a linear dg
functor from the standard dg category of complexes. -/
noncomputable def linearCopowerFunctor (k : Type w) [CommRing k]
    {C : Type u} [DGCategory.{v} C]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
    [DGLinear k C] [HasLinearCopowers k C] (X : C) :
    DGFunctor (Cdg (ModuleCat.{v} k)) C where
  obj K := linearCopowerObj (Cdg.of _ K) X
  map {K L} p := ((linearCopowerIsLinearCopower (Cdg.of _ K) X).coefficientMap
    (linearCopowerIsLinearCopower (Cdg.of _ L) X) p).toAddMonoidHom
  map_d {K L} p q f :=
    (linearCopowerIsLinearCopower (Cdg.of _ K) X).coefficientMap_d
      (linearCopowerIsLinearCopower (Cdg.of _ L) X) p q f
  map_id K :=
    (linearCopowerIsLinearCopower (Cdg.of _ K) X).coefficientMap_id
  map_comp {K L M} p q r h f g :=
    ((linearCopowerIsLinearCopower (Cdg.of _ K) X).coefficientMap_comp
      (linearCopowerIsLinearCopower (Cdg.of _ L) X)
      (linearCopowerIsLinearCopower (Cdg.of _ M) X) p q r h f g).symm

instance linearCopowerFunctor_linear (X : C) :
    (linearCopowerFunctor k X).Linear k where
  map_smul p c f := by
    exact map_smul ((linearCopowerIsLinearCopower _ X).coefficientMap
      (linearCopowerIsLinearCopower _ X) p) c f

@[simp]
lemma linearCopowerFunctor_obj (X : C) (K : Cdg (ModuleCat.{v} k)) :
    (linearCopowerFunctor k X).obj K =
      linearCopowerObj (Cdg.of _ K) X := rfl

lemma linearCopowerFunctor_map (X : C)
    {K L : Cdg (ModuleCat.{v} k)} (p : ℤ) (f : (dgHom K L).X p) :
    (linearCopowerFunctor k X).map p f =
      (linearCopowerIsLinearCopower (Cdg.of _ K) X).coefficientMap
    (linearCopowerIsLinearCopower (Cdg.of _ L) X) p f := rfl

end Selected

end CategoryTheory
