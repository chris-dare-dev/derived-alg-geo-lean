/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Data.Int.Interval

/-!
# Localization of bounded-source Hom complexes

When the source complex is supported in a finite interval and its terms are
finitely presented, localization of modules commutes with each degree of its
Hom complex. The comparison also commutes with the Hom-complex differential.
Finite projective terms provide a useful specialization.

This is a cochain-level statement. It does not yet identify cohomology of Hom
complexes, derived-category Homs, or bounded-coherent geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  (a b n : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]

private abbrev finiteCochain :=
  (i : {p : ℤ // p ∈ Finset.Icc a b}) → (P.X i.1 ⟶ Q.X (i.1 + n))

private def cochainRestrict :
    Cochain P Q n →ₗ[R] finiteCochain P Q a b n where
  toFun γ i := γ.v i.1 (i.1 + n) rfl
  map_add' x y := by
    funext i
    rfl
  map_smul' r x := by
    funext i
    rfl

private lemma cochain_eq_zero_outside (γ : Cochain P Q n) (p : ℤ)
    (hp : p ∉ Finset.Icc a b) : γ.v p (p + n) rfl = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact (P.isZero_of_isStrictlyGE a p h).eq_zero_of_src _
  · exact (P.isZero_of_isStrictlyLE b p h).eq_zero_of_src _

private def cochainExtend :
    finiteCochain P Q a b n →ₗ[R] Cochain P Q n where
  toFun v := Cochain.mk fun p q hpq => by
    subst q
    exact if hp : p ∈ Finset.Icc a b then v ⟨p, hp⟩ else 0
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
  map_smul' r x := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]

private def cochainFiniteEquiv :
    Cochain P Q n ≃ₗ[R] finiteCochain P Q a b n where
  toLinearMap := cochainRestrict P Q a b n
  invFun := cochainExtend P Q a b n
  left_inv γ := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [cochainExtend, cochainRestrict, Cochain.mk_v, Finset.mem_Icc, hp]
    · have hfin : p ∉ Finset.Icc a b := by simpa only [Finset.mem_Icc] using hp
      simp [cochainExtend, Cochain.mk_v, Finset.mem_Icc, hp,
        cochain_eq_zero_outside P Q a b n γ p hfin]
  right_inv v := by
    funext i
    have hi : a ≤ (i : ℤ) ∧ (i : ℤ) ≤ b := Finset.mem_Icc.mp i.2
    simp [cochainExtend, cochainRestrict, Cochain.mk_v, Finset.mem_Icc, hi]

variable (S : Submonoid R)

private abbrev localizedP :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P

private abbrev localizedQ :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q

private instance localizedP_ge : CochainComplex.IsStrictlyGE (localizedP P S) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  change IsZero ((ModuleCat.localizedModuleFunctor.{u} S).obj (P.X i))
  exact (ModuleCat.localizedModuleFunctor.{u} S).map_isZero
    (P.isZero_of_isStrictlyGE a i hi)

private instance localizedP_le : CochainComplex.IsStrictlyLE (localizedP P S) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  change IsZero ((ModuleCat.localizedModuleFunctor.{u} S).obj (P.X i))
  exact (ModuleCat.localizedModuleFunctor.{u} S).map_isZero
    (P.isZero_of_isStrictlyLE b i hi)

/-- The cochain map induced by localizing both complexes degreewise. -/
def cochainLocalizedMap :
    Cochain P Q n →ₗ[R]
      Cochain
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q)
        n where
  toFun γ := γ.map (ModuleCat.localizedModuleFunctor.{u} S)
  map_add' x y := by
    exact Cochain.map_add x y (ModuleCat.localizedModuleFunctor.{u} S)
  map_smul' r x := by
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.map_v, Cochain.smul_v]
    apply ModuleCat.hom_ext
    dsimp [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
    simp only [map_smul]
    ext y
    change r •
      ((IsLocalizedModule.mapExtendScalars S
        ((P.X p).localizedModuleMkLinearMap S)
        ((Q.X q).localizedModuleMkLinearMap S) (Localization S))
        (x.v p q hpq).hom) y =
      (algebraMap R (Localization S) r) •
        ((IsLocalizedModule.mapExtendScalars S
          ((P.X p).localizedModuleMkLinearMap S)
          ((Q.X q).localizedModuleMkLinearMap S) (Localization S))
          (x.v p q hpq).hom) y
    exact (IsScalarTower.algebraMap_smul (Localization S) r _).symm

private def homLocalizedMap (M N : ModuleCat.{u} R) :
    (M ⟶ N) →ₗ[R] (M.localizedModule S ⟶ N.localizedModule S) := by
  let eR : (M ⟶ N) ≃ₗ[R] (M →ₗ[R] N) := ModuleCat.homLinearEquiv
  let eA : (M.localizedModule S ⟶ N.localizedModule S) ≃ₗ[R]
      (M.localizedModule S →ₗ[Localization S] N.localizedModule S) :=
    ModuleCat.homLinearEquiv
  exact eA.symm.toLinearMap ∘ₗ
    (IsLocalizedModule.mapExtendScalars S
      (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
      (Localization S)) ∘ₗ eR.toLinearMap

private lemma homLocalizedMap_isLocalized (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    IsLocalizedModule S (homLocalizedMap S M N) := by
  let eR : (M ⟶ N) ≃ₗ[R] (M →ₗ[R] N) := ModuleCat.homLinearEquiv
  let eA : (M.localizedModule S ⟶ N.localizedModule S) ≃ₗ[R]
      (M.localizedModule S →ₗ[Localization S] N.localizedModule S) :=
    ModuleCat.homLinearEquiv
  let f := IsLocalizedModule.mapExtendScalars S
    (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
    (Localization S)
  change IsLocalizedModule S (eA.symm.toLinearMap ∘ₗ f ∘ₗ eR.toLinearMap)
  letI : IsLocalizedModule S f := inferInstance
  letI : IsLocalizedModule S (eA.symm.toLinearMap ∘ₗ f) :=
    IsLocalizedModule.of_linearEquiv S f eA.symm
  exact IsLocalizedModule.of_linearEquiv_right S
    (eA.symm.toLinearMap ∘ₗ f) eR

private lemma homLocalizedMap_apply (M N : ModuleCat.{u} R) (f : M ⟶ N) :
    homLocalizedMap S M N f = (ModuleCat.localizedModuleFunctor.{u} S).map f := by
  rfl

/-- Degreewise localization respects the Hom-complex differential. -/
theorem cochainLocalizedMap_delta (m : ℤ) (γ : Cochain P Q n) :
    cochainLocalizedMap P Q m S (δ n m γ) =
      δ n m (cochainLocalizedMap P Q n S γ) := by
  exact (δ_map n m γ (ModuleCat.localizedModuleFunctor.{u} S)).symm

private def homLocalizedMapGeneric (M N : ModuleCat.{u} R) :
    (M ⟶ N) →ₗ[R]
      ((ModuleCat.localizedModuleFunctor.{u} S).obj M ⟶
        (ModuleCat.localizedModuleFunctor.{u} S).obj N) where
  toFun f := (ModuleCat.localizedModuleFunctor.{u} S).map f
  map_add' f g := by
    exact (ModuleCat.localizedModuleFunctor.{u} S).map_add
  map_smul' r f := by
    apply ModuleCat.hom_ext
    dsimp [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
    simp only [map_smul]
    ext x
    change r •
      ((IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) (Localization S)) f.hom) x =
      (algebraMap R (Localization S) r) •
        ((IsLocalizedModule.mapExtendScalars S
          (M.localizedModuleMkLinearMap S)
          (N.localizedModuleMkLinearMap S) (Localization S)) f.hom) x
    exact (IsScalarTower.algebraMap_smul (Localization S) r _).symm

private def localizedHomEquiv (M N : ModuleCat.{u} R) :
    ((ModuleCat.localizedModuleFunctor.{u} S).obj M ⟶
      (ModuleCat.localizedModuleFunctor.{u} S).obj N) ≃ₗ[R]
      (M.localizedModule S ⟶ N.localizedModule S) where
  toFun f := f
  invFun f := f
  left_inv f := rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' r f := by
    apply ModuleCat.hom_ext
    ext x
    let f' : M.localizedModule S ⟶ N.localizedModule S := f
    have he :=
      (ModuleCat.homLinearEquiv (M := M.localizedModule S)
        (N := N.localizedModule S) (S := R)).map_smul r f'
    have hx := congrArg
      (fun g : (M.localizedModule S →ₗ[Localization S] N.localizedModule S) => g x) he
    simp only [ModuleCat.homLinearEquiv_apply, LinearMap.smul_apply] at hx
    change r • f.hom x = (r • f' : M.localizedModule S ⟶ N.localizedModule S).hom x
    rw [show (ModuleCat.homAddEquiv.toFun (r • f')) x =
      (r • f' : M.localizedModule S ⟶ N.localizedModule S).hom x from rfl] at hx
    rw [hx]
    calc
      (r • f.hom x : (ModuleCat.localizedModuleFunctor.{u} S).obj N) =
          (algebraMap R (Localization S) r) • f.hom x :=
        (IsScalarTower.algebraMap_smul (Localization S) r _).symm
      _ = (r • f'.hom x : N.localizedModule S) := by
        letI : Module R (N.localizedModule S) :=
          ModuleCat.instModuleCarrierLocalizationLocalizedModule N S
        letI : IsScalarTower R (Localization S) (N.localizedModule S) :=
          (equivShrink (LocalizedModule S N)).symm.isScalarTower R (Localization S)
        have h : (algebraMap R (Localization S) r) •
            (f'.hom x : N.localizedModule S) =
            (r • (f'.hom x : N.localizedModule S) : N.localizedModule S) :=
          IsScalarTower.algebraMap_smul (Localization S) r _
        exact h

private lemma homLocalizedMapGeneric_isLocalized (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    IsLocalizedModule S (homLocalizedMapGeneric S M N) := by
  have h := homLocalizedMap_isLocalized S M N
  have h' : IsLocalizedModule S
      ((localizedHomEquiv S M N).symm.toLinearMap ∘ₗ
        homLocalizedMap S M N) :=
    IsLocalizedModule.of_linearEquiv S (homLocalizedMap S M N)
      (localizedHomEquiv S M N).symm
  convert h' using 1
  ext f
  rfl

private def finiteLocalizedMap :
    finiteCochain P Q a b n →ₗ[R]
      finiteCochain (localizedP P S) (localizedQ Q S) a b n :=
  LinearMap.pi fun i =>
    (homLocalizedMapGeneric S (P.X i.1) (Q.X (i.1 + n))) ∘ₗ LinearMap.proj i

omit [P.IsStrictlyGE a] [P.IsStrictlyLE b] in
private lemma finiteLocalizedMap_isLocalized
    [∀ i : {p : ℤ // p ∈ Finset.Icc a b}, Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S (finiteLocalizedMap P Q a b n S) := by
  letI (i : {p : ℤ // p ∈ Finset.Icc a b}) :
      IsLocalizedModule S
        (homLocalizedMapGeneric S (P.X i.1) (Q.X (i.1 + n))) :=
    homLocalizedMapGeneric_isLocalized S (P.X i.1) (Q.X (i.1 + n))
  change IsLocalizedModule S (LinearMap.pi fun (i : {p : ℤ // p ∈ Finset.Icc a b}) =>
    (homLocalizedMapGeneric S (P.X i.1) (Q.X (i.1 + n))) ∘ₗ LinearMap.proj i)
  infer_instance

private def localizedCochainRestrictR :
    Cochain (localizedP P S) (localizedQ Q S) n →ₗ[R]
      finiteCochain (localizedP P S) (localizedQ Q S) a b n where
  toFun γ i := γ.v i.1 (i.1 + n) rfl
  map_add' x y := by
    funext i
    rfl
  map_smul' r x := by
    funext i
    rfl

private def localizedCochainExtendR :
    finiteCochain (localizedP P S) (localizedQ Q S) a b n →ₗ[R]
      Cochain (localizedP P S) (localizedQ Q S) n where
  toFun v := Cochain.mk fun p q hpq => by
    subst q
    exact if hp : p ∈ Finset.Icc a b then v ⟨p, hp⟩ else 0
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
  map_smul' r x := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]

private def localizedCochainFiniteEquivR :
    Cochain (localizedP P S) (localizedQ Q S) n ≃ₗ[R]
      finiteCochain (localizedP P S) (localizedQ Q S) a b n where
  toLinearMap := localizedCochainRestrictR P Q a b n S
  invFun := localizedCochainExtendR P Q a b n S
  left_inv γ := (cochainFiniteEquiv (localizedP P S) (localizedQ Q S) a b n).left_inv γ
  right_inv v := (cochainFiniteEquiv (localizedP P S) (localizedQ Q S) a b n).right_inv v

omit [P.IsStrictlyGE a] [P.IsStrictlyLE b] in
private lemma cochainFinite_localized_comm :
    (localizedCochainRestrictR P Q a b n S) ∘ₗ
        cochainLocalizedMap P Q n S =
      (finiteLocalizedMap P Q a b n S) ∘ₗ
        cochainRestrict P Q a b n := by
  ext γ i
  rfl

/-- A strictly bounded source with finitely presented terms makes every
degree of the Hom complex commute with localization. -/
theorem cochainLocalizedMap_isLocalized (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i : {p : ℤ // p ∈ Finset.Icc a b}, Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S (cochainLocalizedMap P Q n S) := by
  letI : IsLocalizedModule S (finiteLocalizedMap P Q a b n S) :=
    finiteLocalizedMap_isLocalized P Q a b n S
  have h₁ : IsLocalizedModule S
      ((finiteLocalizedMap P Q a b n S) ∘ₗ
        (cochainFiniteEquiv P Q a b n).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S
      (finiteLocalizedMap P Q a b n S) (cochainFiniteEquiv P Q a b n)
  have h₂ : IsLocalizedModule S
      ((localizedCochainFiniteEquivR P Q a b n S).symm.toLinearMap ∘ₗ
        (finiteLocalizedMap P Q a b n S) ∘ₗ
          (cochainFiniteEquiv P Q a b n).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv S _
      (localizedCochainFiniteEquivR P Q a b n S).symm
  convert h₂ using 1
  apply LinearMap.ext
  intro γ
  apply (localizedCochainFiniteEquivR P Q a b n S).injective
  have hcomm := LinearMap.congr_fun (cochainFinite_localized_comm P Q a b n S) γ
  change (localizedCochainFiniteEquivR P Q a b n S)
      (cochainLocalizedMap P Q n S γ) =
    (localizedCochainFiniteEquivR P Q a b n S)
      ((localizedCochainFiniteEquivR P Q a b n S).symm
        ((finiteLocalizedMap P Q a b n S)
          ((cochainFiniteEquiv P Q a b n) γ)))
  rw [LinearEquiv.apply_symm_apply]
  change (localizedCochainFiniteEquivR P Q a b n S)
      (cochainLocalizedMap P Q n S γ) =
    (finiteLocalizedMap P Q a b n S) ((cochainFiniteEquiv P Q a b n) γ) at hcomm
  exact hcomm

/-- Finite projective source terms satisfy the finite-presentation hypothesis
of degreewise Hom-complex localization. -/
theorem cochainLocalizedMap_isLocalized_of_finite_projective (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i : {p : ℤ // p ∈ Finset.Icc a b}, Module.Finite R (P.X i.1)]
    [∀ i : {p : ℤ // p ∈ Finset.Icc a b}, Module.Projective R (P.X i.1)] :
    IsLocalizedModule S (cochainLocalizedMap P Q n S) := by
  letI (i : {p : ℤ // p ∈ Finset.Icc a b}) :
      Module.FinitePresentation R (P.X i.1) :=
    Module.finitePresentation_of_projective R (P.X i.1)
  exact cochainLocalizedMap_isLocalized P Q n S a b

end

end CochainComplex.HomComplex
