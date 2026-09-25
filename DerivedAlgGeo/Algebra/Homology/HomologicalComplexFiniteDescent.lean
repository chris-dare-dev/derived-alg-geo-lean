/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.FiniteDescent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Finite-window complex models over a localization

A strictly bounded cochain complex of finite modules over a localization has
a strictly bounded model with finite terms over the base ring. The model is
isomorphic after termwise scalar extension as an ordinary cochain complex.
There is no Noetherian hypothesis and no claim about descending arrows,
derived localization, or a bounded semiorthogonal component.

The construction chooses a finite submodule `B i` of each restricted-scalar
term and sets `L i = B i ⊔ d(B (i - 1))`. The next differential kills the
second summand by `d² = 0`. Its restricted square is literally zero because
each `L i` is a subtype of the original term; no localization faithfulness is
used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace CochainComplex

universe u

/-- A finite strict window of finite modules over a localization has a
termwise finite model over the base ring, isomorphic after ordinary scalar
extension. This is complex-object descent, not descent of a map or a derived
or component-level statement. -/
theorem exists_finite_model_of_isLocalization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite A (K.X i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ i : ℤ, Module.Finite R (L.X i)) ∧
      L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty (K ≅ ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
        (.up ℤ)).obj L) := by
  classical
  let alg : Algebra R A := inferInstance
  let hLoc : @IsLocalization R _ S A _ alg := inferInstance
  have hAlgEq : (algebraMap R A).toAlgebra = alg := toAlgebra_algebraMap
  letI : Algebra R A := (algebraMap R A).toAlgebra
  haveI : IsLocalization S A := by
    exact (congrArg (fun α : Algebra R A => @IsLocalization R _ S A _ α)
      hAlgEq).mpr hLoc
  letI (i : ℤ) : Module R (K.X i) := Module.compHom (K.X i) (algebraMap R A)
  letI (i : ℤ) : IsScalarTower R A (K.X i) := IsScalarTower.of_compHom R A (K.X i)
  let dR (i j : ℤ) : (K.X i) →ₗ[R] (K.X j) := (K.d i j).hom.restrictScalars R
  have hB (i : ℤ) : ∃ B : Submodule R (K.X i),
      Module.Finite R B ∧ IsLocalizedModule S B.subtype := by
    letI : Module.Finite A (K.X i) := hfinite i
    obtain ⟨B, hfin, hloc, _⟩ :=
      Module.exists_finite_submodule_of_isLocalization (R := R) (A := A)
        (N := K.X i) S
    exact ⟨B, hfin, hloc⟩
  let B (i : ℤ) : Submodule R (K.X i) := (hB i).choose
  have hBfinite (i : ℤ) : Module.Finite R (B i) := (hB i).choose_spec.1
  have hBloc (i : ℤ) : IsLocalizedModule S (B i).subtype := (hB i).choose_spec.2
  let L (i : ℤ) : Submodule R (K.X i) :=
    B i ⊔ (B (i - 1)).map (dR (i - 1) i)
  have hLfinite (i : ℤ) : Module.Finite R (L i) := by
    letI : Module.Finite R (B i) := hBfinite i
    letI : Module.Finite R (B (i - 1)) := hBfinite (i - 1)
    dsimp [L]
    infer_instance
  have hLloc (i : ℤ) : IsLocalizedModule S (L i).subtype := by
    letI : IsLocalizedModule S (B i).subtype := hBloc i
    constructor
    · exact (hBloc i).map_units
    · intro n
      obtain ⟨⟨x, s⟩, hs⟩ := (hBloc i).surj n
      exact ⟨(⟨x.1, (le_sup_left : B i ≤ L i) x.2⟩, s), hs⟩
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : x = y := Subtype.ext hxy
      simp [this]
  have hclosure (i : ℤ) (x : K.X i) (hx : x ∈ L i) :
      dR i (i + 1) x ∈ L (i + 1) := by
    change x ∈ B i ⊔ (B (i - 1)).map (dR (i - 1) i) at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    apply Submodule.add_mem
    · have hmap : dR i (i + 1) y ∈ (B i).map (dR i (i + 1)) :=
        Submodule.mem_map_of_mem hy
      have hle : (B i).map (dR i (i + 1)) ≤ L (i + 1) := by
        have hi : i + 1 - 1 = i := by omega
        dsimp only [L]
        rw [hi]
        exact le_sup_right
      exact hle hmap
    · obtain ⟨w, _hw, rfl⟩ := Submodule.mem_map.mp hz
      have hzero : dR i (i + 1) (dR (i - 1) i w) = 0 := by
        change (K.d (i - 1) i ≫ K.d i (i + 1)).hom w = 0
        rw [K.d_comp_d]
        rfl
      rw [hzero]
      exact (L (i + 1)).zero_mem
  let δ (i : ℤ) : (L i) →ₗ[R] (L (i + 1)) :=
    ((dR i (i + 1)).domRestrict (L i)).codRestrict (L (i + 1))
      (fun x => hclosure i x x.property)
  have hδsq (i : ℤ) : (δ (i + 1)).comp (δ i) = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    dsimp only [δ, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
    change (K.d i (i + 1) ≫ K.d (i + 1) (i + 1 + 1)).hom x.1 = 0
    rw [K.d_comp_d]
    rfl
  have hsq (i : ℤ) :
      ModuleCat.ofHom (δ i) ≫ ModuleCat.ofHom (δ (i + 1)) = 0 := by
    apply ModuleCat.hom_ext
    exact hδsq i
  let Lc : CochainComplex (ModuleCat.{u} R) ℤ :=
    CochainComplex.of (fun i => ModuleCat.of R (L i))
      (fun i => ModuleCat.ofHom (δ i)) hsq
  letI (i : ℤ) : IsLocalizedModule S (L i).subtype := hLloc i
  let e (i : ℤ) :
      (ModuleCat.extendScalars (algebraMap R A)).obj (ModuleCat.of R (L i)) ≅
        K.X i := by
    let eLin : A ⊗[R] (L i) ≃ₗ[A] K.X i :=
      (IsLocalizedModule.isBaseChange S A (L i).subtype).equiv
    exact
      { hom := ConcreteCategory.ofHom eLin.toLinearMap
        inv := ConcreteCategory.ofHom eLin.symm.toLinearMap
        hom_inv_id := by
          apply ModuleCat.hom_ext
          exact LinearMap.ext eLin.left_inv
        inv_hom_id := by
          apply ModuleCat.hom_ext
          exact LinearMap.ext eLin.right_inv }
  let F := ModuleCat.extendScalars (algebraMap R A)
  have he_mk (j : ℤ) (y : L j) :
      (e j).hom ((TensorProduct.mk R A (L j) 1) y) = (y : K.X j) := by
    change ((IsLocalizedModule.isBaseChange S A (L j).subtype).equiv)
      ((TensorProduct.mk R A (L j) 1) y) = y.1
    simp
  have he (i : ℤ) :
      F.map (ModuleCat.ofHom (δ i)) ≫ (e (i + 1)).hom =
        (e i).hom ≫ K.d i (i + 1) := by
    apply ModuleCat.hom_ext
    apply (TensorProduct.isBaseChange R (L i) A).algHom_ext
    intro x
    change (e (i + 1)).hom (F.map (ModuleCat.ofHom (δ i))
      ((TensorProduct.mk R A (L i) 1) x)) =
        (K.d i (i + 1)) ((e i).hom ((TensorProduct.mk R A (L i) 1) x))
    dsimp only [F]
    erw [ModuleCat.ExtendScalars.map_tmul]
    rw [he_mk i x]
    change (e (i + 1)).hom ((TensorProduct.mk R A (L (i + 1)) 1) (δ i x)) =
      (K.d i (i + 1)).hom x.1
    rw [he_mk]
    rfl
  have he' (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
      (e i).hom ≫ K.d i j =
        ((F.mapHomologicalComplex (.up ℤ)).obj Lc).d i j ≫ (e j).hom := by
    rw [ComplexShape.up_Rel] at hij
    subst j
    change (e i).hom ≫ K.d i (i + 1) =
      F.map (Lc.d i (i + 1)) ≫ (e (i + 1)).hom
    simpa only [Lc, CochainComplex.of_d] using (he i).symm
  let eComplex : ((F.mapHomologicalComplex (.up ℤ)).obj Lc) ≅ K :=
    HomologicalComplex.Hom.isoOfComponents e he'
  have hLcfinite (i : ℤ) : Module.Finite R (Lc.X i) := hLfinite i
  have hLcGE : Lc.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    letI : Subsingleton (K.X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (K.isZero_of_isStrictlyGE a i hi)
    change IsZero (ModuleCat.of R (L i))
    exact ModuleCat.isZero_of_subsingleton _
  have hLcLE : Lc.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    letI : Subsingleton (K.X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (K.isZero_of_isStrictlyLE b i hi)
    change IsZero (ModuleCat.of R (L i))
    exact ModuleCat.isZero_of_subsingleton _
  exact ⟨Lc, hLcfinite, hLcGE, hLcLE, ⟨eComplex.symm⟩⟩

end CochainComplex
