/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Vanishing of maps from a single object into `D^{≤ -1}`

Let `E : A` and let `P` be a class of objects of `A` such that `Ext^k(E, Y) = 0` for every
`k ≥ 1` and every `Y` in `P`. Then there is no nonzero map from `(singleFunctor A 0).obj E`
into a bounded object of `D^{≤ -1}` whose cohomology objects lie in `P`. This is the
statement that the hypercohomology `Hom(E, M[j])` of such an `M` is computed by
`Hom(E, H^j M)` alone, in the only case where the answer is zero; the proof is dévissage on
the amplitude along the truncation triangles.

The geometric instance is `𝒪_X` on an affine scheme with `P` quasi-coherence, where the
hypothesis is affine vanishing through `Ext^k(𝒪_X, F) ≃ H^k(F)`. That instance is the
bounded half of the compactness of `𝒪_X` in `Dqc(Spec R)` (#723); the unbounded half needs
`M ≅ holim τ≥-n M`, which is not available at this Mathlib pin.

## Main results

* `DerivedCategory.hom_singleFunctor_eq_zero_of_ext_subsingleton` — the single case.
* `DerivedCategory.hom_eq_zero_of_isGE_of_isLE_neg_of_cohomologyIn` — the dévissage.
-/

universe w v u

open CategoryTheory Category Limits Pretriangulated Abelian

namespace DerivedCategory

attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms] (E : A)
  (hE : ∀ (Y : A), P Y → ∀ (k : ℕ), Subsingleton (Ext.{w} E Y (k + 1)))

include hE

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- No maps from `single 0 E` into `single a Y` for `a < 0` and `Y` in `P`: such a map is a
class in `Ext^{-a}(E, Y)`. -/
lemma hom_singleFunctor_eq_zero_of_ext_subsingleton {Y : A} (hY : P Y) {a : ℤ} (ha : a < 0)
    (f : (singleFunctor A 0).obj E ⟶ (singleFunctor A a).obj Y) : f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -((k : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
  let e : (singleFunctor A (-((k : ℤ) + 1))).obj Y ≅
      ((singleFunctor A 0).obj Y)⟦((k + 1 : ℕ) : ℤ)⟧ :=
    (((singleFunctors A).shiftIso ((k + 1 : ℕ) : ℤ) (-((k : ℤ) + 1)) 0
      (by push_cast; omega)).app Y).symm
  have hz : Subsingleton (ShiftedHom ((singleFunctor A 0).obj E)
      ((singleFunctor A 0).obj Y) ((k + 1 : ℕ) : ℤ)) :=
    haveI := hE Y hY k
    Ext.homEquiv.symm.subsingleton
  have h : f ≫ e.hom = 0 := @Subsingleton.elim _ hz _ _
  calc f = (f ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [h, zero_comp]

/-- **Dévissage.** No maps from `single 0 E` into a bounded object of `D^{≤ -1}` whose
cohomology lies in `P`. Induction on the amplitude along the truncation triangles
`τ_{< b} M → M → τ_{≥ b} M`; the first term is concentrated in one degree and the third has
smaller amplitude. -/
theorem hom_eq_zero_of_isGE_of_isLE_neg_of_cohomologyIn {M : DerivedCategory A}
    (hM : cohomologyIn P M) (a : ℤ) [TStructure.t.IsGE M a] [TStructure.t.IsLE M (-1)]
    (f : (singleFunctor A 0).obj E ⟶ M) : f = 0 := by
  suffices h : ∀ (n : ℕ) (M : DerivedCategory A), cohomologyIn P M →
      TStructure.t.IsGE M (-1 - n) → TStructure.t.IsLE M (-1) →
      ∀ f : (singleFunctor A 0).obj E ⟶ M, f = 0 by
    refine h (-1 - a).toNat M hM ?_ inferInstance f
    exact TStructure.t.isGE_of_ge M (-1 - ((-1 - a).toNat : ℤ)) a (by omega)
  intro n
  induction n with
  | zero =>
    intro M hM hge hle f
    haveI := hge
    haveI := hle
    haveI : TStructure.t.IsGE M (-1) := TStructure.t.isGE_of_ge M (-1) (-1 - ((0 : ℕ) : ℤ))
      (by simp)
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M (-1)
    have hY : P Y := prop_of_cohomologyIn_singleFunctor_obj P
      ((cohomologyIn P).prop_of_iso e hM)
    have h : f ≫ e.hom = 0 :=
      hom_singleFunctor_eq_zero_of_ext_subsingleton P E hE hY (by omega) (f ≫ e.hom)
    calc f = (f ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
      _ = 0 := by rw [h, zero_comp]
  | succ n ih =>
    intro M hM hge hle f
    haveI := hge
    haveI := hle
    let T := (TStructure.t.triangleLTGE (-1 - n)).obj M
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished (-1 - n) M
    -- the third term has amplitude `n`
    have h₃ : f ≫ T.mor₂ = 0 := by
      refine ih ((TStructure.t.truncGE (-1 - n)).obj M) (cohomologyIn_truncGE P hM _) ?_ ?_ _
      · exact inferInstance
      · exact inferInstance
    -- the first term is concentrated in degree `-2 - n`
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT f h₃
    have hg0 : g = 0 := by
      haveI : TStructure.t.IsGE ((TStructure.t.truncLT (-1 - n)).obj M) (-1 - ((n + 1 : ℕ) : ℤ)) :=
        inferInstance
      haveI : TStructure.t.IsGE ((TStructure.t.truncLT (-1 - n)).obj M) (-1 - n - 1) :=
        TStructure.t.isGE_of_ge _ (-1 - n - 1) (-1 - ((n + 1 : ℕ) : ℤ)) (by push_cast; omega)
      haveI : TStructure.t.IsLE ((TStructure.t.truncLT (-1 - n)).obj M) (-1 - n - 1) :=
        inferInstance
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((TStructure.t.truncLT (-1 - n)).obj M) (-1 - n - 1)
      have hY : P Y := prop_of_cohomologyIn_singleFunctor_obj P
        ((cohomologyIn P).prop_of_iso e (cohomologyIn_truncLT P hM _))
      have h : g ≫ e.hom = 0 :=
        hom_singleFunctor_eq_zero_of_ext_subsingleton P E hE hY (by omega) (g ≫ e.hom)
      calc g = (g ≫ e.hom) ≫ e.inv := (Iso.eq_comp_inv e).2 rfl
        _ = 0 := by rw [h, zero_comp]
    rw [hg, hg0]
    exact zero_comp

end DerivedCategory
