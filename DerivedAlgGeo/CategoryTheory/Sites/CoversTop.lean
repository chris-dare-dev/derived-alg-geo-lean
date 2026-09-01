/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-!
# Transporting families that cover the terminal object

Covering families on arbitrary sites can be transported through equivalences whose forward
functors preserve covers. This is site-theoretic infrastructure and does not require sheaves or
a geometric realization of either site.
-/

open CategoryTheory

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {I : Type*} {U : I → C}

/-- An equivalence whose forward functor preserves covers sends a family covering the terminal
object to a family covering the terminal object. -/
lemma CoversTop.map_equivalence :
    (hU : J.CoversTop U) → (e : _root_.CategoryTheory.Equivalence C D) →
      CoverPreserving J K e.functor →
      K.CoversTop (fun i ↦ e.functor.obj (U i)) := by
  intro hU e he
  have hcover (Z : C) :
      Sieve.ofObjects (fun i ↦ e.functor.obj (U i)) (e.functor.obj Z) ∈
        K (e.functor.obj Z) := by
    refine K.superset_covering ?_
      (CoverPreserving.cover_preserve he (hU Z))
    intro T g hg
    obtain ⟨A, a, b, ha, rfl⟩ := hg
    obtain ⟨i, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff U a).mp ha
    exact (Sieve.mem_ofObjects_iff _ _).mpr ⟨i, ⟨b ≫ e.functor.map c⟩⟩
  intro Z
  refine K.superset_covering ?_
    (K.pullback_stable (e.counitInv.app Z) (hcover (e.inverse.obj Z)))
  intro T g hg
  change ∃ i, Nonempty (T ⟶ e.functor.obj (U i)) at hg ⊢
  exact hg

end CategoryTheory.GrothendieckTopology
