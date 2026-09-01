/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import DerivedAlgGeo.Algebra.Homology.DGCategory.H0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Complexes

/-!
# The seam: `H⁰(C^dg A)` and the homotopy category

`dg-enhancements-e4`'s theorem. The route is to identify this repository's
`cocycles` and `coboundaries` with Mathlib's, so that the Hom-groups of
`H⁰(C^dg A)` *are* `CochainComplex.HomComplex.CohomologyClass _ _ 0`, and then
to use `CohomologyClass.homAddEquiv`, which Mathlib already proves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

namespace Cdg

/-- This repository's degree-zero cocycles are Mathlib's. -/
lemma cocycles_eq (K L : Cdg A) :
    cocycles K L = HomComplex.cocycle (of A K) (of A L) 0 := rfl

/-- This repository's degree-zero coboundaries are Mathlib's, transported along
`cocycles_eq`. Mathlib's version is a subgroup of the cocycles and asks for a
primitive in degree `m` with `m + 1 = 0`; this one is the range of `δ (-1) 0`.
The two conditions are the same condition. -/
lemma mem_coboundaries_iff' (K L : Cdg A) (f : (DGCategoryStruct.dgHom K L).X 0) :
    f ∈ _root_.CategoryTheory.coboundaries K L ↔
      ∃ β : Cochain (of A K) (of A L) (-1), δ (-1) 0 β = f :=
  Iff.rfl

/-! ## Crossing the instance boundary

`Cocycle K L 0` and `↥(cocycles K L)` are the same subtype of the same group,
but `Cocycle` is a `def` carrying `instAddCommGroupCocycle` while the subgroup
carries the one `AddSubgroup` supplies. `AddSubgroup` is indexed by that
instance, so the two subgroup terms do not share a type for `rw`, and an `ext`
proof fails on an application type mismatch rather than on content.

Building the maps explicitly avoids the question: a hand-written
`AddMonoidHom` typechecks by defeq, where instance *matching* would not. -/

/-- This repository's degree-zero cocycles, as Mathlib's. -/
def toCocycle (K L : Cdg A) : ↥(cocycles K L) →+ Cocycle (of A K) (of A L) 0 where
  toFun z := ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- And back. -/
def ofCocycle (K L : Cdg A) : Cocycle (of A K) (of A L) 0 →+ ↥(cocycles K L) where
  toFun z := ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

-- Not `@[simp]`: the left-hand side simplifies further, so it can never be in
-- simp-normal form and the `simpNF` linter rejects it. It is used by name.
lemma toCocycle_val (K L : Cdg A) (z : ↥(cocycles K L)) :
    (toCocycle K L z).1 = z.1 := rfl

-- Not `@[simp]`: the left-hand side simplifies further, so it can never be in
-- simp-normal form and the `simpNF` linter rejects it. It is used by name.
lemma ofCocycle_val (K L : Cdg A) (z : Cocycle (of A K) (of A L) 0) :
    (ofCocycle K L z).1 = z.1 := rfl

lemma ofCocycle_toCocycle (K L : Cdg A) (z : ↥(cocycles K L)) :
    ofCocycle K L (toCocycle K L z) = z := rfl

lemma toCocycle_ofCocycle (K L : Cdg A) (z : Cocycle (of A K) (of A L) 0) :
    toCocycle K L (ofCocycle K L z) = z := rfl

/-- The two subtypes are the same group; only their instance paths differ. -/
def cocycleAddEquiv (K L : Cdg A) : ↥(cocycles K L) ≃+ Cocycle (of A K) (of A L) 0 where
  toFun := toCocycle K L
  invFun := ofCocycle K L
  left_inv := ofCocycle_toCocycle K L
  right_inv := toCocycle_ofCocycle K L
  map_add' _ _ := rfl

/-! ## Lifting the identification to the quotients -/

lemma coboundariesIn_le_comap (K L : Cdg A) :
    H0.coboundariesIn K L ≤
      (HomComplex.coboundaries (of A K) (of A L) 0).comap (toCocycle K L) := by
  intro z hz
  rw [AddSubgroup.mem_comap, HomComplex.mem_coboundaries_iff _ (-1) (by omega)]
  exact hz

lemma coboundaries_le_comap (K L : Cdg A) :
    HomComplex.coboundaries (of A K) (of A L) 0 ≤
      (H0.coboundariesIn K L).comap (ofCocycle K L) := by
  intro z hz
  rw [HomComplex.mem_coboundaries_iff _ (-1) (by omega)] at hz
  exact hz

/-- The Hom-group of `H⁰(C^dg A)` is Mathlib's group of degree-zero cohomology
classes. Both directions are `QuotientAddGroup.map` of the corresponding
`AddMonoidHom`, and both round trips are `rfl` on representatives. -/
def homEquivCohomologyClass (K L : Cdg A) :
    (↥(cocycles K L) ⧸ H0.coboundariesIn K L) ≃+
      CohomologyClass (of A K) (of A L) 0 where
  toFun := QuotientAddGroup.map _ _ (toCocycle K L) (coboundariesIn_le_comap K L)
  invFun := QuotientAddGroup.map _ _ (ofCocycle K L) (coboundaries_le_comap K L)
  left_inv := by rintro ⟨z⟩; rfl
  right_inv := by rintro ⟨z⟩; rfl
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl

/-! ## The Hom-level seam -/

/-- Postcomposition with an isomorphism, as an isomorphism of Hom-groups. Built
by hand because it is used once and the additivity is one `simp`. -/
def postcompAddEquiv {D : Type*} [Category D] [Preadditive D] {X Y Y' : D} (e : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X ⟶ Y') where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := by simp [Preadditive.add_comp]

/-- **The Hom-level seam.** A degree-zero cohomology class in `C^dg A` is a
morphism of the homotopy category, and the correspondence is an isomorphism of
abelian groups.

Everything to the right of `homEquivCohomologyClass` is Mathlib's: the middle
step is `CohomologyClass.homAddEquiv`, and the last undoes the `⟦0⟧` its
statement carries. -/
noncomputable def homSeam (K L : Cdg A) :
    (↥(cocycles K L) ⧸ H0.coboundariesIn K L) ≃+
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (of A K) ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (of A L)) :=
  (homEquivCohomologyClass K L).trans
    (CohomologyClass.homAddEquiv.trans
      (postcompAddEquiv ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapIso
        ((shiftFunctorZero (CochainComplex A ℤ) ℤ).app (of A L)))))

/-! ## The functor `H⁰(C^dg A) ⥤ K(A)` -/

/-- Composition of degree-zero cocycles names composition of morphisms. Both
sides are `z.v i i ≫ w.v i i` in each degree. -/
lemma homOf_comp {K L M : CochainComplex A ℤ} (z : Cocycle K L 0) (w : Cocycle L M 0)
    (hzw : ((z : Cochain K L 0).comp (w : Cochain L M 0) (add_zero 0)) ∈
      HomComplex.cocycle K M 0) :
    Cocycle.homOf ⟨_, hzw⟩ = Cocycle.homOf z ≫ Cocycle.homOf w := by
  ext i
  simp [Cochain.comp_zero_cochain_v]

/-- Two degree-zero cocycles differing by a coboundary name homotopic
morphisms, so they agree in the homotopy category. -/
lemma quotient_map_homOf_eq {K L : CochainComplex A ℤ}
    (z w : Cocycle K L 0) (β : Cochain K L (-1))
    (hβ : (z : Cochain K L 0) = δ (-1) 0 β + (w : Cochain K L 0)) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Cocycle.homOf z) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (Cocycle.homOf w) := by
  refine HomotopyCategory.eq_of_homotopy _ _ ((Cochain.equivHomotopy _ _).symm ⟨β, ?_⟩)
  simpa using hβ

/-- `homOf_comp`, restated with `dgComp` in place of `Cochain.comp`. The two are
the same by `dgComp_eq`, but the functor's goal is built from `dgComp`, and `rw`
matches syntactically. -/
lemma homOf_dgComp {K L M : Cdg A} (z : ↥(cocycles K L)) (w : ↥(cocycles L M))
    (hzw : (DGCategoryStruct.dgComp 0 0 0 (by omega) z.1 w.1) ∈ cocycles K M) :
    Cocycle.homOf (toCocycle K M ⟨_, hzw⟩) =
      Cocycle.homOf (toCocycle K L z) ≫ Cocycle.homOf (toCocycle L M w) :=
  homOf_comp _ _ _

/-- **The seam functor.** `H⁰(C^dg A) ⥤ K(A)`: the identity on objects, sending
a cohomology class to the morphism its representative names. -/
noncomputable def h0Functor : H0 (Cdg A) ⥤ HomotopyCategory A (ComplexShape.up ℤ) where
  obj K := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (of A (H0.of (Cdg A) K))
  map {K L} f :=
    Quotient.liftOn' f
      (fun z => (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (Cocycle.homOf (toCocycle _ _ z)))
      (by
        rintro z w hzw
        obtain ⟨β, hβ⟩ := QuotientAddGroup.leftRel_apply.mp hzw
        -- Everything below stays in the carrier type `((dgHom K L).X _)`, where
        -- `.hom` is an honest `AddMonoidHom` and `map_neg` applies. Mixing that
        -- type with `Cochain` in one expression is what `+` refuses, even
        -- though they are defeq; `exact` crosses the boundary at the end.
        refine quotient_map_homOf_eq (toCocycle _ _ z) (toCocycle _ _ w) (-β) ?_
        have key :
            z.1 = ((DGCategoryStruct.dgHom (H0.of (Cdg A) K) (H0.of (Cdg A) L)).d (-1) 0).hom (-β)
              + w.1 := by
          rw [map_neg, hβ]
          simp
        exact key)

  map_id K := by
    show (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _ = _
    rw [show Cocycle.homOf (toCocycle _ _ ⟨DGCategoryStruct.dgId (H0.of (Cdg A) K),
        DGCategory.dgId_cocycle _⟩) = 𝟙 (of A (H0.of (Cdg A) K)) from
      Cocycle.homOf_ofHom_eq_self _]
    exact (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_id _
  map_comp {K L M} f g := by
    induction f using Quotient.ind with
    | _ z =>
      induction g using Quotient.ind with
      | _ w =>
        show (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _ =
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _ ≫
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _
        rw [homOf_dgComp z w, Functor.map_comp]


/-! ## The seam functor is an equivalence -/

instance : h0Functor (A := A).Faithful where
  map_injective {K L} f g h := by
    induction f using Quotient.ind with
    | _ z =>
      induction g using Quotient.ind with
      | _ w =>
        -- Equal images means the two representatives are homotopic, and a
        -- homotopy is exactly a primitive for their difference.
        obtain ⟨β, hβ⟩ := (Cochain.equivHomotopy _ _)
          (HomotopyCategory.homotopyOfEq _ _ h)
        -- `hβ` is already an identity of `Cochain`s once the `ofHom ∘ homOf`
        -- round trip is collapsed; keeping everything there avoids the carrier.
        rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.cochain_ofHom_homOf_eq_coe] at hβ
        apply QuotientAddGroup.eq.mpr
        refine ⟨-β, ?_⟩
        have key : δ (-1) 0 (-β) =
            -(↑(toCocycle _ _ z) : Cochain (of A (H0.of (Cdg A) K))
                (of A (H0.of (Cdg A) L)) 0) + ↑(toCocycle _ _ w) := by
          rw [δ_neg, hβ]
          abel
        exact key

instance : h0Functor (A := A).Full where
  map_surjective {K L} φ := by
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective φ
    exact ⟨QuotientAddGroup.mk ⟨Cochain.ofHom f, δ_ofHom f⟩, by
      show (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map _ = φ
      rw [show Cocycle.homOf (toCocycle _ _ ⟨Cochain.ofHom f, _⟩) = f from
        Cocycle.homOf_ofHom_eq_self f]
      exact hf⟩

instance : h0Functor (A := A).EssSurj where
  mem_essImage Y := ⟨(Y.as : Cdg A), ⟨Iso.refl _⟩⟩

instance : h0Functor (A := A).IsEquivalence where

/-- **The seam.** `H⁰(C^dg A) ≌ K(A)`: the `H⁰` of the dg category of cochain
complexes is the homotopy category. -/
noncomputable def seam : H0 (Cdg A) ≌ HomotopyCategory A (ComplexShape.up ℤ) :=
  (h0Functor (A := A)).asEquivalence

end Cdg

end CategoryTheory
