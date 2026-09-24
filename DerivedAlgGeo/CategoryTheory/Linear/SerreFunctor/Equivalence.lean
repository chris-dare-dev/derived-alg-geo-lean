/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license, as described in the file LICENSE.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Basic
import DerivedAlgGeo.CategoryTheory.Linear.Opposite
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Full faithfulness and co-Serre duality

Finite-dimensionality of all Hom spaces lets right Serre duality identify each
Hom space with its double dual. This module uses that identification and the
naturality laws to prove full faithfulness, and derives an equivalence only
when independent co-Serre data is supplied.

## Main definitions

`CoSerreFunctorData` abbreviates the canonical `SerreFunctorData k Cᵒᵖ` root.
Its functor and duality accessors view that opposite-category presentation on
`C`.

## Main results

`SerreFunctorData.fullyFaithful` and `CoSerreFunctorData.fullyFaithful` use
double-dual evaluation. `CoSerreFunctorData.adjunction` combines the two
dualities without a Hom-finiteness assumption. `SerreFunctorData.isEquivalence`
uses that adjunction and the full faithfulness of both functors.

## Implementation notes

The adjunction is oriented `E.S ⊣ D.S`; the co-Serre witness supplies essential
surjectivity rather than being inferred from right Serre data. This module
needs no shift or triangulated structure.

## References

A. I. Bondal and M. M. Kapranov, “Representable functors, Serre functors, and
reconstructions,” *Math. USSR-Izv.* 35 (1990), 519–541.

## Tags

Serre functor, co-Serre functor, full faithfulness, Hom-finite, adjunction
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C]

private noncomputable def serreHomEquiv [HomFinite k C]
    (D : SerreFunctorData k C) (A B : C) :
    (A ⟶ B) ≃ₗ[k] (D.S.obj A ⟶ D.S.obj B) := by
  let e₁ : (A ⟶ B) ≃ₗ[k] Module.Dual k (Module.Dual k (A ⟶ B)) :=
    Module.evalEquiv k (A ⟶ B)
  let e₂ : Module.Dual k (Module.Dual k (A ⟶ B)) ≃ₗ[k]
      Module.Dual k (B ⟶ D.S.obj A) :=
    (D.eta A B).symm.dualMap
  exact e₁.trans (e₂.trans (D.eta B (D.S.obj A)))

private theorem serreHomEquiv_apply [HomFinite k C] (D : SerreFunctorData k C)
    (A B : C) (f : A ⟶ B) : serreHomEquiv k C D A B f = D.S.map f := by
  let phi : Module.Dual k (A ⟶ D.S.obj A) :=
    (D.eta A (D.S.obj A)).symm (𝟙 (D.S.obj A))
  have hdual (g : B ⟶ D.S.obj A) : (D.eta A B).symm g =
      phi.comp (Linear.rightComp k A g) := by
    apply (D.eta A B).injective
    simpa [phi] using
      (D.naturality_right (A := A) (B := D.S.obj A) (B' := B) g phi).symm
  have hp : (D.eta A B).symm.dualMap (Module.evalEquiv k (A ⟶ B) f) =
      phi.comp (Linear.leftComp k (D.S.obj A) f) := by
    ext g
    simp only [Module.evalEquiv_apply, LinearMap.comp_apply, Linear.leftComp_apply]
    exact congrArg (fun q : Module.Dual k (A ⟶ B) => q f) (hdual g)
  change D.eta B (D.S.obj A)
      ((D.eta A B).symm.dualMap (Module.evalEquiv k (A ⟶ B) f)) = D.S.map f
  rw [hp]
  simpa [phi] using D.naturality_left f phi

/-- A right Serre functor is fully faithful when every Hom space is
finite-dimensional. The proof uses `Module.evalEquiv` for the named
double-dual step. -/
noncomputable def SerreFunctorData.fullyFaithful [HomFinite k C]
    (D : SerreFunctorData k C) : D.S.FullyFaithful where
  preimage {A B} f := (serreHomEquiv k C D A B).symm f
  map_preimage {A B} f := by
    rw [← serreHomEquiv_apply k C D A B]
    exact (serreHomEquiv k C D A B).apply_symm_apply f
  preimage_map {A B} f := by
    rw [← serreHomEquiv_apply k C D A B]
    exact (serreHomEquiv k C D A B).symm_apply_apply f

/-! A co-Serre witness is the right Serre-data root on the opposite category.
This abbreviation keeps the same canonical duality fields rather than
introducing a second structure with mirrored data. -/
abbrev CoSerreFunctorData := SerreFunctorData k Cᵒᵖ

variable {k C}

private def homOpLinearEquiv (A B : C) :
    (A ⟶ B) ≃ₗ[k] (Opposite.op B ⟶ Opposite.op A) where
  toFun f := f.op
  invFun f := f.unop
  left_inv f := rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

private def homUnopLinearEquiv (A B : Cᵒᵖ) :
    (A ⟶ B) ≃ₗ[k] (Opposite.unop B ⟶ Opposite.unop A) where
  toFun f := f.unop
  invFun f := f.op
  left_inv f := rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

private theorem homOpLinearEquiv_dual_leftComp {A A' B : C} (f : A ⟶ A')
    (phi : Module.Dual k (A ⟶ B)) :
    (homOpLinearEquiv (k := k) A' B).dualMap.symm
        (phi.comp (Linear.leftComp k B f)) =
      ((homOpLinearEquiv (k := k) A B).dualMap.symm phi).comp
        (Linear.rightComp k (Opposite.op B) f.op) := by
  ext g
  simp [homOpLinearEquiv, Linear.leftComp, Linear.rightComp]

private theorem homOpLinearEquiv_dual_rightComp {A B B' : C} (g : B' ⟶ B)
    (phi : Module.Dual k (A ⟶ B)) :
    (homOpLinearEquiv (k := k) A B').dualMap.symm
        (phi.comp (Linear.rightComp k A g)) =
      ((homOpLinearEquiv (k := k) A B).dualMap.symm phi).comp
        (Linear.leftComp k (Opposite.op A) g.op) := by
  ext f
  simp [homOpLinearEquiv, Linear.leftComp, Linear.rightComp]

namespace CoSerreFunctorData

/-- View the opposite-category Serre endofunctor as an endofunctor of `C`. -/
def S (D : CoSerreFunctorData (k := k) (C := C)) : C ⥤ C :=
  (SerreFunctorData.S D).unop

/-- View opposite-category Serre duality in the co-Serre orientation on `C`. -/
def eta (D : CoSerreFunctorData (k := k) (C := C)) (A B : C) :
    Module.Dual k (A ⟶ B) ≃ₗ[k] (D.S.obj B ⟶ A) := by
  let eSource := homOpLinearEquiv (k := k) A B
  let eTarget :=
    homUnopLinearEquiv (k := k) (Opposite.op A)
      ((SerreFunctorData.S D).obj (Opposite.op B))
  exact eSource.dualMap.symm.trans
    ((SerreFunctorData.eta D (Opposite.op B) (Opposite.op A)).trans eTarget)

/-- Naturality in the first variable, transported from opposite-category
Serre naturality. -/
theorem naturality_left (D : CoSerreFunctorData (k := k) (C := C))
    {A A' B : C} (f : A ⟶ A') (phi : Module.Dual k (A ⟶ B)) :
    D.eta A' B (phi.comp (Linear.leftComp k B f)) = D.eta A B phi ≫ f := by
  let eTarget := homUnopLinearEquiv (k := k) (Opposite.op A')
    ((SerreFunctorData.S D).obj (Opposite.op B))
  change eTarget
      (SerreFunctorData.eta D (Opposite.op B) (Opposite.op A')
        ((homOpLinearEquiv (k := k) A' B).dualMap.symm
          (phi.comp (Linear.leftComp k B f)))) =
    eTarget
      (f.op ≫ SerreFunctorData.eta D (Opposite.op B) (Opposite.op A)
        ((homOpLinearEquiv (k := k) A B).dualMap.symm phi))
  rw [homOpLinearEquiv_dual_leftComp]
  exact congrArg eTarget
    (SerreFunctorData.naturality_right D (f.op)
      ((homOpLinearEquiv (k := k) A B).dualMap.symm phi))

/-- Naturality in the second variable, transported from opposite-category
Serre naturality. -/
theorem naturality_right (D : CoSerreFunctorData (k := k) (C := C))
    {A B B' : C} (g : B' ⟶ B) (phi : Module.Dual k (A ⟶ B)) :
    D.eta A B' (phi.comp (Linear.rightComp k A g)) = D.S.map g ≫ D.eta A B phi := by
  let eTarget := homUnopLinearEquiv (k := k) (Opposite.op A)
    ((SerreFunctorData.S D).obj (Opposite.op B'))
  change eTarget
      (SerreFunctorData.eta D (Opposite.op B') (Opposite.op A)
        ((homOpLinearEquiv (k := k) A B').dualMap.symm
          (phi.comp (Linear.rightComp k A g)))) =
    eTarget
      (SerreFunctorData.eta D (Opposite.op B) (Opposite.op A)
        ((homOpLinearEquiv (k := k) A B).dualMap.symm phi) ≫
        (SerreFunctorData.S D).map (g.op))
  rw [homOpLinearEquiv_dual_rightComp]
  exact congrArg eTarget
    (SerreFunctorData.naturality_left D (g.op)
      ((homOpLinearEquiv (k := k) A B).dualMap.symm phi))

end CoSerreFunctorData
/-- A co-Serre functor is fully faithful under finite-dimensional Hom
hypotheses. This reuses full faithfulness of the canonical Serre-data root on
the opposite category. -/
noncomputable def CoSerreFunctorData.fullyFaithful [HomFinite k C]
    (D : CoSerreFunctorData (k := k) (C := C)) : D.S.FullyFaithful := by
  letI : HomFinite k Cᵒᵖ := ⟨fun A B => by
    exact Module.Finite.equiv (homUnopLinearEquiv (k := k) A B).symm⟩
  change (SerreFunctorData.S D).unop.FullyFaithful
  exact (SerreFunctorData.fullyFaithful (k := k) (C := Cᵒᵖ) D).unop

/-- The two pointwise dualities give an adjunction `D.S ⊣ E.S`.

Hom-finiteness is not needed for this adjunction: only the two supplied
duality equivalences and their naturality equations enter the Hom-set
equivalence. -/
noncomputable def CoSerreFunctorData.adjunction
    (D : CoSerreFunctorData (k := k) (C := C))
    (E : SerreFunctorData k C) : D.S ⊣ E.S :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => (D.eta Y X).symm.trans (E.eta Y X)
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      change D.eta Y X' ((E.eta Y X').symm (f ≫ g)) =
        D.S.map f ≫ D.eta Y X ((E.eta Y X).symm g)
      rw [← D.naturality_right f ((E.eta Y X).symm g)]
      apply congrArg (D.eta Y X')
      apply (E.eta Y X').injective
      simpa using (E.naturality_right f ((E.eta Y X).symm g)).symm
    homEquiv_naturality_right := by
      intro X Y Y' f g
      change E.eta Y' X ((D.eta Y' X).symm (f ≫ g)) =
        E.eta Y X ((D.eta Y X).symm f) ≫ E.S.map g
      rw [← E.naturality_left g ((D.eta Y X).symm f)]
      apply congrArg (E.eta Y' X)
      apply (D.eta Y' X).injective
      simpa using (D.naturality_left g ((D.eta Y X).symm f)).symm
  }

/-- Right Serre data is an equivalence when a co-Serre witness is also
supplied. The proof uses the adjunction from `CoSerreFunctorData.adjunction`;
full faithfulness of both adjoints makes its unit and counit isomorphisms. -/
theorem SerreFunctorData.isEquivalence [HomFinite k C]
    (D : SerreFunctorData k C) (E : CoSerreFunctorData (k := k) (C := C)) :
    D.S.IsEquivalence := by
  letI : D.S.Full := D.fullyFaithful.full
  letI : D.S.Faithful := D.fullyFaithful.faithful
  letI : E.S.Full := E.fullyFaithful.full
  letI : E.S.Faithful := E.fullyFaithful.faithful
  let h : E.S ⊣ D.S := E.adjunction D
  letI : ∀ X, IsIso (h.unit.app X) := fun X => by infer_instance
  letI : ∀ X, IsIso (h.counit.app X) := fun X => by infer_instance
  exact h.toEquivalence.isEquivalence_inverse

/-- Use this adapter when a downstream API requires the stronger
`SerreCategoryData` package; keeping the co-Serre witness explicit prevents
right Serre data from being silently upgraded to an autoequivalence. -/
noncomputable def SerreFunctorData.toSerreCategoryData [HomFinite k C]
    (D : SerreFunctorData k C) (E : CoSerreFunctorData (k := k) (C := C)) :
    SerreCategoryData k C :=
  ⟨D, D.isEquivalence E⟩

end CategoryTheory.SerreFunctor
