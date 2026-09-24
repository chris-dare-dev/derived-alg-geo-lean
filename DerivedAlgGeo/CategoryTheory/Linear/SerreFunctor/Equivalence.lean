/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license, as described in the file LICENSE.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Full faithfulness and co-Serre duality

For a right Serre datum `D`, finite-dimensionality of each Hom space identifies
that space with its double dual. Together with the two Serre equivalences this
gives the Hom equivalence induced by `D.S.map`, so `D.S` is fully faithful.
The `HomFinite` assumption is explicit because `Module.evalEquiv` is the
load-bearing double-dual step.

Essential surjectivity is separate supplied data. A `CoSerreFunctorData` is a
chosen functor with the opposite duality and its two naturality laws; it is not
derived from right Serre data. Literature criteria that construct a co-Serre
functor or identify it with a quasi-inverse require hypotheses not formalized
here. The two dualities yield an adjunction, and Hom-finiteness makes both
adjoints fully faithful. We use Mathlib's adjunction-to-equivalence API: its
unit and counit are isomorphisms by those two full-faithfulness results. This
keeps essential surjectivity tied to the co-Serre input.

This module has no shift or triangulated assumptions. In particular it does
not construct a `TriEquiv`; that refinement belongs with the shift-dependent
triangulated theory.
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

/-- Supplied co-Serre duality for a chosen endofunctor.

This is independent input, not a consequence of `SerreFunctorData`. The
literature hypotheses that produce a co-Serre functor or identify it with a
quasi-inverse are not formalized by this repository. -/
structure CoSerreFunctorData where
  /-- The chosen co-Serre endofunctor. -/
  S : C ⥤ C
  /-- Co-Serre duality, pointwise. -/
  eta : ∀ A B : C, Module.Dual k (A ⟶ B) ≃ₗ[k] (S.obj B ⟶ A)
  /-- Naturality in the first, covariant variable. -/
  naturality_left : ∀ {A A' B : C} (f : A ⟶ A')
      (phi : Module.Dual k (A ⟶ B)),
    eta A' B (phi.comp (Linear.leftComp k B f)) = eta A B phi ≫ f
  /-- Naturality in the second, contravariant variable. -/
  naturality_right : ∀ {A B B' : C} (g : B' ⟶ B)
      (phi : Module.Dual k (A ⟶ B)),
    eta A B' (phi.comp (Linear.rightComp k A g)) = S.map g ≫ eta A B phi

variable {k C}

private noncomputable def coSerreHomEquiv [HomFinite k C]
    (D : CoSerreFunctorData k C) (A B : C) :
    (A ⟶ B) ≃ₗ[k] (D.S.obj A ⟶ D.S.obj B) := by
  let e₁ : (A ⟶ B) ≃ₗ[k] Module.Dual k (Module.Dual k (A ⟶ B)) :=
    Module.evalEquiv k (A ⟶ B)
  let e₂ : Module.Dual k (Module.Dual k (A ⟶ B)) ≃ₗ[k]
      Module.Dual k (D.S.obj B ⟶ A) :=
    (D.eta A B).dualMap.symm
  exact e₁.trans (e₂.trans (D.eta (D.S.obj B) A))

private theorem coSerreHomEquiv_apply [HomFinite k C]
    (D : CoSerreFunctorData (k := k) (C := C)) (A B : C) (f : A ⟶ B) :
    coSerreHomEquiv D A B f = D.S.map f := by
  let phi : Module.Dual k (D.S.obj B ⟶ B) :=
    (D.eta (D.S.obj B) B).symm (𝟙 (D.S.obj B))
  have hdual (g : D.S.obj B ⟶ A) : (D.eta A B).symm g =
      phi.comp (Linear.leftComp k B g) := by
    apply (D.eta A B).injective
    simpa [phi] using
      (D.naturality_left (A := D.S.obj B) (A' := A) (B := B) g phi).symm
  have hp : (D.eta A B).dualMap.symm (Module.evalEquiv k (A ⟶ B) f) =
      phi.comp (Linear.rightComp k (D.S.obj B) f) := by
    ext g
    simp only [Module.evalEquiv_apply, LinearMap.comp_apply, Linear.rightComp_apply]
    exact congrArg (fun q : Module.Dual k (A ⟶ B) => q f) (hdual g)
  change D.eta (D.S.obj B) A
      ((D.eta A B).dualMap.symm (Module.evalEquiv k (A ⟶ B) f)) = D.S.map f
  rw [hp]
  simpa [phi] using
    (D.naturality_right (A := D.S.obj B) (B := B) (B' := A) f phi)

/-- A co-Serre functor is fully faithful under finite-dimensional Hom
hypotheses. This is the opposite-category form of the right Serre argument,
written here with the same explicit double-dual step. -/
noncomputable def CoSerreFunctorData.fullyFaithful [HomFinite k C]
    (D : CoSerreFunctorData (k := k) (C := C)) : D.S.FullyFaithful where
  preimage {A B} f := (coSerreHomEquiv D A B).symm f
  map_preimage {A B} f := by
    rw [← coSerreHomEquiv_apply D A B]
    exact (coSerreHomEquiv D A B).apply_symm_apply f
  preimage_map {A B} f := by
    rw [← coSerreHomEquiv_apply D A B]
    exact (coSerreHomEquiv D A B).symm_apply_apply f

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

/-- Package the resulting autoequivalence in the existing Serre category
API. -/
noncomputable def SerreFunctorData.toSerreCategoryData [HomFinite k C]
    (D : SerreFunctorData k C) (E : CoSerreFunctorData (k := k) (C := C)) :
    SerreCategoryData k C :=
  ⟨D, D.isEquivalence E⟩

end CategoryTheory.SerreFunctor
