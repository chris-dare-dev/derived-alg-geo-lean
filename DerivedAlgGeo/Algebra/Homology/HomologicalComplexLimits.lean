/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Coproducts of homological complexes, degreewise

A coproduct of homological complexes is computed degreewise: evaluation in each degree
preserves it.  This file names the degreewise identification (`sigmaXIso`), the two
summand-inclusion lemmas, extensionality for maps out of a degree of the coproduct
(`sigmaX_ext_from`), and the degreewise description of a family of maps out of the summands
(`sigmaXDesc`), in the shape of Mathlib's `biprodXIso` for binary biproducts.  The consumer is
`Homotopy.sigma`, which assembles homotopies on the summands into one on the coproduct.

## Main definitions

* `HomologicalComplex.sigmaXIso`: `(∐ X).X i ≅ ∐ fun k => (X k).X i`.
* `HomologicalComplex.sigmaXDesc`: the degreewise map out of `(∐ X).X i` assembled from maps
  out of the summands.

## Main results

* `HomologicalComplex.ι_f_sigmaXIso_hom`, `ι_sigmaXIso_inv`: the summand inclusions on both
  sides of the identification.
* `HomologicalComplex.sigmaX_ext_from`: maps out of `(∐ X).X i` are determined by their
  restrictions to the summands.

## Implementation notes

`sigmaXIso` is `PreservesCoproduct.iso (eval C c i) X` rather than
`asIso (sigmaComparison (eval C c i) X)`: inside a definition, the `IsIso` search for the
comparison enters the coproduct instance on `HomologicalComplex C c` and does not terminate.
-/

open CategoryTheory Category Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  {κ : Type w} [HasColimitsOfShape (Discrete κ) C] (X : κ → HomologicalComplex C c)

/-- Evaluation at `i` preserves the coproduct; see the implementation notes for the choice of
spelling. -/
noncomputable def sigmaXIso (i : ι) : (∐ X).X i ≅ ∐ fun k => (X k).X i :=
  PreservesCoproduct.iso (eval C c i) X

@[reassoc (attr := simp)]
lemma ι_sigmaXIso_inv (k : κ) (i : ι) :
    Sigma.ι (fun k => (X k).X i) k ≫ (sigmaXIso X i).inv = (Sigma.ι X k).f i :=
  ι_comp_sigmaComparison (eval C c i) X k

@[reassoc (attr := simp)]
lemma ι_f_sigmaXIso_hom (k : κ) (i : ι) :
    (Sigma.ι X k).f i ≫ (sigmaXIso X i).hom = Sigma.ι (fun k => (X k).X i) k := by
  rw [← ι_sigmaXIso_inv X k i, assoc, Iso.inv_hom_id, comp_id]

variable {X}

/-- Maps out of `(∐ X).X i` are determined by their restrictions to the summands, since
evaluation preserves the coproduct. -/
lemma sigmaX_ext_from {i : ι} {A : C} {f g : (∐ X).X i ⟶ A}
    (h : ∀ k, (Sigma.ι X k).f i ≫ f = (Sigma.ι X k).f i ≫ g) : f = g := by
  rw [← cancel_epi (sigmaXIso X i).inv]
  ext k
  simp only [ι_sigmaXIso_inv_assoc, h k]

variable {Y : HomologicalComplex C c}

/-- The degreewise map out of `(∐ X).X i` assembled from maps out of the summands: the
degreewise identification followed by `Sigma.desc`. -/
noncomputable def sigmaXDesc (φ : ∀ k, ∀ i j, (X k).X i ⟶ Y.X j) (i j : ι) :
    (∐ X).X i ⟶ Y.X j :=
  (sigmaXIso X i).hom ≫ Sigma.desc fun k => φ k i j

@[reassoc (attr := simp)]
lemma ι_f_sigmaXDesc (φ : ∀ k, ∀ i j, (X k).X i ⟶ Y.X j) (k : κ) (i j : ι) :
    (Sigma.ι X k).f i ≫ sigmaXDesc φ i j = φ k i j := by
  simp only [sigmaXDesc, ι_f_sigmaXIso_hom_assoc, Sigma.ι_desc]

end HomologicalComplex
