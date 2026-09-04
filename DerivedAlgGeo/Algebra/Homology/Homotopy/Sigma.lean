/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Homotopy
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits

/-!
# Homotopies on a coproduct of complexes

A family of homotopies on the summands of a coproduct of complexes assembles into a homotopy
on the coproduct (`Homotopy.sigma`): the components are the degreewise descriptions
`HomologicalComplex.sigmaXDesc` of the given components, and the homotopy identity holds after
restriction to each summand because the differential of the coproduct commutes with the
summand inclusions.  This is what makes the quotient functor to the homotopy category
preserve coproducts.

## Main definitions

* `Homotopy.sigma`: the assembled homotopy.
-/

open CategoryTheory Category Limits

universe w v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {κ : Type w} [HasColimitsOfShape (Discrete κ) C]
  {X : κ → HomologicalComplex C c} {Y : HomologicalComplex C c}

open HomologicalComplex in
/-- Homotopies on the summands of a coproduct assemble to a homotopy on the coproduct: the
components are `sigmaXDesc` of the components, and the homotopy identity holds after
restriction to each summand because the differential of the coproduct commutes with the
summand inclusions. -/
noncomputable def sigma {g g' : ∐ X ⟶ Y}
    (H : ∀ k, Homotopy (Sigma.ι X k ≫ g) (Sigma.ι X k ≫ g')) : Homotopy g g' where
  hom i j := sigmaXDesc (fun k => (H k).hom) i j
  zero i j hij := by
    apply sigmaX_ext_from
    intro k
    rw [ι_f_sigmaXDesc, comp_zero]
    exact (H k).zero i j hij
  comm i := by
    apply sigmaX_ext_from
    intro k
    have hd : (Sigma.ι X k).f i ≫ dNext i (sigmaXDesc fun k => (H k).hom) =
        dNext i (H k).hom := by
      change (Sigma.ι X k).f i ≫ ((∐ X).d i (c.next i) ≫ sigmaXDesc _ (c.next i) i) =
        (X k).d i (c.next i) ≫ (H k).hom (c.next i) i
      rw [← assoc, Hom.comm, assoc, ι_f_sigmaXDesc]
    have hp : (Sigma.ι X k).f i ≫ prevD i (sigmaXDesc fun k => (H k).hom) =
        prevD i (H k).hom := by
      change (Sigma.ι X k).f i ≫ (sigmaXDesc _ i (c.prev i) ≫ Y.d (c.prev i) i) =
        (H k).hom i (c.prev i) ≫ Y.d (c.prev i) i
      rw [← assoc, ι_f_sigmaXDesc]
    rw [Preadditive.comp_add, Preadditive.comp_add, hd, hp, ← comp_f, ← comp_f, (H k).comm i]

end Homotopy
