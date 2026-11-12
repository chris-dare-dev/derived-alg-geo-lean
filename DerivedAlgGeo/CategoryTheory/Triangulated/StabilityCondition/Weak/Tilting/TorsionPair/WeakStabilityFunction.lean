/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Splitting
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.Basic

/-!
# The torsion pair of a weak stability function at a slope cutoff

For a weak stability function `W` on an abelian category with the
Harder--Narasimhan property, and a cutoff `μ₀ : WithTop ℝ`, the two classes of
`CategoryTheory/Abelian/Stability/Weak/Cutoff.lean`

```
T μ₀ = {E | every weak HN slope of E exceeds μ₀}   F μ₀ = {E | every one is at most μ₀}
```

are a `TorsionPair`.  Both axioms are proved:

* `hom_eq_zero` is `hom_eq_zero_of_mem_hnTors_of_mem_hnFree` — the image of a
  map is a quotient of the source and a subobject of the target, so
  `μMinus_le_of_epi` and `μPlus_le_of_mono` trap its slopes in the empty
  interval `(μ₀, μ₀]`;
* `exists_shortExact` is `exists_shortExact_hnTors_hnFree`
  (`CategoryTheory/Abelian/Stability/Weak/Splitting.lean`) — the HN chain cut at
  the index where its slopes cross `μ₀`.

## Main definitions

All in the namespace `CategoryTheory.Triangulated.WeakStabilityFunctionOn`.

* `hnTorsProperty`, `hnFreeProperty` — the torsion and torsion-free classes at
  a weak slope cutoff, as `ObjectProperty`s.
* `hnTorsionPair` — the two classes as a `Tilting.TorsionPair`.

## Main results

* `hnTorsionPair_tors`, `hnTorsionPair_free` — the two classes of the pair.
* `hnTorsProperty_isClosedUnderIsomorphisms`,
  `hnFreeProperty_isClosedUnderIsomorphisms` — both classes are closed under
  isomorphisms.

## Implementation notes

### Where the splitting axiom is delicate

The Hom-vanishing axiom is the strict theory's argument almost verbatim.  The
splitting axiom is not, and the obstruction is two levels below where it looks:
not in `Cutoff.lean` and not in the torsion-pair assembly, but in
`Uniqueness/SubobjectLattice.lean`, whose `pullback_imageSubobject_eq` and
`cokernelPullbackIso` are proved from `semiClosedUpperHalfPlane_ne_zero` —
*a nonzero object has nonzero charge*.  That is exactly the implication weak
stability drops, and it fails on exactly the object the surface case of
Bridgeland's Lemma 6.2 is about.  Both statements are true in any abelian
category; `CategoryTheory/SubobjectCorrespondence.lean` proves them without a
charge, and `CategoryTheory/Abelian/Stability/Weak/Tail.lean` builds the
truncation on top of them.

### Cutoff by slope, not by phase

The strict pair (`TorsionPair/StabilityFunction.lean`) is cut by a phase
`β : ℝ`.  This one is cut by a slope in `WithTop ℝ`, which is what lets a
rank-zero object — slope `⊤`, no phase at all — sit in `T μ₀` at every finite
cutoff (`WeakSlopeData.mem_hnTors_of_rank_zero`).

## References

* Bridgeland, *Stability conditions on K3 surfaces*, arXiv:math/0307164,
  Lemma 6.2.

## Tags

weak stability function, torsion pair, slope cutoff, Harder--Narasimhan
filtration
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Triangulated.Tilting

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

/-- The torsion class at a weak slope cutoff, as an `ObjectProperty`. -/
def hnTorsProperty (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ) :
    ObjectProperty A := fun E => E ∈ hnTors W μ₀

/-- The torsion-free class at a weak slope cutoff, as an `ObjectProperty`. -/
def hnFreeProperty (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ) :
    ObjectProperty A := fun E => E ∈ hnFree W μ₀

instance hnTorsProperty_isClosedUnderIsomorphisms
    (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ) :
    (hnTorsProperty W μ₀).IsClosedUnderIsomorphisms :=
  ⟨fun e h => hnTors_of_iso e h⟩

instance hnFreeProperty_isClosedUnderIsomorphisms
    (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ) :
    (hnFreeProperty W μ₀).IsClosedUnderIsomorphisms :=
  ⟨fun e h => hnFree_of_iso e h⟩

/-- **The two classes at a weak slope cutoff are a torsion pair.** -/
def hnTorsionPair (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ)
    (hHN : W.HasHNProperty) : TorsionPair A where
  tors := hnTorsProperty W μ₀
  free := hnFreeProperty W μ₀
  hom_eq_zero _ _ hX hY f := hom_eq_zero_of_mem_hnTors_of_mem_hnFree hHN hX hY f
  exists_shortExact E := exists_shortExact_hnTors_hnFree hHN (μ₀ := μ₀) E

@[simp]
theorem hnTorsionPair_tors (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ)
    (hHN : W.HasHNProperty) :
    (hnTorsionPair W μ₀ hHN).tors = hnTorsProperty W μ₀ := rfl

@[simp]
theorem hnTorsionPair_free (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ)
    (hHN : W.HasHNProperty) :
    (hnTorsionPair W μ₀ hHN).free = hnFreeProperty W μ₀ := rfl

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
