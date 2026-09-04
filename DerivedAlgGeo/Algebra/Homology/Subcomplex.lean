/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Subcomplexes from degreewise subobject data

Neither Mathlib nor this repository has a way to build a subcomplex of a `HomologicalComplex`
from a degreewise family of subobjects. Mathlib goes the other way — a mono of complexes is
degreewise mono (`HomologicalComplexLimits.lean`) — and has the degreewise exactness criteria,
but nothing assembles degreewise data into a complex.

This file supplies that. The point worth stating is how little is needed: given objects with
monomorphisms into the ambient complex and differentials that commute with its own, **both**
`HomologicalComplex` laws are automatic. `shape` and `d_comp_d'` are each proved by cancelling
the mono in the next degree, so a caller supplies no coherence beyond the commuting squares.

## Main definitions

* `SubcomplexData`: objects, monos into `K`, and differentials commuting with `K`'s.
* `SubcomplexData.toComplex`: the resulting complex.
* `SubcomplexData.toComplexι`: its inclusion into `K`, a monomorphism of complexes.

## Why this exists

Stacks 13.17.4 (tag 0FCL) — `D⁻(𝓑) → D⁻_𝓑(𝓐)` is an equivalence for a Serre subcategory
`𝓑 ⊆ 𝓐` with the lifting property — is proved by a dévissage that constructs, by descending
induction, subobjects `E^i ⊂ X^i` lying in `𝓑` and assembles them into a subcomplex
quasi-isomorphic to the original. This is the assembly step of that argument, isolated because
it is independent of `𝓑`, of the Serre condition, and of the induction that produces the `E^i`.

## Implementation notes

The data is unbundled from `Subobject`: a family `X` with monos, rather than a family of
`Subobject (K.X i)`. The subobject-valued form needs the restriction condition as an inequality
`(Subobject.«exists» (K.d i j)).obj (S i) ≤ S j` and then has to extract the differential from
it; that is a further step, and this is the primitive it would be built on.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}
  (K : HomologicalComplex V c)

/-- Degreewise subobject data for a complex `K`: an object in each degree, a monomorphism into
`K` in each degree, and differentials commuting with those of `K`. -/
structure SubcomplexData where
  /-- The object in degree `i`. -/
  X : ι → V
  /-- The monomorphism into `K` in degree `i`. -/
  ι : ∀ i, X i ⟶ K.X i
  /-- Each inclusion is a monomorphism; this is what makes the complex laws automatic. -/
  mono : ∀ i, Mono (ι i)
  /-- The restricted differential. -/
  d : ∀ i j, X i ⟶ X j
  /-- The differentials commute with the inclusions. -/
  comm : ∀ i j, d i j ≫ ι j = ι i ≫ K.d i j

namespace SubcomplexData

variable {K} (S : SubcomplexData K)

attribute [instance] SubcomplexData.mono

/-- The subcomplex determined by degreewise subobject data.

Neither complex law is a hypothesis: `shape` holds because `d i j ≫ ι j` factors through
`K.d i j = 0`, and `d_comp_d'` because it factors through `K.d i j ≫ K.d j k = 0`. Both then
follow by cancelling the monomorphism in the target degree. -/
@[simps]
def toComplex : HomologicalComplex V c where
  X := S.X
  d := S.d
  shape i j h := by
    have : S.d i j ≫ S.ι j = 0 := by rw [S.comm, K.shape i j h, comp_zero]
    simpa using (cancel_mono (S.ι j)).1 (by simpa using this)
  d_comp_d' i j k _ _ := by
    have : (S.d i j ≫ S.d j k) ≫ S.ι k = 0 := by
      rw [Category.assoc, S.comm, ← Category.assoc, S.comm, Category.assoc,
        K.d_comp_d, comp_zero]
    simpa using (cancel_mono (S.ι k)).1 (by simpa using this)

/-- The inclusion of the subcomplex into `K`. -/
@[simps]
def toComplexι : S.toComplex ⟶ K where
  f := S.ι
  comm' i j _ := (S.comm i j).symm

/-- The inclusion is a monomorphism of complexes, being one in each degree. -/
instance : Mono S.toComplexι :=
  HomologicalComplex.mono_of_mono_f _ (fun i => S.mono i)

end SubcomplexData

/-- `K` as a subcomplex of itself. -/
@[simps]
def SubcomplexData.top : SubcomplexData K where
  X := K.X
  ι _ := 𝟙 _
  mono _ := inferInstance
  d := K.d
  comm i j := by simp

/-- A degreewise monomorphism of complexes is subcomplex data.

Stated with `[∀ i, Mono (φ.f i)]` rather than `[Mono φ]`: the two agree when the ambient
category has finite limits (`HomologicalComplex.mono_of_mono_f` and its converse), but the
degreewise form is what the construction uses and it needs no hypothesis on `V`. -/
@[simps]
def SubcomplexData.ofDegreewiseMono {L : HomologicalComplex V c} (φ : L ⟶ K)
    [∀ i, Mono (φ.f i)] : SubcomplexData K where
  X := L.X
  ι := φ.f
  mono i := inferInstance
  d := L.d
  comm i j := (φ.comm i j).symm

end HomologicalComplex
