/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Collection

/-!
# An exceptional object in the derived category of a field

The abstract layer gets its real inhabitant: the residue field, as a complex
concentrated in degree zero, is an exceptional object of
`DerivedCategory (ModuleCat k)`, and it assembles into a length-one
exceptional collection with its semiorthogonal sequence. This discharges the
design note's requirement — `.claude/notes/2026-08-28-semiorthogonal-reconnaissance.md`
§4: "issue #852 requires those notions to be added only when a theorem
consumes each property" — for this milestone, with a non-geometric consumer
that leaves the projective-families lane's territory untouched.

## Why this category

`Mathlib/Algebra/Homology/DerivedCategory/Linear.lean` provides
`noncomputable instance : Linear R (DerivedCategory C)` and
`instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R` — the
latter is exactly the shift-linearity hypothesis `IsExceptional.shift` had to
assume in general, and the derived category is one of the few places in
Mathlib where it is a global instance. `HasDerivedCategory.{w} (ModuleCat k)`
is a hypothesis throughout; `HasDerivedCategory.standard` supplies it at
`max u v` for `C : Type u` with `Category.{v} C` — here `u + 1`, since
`ModuleCat.{u} k : Type (u + 1)` — when a caller needs a concrete choice.

## Fullness is not claimed — and is expected to be false

`ObjectProperty.triangEnvelope` reaches only objects assembled from the
generator by shifts, binary products, retracts, and FINITELY many extension
steps (`triangEnvelope = ⨆ n, triangEnvelopeIter n`). An object of the
unbounded `DerivedCategory (ModuleCat k)` with infinitely many nonzero
cohomology objects is not reachable that way, so `IsFull` for the length-one
collection is expected to be FALSE here, not merely unproved. Fullness
belongs to a bounded-derived-category consumer, which this milestone does not
file.

## Main definitions

* `residueObject` — the field in degree zero.
* `exceptionalCollection_residueObject` — the length-one collection over
  `PUnit`, through `ExceptionalCollection.ofExceptional`.

## Main results

* `isExceptional_residueObject` — exceptionality, in three parts:
  endomorphisms through the fully faithful `k`-linear `singleFunctor` and
  `End(k) = k`; positive shifts through projectivity of `k` and the vanishing
  of higher `Ext`; negative shifts through the canonical t-structure.
* `ModuleCat.algebraMap_end_self_bijective` — the base case: evaluation at
  `1` inverts `algebraMap` into the linear endomorphisms of the ring itself.
* `exceptionalCollection_residueObject_component` — the single component is
  the envelope of the shift closure of the residue object.

## References

* Bondal, *Representations of associative algebras and coherent sheaves*,
  Izv. Akad. Nauk SSSR (1989).
* Huybrechts, *Fourier–Mukai Transforms in Algebraic Geometry*, §1.4.

## Tags

exceptional object, derived category, residue field
-/

universe w u

namespace CategoryTheory.ModuleCat

/-- `algebraMap` into the linear endomorphisms of the ring itself is
bijective: evaluation at `1` inverts it. The base case the derived-category
transport stands on; only commutativity enters, so a `CommRing` suffices. -/
theorem algebraMap_end_self_bijective (R : Type u) [CommRing R] :
    Function.Bijective (algebraMap R (End (ModuleCat.of R R))) := by
  constructor
  · intro c c' h
    have := congrArg (fun f => (ModuleCat.Hom.hom f) (1 : R)) h
    simpa [algebraMap_end_apply] using this
  · intro f
    refine ⟨(ModuleCat.Hom.hom f) 1, ?_⟩
    rw [algebraMap_end_apply]
    apply ModuleCat.hom_ext
    ext
    simp [mul_comm]

end CategoryTheory.ModuleCat

namespace CategoryTheory.Triangulated

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (ModuleCat.{u} k)]

/-- The residue field, as a complex concentrated in degree zero.
Deliberately an `abbrev`: instance search must see the `singleFunctor`
application to find the t-structure `IsLE`/`IsGE` instances the negative-shift
argument consumes. -/
noncomputable abbrev residueObject : DerivedCategory (ModuleCat.{u} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)

/-- **The residue field in degree zero is exceptional.** Endomorphisms:
`singleFunctor` is fully faithful and `k`-linear, so `algebraMap`
bijectivity transports from `End(k) = k`. Positive shifts: `k` is projective,
so higher `Ext` vanishes, read through `Ext.homEquiv`. Negative shifts: the
source is `IsLE 0` and the shifted target `IsGE (-n)` for the canonical
t-structure, so the map vanishes by `TStructure.zero`. -/
theorem isExceptional_residueObject : IsExceptional k (residueObject k) := by
  constructor
  · intro n hn f
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · haveI : DerivedCategory.TStructure.t.IsGE
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} k)) n).obj
            (residueObject k)) (-n) :=
        DerivedCategory.TStructure.t.isGE_shift (residueObject k) 0 n (-n)
          (by omega)
      exact DerivedCategory.TStructure.t.zero f 0 (-n) (by omega)
    · haveI := CategoryTheory.hasExt_of_hasDerivedCategory (ModuleCat.{u} k)
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) :=
        ⟨(n - 1).toNat, by omega⟩
      haveI := Abelian.Ext.subsingleton_of_projective (C := ModuleCat.{u} k)
        (ModuleCat.of k k) (ModuleCat.of k k) m
      haveI : Subsingleton (residueObject k ⟶
          (residueObject k)⟦((m + 1 : ℕ) : ℤ)⟧) :=
        (Abelian.Ext.homEquiv (X := ModuleCat.of k k)
          (Y := ModuleCat.of k k) (n := m + 1)).symm.subsingleton
      exact Subsingleton.elim f 0
  · have hcomp : ∀ c : k,
        algebraMap k (End (residueObject k)) c
          = (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
              (algebraMap k (End (ModuleCat.of k k)) c) := by
      intro c
      rw [algebraMap_end_apply, algebraMap_end_apply,
        Functor.Linear.map_smul, Functor.map_id]
    constructor
    · intro c c' hcc
      exact (ModuleCat.algebraMap_end_self_bijective k).1
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map_injective
          (by rw [← hcomp, ← hcomp, hcc]))
    · intro g
      obtain ⟨g', hg'⟩ :=
        (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map_surjective g
      obtain ⟨c, hc⟩ := (ModuleCat.algebraMap_end_self_bijective k).2 g'
      exact ⟨c, by rw [hcomp, hc, hg']⟩

/-- The length-one exceptional collection on the residue object — the honest
inhabitant of `ExceptionalCollection` in the tree, through `ofExceptional`.
Its semiorthogonal sequence exists by the collection layer; fullness is not
claimed, and is expected to fail — see the module docstring. -/
noncomputable def exceptionalCollection_residueObject :
    ExceptionalCollection k (DerivedCategory (ModuleCat.{u} k)) PUnit :=
  ExceptionalCollection.ofExceptional (isExceptional_residueObject k)

/-- The single component of the length-one collection is the triangulated
envelope of the shift closure of the residue object. -/
@[simp]
theorem exceptionalCollection_residueObject_component :
    (exceptionalCollection_residueObject k).component PUnit.unit
      = (ObjectProperty.shiftClosure
          (fun X => X = residueObject k) ℤ).triangEnvelope :=
  rfl

end CategoryTheory.Triangulated
