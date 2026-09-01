/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Relative

/-!
# Comparing the repository's perfect-complex notions

The repository uses three deliberately different notions:

* `schemePerfect X` is the absolute thick envelope of finite locally free
  coherent sheaves in `D(Coh X)`;
* `schemeRelativePerfect p` is pseudo-coherence plus local finite Tor
  amplitude over a chosen morphism `p`, inside `Dqc(X)`;
* `Coh.TwoTermPerfectDeterminantData F` is explicit presentation data for a
  degree-zero coherent sheaf, restricted to a two-term finite locally free
  resolution.

Only the valid forgetful direction involving the presentation data is proved
here: a two-term resolution gives an absolute perfect object, which then maps
to the defining essential image of perfect objects in `Dqc(X)`. Relative
perfection depends on the base morphism and is not identified with absolute
perfection without an additional geometric theorem.
-/

namespace AlgebraicGeometry

open CategoryTheory
open AlgebraicGeometry.DerivedCategory.Dqc

universe u

/-- Relative perfection always includes pseudo-coherence. It does not, by
itself, identify the object with the absolute perfect locus in `Dqc(X)`. -/
theorem schemeRelativePerfect_le_schemePseudoCoherent
    {X S : Scheme.{u}} (p : X ⟶ S) :
    schemeRelativePerfect p ≤ schemePseudoCoherent X :=
  fun _ hE ↦ hE.1

end AlgebraicGeometry

namespace AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc

noncomputable section

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {F : Coh X}

/-- The degree-zero coherent-derived object represented by the target sheaf
of a two-term finite locally free resolution. -/
noncomputable def derivedObject (_D : TwoTermPerfectDeterminantData F) :
    SchemeCoherentDerivedCategory X :=
  (DerivedCategory.singleFunctor (Coh X) 0).obj F

/-- A two-term finite locally free resolution places its degree-zero target
in the absolute perfect thick envelope. -/
theorem derivedObject_mem_schemePerfect
    (D : TwoTermPerfectDeterminantData F) :
    schemePerfect X D.derivedObject := by
  letI : (schemeFiniteLocallyFreeGenerator X).Nonempty :=
    ⟨_, SchemePerfectDerivedCategory.structureSheaf_mem_generator X⟩
  change (schemeFiniteLocallyFreeGenerator X).triangEnvelope D.derivedObject
  have hleft : (schemeFiniteLocallyFreeGenerator X).triangEnvelope
      ((DerivedCategory.singleFunctor (Coh X) 0).obj D.resolution.X₁) :=
    (schemeFiniteLocallyFreeGenerator X).le_triangEnvelope _
      ⟨D.resolution.X₁, D.left.rank,
        ⟨D.left.finiteLocallyFree⟩, ⟨Iso.refl _⟩⟩
  have hmiddle : (schemeFiniteLocallyFreeGenerator X).triangEnvelope
      ((DerivedCategory.singleFunctor (Coh X) 0).obj D.resolution.X₂) :=
    (schemeFiniteLocallyFreeGenerator X).le_triangEnvelope _
      ⟨D.resolution.X₂, D.middle.rank,
        ⟨D.middle.finiteLocallyFree⟩, ⟨Iso.refl _⟩⟩
  have hright : (schemeFiniteLocallyFreeGenerator X).triangEnvelope
      ((DerivedCategory.singleFunctor (Coh X) 0).obj D.resolution.X₃) :=
    (schemeFiniteLocallyFreeGenerator X).triangEnvelope.ext_of_isTriangulatedClosed₃
      D.shortExact.singleTriangle D.shortExact.singleTriangle_distinguished
        hleft hmiddle
  exact (schemeFiniteLocallyFreeGenerator X).triangEnvelope.prop_of_iso
    ((DerivedCategory.singleFunctor (Coh X) 0).mapIso D.targetIso) hright

/-- Forget two-term presentation data to the canonical absolute perfect
derived category. -/
noncomputable def toSchemePerfectDerivedCategory
    (D : TwoTermPerfectDeterminantData F) :
    SchemePerfectDerivedCategory X :=
  ⟨D.derivedObject, D.derivedObject_mem_schemePerfect⟩

/-- The absolute perfect object supplied by a two-term resolution, mapped to
the honest `Dqc(X)` locus. -/
noncomputable def toDqc (D : TwoTermPerfectDeterminantData F) :
    SchemeQuasicoherentDerivedCategory X :=
  (SchemeBoundedCoherentDqcCategory.ι X).obj
    ((perfectDerivedToDqc X).obj D.toSchemePerfectDerivedCategory)

/-- The `Dqc(X)` object obtained from a two-term finite locally free
resolution belongs to the canonical absolute-perfect essential image. -/
theorem toDqc_mem_schemePerfectInDqc
    (D : TwoTermPerfectDeterminantData F) :
    schemePerfectInDqc X D.toDqc :=
  perfectDerivedToDqc_obj_mem_schemePerfectInDqc X
    D.toSchemePerfectDerivedCategory

end

end AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData
