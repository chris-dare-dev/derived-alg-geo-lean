/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.CompactClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Restriction

/-!
# Semiorthogonal sequences after scheme base change

This file assembles the componentwise K-flat constructions into the three
ordered families appearing in Proposition 3.15 and Theorem 3.17 of
arXiv:1902.08184:

* the perfect-envelope sequence on `Dqc(X_T)`;
* its coproduct-and-extension closure, the quasicoherent sequence;
* the inverse-image sequence on the intrinsic bounded-coherent locus.

The only new geometric input is `PerfectComponentsSemiorthogonal`, the
Hom-vanishing between the perfect envelopes. Compactness of those envelopes
then propagates this input to the quasicoherent components, and faithfulness
of the bounded-coherent inclusion reflects it to the bounded components.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

abbrev SourceDqc (X : SchemeBaseChange S) :=
  Dqc.SchemeQuasicoherentDerivedCategory X.left

abbrev TargetDqc (X T : SchemeBaseChange S) :=
  Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left

namespace KFlatBaseChangeData

variable (A : SemiorthogonalSequence (SourceDqc X) ι)

/-- The geometric Hom-vanishing input between the perfect base-change
envelopes. This obligation is isolated from the formal closure arguments. -/
def PerfectComponentsSemiorthogonal : Prop :=
  ∀ ⦃i j : ι⦄, i < j →
    D.perfectEnvelope (A.component j) ≤
      (D.perfectEnvelope (A.component i)).rightOrthogonal

/-- The sequence of perfect base-change envelopes on `Dqc(X_T)`. -/
def perfectSequence (horth : D.PerfectComponentsSemiorthogonal A) :
    SemiorthogonalSequence (TargetDqc X T) ι where
  component i := D.perfectEnvelope (A.component i)
  semiorthogonal := horth

@[simp]
theorem perfectSequence_component
    (horth : D.PerfectComponentsSemiorthogonal A) (i : ι) :
    (D.perfectSequence A horth).component i =
      D.perfectEnvelope (A.component i) :=
  rfl

/-- Compactness propagates perfect-envelope semiorthogonality to the
quasicoherent base-change components. -/
theorem quasicoherentComponentsSemiorthogonal
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    ∀ ⦃i j : ι⦄, i < j →
      D.quasicoherentComponent (A.component j) ≤
        (D.quasicoherentComponent (A.component i)).rightOrthogonal := by
  intro i j hij
  exact ObjectProperty.coprodClosure_le_rightOrthogonal_coprodClosure
    (D.perfectEnvelope_le_compact (A.component i) hcompact)
    (horth hij)

/-- The quasicoherent base-change sequence `(Dqc)_T`. -/
def quasicoherentSequence
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    SemiorthogonalSequence (TargetDqc X T) ι where
  component i := D.quasicoherentComponent (A.component i)
  semiorthogonal := D.quasicoherentComponentsSemiorthogonal A hcompact horth

@[simp]
theorem quasicoherentSequence_component
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) (i : ι) :
    (D.quasicoherentSequence A hcompact horth).component i =
      D.quasicoherentComponent (A.component i) :=
  rfl

/-- The bounded-coherent base-change sequence `D_T`, obtained by restricting
the quasicoherent sequence along the canonical fully faithful inclusion. -/
def boundedSequence
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    SemiorthogonalSequence
      (Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ T).left) ι :=
  (D.quasicoherentSequence A hcompact horth).inverseImage
    (boundedCoherentFiberToDqc X T)

@[simp]
theorem boundedSequence_component
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) (i : ι) :
    (D.boundedSequence A hcompact horth).component i =
      D.boundedComponent (A.component i) :=
  rfl

/-- The bounded-coherent inclusion is compatible with the bounded and
quasicoherent base-change sequences. -/
theorem boundedSequence_compatible
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.boundedSequence A hcompact horth).CompatibleWith
      (boundedCoherentFiberToDqc X T)
      (D.quasicoherentSequence A hcompact horth) :=
  SemiorthogonalSequence.inverseImage_compatible _ _

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
