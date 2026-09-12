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

The geometric semiorthogonality input is split into an additive Hom reduction
(`ExternalProductHomReduction`) and the statement that its source-side
objects remain in the later component (`PreservesSourceComponents`). Source
semiorthogonality then proves Hom-vanishing between shifts of the concrete
external products. Formal closure extends this first to the perfect envelopes
and then, using compactness, to the quasicoherent components. Faithfulness of
the bounded-coherent inclusion reflects it to the bounded components.
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

/-- The compact-object model for `Perf(X_T)`. -/
abbrev TargetPerfect (X T : SchemeBaseChange S) :=
  (ObjectProperty.compactObjects.{u} (C := TargetDqc X T)).FullSubcategory

/-- The canonical inclusion of the compact-object model of `Perf(X_T)` into
`Dqc(X_T)`. -/
abbrev targetPerfectToDqc (X T : SchemeBaseChange S) :
    TargetPerfect X T ⥤ TargetDqc X T :=
  (ObjectProperty.compactObjects.{u} (C := TargetDqc X T)).ι

namespace KFlatBaseChangeData

/-- Closing the shifted K-flat generators under triangles and retracts gives
the same perfect envelope as closing the unshifted generators. -/
theorem shiftedPerfectGenerators_triangEnvelope_eq
    (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    [P.ContainsZero] :
    (D.shiftedPerfectGenerators P).triangEnvelope = D.perfectEnvelope P := by
  letI : (D.perfectGenerators P).Nonempty :=
    perfectBaseChangeGenerators_nonempty X T P (D.externalProduct P)
  exact ObjectProperty.shiftClosure_triangEnvelope_eq (D.perfectGenerators P)

variable (A : SemiorthogonalSequence (SourceDqc X) ι)

/-- The geometric Hom-vanishing statement on the concrete K-flat external
products. It is quantified over shifts because the perfect components are
their triangulated envelopes. -/
def PerfectExternalProductsSemiorthogonal : Prop :=
  ∀ ⦃i j : ι⦄, i < j →
    ∀ (Fi : SourcePerfectPartCategory X (A.component i))
      (Gi : CompactDqcFiber T)
      (Fj : SourcePerfectPartCategory X (A.component j))
      (Gj : CompactDqcFiber T) (a b : ℤ)
      (f : (((D.externalProduct (A.component i)).obj Fi).obj Gi)⟦a⟧ ⟶
        (((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧),
      f = 0

/-- A tensor-duality/adjunction reduction for morphisms between K-flat
external products.

The reduced object is deliberately separate from any component-membership
claim. In a geometric construction, `homEquiv` is the composite of tensor
duality and pullback-pushforward adjunction; preservation of components is
the additional `S`-linearity/projection-formula input below. -/
structure ExternalProductHomReduction where
  /-- The source-side object representing morphisms out of the earlier
  external-product factor. -/
  reductionObject :
    ∀ ⦃j : ι⦄, SourcePerfectPartCategory X (A.component j) →
      CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → SourceDqc X
  /-- The additive Hom equivalence obtained from duality and adjunction. -/
  homEquiv :
    ∀ ⦃i j : ι⦄ (Fi : SourcePerfectPartCategory X (A.component i))
      (Gi : CompactDqcFiber T)
      (Fj : SourcePerfectPartCategory X (A.component j))
      (Gj : CompactDqcFiber T) (a b : ℤ),
      ((((D.externalProduct (A.component i)).obj Fi).obj Gi)⟦a⟧ ⟶
          (((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧) ≃+
        (Fi.obj ⟶ reductionObject Fj Gi Gj a b)

namespace ExternalProductHomReduction

/-- The source-side reductions stay in the component of their later
external-product factor. This is the `S`-linearity/projection-formula half of
the geometric argument. -/
def PreservesSourceComponents
    (R : D.ExternalProductHomReduction A) : Prop :=
  ∀ ⦃j : ι⦄ (Fj : SourcePerfectPartCategory X (A.component j))
    (Gi Gj : CompactDqcFiber T) (a b : ℤ),
    A.component j (R.reductionObject Fj Gi Gj a b)

/-- Source semiorthogonality kills every target morphism after an additive
Hom reduction whose reduced objects remain in the later component. -/
theorem hom_eq_zero (R : D.ExternalProductHomReduction A)
    (hR : R.PreservesSourceComponents) ⦃i j : ι⦄ (hij : i < j)
    (Fi : SourcePerfectPartCategory X (A.component i))
    (Gi : CompactDqcFiber T)
    (Fj : SourcePerfectPartCategory X (A.component j))
    (Gj : CompactDqcFiber T) (a b : ℤ)
    (f : (((D.externalProduct (A.component i)).obj Fi).obj Gi)⟦a⟧ ⟶
      (((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧) :
    f = 0 := by
  apply (R.homEquiv Fi Gi Fj Gj a b).injective
  rw [map_zero]
  exact A.hom_eq_zero hij Fi.property.1
    (hR Fj Gi Gj a b) ((R.homEquiv Fi Gi Fj Gj a b) f)

end ExternalProductHomReduction

/-- Tensor-duality/adjunction Hom reduction plus source-component
preservation proves the concrete external-product semiorthogonality
obligation. -/
theorem perfectExternalProductsSemiorthogonal_of_homReduction
    (R : D.ExternalProductHomReduction A)
    (hR : R.PreservesSourceComponents) :
    D.PerfectExternalProductsSemiorthogonal A := by
  intro i j hij Fi Gi Fj Gj a b f
  exact ExternalProductHomReduction.hom_eq_zero
    (D := D) (A := A) R hR hij Fi Gi Fj Gj a b f

/-- The generator-level geometric Hom-vanishing input: every shifted
external-product generator from a later component is right orthogonal to
every shifted external-product generator from an earlier component. -/
def ShiftedPerfectGeneratorsSemiorthogonal : Prop :=
  ∀ ⦃i j : ι⦄, i < j →
    D.shiftedPerfectGenerators (A.component j) ≤
      (D.shiftedPerfectGenerators (A.component i)).rightOrthogonal

/-- Morphism-level vanishing for the concrete external products implies
semiorthogonality of their shift-and-isomorphism closures. -/
theorem shiftedPerfectGeneratorsSemiorthogonal_of_externalProducts
    (horth : D.PerfectExternalProductsSemiorthogonal A) :
    D.ShiftedPerfectGeneratorsSemiorthogonal A := by
  intro i j hij V hV U f hU
  rcases hU with ⟨Ui, a, eU, Fi, Gi, ⟨eUi⟩⟩
  rcases hV with ⟨Vj, b, eV, Fj, Gj, ⟨eVj⟩⟩
  let eSource :
      (((D.externalProduct (A.component i)).obj Fi).obj Gi)⟦a⟧ ≅ U :=
    ((shiftFunctor (TargetDqc X T) a).mapIso eUi).trans eU.symm
  let eTarget : V ≅
      (((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧ :=
    eV.trans ((shiftFunctor (TargetDqc X T) b).mapIso eVj).symm
  rw [← cancel_epi eSource.hom, ← cancel_mono eTarget.hom]
  simpa [Category.assoc] using
    horth hij Fi Gi Fj Gj a b (eSource.hom ≫ f ≫ eTarget.hom)

/-- Shifted-generator semiorthogonality implies the concrete morphism-level
vanishing statement. -/
theorem perfectExternalProductsSemiorthogonal_of_shiftedGenerators
    (horth : D.ShiftedPerfectGeneratorsSemiorthogonal A) :
    D.PerfectExternalProductsSemiorthogonal A := by
  intro i j hij Fi Gi Fj Gj a b f
  exact horth hij _
    (D.externalProduct_shift_mem_shiftedPerfectGenerators
      (A.component j) Fj Gj b) f
    (D.externalProduct_shift_mem_shiftedPerfectGenerators
      (A.component i) Fi Gi a)

/-- The paper-facing Hom-vanishing statement is exactly shifted-generator
semiorthogonality. -/
theorem perfectExternalProductsSemiorthogonal_iff_shiftedGenerators :
    D.PerfectExternalProductsSemiorthogonal A ↔
      D.ShiftedPerfectGeneratorsSemiorthogonal A :=
  ⟨D.shiftedPerfectGeneratorsSemiorthogonal_of_externalProducts A,
    D.perfectExternalProductsSemiorthogonal_of_shiftedGenerators A⟩

/-- The geometric Hom-vanishing input between the perfect base-change
envelopes. This obligation is isolated from the formal closure arguments. -/
def PerfectComponentsSemiorthogonal : Prop :=
  ∀ ⦃i j : ι⦄, i < j →
    D.perfectEnvelope (A.component j) ≤
      (D.perfectEnvelope (A.component i)).rightOrthogonal

/-- Generator-level semiorthogonality implies semiorthogonality of the
perfect base-change envelopes. All closure under shifts, cones, and retracts
is discharged formally. -/
theorem perfectComponentsSemiorthogonal_of_shiftedGenerators
    (hA : A.HasTriangulatedComponents)
    (horth : D.ShiftedPerfectGeneratorsSemiorthogonal A) :
    D.PerfectComponentsSemiorthogonal A := by
  intro i j hij
  letI : (A.component i).IsTriangulated := hA i
  letI : (A.component j).IsTriangulated := hA j
  simpa only [D.shiftedPerfectGenerators_triangEnvelope_eq] using
    ObjectProperty.triangEnvelope_le_rightOrthogonal_triangEnvelope
      (D.shiftedPerfectGenerators (A.component i))
      (D.shiftedPerfectGenerators (A.component j)) (horth hij)

/-- Concrete shifted external-product Hom-vanishing implies
semiorthogonality of the perfect base-change envelopes. -/
theorem perfectComponentsSemiorthogonal_of_externalProducts
    (hA : A.HasTriangulatedComponents)
    (horth : D.PerfectExternalProductsSemiorthogonal A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_shiftedGenerators A hA
    (D.shiftedPerfectGeneratorsSemiorthogonal_of_externalProducts A horth)

/-- A tensor-duality/adjunction Hom reduction whose reduced objects stay in
the later source component implies semiorthogonality of the perfect
base-change envelopes. -/
theorem perfectComponentsSemiorthogonal_of_homReduction
    (hA : A.HasTriangulatedComponents)
    (R : D.ExternalProductHomReduction A)
    (hR : R.PreservesSourceComponents) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_externalProducts A hA
    (D.perfectExternalProductsSemiorthogonal_of_homReduction A R hR)

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

/-- The perfect base-change sequence on the compact-object model of
`Perf(X_T)`, obtained by restricting the ambient perfect-envelope sequence. -/
def perfectCategorySequence
    (horth : D.PerfectComponentsSemiorthogonal A) :
    SemiorthogonalSequence (TargetPerfect X T) ι :=
  (D.perfectSequence A horth).inverseImage (targetPerfectToDqc X T)

@[simp]
theorem perfectCategorySequence_component
    (horth : D.PerfectComponentsSemiorthogonal A) (i : ι) :
    (D.perfectCategorySequence A horth).component i =
      (D.perfectEnvelope (A.component i)).inverseImage
        (targetPerfectToDqc X T) :=
  rfl

/-- The compact-object inclusion is compatible with the perfect-category and
ambient perfect-envelope sequences. -/
theorem perfectCategorySequence_compatible
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.perfectCategorySequence A horth).CompatibleWith
      (targetPerfectToDqc X T) (D.perfectSequence A horth) :=
  SemiorthogonalSequence.inverseImage_compatible _ _

/-- Triangulated source components give triangulated perfect base-change
components on the compact-object carrier. -/
theorem perfectCategorySequence_hasTriangulatedComponents
    (hA : A.HasTriangulatedComponents)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.perfectCategorySequence A horth).HasTriangulatedComponents := by
  intro i
  letI : (A.component i).IsTriangulated := hA i
  change ((D.perfectEnvelope (A.component i)).inverseImage
    (targetPerfectToDqc X T)).IsTriangulated
  infer_instance

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

/-- Triangulated source components give triangulated quasicoherent
base-change components. -/
theorem quasicoherentSequence_hasTriangulatedComponents
    (hA : A.HasTriangulatedComponents)
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) :
    (D.quasicoherentSequence A hcompact horth).HasTriangulatedComponents := by
  intro i
  letI : (A.component i).IsTriangulated := hA i
  change (D.quasicoherentComponent (A.component i)).IsTriangulated
  infer_instance

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

/-- If bounded coherent cohomology is triangulated on the fibre product,
then triangulated source components give triangulated bounded base-change
components. -/
theorem boundedSequence_hasTriangulatedComponents
    (hA : A.HasTriangulatedComponents)
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A)
    [(Dqc.schemeBoundedCoherentCohomology
      (X ⨯ T).left).IsTriangulated] :
    (D.boundedSequence A hcompact horth).HasTriangulatedComponents := by
  intro i
  letI : (A.component i).IsTriangulated := hA i
  letI : (D.quasicoherentComponent
      (A.component i)).IsTriangulated := inferInstance
  letI : (D.quasicoherentComponent
      (A.component i)).IsClosedUnderIsomorphisms := inferInstance
  letI : (boundedCoherentFiberToDqc X T).CommShift ℤ := inferInstance
  letI : (boundedCoherentFiberToDqc X T).IsTriangulated := inferInstance
  change ((D.quasicoherentComponent (A.component i)).inverseImage
    (boundedCoherentFiberToDqc X T)).IsTriangulated
  infer_instance

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
