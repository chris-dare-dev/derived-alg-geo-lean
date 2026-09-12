/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Stable

/-!
# Mass--Hom bounds on bounded coherent derived categories

This file only identifies the geometric test class.  It does not manufacture
Hom-finiteness: a consumer must supply the appropriate geometric finiteness
input before forming a mass--Hom bound.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe w u u'

/-- Perfect objects viewed inside `Dᵇ(Coh X)`.  The property is the inverse
image of `schemePerfect X` along the fully faithful bounded inclusion. -/
def boundedSchemePerfect (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ObjectProperty (SchemeBoundedCoherentDerivedCategory X) :=
  (schemePerfect X).inverseImage DerivedCategory.Bounded.ι

@[simp]
theorem boundedSchemePerfect_iff (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : SchemeBoundedCoherentDerivedCategory X) :
    boundedSchemePerfect X E ↔
      schemePerfect X (DerivedCategory.Bounded.ι.obj E) :=
  Iff.rfl

/-- The mass--Hom predicate specialized to perfect test objects in
`Dᵇ(Coh X)`. Hom-finiteness and `k`-linearity stay explicit inputs. -/
abbrev HasPerfectMassHomBound {k : Type w} [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [Linear k (SchemeBoundedCoherentDerivedCategory X)]
    [CategoryTheory.SerreFunctor.HomFinite k
      (SchemeBoundedCoherentDerivedCategory X)]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ (SchemeBoundedCoherentDerivedCategory X) →+ Λ}
    (σ : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X) v) : Prop :=
  σ.HasMassHomBound (k := k) (boundedSchemePerfect X)

/-- Remark 7.2: stable-target bounds on a classically generating collection
give the perfect mass--Hom bound.  Classical generation is kept as the
explicit equality `G.triangEnvelope = boundedSchemePerfect X`; this abstract
adapter does not manufacture a geometric generating theorem. -/
theorem hasPerfectMassHomBound_of_stable_generators
    {k : Type w} [Field k]
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [Linear k (SchemeBoundedCoherentDerivedCategory X)]
    [∀ n : ℤ,
      (shiftFunctor (SchemeBoundedCoherentDerivedCategory X) n).Linear k]
    [CategoryTheory.SerreFunctor.HomFinite k
      (SchemeBoundedCoherentDerivedCategory X)]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ (SchemeBoundedCoherentDerivedCategory X) →+ Λ}
    (σ : StabilityCondition.WithClassMap
      (SchemeBoundedCoherentDerivedCategory X) v)
    (G : ObjectProperty (SchemeBoundedCoherentDerivedCategory X))
    (hG : G.triangEnvelope = boundedSchemePerfect X)
    (hJH : σ.slicing.HasJordanHolderFiltrations)
    (hstable : σ.HasStableMassHomBound (k := k) G) :
    HasPerfectMassHomBound (k := k) X σ := by
  change σ.HasMassHomBound (k := k) (boundedSchemePerfect X)
  rw [← hG]
  exact hstable.triangEnvelope hJH

end


end AlgebraicGeometry.DerivedCategory
