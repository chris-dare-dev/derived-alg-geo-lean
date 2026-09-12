/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Basic

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

end


end AlgebraicGeometry.DerivedCategory
