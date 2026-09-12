/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentPullback
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Stable
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Transfer

/-!
# Mass--Hom bounds on bounded coherent derived categories

This file only identifies the geometric test class.  It does not manufacture
Hom-finiteness: a consumer must supply the appropriate geometric finiteness
input before forming a mass--Hom bound.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory

open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
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

/-! ## Finite pullback transfer -/

/-- **The finite-morphism pullback half of Lemma 7.4, with its two unfinished
geometric inputs explicit.**

For a finite morphism, `boundedCoherentDerivedPushforward f` is the actual
exact direct image used to construct `f^♯σ`.  Any linear left adjoint `pull`
transfers the mass--Hom bound provided its perfect images classically generate
the source perfect test class.

The repository does not yet construct the required bounded coherent derived
pullback for an arbitrary finite morphism: `perfectDerivedPullback` is defined
only under the exact coherent-pullback contract and has domain `Perf`, whereas
the adjunction here is against all of `Dᵇ(Coh)`.  Accordingly `pull`, `adj`, and
the generation containment are parameters rather than manufactured instances.
The future geometric discharges are tracked by #1033 and #723. -/
theorem hasPerfectMassHomBound_finitePullback
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsFinite f.left]
    {k : Type w} [Field k]
    [Linear k T.BoundedCoherentDerivedFiber]
    [Linear k U.BoundedCoherentDerivedFiber]
    [∀ n : ℤ, (shiftFunctor T.BoundedCoherentDerivedFiber n).Linear k]
    [CategoryTheory.SerreFunctor.HomFinite k T.BoundedCoherentDerivedFiber]
    [CategoryTheory.SerreFunctor.HomFinite k U.BoundedCoherentDerivedFiber]
    {Λ : Type u'} [AddCommGroup Λ]
    {v : K₀ U.BoundedCoherentDerivedFiber →+ Λ}
    (σ : StabilityCondition.WithClassMap U.BoundedCoherentDerivedFiber v)
    (hσ : HasPerfectMassHomBound (k := k) U.left σ)
    (hpre : BoundedCoherentPushforwardPreimageData f σ.slicing)
    (pull : U.BoundedCoherentDerivedFiber ⥤ T.BoundedCoherentDerivedFiber)
    [pull.Additive] [pull.Linear k]
    (adj : pull ⊣ boundedCoherentDerivedPushforward f)
    (hgen : boundedSchemePerfect T.left ≤
      ((boundedSchemePerfect U.left).map pull).triangEnvelope) :
    HasPerfectMassHomBound (k := k) T.left
      (σ.boundedCoherentPullback f hpre) := by
  change (σ.preimage (boundedCoherentDerivedPushforward f)
    hpre.preimageData).HasMassHomBound (k := k) (boundedSchemePerfect T.left)
  exact hσ.preimage adj hpre.preimageData hgen

end


end AlgebraicGeometry.DerivedCategory
