/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.Semistable
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.PreStability

/-!
# The support property under transfer

Remarks 3.2 and 3.7 of arXiv:2607.28411v1 observe that once the preimage
collection is a slicing, the transported condition `f^♯σ` or `f_♯σ` satisfies
the support property with respect to the *same* quadratic form as `σ`, on the
class map `v ∘ K₀(F)`.  The last paragraph of the proof of Proposition 3.4 of
arXiv:2601.22994 makes the same observation for the norm-bound formulation.

## Main results

* `PreStabilityCondition.WithClassMap.preimage_semistableClasses_subset`: the
  semistable classes of the transported condition are semistable classes of
  the original one.  This is the whole content: every nonzero semistable
  object of the transported condition maps to a nonzero semistable object of
  the same phase, and its transported class is the class of that image.
* `PreStabilityCondition.WithClassMap.HasSupportProperty.preimage`: the
  norm-bound support property transfers with the same real-linear charge and
  the same constant.
* `PreStabilityCondition.WithClassMap.QuadraticSupportData.preimage`: genuine
  quadratic support transfers with the same quadratic form, which is the form
  in which the paper states the support property (Definition 2.2).

## Implementation notes

Both transfer theorems are monotonicity of the underlying numerical
predicates in the selected locus, applied to the inclusion of semistable
classes.  Nothing about the functor beyond the lifting witness enters; in
particular the negative-definiteness of the quadratic form on the kernel of
the charge is a statement about `Λ_ℝ` and `Z` alone and is untouched.

## References

* arXiv:2607.28411v1, Remarks 3.2 and 3.7.
* arXiv:2601.22994, Proposition 3.4.
-/

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

noncomputable section

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {v : K₀ D →+ V}
variable (σ : WithClassMap D v) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : σ.slicing.PreimageData F)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Every semistable class of the transported condition is a semistable class
of the original condition: a nonzero object semistable of phase `φ` for the
preimage slicing has a nonzero image semistable of phase `φ`, and the class
map `v ∘ K₀(F)` evaluates to the class of that image. -/
theorem preimage_semistableClasses_subset :
    (σ.preimage F h).semistableClasses ⊆ σ.semistableClasses := by
  rintro x ⟨φ, E, hP, hE, rfl⟩
  refine ⟨φ, F.obj E, hP, h.not_isZero_obj hE, ?_⟩
  change v (K₀.map F (K₀.of C E)) = v (K₀.of D (F.obj E))
  rw [K₀.map_of]

omit [FiniteDimensional ℝ V] in
/-- The norm-bound support property transfers along a phase-detecting
functor, with the same real-linear charge and the same constant, since the
transported semistable locus is contained in the original one. -/
theorem HasSupportProperty.preimage {Zlin : V →ₗ[ℝ] ℂ}
    (hσ : σ.HasSupportProperty Zlin) : (σ.preimage F h).HasSupportProperty Zlin :=
  WeakStabilityCondition.Support.HasSupportProperty.mono hσ
    (σ.preimage_semistableClasses_subset F h)

omit [FiniteDimensional ℝ V] in
/-- Genuine quadratic support transfers along a phase-detecting functor with
the same quadratic form and the same charge: `HasQuadraticSupportProperty.mono`
keeps the witness `Q` verbatim, since the transported semistable locus is a
subset.  This is the support half of Remarks 3.2 and 3.7 of
arXiv:2607.28411v1; the local-finiteness half is
`Slicing.PreimageData.isLocallyFinite`, and only the two together give a
stability condition for `(V, v ∘ K₀(F))`. -/
theorem QuadraticSupportData.preimage {Zlin : V →ₗ[ℝ] ℂ}
    (hσ : σ.QuadraticSupportData Zlin) :
    (σ.preimage F h).QuadraticSupportData Zlin :=
  ⟨hσ.charge_compatible, hσ.quadratic.mono (σ.preimage_semistableClasses_subset F h)⟩

end

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
