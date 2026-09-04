/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic

/-!
# The projections off a dg cone

`IsConeOf` states its universal property for maps *into* the cone: `Hom(W, Z)`
splits as a product of `Hom(W, X)` in degree `+1` and `Hom(W, Y)`. The maps *out* of the cone that a
triangle needs are not part of the data, and this file extracts them.

The extraction is the standard one and needs no new hypothesis: apply the
splitting to `dgId Z` itself. That gives `fst : (dgHom Z X).X 1` and
`snd : (dgHom Z Y).X 0` with `fst ≫ inl + snd ≫ inr = dgId Z`.

## The projection is closed, and that is where the work is

`fst` is not closed by construction — it is one half of a splitting of an
identity, and nothing in `IsConeOf` mentions its differential. What forces it is
*uniqueness* of the splitting: differentiate the splitting of `dgId Z`, use
`δ (dgId Z) = 0` and `δ inl = f ≫ inr`, and the result is a second splitting of
`0`. Injectivity then reads off both `δ fst = 0` and `δ snd = -(fst ≫ f)`.

So the connecting map of the triangle is closed for a reason, rather than by
assumption, and the cone's `snd` fails to be closed by exactly the term that
makes the triangle rotate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace IsConeOf

variable {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z)

/-- The splitting of `dgId Z` along the cone's two inclusions. -/
noncomputable def splitId : (dgHom Z X).X 1 × (dgHom Z Y).X 0 :=
  ((hc.bijective Z 0 1 (by omega)).surjective (dgId Z)).choose

/-- The degree-`1` projection of the cone onto the source. -/
noncomputable def fst : (dgHom Z X).X 1 := hc.splitId.1

/-- The degree-`0` projection of the cone onto the target. -/
noncomputable def snd : (dgHom Z Y).X 0 := hc.splitId.2

/-- The two projections split the identity. -/
lemma fst_inl_add_snd_inr :
    dgComp 1 (-1) 0 (by omega) hc.fst hc.inl +
      dgComp 0 0 0 (by omega) hc.snd hc.inr = dgId Z :=
  ((hc.bijective Z 0 1 (by omega)).surjective (dgId Z)).choose_spec

/-- **The splitting of the identity is unique.** `fst` and `snd` are
`Classical.choice` on a surjectivity, so the only handle on them is the equation
they satisfy; the cone's injectivity clause turns that equation into a
characterisation. Every identification of `fst` or `snd` with a concretely given
element goes through here. -/
lemma splitId_unique {a : (dgHom Z X).X 1} {b : (dgHom Z Y).X 0}
    (h : dgComp 1 (-1) 0 (by omega) a hc.inl + dgComp 0 0 0 (by omega) b hc.inr = dgId Z) :
    a = hc.fst ∧ b = hc.snd := by
  have hpair := (hc.bijective Z 0 1 (by omega)).injective
    (a₁ := (a, b)) (a₂ := (hc.fst, hc.snd)) ?_
  · exact ⟨congrArg (fun ab => ab.1) hpair, congrArg (fun ab => ab.2) hpair⟩
  · show dgComp 1 (-1) 0 (by omega) a hc.inl + dgComp 0 0 0 (by omega) b hc.inr =
      dgComp 1 (-1) 0 (by omega) hc.fst hc.inl + dgComp 0 0 0 (by omega) hc.snd hc.inr
    rw [h, hc.fst_inl_add_snd_inr]

/-- Differentiating the splitting of the identity: the projection's differential
composed into the cone equals the two `inr`-terms it has to cancel against.

Everything below is read off this one equation, which is why it is stated in the
raw form the Leibniz rule produces rather than in a tidied one. -/
lemma delta_splitId_key :
    dgComp 2 (-1) 1 (by omega) (((dgHom Z X).d 1 2).hom hc.fst) hc.inl =
      dgComp 1 0 1 (by omega) (dgComp 1 0 1 (by omega) hc.fst f) hc.inr +
        dgComp 1 0 1 (by omega) (((dgHom Z Y).d 0 1).hom hc.snd) hc.inr := by
  have h := congrArg ((dgHom Z Z).d 0 1).hom hc.fst_inl_add_snd_inr
  rw [map_add, dgId_cocycle,
    dgComp_leibniz 1 (-1) 0 1 (by omega) (by omega),
    dgComp_leibniz 0 0 0 1 (by omega) (by omega)] at h
  -- The Leibniz rule produces its degrees as `-1 + 1`, `0 + 1` and `1 + 1`, while
  -- `δ_inl` and `inr_closed` are stated at `0` and `1`. The numerals are
  -- definitionally equal, so the restatement is `h` itself -- but `rw` cannot
  -- cross the gap, because the indices sit inside `HomologicalComplex.d`.
  have h' : dgComp 1 0 1 (by omega) hc.fst (((dgHom X Z).d (-1) 0).hom hc.inl) +
        (-1 : ℤ).negOnePow •
          dgComp 2 (-1) 1 (by omega) (((dgHom Z X).d 1 2).hom hc.fst) hc.inl +
      (dgComp 0 1 1 (by omega) hc.snd (((dgHom Y Z).d 0 1).hom hc.inr) +
        (0 : ℤ).negOnePow •
          dgComp 1 0 1 (by omega) (((dgHom Z Y).d 0 1).hom hc.snd) hc.inr) = 0 := h
  rw [hc.δ_inl, hc.inr_closed,
    ← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)] at h'
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  rw [hneg, Int.negOnePow_zero] at h'
  simp only [map_zero, Units.neg_smul, one_smul] at h'
  -- `h'` is `B - A + C = 0` with `A` the goal's left side; `abel` supplies the
  -- rearrangement and `h'` supplies the zero.
  have hrw : dgComp 2 (-1) 1 (by omega) (((dgHom Z X).d 1 2).hom hc.fst) hc.inl -
      (dgComp 1 0 1 (by omega) (dgComp 1 0 1 (by omega) hc.fst f) hc.inr +
        dgComp 1 0 1 (by omega) (((dgHom Z Y).d 0 1).hom hc.snd) hc.inr) =
      -(dgComp 1 0 1 (by omega) (dgComp 1 0 1 (by omega) hc.fst f) hc.inr -
          dgComp 2 (-1) 1 (by omega) (((dgHom Z X).d 1 2).hom hc.fst) hc.inl +
        dgComp 1 0 1 (by omega) (((dgHom Z Y).d 0 1).hom hc.snd) hc.inr) := by
    abel
  refine sub_eq_zero.mp ?_
  rw [hrw, neg_eq_zero]
  abel_nf
  abel_nf at h'
  exact h'

/-- **The projection onto the source is closed.** Nothing in `IsConeOf` says so;
what forces it is uniqueness of the splitting, applied to the differentiated
identity. `fst` and the correction term are the unique pair splitting `0`, and
the pair of zeros splits it too. -/
lemma delta_fst_and_snd : ((dgHom Z X).d 1 2).hom hc.fst = 0 ∧
    ((dgHom Z Y).d 0 1).hom hc.snd = -dgComp 1 0 1 (by omega) hc.fst f := by
  have hpair := (hc.bijective Z 1 2 (by omega)).injective
    (a₁ := (((dgHom Z X).d 1 2).hom hc.fst,
      -(dgComp 1 0 1 (by omega) hc.fst f + ((dgHom Z Y).d 0 1).hom hc.snd)))
    (a₂ := (0, 0)) ?_
  · refine ⟨congrArg (fun ab => ab.1) hpair, ?_⟩
    have h2 := congrArg (fun ab => ab.2) hpair
    simp only [neg_eq_zero] at h2
    exact eq_neg_of_add_eq_zero_right h2
  · show dgComp 2 (-1) 1 (by omega) _ hc.inl + dgComp 1 0 1 (by omega) _ hc.inr =
      dgComp 2 (-1) 1 (by omega) 0 hc.inl + dgComp 1 0 1 (by omega) 0 hc.inr
    rw [hc.delta_splitId_key]
    simp [map_neg, map_add]

/-- The projection onto the source is closed. -/
lemma delta_fst : ((dgHom Z X).d 1 2).hom hc.fst = 0 := hc.delta_fst_and_snd.1

/-- The projection onto the target is *not* closed, and this is by how much. The
term is what makes the triangle rotate. -/
lemma delta_snd :
    ((dgHom Z Y).d 0 1).hom hc.snd = -dgComp 1 0 1 (by omega) hc.fst f :=
  hc.delta_fst_and_snd.2

/-- `inr` followed by the two projections: the splitting of `inr` itself. Both
halves come from one application of uniqueness, so they are proved together. -/
lemma inr_comp_fst_and_snd :
    dgComp 0 1 1 (by omega) hc.inr hc.fst = 0 ∧
      dgComp 0 0 0 (by omega) hc.inr hc.snd = dgId Y := by
  have hpair := (hc.bijective Y 0 1 (by omega)).injective
    (a₁ := (dgComp 0 1 1 (by omega) hc.inr hc.fst, dgComp 0 0 0 (by omega) hc.inr hc.snd))
    (a₂ := (0, dgId Y)) ?_
  · exact ⟨congrArg (fun ab => ab.1) hpair, congrArg (fun ab => ab.2) hpair⟩
  · show dgComp 1 (-1) 0 (by omega) _ hc.inl + dgComp 0 0 0 (by omega) _ hc.inr =
      dgComp 1 (-1) 0 (by omega) 0 hc.inl + dgComp 0 0 0 (by omega) (dgId Y) hc.inr
    rw [dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega),
      dgComp_assoc 0 0 0 0 0 0 (by omega) (by omega) (by omega),
      ← map_add, hc.fst_inl_add_snd_inr, dgComp_id]
    simp [dgId_comp]

/-- `inl` followed by the two projections: the splitting of `inl` itself, and the
other half of the biproduct-like orthogonality. -/
lemma inl_comp_fst_and_snd :
    dgComp (-1) 1 0 (by omega) hc.inl hc.fst = dgId X ∧
      dgComp (-1) 0 (-1) (by omega) hc.inl hc.snd = 0 := by
  have hpair := (hc.bijective X (-1) 0 (by omega)).injective
    (a₁ := (dgComp (-1) 1 0 (by omega) hc.inl hc.fst,
      dgComp (-1) 0 (-1) (by omega) hc.inl hc.snd))
    (a₂ := (dgId X, 0)) ?_
  · exact ⟨congrArg (fun ab => ab.1) hpair, congrArg (fun ab => ab.2) hpair⟩
  · show dgComp 0 (-1) (-1) (by omega) _ hc.inl + dgComp (-1) 0 (-1) (by omega) _ hc.inr =
      dgComp 0 (-1) (-1) (by omega) (dgId X) hc.inl +
        dgComp (-1) 0 (-1) (by omega) 0 hc.inr
    rw [dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega),
      dgComp_assoc (-1) 0 0 (-1) 0 (-1) (by omega) (by omega) (by omega),
      ← map_add, hc.fst_inl_add_snd_inr, dgComp_id]
    simp [dgId_comp]

/-- The source's inclusion is a section of the cone's projection to it. -/
lemma inl_comp_fst : dgComp (-1) 1 0 (by omega) hc.inl hc.fst = dgId X :=
  hc.inl_comp_fst_and_snd.1

/-- And it is orthogonal to the projection onto the target. -/
lemma inl_comp_snd : dgComp (-1) 0 (-1) (by omega) hc.inl hc.snd = 0 :=
  hc.inl_comp_fst_and_snd.2

/-- The cone's projection to the source is orthogonal to the target's inclusion.
This is the `g ≫ h = 0` of the triangle, before the shift is applied. -/
lemma inr_comp_fst : dgComp 0 1 1 (by omega) hc.inr hc.fst = 0 :=
  hc.inr_comp_fst_and_snd.1

/-- And the target's inclusion is a section of the cone's projection to it. -/
lemma inr_comp_snd : dgComp 0 0 0 (by omega) hc.inr hc.snd = dgId Y :=
  hc.inr_comp_fst_and_snd.2

section ToShift

variable {X' : C} (s : IsShiftBy X 1 X')

/-- The connecting morphism of the triangle: project to the source, then cross
the shift. Degree zero, because `fst` has degree `1` and `s.hom` degree `-1`. -/
noncomputable def toShift : (dgHom Z X').X 0 :=
  dgComp 1 (-1) 0 (by omega) hc.fst s.hom

/-- It is closed, because both factors are — `delta_fst` for the projection, and
`IsShiftBy.hom_closed` for the shift. -/
lemma toShift_closed : ((dgHom Z X').d 0 1).hom (hc.toShift s) = 0 := by
  refine dgComp_closed (p := 1) (q := -1) (r := 0) (r' := 1) (by omega) (by omega)
    hc.delta_fst ?_
  simpa using s.hom_closed

/-- So the connecting morphism is a morphism of `Z⁰`, and hence of `H⁰`. -/
lemma toShift_mem_cocycles : hc.toShift s ∈ cocycles Z X' :=
  hc.toShift_closed s

/-- **Changing the shift changes the connecting morphism by the comparison.**
`toShift` reads its witness only through `hom`, and the comparison of two shifts
cancels the first witness against the second. This is what lets the cone triangle
be stated at the *chosen* shift and still be recognised in a model where a
different shift is the natural one. -/
lemma toShift_comp_compare {X'' : C} (t : IsShiftBy X 1 X'') :
    dgComp 0 0 0 (by omega) (hc.toShift s) (IsShiftBy.compare s t) = hc.toShift t := by
  rw [toShift, toShift, IsShiftBy.compare,
    dgComp_assoc 1 (-1) 0 0 (-1) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc (-1) 1 (-1) 0 0 (-1) (by omega) (by omega) (by omega),
    IsShiftBy.hom_inv, dgId_comp]

/-- The triangle composes to zero at the second vertex: `inr` followed by the
connecting morphism vanishes on the nose, not merely up to homotopy. -/
lemma inr_comp_toShift :
    dgComp 0 0 0 (by omega) hc.inr (hc.toShift s) = 0 := by
  rw [toShift, ← dgComp_assoc 0 1 (-1) 1 0 0 (by omega) (by omega) (by omega),
    hc.inr_comp_fst]
  simp

end ToShift

include hc in
/-- **The morphism a cone is built on is automatically closed.** `IsConeOf` does
not ask for it: what it asks is `δ inl = f ≫ inr`, and applying `δ` twice turns
that into `(δ f) ≫ inr = 0`. Uniqueness of the splitting then reads off `δ f = 0`.

So `exists_cone`'s cocycle hypothesis is needed to *produce* a cone, not to use
one. -/
lemma delta_f : ((dgHom X Y).d 0 1).hom f = 0 := by
  have hd2 : ((dgHom X Z).d 0 1).hom (dgComp 0 0 0 (by omega) f hc.inr) = 0 := by
    rw [← hc.δ_inl, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
    simp
  have hleib : ((dgHom X Z).d 0 1).hom (dgComp 0 0 0 (by omega) f hc.inr) =
      dgComp 0 1 1 (by omega) f (((dgHom Y Z).d 0 1).hom hc.inr) +
        (0 : ℤ).negOnePow •
          dgComp 1 0 1 (by omega) (((dgHom X Y).d 0 1).hom f) hc.inr :=
    dgComp_leibniz (X := X) (Y := Y) (Z := Z) 0 0 0 1 (by omega) (by omega) f hc.inr
  rw [hleib, hc.inr_closed, Int.negOnePow_zero, one_smul] at hd2
  simp only [map_zero, zero_add] at hd2
  have hpair := (hc.bijective X 1 2 (by omega)).injective
    (a₁ := (0, ((dgHom X Y).d 0 1).hom f)) (a₂ := (0, 0)) ?_
  · exact congrArg (fun ab => ab.2) hpair
  · show dgComp 2 (-1) 1 (by omega) 0 hc.inl + dgComp 1 0 1 (by omega) _ hc.inr =
      dgComp 2 (-1) 1 (by omega) 0 hc.inl + dgComp 1 0 1 (by omega) 0 hc.inr
    simpa using hd2

section Contractible

/-- **The cone on an identity is contractible.** `snd ≫ inl` is a primitive for
the cone's identity, so the cone becomes a zero object in `H⁰`.

Both corrections conspire: `δ inl = f ≫ inr` contributes the `snd ≫ inr` half,
and `δ snd = -(fst ≫ f)` — the failure of `snd` to be closed — contributes the
`fst ≫ inl` half with the sign the Leibniz rule supplies. At `f = dgId` the two
halves are exactly the splitting of `dgId Z`. -/
lemma dgId_mem_coboundaries_of_dgId {X Z : C} (hc : IsConeOf (dgId X) Z) :
    dgId Z ∈ coboundaries Z Z := by
  refine ⟨dgComp 0 (-1) (-1) (by omega) hc.snd hc.inl, ?_⟩
  -- The Leibniz rule, restated at normalized degrees: it produces `-1 + 1` and
  -- `0 + 1` where `δ_inl` and `delta_snd` are stated at `0` and `1`.
  have hleib : ((dgHom Z Z).d (-1) 0).hom
        (dgComp 0 (-1) (-1) (by omega) hc.snd hc.inl) =
      dgComp 0 0 0 (by omega) hc.snd (((dgHom X Z).d (-1) 0).hom hc.inl) +
        (-1 : ℤ).negOnePow •
          dgComp 1 (-1) 0 (by omega) (((dgHom Z X).d 0 1).hom hc.snd) hc.inl :=
    dgComp_leibniz (X := Z) (Y := X) (Z := Z) 0 (-1) (-1) 0 (by omega) (by omega)
      hc.snd hc.inl
  have hneg : (-1 : ℤ).negOnePow = -1 := by decide
  rw [hleib, hc.δ_inl, hc.delta_snd, dgComp_id, dgId_comp, hneg]
  simp only [Units.neg_smul, one_smul, map_neg, AddMonoidHom.neg_apply, neg_neg]
  rw [← hc.fst_inl_add_snd_inr]
  abel

end Contractible

end IsConeOf

end CategoryTheory
