/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Support
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealFormSignature
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallFiniteness

/-!
# The Hodge certificate is the signature hypothesis

`PeriodDomain.HasSignatureTwo` is carried as an assumption by every result in
the period-domain layer: the negative definiteness on `Wᗮ` that bounds spherical
classes, the wall-finiteness theorems, the orientation cocycle.
`Mukai/RealFormSignature.lean` reduces it, for a Mukai extension, to the
signature of the middle summand:

```text
sigPos b = 1  and  sigNeg b + 1 = dim V   ⟹   HasSignatureTwo (realForm b).
```

What was missing was the left-hand side.  This file supplies it from
`DivisorSpace.HodgeDefinite`, the certificate `Divisorial/Discriminant.lean`
already uses for the support property, so one hypothesis now serves both.

## The decomposition

`HodgeDefinite S H` says `H² > 0` and that the form is negative definite on
`H^⊥`.  That is exactly an orthogonal splitting

```text
D = ℝH ⊕ H^⊥,
```

positive definite on a line and negative definite on the complement, so
`sigPos = 1` and `sigNeg = dim D - 1` by `QuadraticMap.sigPos_eq_add`.  Nothing
deeper happens; the content is that `HodgeDefinite` was already the right
certificate, and the inequality certificate `HodgeIndex` is *not* — it permits
an isotropic class in `H^⊥`, which would put a radical in the form and break the
count.

## What this unlocks

`hasSignatureTwo_of_hodgeDefinite` turns every period-domain result into a
statement about a divisor space.  The one taken here is Bridgeland's local
finiteness in the pointwise form:

* `finite_walls_through_expPlane` — for a lattice in the real Mukai extension,
  only finitely many spherical classes have a wall through the plane spanned by
  `Re exp(B + iω)` and `Im exp(B + iω)`.

The plane is positive by `Mukai.isPositivePair_exp`, which needs only
`ω² > 0`; the signature comes from the Hodge certificate.  So the hypotheses of
the finiteness statement are exactly "the divisor space is Hodge" and "`ω` is in
the positive cone", which is what one wants.

The *region-wise* statement — finitely many walls meeting a family of planes —
is not proved here, because it needs a uniform coercivity constant and
`QuadraticForm/WallFiniteness.lean` records why one plane does not supply it.
It is proved in `Divisorial/Region.lean` for a **compact** family, using the
`PlaneRegion` of `QuadraticForm/WallRegion.lean`, whose only missing input was
the signature this file supplies.

No geometry is asserted: `D` is an arbitrary finite-dimensional real divisor
space and the lattice is the `ℤ`-span of an `ℝ`-basis.
-/

open QuadraticMap Mukai

universe v w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

namespace DivisorSpace

/-! ### The signature of a Hodge divisor space -/

section Signature

variable {D : Type w} [AddCommGroup D] [Module ℝ D]
variable (S : DivisorSpace D)

/-- The intersection form of a divisor space, bundled as a quadratic form.  This
is the *unhalved* self-pairing, which is the normalisation
`hasSignatureTwo_realForm` consumes. -/
abbrev intersectionQuadratic : QuadraticForm ℝ D :=
  LinearMap.BilinMap.toQuadraticMap S.intersection

/-- Not a `simp` lemma: `intersectionQuadratic` is an `abbrev`, so
`LinearMap.BilinMap.toQuadraticMap_apply` already rewrites the left-hand side by
`dsimp` and the normal-form linter rejects the attribute. -/
theorem intersectionQuadratic_apply (x : D) : S.intersectionQuadratic x = S.pair x x := rfl

theorem polar_intersectionQuadratic (x y : D) :
    polar (⇑S.intersectionQuadratic) x y = 2 * S.pair x y := by
  rw [intersectionQuadratic, LinearMap.BilinMap.polar_toQuadraticMap]
  have h : S.intersection y x = S.intersection x y := S.pair_comm y x
  simp only [DivisorSpace.pair] at h ⊢
  linarith

variable {S} {H : D}

/-- The `H`-line, the positive summand. -/
private def hLine (H : D) : Submodule ℝ D := Submodule.span ℝ ({H} : Set D)

/-- The orthogonal complement of `H`, the negative summand. -/
private def hPerp (S : DivisorSpace D) (H : D) : Submodule ℝ D :=
  LinearMap.ker (S.intersection H)

private theorem mem_hPerp_iff {x : D} : x ∈ hPerp S H ↔ S.pair H x = 0 := Iff.rfl

private theorem isCompl_hLine_hPerp (h : S.HodgeDefinite H) :
    IsCompl (hLine H) (hPerp S H) := by
  have hH : S.intersection H H ≠ 0 := ne_of_gt h.H_square_pos
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    have hzero : a * S.intersection H H = 0 := by
      have hker := mem_hPerp_iff.mp hx'
      rw [← ha] at hker
      simpa [DivisorSpace.pair, smul_eq_mul] using hker
    have hazero : a = 0 := (mul_eq_zero.mp hzero).resolve_right hH
    rw [← ha, hazero, zero_smul]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    refine Submodule.mem_sup.mpr ⟨(S.pair H x / S.pair H H) • H,
      Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
      x - (S.pair H x / S.pair H H) • H, ?_, by abel⟩
    show S.pair H (x - (S.pair H x / S.pair H H) • H) = 0
    simp only [DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring

private theorem orth_hLine_hPerp (S : DivisorSpace D) (H : D) :
    ∀ w ∈ hLine H, ∀ w' ∈ hPerp S H, polar (⇑S.intersectionQuadratic) w w' = 0 := by
  intro w hw w' hw'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [polar_intersectionQuadratic]
  have hsmul : S.pair (a • H) w' = a * S.pair H w' := by
    simp [DivisorSpace.pair]
  rw [hsmul, mem_hPerp_iff.mp hw']
  ring

private theorem posDef_restrict_hLine (h : S.HodgeDefinite H) :
    (S.intersectionQuadratic.restrict (hLine H)).PosDef := by
  intro x hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  have hane : a ≠ 0 := by
    intro hc
    apply hx
    apply Subtype.ext
    simp [← ha, hc]
  have hval : S.intersectionQuadratic (x : D) = a ^ 2 * S.pair H H := by
    rw [← ha]
    simp only [intersectionQuadratic_apply, DivisorSpace.pair, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [restrict_apply, hval]
  have hsq : 0 < a ^ 2 := by positivity
  exact mul_pos hsq h.H_square_pos

private theorem negDef_restrict_hPerp (h : S.HodgeDefinite H) :
    (-(S.intersectionQuadratic.restrict (hPerp S H))).PosDef := by
  intro x hx
  have hxne : (x : D) ≠ 0 := fun hc => hx (Subtype.ext hc)
  have hneg : S.pair (x : D) (x : D) < 0 := h.neg_definite _ (mem_hPerp_iff.mp x.2) hxne
  have hval : (-(S.intersectionQuadratic.restrict (hPerp S H))) x
      = -(S.pair (x : D) (x : D)) := rfl
  rw [hval]
  linarith

private theorem finrank_hLine (h : S.HodgeDefinite H) :
    Module.finrank ℝ (hLine H) = 1 := by
  have hHne : H ≠ 0 := by
    intro hc
    have hsq := h.H_square_pos
    rw [hc] at hsq
    simp [DivisorSpace.pair] at hsq
  rw [hLine, finrank_span_singleton hHne]

variable [FiniteDimensional ℝ D]

/-- **The indices of inertia of a Hodge divisor space.**

`HodgeDefinite` is precisely the statement that the intersection form has
signature `(1, dim D - 1)`, and this is the translation. -/
theorem sigPos_sigNeg_of_hodgeDefinite (h : S.HodgeDefinite H) :
    sigPos S.intersectionQuadratic = 1 ∧
      sigNeg S.intersectionQuadratic + 1 = Module.finrank ℝ D := by
  obtain ⟨hP₁, hN₁, hnd₁⟩ := sigPos_eq_finrank_of_posDef (posDef_restrict_hLine h)
  obtain ⟨hN₂, hP₂, hnd₂⟩ := sigNeg_eq_finrank_of_negDef (negDef_restrict_hPerp h)
  obtain ⟨hsplitP, hsplitN⟩ :=
    QuadraticMap.sigPos_eq_add (Q := S.intersectionQuadratic)
      (isCompl_hLine_hPerp h) (orth_hLine_hPerp S H) hnd₁ hnd₂
  have hdim := Submodule.finrank_add_eq_of_isCompl (isCompl_hLine_hPerp h)
  rw [finrank_hLine h] at hP₁ hdim
  refine ⟨by rw [hsplitP, hP₁, hP₂], ?_⟩
  rw [hsplitN, hN₁, hN₂]
  omega

/-- **The Hodge certificate is the signature hypothesis.**

Every period-domain theorem carrying `HasSignatureTwo` is therefore available
for the real Mukai extension of a Hodge divisor space, with no further
assumption. -/
theorem hasSignatureTwo_of_hodgeDefinite (h : S.HodgeDefinite H) :
    PeriodDomain.HasSignatureTwo (Mukai.realForm S.intersection) := by
  obtain ⟨hP, hN⟩ := sigPos_sigNeg_of_hodgeDefinite h
  exact Mukai.hasSignatureTwo_realForm S.intersection
    (fun x y => S.pair_comm x y) hP hN

end Signature

/-! ### Finitely many spherical walls through an exponential plane -/

section Finiteness

variable {D : Type w} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {S : DivisorSpace D} {H : D}

/-- The positive plane of `exp(B + iω)`, spanned by its real and imaginary
parts. -/
def expPlane (S : DivisorSpace D) (B omega : D) : Submodule ℝ (Mukai.RealExtension D) :=
  PeriodDomain.pairSpan (Mukai.expRe S.intersection B omega)
    (Mukai.expIm S.intersection B omega)

/-- The exponential plane is a positive plane as soon as `ω² > 0`; the `B`-field
is unconstrained. -/
theorem isPositivePlane_expPlane (S : DivisorSpace D) (B omega : D)
    (homega : 0 < S.pair omega omega) :
    PeriodDomain.IsPositivePlane (Mukai.realForm S.intersection) (expPlane S B omega) :=
  Mukai.isPositivePair_exp S.intersection B omega (fun x y => S.pair_comm x y) homega

variable [FiniteDimensional ℝ D]

/-- **Bridgeland's local finiteness, on a divisor space.**

For a lattice in the real Mukai extension, only finitely many spherical classes
have a wall through the plane of `exp(B + iω)`.  The two hypotheses are the
Hodge certificate for the divisor space and positivity of `ω²`; nothing else
enters.

This is the pointwise statement.  The region-wise one needs a `PlaneRegion`
carrying its own coercivity constant, for the reason
`QuadraticForm/WallFiniteness.lean` records. -/
theorem finite_walls_through_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    {δ : Mukai.RealExtension D |
        PeriodDomain.IsSphericalClass (Mukai.realForm S.intersection) δ ∧
        expPlane S B omega ∈ PeriodDomain.wall (Mukai.realForm S.intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))}.Finite :=
  PeriodDomain.finite_walls_through (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

/-- The same finiteness, said as a bounded set of spherical classes orthogonal
to the plane. -/
theorem finite_sphericalOrthogonal_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    (PeriodDomain.sphericalOrthogonal (Mukai.realForm S.intersection) (expPlane S B omega)
      ∩ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))).Finite :=
  PeriodDomain.finite_sphericalOrthogonal_inter (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

end Finiteness

end DivisorSpace

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
