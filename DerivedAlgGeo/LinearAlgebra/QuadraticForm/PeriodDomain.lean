/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Real

/-!
# The period domain of a real quadratic space of signature `(2, n - 2)`

A quadratic space `(M, Q)` over `ℝ` whose signature is `(2, n - 2)` carries a
distinguished family of two-dimensional subspaces: the **positive planes**, the
planes on which `Q` is positive definite. The set of them is the **period
domain**, and deleting from it the planes orthogonal to a class of square `-2`
leaves the **cut period domain**.

The names come from the K3 case, where `M = N(X) ⊗ ℝ` for the numerical
Grothendieck group of a K3 surface with its Mukai pairing, the signature is
`(2, ρ(X))`, and the cut domain is Bridgeland's `P₀⁺(X)` — the target of the
covering map of *Stability conditions on K3 surfaces*, Theorem 1.1.

**No geometry is asserted here.** Every statement below is a statement about an
arbitrary real quadratic space of signature `(2, n - 2)` and is true whether or
not any K3 surface exists; the identification of such a space with `N(X) ⊗ ℝ`
needs `Dᵇ(Coh X)`, Chern characters and Hirzebruch–Riemann–Roch, none of which
appear here. This is the discipline `LinearAlgebra/Lattice/Mukai/Basic.lean`
states for the integral lattice, applied to its real span.

## The two conventions, and which one is used

Bridgeland writes the pairing bilinearly: a spherical class has `(δ, δ) = -2`.
Mathlib's signature API is quadratic-form-native (`sigPos`, `sigNeg`), and the
bilinear form belonging to a `QuadraticForm` is its polar form, which satisfies
`polar Q δ δ = 2 * Q δ`. Both readings are kept: `Q` carries the Sylvester
theory, `Q.polarBilin` **is** the pairing, `IsSphericalClass` is stated as
`polar Q δ δ = -2` so it can be compared with the paper unchanged, and
`isSphericalClass_iff_apply` records that this is `Q δ = -1`.

## Main results

* `Nondegenerate` of the form, from the signature hypothesis alone.
* `isCompl_orthogonal` — `M = W ⊕ Wᗮ` for a positive plane `W`.
* `neg_of_mem_orthogonal` and `negDef_orthogonal` — **the engine**: `Q` is
  negative definite on `Wᗮ`. Every finiteness statement about the walls
  eventually rests on this, since it is what makes the pairing definite on the
  space where the wall classes live.
* `notMem_of_isSphericalClass` — a spherical class lies in no positive plane.
* `mem_orthogonal_span_pair_iff` — orthogonality to a plane spanned by two
  vectors is orthogonality to both, which is what makes it a closed condition
  downstream.
* `mem_wall_iff_mem_orthogonal` — a positive plane lies on the wall of `δ`
  exactly when `δ` is orthogonal to it, which is how the previous item is used.
  A wall does **not** meet its plane in a proper subspace: `W ⊆ δ^⊥` is exactly
  the wall condition, and it is compatible with `δ ∉ W` because `δ` lies in
  `Wᗮ`.
* `periodDomain₀_sphericalClasses_univ_eq_empty` — the cut must be taken by a
  *set* of classes: cutting by every real class of square `-2` empties the
  domain. Bridgeland cuts by the lattice `Δ(X)`, which is discrete.
* `exists_isPositivePlane` and `stdForm_hasSignatureTwo` — the hypothesis is
  inhabited and its period domain is nonempty, so nothing above is vacuous.
  `sigPos Q = 2` carries its own positive plane; `stdForm` is `x₀² + x₁² - x₂²`
  on `ℝ³`, the smallest space the hypothesis holds for.

## What is deliberately absent

* **Finiteness of the wall family.** That needs a lattice inside `M` and its
  discreteness on top of `negDef_orthogonal`; it is not a statement about the
  real quadratic space alone.
* **The component `P⁺` of `P`.** Choosing the connected component containing
  `exp(iω)` is orientation data on the positive plane. Nothing below needs it.
* **The complex form.** Bridgeland's domain sits in `M ⊗ ℝ ℂ` and is cut out by
  a condition on `Re Ω` and `Im Ω`. The plane they span carries exactly that
  condition, so the two-plane presentation is the same set without paying for
  complexification.
-/

open QuadraticMap

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

section Defs

variable (Q : QuadraticForm ℝ M)

/-- A **positive plane**: a two-dimensional subspace on which `Q` is positive
definite. In the K3 case these are the planes spanned by `Re Ω` and `Im Ω` for
`Ω` in Bridgeland's `P(X)`. -/
structure IsPositivePlane (W : Submodule ℝ M) : Prop where
  /-- The subspace is a plane. -/
  finrank_eq : Module.finrank ℝ W = 2
  /-- `Q` is positive definite on it. -/
  posDef : (Q.restrict W).PosDef

/-- The signature hypothesis: `(2, n - 2)`, written without truncated
subtraction. Nondegeneracy is a consequence rather than a field, see
`nondegenerate`. -/
structure HasSignatureTwo : Prop where
  /-- The positive index of inertia is `2`. -/
  sigPos_eq : sigPos Q = 2
  /-- The negative index of inertia takes up everything else. -/
  sigNeg_add_two : sigNeg Q + 2 = Module.finrank ℝ M

/-- A **spherical class**: `(δ, δ) = -2` for the pairing, which is the polar
form of `Q`. Stated bilinearly so that it reads as in the source; see
`isSphericalClass_iff_apply` for the quadratic form of the same condition. -/
def IsSphericalClass (δ : M) : Prop := polar Q δ δ = -2

/-- The orthogonal complement with respect to the pairing. -/
abbrev orthogonal (W : Submodule ℝ M) : Submodule ℝ M :=
  LinearMap.BilinForm.orthogonal Q.polarBilin W

/-- The **wall** of a class `δ`: the positive planes orthogonal to `δ`. For a
K3 surface this is the hyperplane `δ^⊥` of Bridgeland's period domain, read on
the plane rather than on a complex vector spanning it. -/
def wall (δ : M) : Set (Submodule ℝ M) :=
  {W | IsPositivePlane Q W ∧ ∀ w ∈ W, polar Q δ w = 0}

/-- The **period domain**: all positive planes. -/
def periodDomain : Set (Submodule ℝ M) := {W | IsPositivePlane Q W}

/-- The spherical classes of a set of classes — Bridgeland's `Δ(X)` when the
set is the Mukai lattice. -/
def sphericalClasses (Λ : Set M) : Set M := {δ ∈ Λ | IsSphericalClass Q δ}

/-- The **cut period domain**, `P₀`: the positive planes lying on no wall of a
class in `Δ`.

`Δ` is a parameter, and it must be: cutting by *every* real class of square `-2`
deletes the whole domain, since the negative definite `Wᗮ` of any positive plane
contains such a class. That is `periodDomain₀_sphericalClasses_univ_eq_empty`
below, and it is why Bridgeland cuts by the lattice `Δ(X)`, which is discrete.
The intended argument is `sphericalClasses Q Λ` for a lattice `Λ`. -/
def periodDomain₀ (Δ : Set M) : Set (Submodule ℝ M) :=
  {W ∈ periodDomain Q | ∀ δ ∈ Δ, W ∉ wall Q δ}

end Defs

variable {Q : QuadraticForm ℝ M}

/-- The pairing is symmetric, hence reflexive. -/
theorem polarBilin_isRefl : Q.polarBilin.IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  exact (polar_comm (⇑Q) y x).trans h

theorem mem_orthogonal_iff {W : Submodule ℝ M} {u : M} :
    u ∈ orthogonal Q W ↔ ∀ w ∈ W, polar (⇑Q) w u = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

/-- Orthogonality to a plane spanned by two vectors is orthogonality to both,
which is what makes it a closed condition. -/
theorem mem_orthogonal_span_pair_iff {x y u : M} :
    u ∈ orthogonal Q (Submodule.span ℝ ({x, y} : Set M)) ↔
      polar (⇑Q) x u = 0 ∧ polar (⇑Q) y u = 0 := by
  rw [mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h x (Submodule.subset_span (by simp)), h y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ w hw
    have hle : Submodule.span ℝ ({x, y} : Set M) ≤ LinearMap.ker (Q.polarBilin.flip u) := by
      rw [Submodule.span_le]
      rintro z (rfl | rfl) <;> simp [LinearMap.mem_ker, hx, hy]
    simpa [LinearMap.mem_ker] using hle hw

/-- A spherical class is one with `Q δ = -1`; the factor two is the difference
between the pairing and its quadratic form. -/
theorem isSphericalClass_iff_apply {δ : M} : IsSphericalClass Q δ ↔ Q δ = -1 := by
  rw [IsSphericalClass, polar_self, two_nsmul]
  constructor <;> intro h <;> linarith

/-- A positive plane lies on the wall of `δ` exactly when `δ` is orthogonal to
it. This is the form in which the wall condition meets `negDef_orthogonal`. -/
theorem mem_wall_iff_mem_orthogonal {W : Submodule ℝ M} {δ : M}
    (hW : IsPositivePlane Q W) : W ∈ wall Q δ ↔ δ ∈ orthogonal Q W := by
  rw [wall, Set.mem_setOf_eq, mem_orthogonal_iff]
  refine ⟨fun h w hw => ?_, fun h => ⟨hW, fun w hw => ?_⟩⟩
  · exact (polar_comm (⇑Q) w δ).trans (h.2 w hw)
  · exact (polar_comm (⇑Q) δ w).trans (h w hw)

/-- A spherical class lies in no positive plane: it has negative square and the
form is positive definite on the plane. This is why a wall meets its plane in
the orthogonal complement of the plane rather than inside it. -/
theorem notMem_of_isSphericalClass {W : Submodule ℝ M} {δ : M}
    (hW : IsPositivePlane Q W) (hδ : IsSphericalClass Q δ) : δ ∉ W := by
  intro hmem
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [isSphericalClass_iff_apply, h, map_zero] at hδ
    norm_num at hδ
  have hpos : 0 < (Q.restrict W) ⟨δ, hmem⟩ := hW.posDef _ (by simpa using hδ0)
  rw [restrict_apply, isSphericalClass_iff_apply.mp hδ] at hpos
  norm_num at hpos

/-- The pairing is nondegenerate on a positive plane: a vector of the plane
orthogonal to the whole plane is orthogonal to itself, so its square vanishes
and positive definiteness kills it. -/
theorem restrict_nondegenerate_of_isPositivePlane {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) :
    (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate := by
  have key : ∀ x : W, LinearMap.BilinForm.restrict Q.polarBilin W x x = 0 → x = 0 := by
    intro x hxx
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      polarBilin_apply_apply, polar_self, two_nsmul] at hxx
    by_contra hx0
    have hpos := hW.posDef x hx0
    rw [restrict_apply] at hpos
    linarith
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

/-- Adjoining a vector of positive square from `Wᗮ` to a positive plane gives a
three-dimensional positive definite subspace. This is the whole content of
`nonpos_of_mem_orthogonal`: `sigPos = 2` forbids such a subspace. -/
private theorem posDef_sup_span {W : Submodule ℝ M} (hW : IsPositivePlane Q W)
    {u : M} (hu : u ∈ orthogonal Q W) (hQu : 0 < Q u) :
    (Q.restrict (W ⊔ (ℝ ∙ u))).PosDef := by
  rintro ⟨x, hx⟩ hx0
  rw [Submodule.mem_sup] at hx
  obtain ⟨w, hw, z, hz, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hpolar : polar (⇑Q) w (a • u) = 0 := by
    rw [polar_smul_right, mem_orthogonal_iff.mp hu w hw, smul_zero]
  have hval : Q (w + a • u) = Q w + (a * a) * Q u := by
    have := polar_add_right (Q := Q) w w (a • u)
    simp only [polar, QuadraticMap.map_smul, smul_eq_mul] at hpolar ⊢
    linarith [hpolar]
  rw [restrict_apply, hval]
  have hne : w ≠ 0 ∨ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (by simp [hcon.1, hcon.2])
  have hw' : 0 ≤ Q w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · exact le_of_lt (by simpa [restrict_apply] using hW.posDef ⟨w, hw⟩ (by simpa using hw0))
  rcases hne with hne | hne
  · have : 0 < Q w := by
      simpa [restrict_apply] using hW.posDef ⟨w, hw⟩ (by simpa using hne)
    nlinarith [mul_self_nonneg a]
  · nlinarith [mul_self_pos.mpr hne]

/-- On a subspace where `Q` is nonpositive, an isotropic vector is orthogonal to
everything: `t = c / (1 - Q y)` makes `Q (u + t • y) = c² / (1 - Q y)²`, which is
positive as soon as the pairing `c` is nonzero. -/
private theorem polar_eq_zero_of_nonpos {S : Submodule ℝ M}
    (hle : ∀ y ∈ S, Q y ≤ 0) {u : M} (hu : u ∈ S) (hQu : Q u = 0) {y : M} (hy : y ∈ S) :
    polar (⇑Q) u y = 0 := by
  by_contra hc
  set c := polar (⇑Q) u y with hcdef
  set q := Q y with hqdef
  have hq : q ≤ 0 := hle y hy
  have h1 : (0 : ℝ) < 1 - q := by linarith
  set t := c / (1 - q) with htdef
  have hmem : u + t • y ∈ S := S.add_mem hu (S.smul_mem t hy)
  have hval : Q (u + t • y) = Q u + (t * t) * q + t * c := by
    have h₁ : polar (⇑Q) u (t • y) = t * c := by
      rw [polar_smul_right, smul_eq_mul]
    have h₂ : Q (t • y) = (t * t) * Q y := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
    have h₃ : polar (⇑Q) u (t • y) = Q (u + t • y) - Q u - Q (t • y) := rfl
    rw [h₁, h₂] at h₃
    linarith
  have hpos : 0 < Q (u + t • y) := by
    rw [hval, hQu, htdef]
    have hne : c * c > 0 := mul_self_pos.mpr hc
    have : c / (1 - q) * (c / (1 - q)) * q + c / (1 - q) * c
        = c * c / ((1 - q) * (1 - q)) := by
      field_simp
      ring
    rw [zero_add, this]
    positivity
  exact absurd (hle _ hmem) (not_le.mpr hpos)

section FiniteDimensional

variable [FiniteDimensional ℝ M]

/-- The signature hypothesis leaves no radical. -/
theorem nondegenerate (hsig : HasSignatureTwo Q) : Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hsig.sigPos_eq, ← hsig.sigNeg_add_two] at h
  omega

/-- `M = W ⊕ Wᗮ` for a positive plane `W`. -/
theorem isCompl_orthogonal {W : Submodule ℝ M} (hW : IsPositivePlane Q W) :
    IsCompl W (orthogonal Q W) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate polarBilin_isRefl
    (restrict_nondegenerate_of_isPositivePlane hW)

/-- **`Q` is nonpositive on the orthogonal complement of a positive plane.**
A vector of positive square there would produce a three-dimensional positive
definite subspace, and `sigPos Q = 2`. -/
theorem nonpos_of_mem_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) {u : M} (hu : u ∈ orthogonal Q W) : Q u ≤ 0 := by
  by_contra hQu
  push Not at hQu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hQu
    exact lt_irrefl _ hQu
  have hdisj : Disjoint W (ℝ ∙ u) :=
    (isCompl_orthogonal hW).disjoint.mono_right (by simpa using hu)
  have hinf : W ⊓ (ℝ ∙ u) = ⊥ := disjoint_iff.mp hdisj
  have hrank : Module.finrank ℝ (W ⊔ (ℝ ∙ u) : Submodule ℝ M) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ u)
    rw [hinf, hW.finrank_eq, finrank_span_singleton hu0] at h
    simpa using h
  have hle := le_sigPos_of_posDef Q (posDef_sup_span hW hu hQu)
  rw [hrank, hsig.sigPos_eq] at hle
  omega

/-- **The engine.** On the orthogonal complement of a positive plane the form is
negative definite.

`nonpos_of_mem_orthogonal` gives nonpositivity; an isotropic vector there would
be orthogonal to `Wᗮ` by `polar_eq_zero_of_nonpos` and to `W` by construction,
hence to `M = W ⊕ Wᗮ`, hence in the radical, which the signature hypothesis
makes trivial. -/
theorem neg_of_mem_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) {u : M} (hu : u ∈ orthogonal Q W) (hu0 : u ≠ 0) :
    Q u < 0 := by
  rcases lt_or_eq_of_le (nonpos_of_mem_orthogonal hsig hW hu) with h | h
  · exact h
  · exfalso
    have hQu : Q u = 0 := h
    have hperp : ∀ y ∈ orthogonal Q W, polar (⇑Q) u y = 0 := fun y hy =>
      polar_eq_zero_of_nonpos (fun z hz => nonpos_of_mem_orthogonal hsig hW hz) hu hQu hy
    have hW' : ∀ w ∈ W, polar (⇑Q) u w = 0 := fun w hw =>
      (polar_comm (⇑Q) u w).trans (mem_orthogonal_iff.mp hu w hw)
    have htop : ∀ z : M, polar (⇑Q) u z = 0 := by
      intro z
      have hz : z ∈ W ⊔ orthogonal Q W := by
        rw [(isCompl_orthogonal hW).sup_eq_top]
        trivial
      rw [Submodule.mem_sup] at hz
      obtain ⟨w, hw, v, hv, rfl⟩ := hz
      rw [polar_add_right, hW' w hw, hperp v hv, add_zero]
    have hrad : u ∈ Q.radical := by
      refine ⟨hQu, ?_⟩
      ext z
      simpa using htop z
    rw [(nondegenerate_iff_radical_eq_bot.mp (nondegenerate hsig))] at hrad
    exact hu0 hrad

/-- `negDef_orthogonal` in the shape `sigNeg` consumes: `-Q` is positive
definite on `Wᗮ`. -/
theorem negDef_orthogonal (hsig : HasSignatureTwo Q) {W : Submodule ℝ M}
    (hW : IsPositivePlane Q W) : ((-Q).restrict (orthogonal Q W)).PosDef := by
  rintro ⟨u, hu⟩ hu0
  have : u ≠ 0 := by simpa using hu0
  simpa [restrict_apply] using neg_of_mem_orthogonal hsig hW hu this

/-- The complement of a positive plane is a hyperplane pair short of `M`. Only
the splitting is used, so the signature hypothesis is not needed. -/
theorem finrank_orthogonal {W : Submodule ℝ M} (hW : IsPositivePlane Q W) :
    Module.finrank ℝ (orthogonal Q W) + 2 = Module.finrank ℝ M := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_orthogonal hW)
  rw [hW.finrank_eq] at h
  omega


/-- **Cutting by every real class of square `-2` deletes the whole domain.**

The orthogonal complement of a positive plane is negative definite and, once the
space has dimension at least three, nonzero; scaling any vector of it to square
`-1` produces a real spherical class orthogonal to the plane. So every positive
plane lies on such a wall.

This is why `periodDomain₀` takes the class set as a parameter, and why
Bridgeland cuts by the discrete `Δ(X)` rather than by all of `{δ | ⟪δ,δ⟫ = -2}`.
-/
theorem periodDomain₀_sphericalClasses_univ_eq_empty (hsig : HasSignatureTwo Q)
    (hdim : 3 ≤ Module.finrank ℝ M) :
    periodDomain₀ Q (sphericalClasses Q Set.univ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro W ⟨hW, hcut⟩
  have hWpos : IsPositivePlane Q W := hW
  -- the complement is nonzero
  have hrank : Module.finrank ℝ (orthogonal Q W) + 2 = Module.finrank ℝ M :=
    finrank_orthogonal hWpos
  have hpos : 0 < Module.finrank ℝ (orthogonal Q W) := by omega
  have hnt : Nontrivial (orthogonal Q W) := (Module.finrank_pos_iff).mp hpos
  obtain ⟨u, hu0⟩ := exists_ne (0 : orthogonal Q W)
  have humem : (u : M) ∈ orthogonal Q W := u.2
  have hune : (u : M) ≠ 0 := by simpa using hu0
  have hQu : Q (u : M) < 0 := neg_of_mem_orthogonal hsig hWpos humem hune
  -- scale it to square `-1`, i.e. to a spherical class
  have hQne : Q (u : M) ≠ 0 := ne_of_lt hQu
  have hfrac : 0 < -1 / Q (u : M) := div_pos_of_neg_of_neg (by norm_num) hQu
  set c : ℝ := Real.sqrt (-1 / Q (u : M)) with hc
  have hcsq : c * c = -1 / Q (u : M) := Real.mul_self_sqrt hfrac.le
  set δ : M := c • (u : M) with hδ
  have hQδ : Q δ = -1 := by
    rw [hδ, QuadraticMap.map_smul, smul_eq_mul, hcsq]
    field_simp
  have hsph : IsSphericalClass Q δ := by
    rw [isSphericalClass_iff_apply, hQδ]
  have hmem : δ ∈ orthogonal Q W := Submodule.smul_mem _ _ humem
  exact hcut δ ⟨Set.mem_univ δ, hsph⟩ ((mem_wall_iff_mem_orthogonal hWpos).mpr hmem)

/-- **The period domain of a signature `(2, n - 2)` space is nonempty.**

`sigPos Q = 2` is exactly the assertion that a two-dimensional positive definite
subspace is available, so the hypothesis carries its own witness and nothing
below is vacuous. -/
theorem exists_isPositivePlane (hsig : HasSignatureTwo Q) :
    ∃ W : Submodule ℝ M, IsPositivePlane Q W := by
  obtain ⟨W, hrank, hposDef⟩ := exists_finrank_eq_sigPos_and_posDef Q
  exact ⟨W, ⟨hrank.trans hsig.sigPos_eq, hposDef⟩⟩

theorem periodDomain_nonempty (hsig : HasSignatureTwo Q) : (periodDomain Q).Nonempty :=
  exists_isPositivePlane hsig

end FiniteDimensional

section Witness

/-- The diagonal form `x₀² + x₁² - x₂²` on `ℝ³`. It is the smallest quadratic
space satisfying `HasSignatureTwo`, and it is here so that the hypothesis is
known to be inhabited rather than merely stated. -/
noncomputable def stdForm : QuadraticForm ℝ (Fin 3 → ℝ) :=
  weightedSumSquares ℝ ![(1 : ℝ), 1, -1]

theorem stdForm_hasSignatureTwo : HasSignatureTwo stdForm := by
  have hpos : {i : Fin 3 | 0 < ![(1 : ℝ), 1, -1] i} = ({0, 1} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num
  have hneg : {i : Fin 3 | ![(1 : ℝ), 1, -1] i < 0} = ({2} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [Fin.ext_iff]
  constructor
  · rw [stdForm, QuadraticForm.sigPos_weightedSumSquares, hpos]
    exact Set.ncard_pair (by decide)
  · rw [stdForm, QuadraticForm.sigNeg_weightedSumSquares, hneg, Set.ncard_singleton]
    simp

end Witness

section SignatureOne

variable [FiniteDimensional ℝ M]

omit [FiniteDimensional ℝ M] in
private theorem apply_smul_add_smul (Q : QuadraticForm ℝ M) (u v : M) (a b : ℝ) :
    Q (a • u + b • v) = a ^ 2 * Q u + b ^ 2 * Q v + a * b * polar (⇑Q) u v := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right]
  ring

/-- **`Q` is nonpositive on the orthogonal complement of a positive vector when
`sigPos Q = 1`.**

The signature-one companion of `nonpos_of_mem_orthogonal`, which is the same
statement one dimension up. A vector of positive square orthogonal to `u` would
span, with `u`, a two-dimensional positive definite subspace, and `sigPos Q = 1`
forbids that.

With `Q` the intersection form of `NS(X) ⊗ ℝ` this **is** the Hodge index
theorem in the form §6 consumes: `c · ω = 0` and `ω² > 0` give `c² ≤ 0`. Stated
here rather than in the Mukai files because it is a fact about a real quadratic
space and mentions no geometry.

Note the orthogonality hypothesis is on `polar`, which for a form built by
`toQuadraticMap` is **twice** the underlying pairing; over `ℝ` that is
immaterial for vanishing, but see `Mukai/RealForm.lean` on why the factor is
not immaterial elsewhere. -/
theorem nonpos_of_sigPos_eq_one (Q : QuadraticForm ℝ M) (hsig : sigPos Q = 1)
    {u v : M} (hu : 0 < Q u) (horth : polar (⇑Q) u v = 0) : Q v ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hcon
  have hinf : (ℝ ∙ u) ⊓ (ℝ ∙ v) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx2
    have h1 : polar (⇑Q) u (b • v) = 0 := by
      rw [polar_smul_right, horth, smul_zero]
    have h2 : polar (⇑Q) u (a • u) = 0 := by rw [← hb]; exact h1
    rw [polar_smul_right, polar_self] at h2
    have h3 : a * (2 * Q u) = 0 := by simpa [smul_eq_mul] using h2
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (by positivity)
    simp [ha]
  have hpos : (Q.restrict ((ℝ ∙ u) ⊔ (ℝ ∙ v))).PosDef := by
    rintro ⟨x, hx⟩ hx0
    rw [Submodule.mem_sup] at hx
    obtain ⟨w, hw, z, hz, rfl⟩ := hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [restrict_apply, apply_smul_add_smul Q u v a b, horth]
    have hne : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hx0
    have h1 : 0 ≤ a ^ 2 * Q u := by positivity
    have h2 : 0 ≤ b ^ 2 * Q v := by positivity
    rcases not_and_or.mp hne with h | h
    · have : 0 < a ^ 2 * Q u := by positivity
      linarith
    · have : 0 < b ^ 2 * Q v := by positivity
      linarith
  have hrank : Module.finrank ℝ ((ℝ ∙ u) ⊔ (ℝ ∙ v) : Submodule ℝ M) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ u) (ℝ ∙ v)
    rw [hinf, finrank_span_singleton hu0, finrank_span_singleton hv0] at h
    simpa using h
  have hle := le_sigPos_of_posDef Q hpos
  rw [hrank, hsig] at hle
  omega

end SignatureOne

end PeriodDomain
