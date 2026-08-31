/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Module

/-!
# Degree-zero homogeneous localization of graded modules

This file supplies the algebraic input missing from Mathlib's `Proj` API. Mathlib already
constructs the degree-zero homogeneous localization ring `HomogeneousLocalization 𝒜 S` and
the ordinary localized module `LocalizedModule S M`. We isolate inside the latter the fractions
whose module numerator and ring denominator lie in matching graded pieces.

The construction is intentionally indexed by the same additive grading monoid on the ring and
the module. Integer shifts, which reconcile a natural grading on the ring with an integer-indexed
family of module twists, belong to the separate graded-shift layer.

## Localizing away from one element

`awayMk` writes the fraction `m / fⁿ`, and two statements make it a usable normal form:

* `exists_awayMk` — every degree-zero fraction away from `f` *is* an `awayMk`. The denominator
  is a power of `f` by construction; what has to be proved is that the `NumDenSameDeg` degree
  certificate is forced to be `n • deg f`, which is `DirectSum.degree_eq_of_mem_mem` once `fⁿ`
  is known to be nonzero.
* `awayMk_eq_awayMk_iff` — two such fractions agree exactly when they cross-multiply, with no
  residual `∃ u` from the localization. The `∃ u` is what the general
  `mk_eq_mk_iff` leaves behind; cancelling it is where the domain and torsion-freeness
  hypotheses are spent, and they are spent nowhere else.

Together these turn `DegreeZeroLocalization 𝒜 𝓜 (.powers f)` into fractions with an explicit
representative and a computable equality test, which is what any basis for it has to start from
(see the Laurent monomial basis of #491).

`awayMk_eq_zero_iff` specialises the equality test to the zero fraction, which is what makes the
numerator a faithful record: any independence statement about fractions reduces to one about
numerators.

`awayMk_zero`, `awayMk_add`, `awayMk_sum` and `awayMk_shift` are the arithmetic that goes with
the normal form: the first three are additivity in the numerator at a fixed denominator, and the
last puts two fractions over a common denominator. Spanning arguments need exactly this pair —
decompose a numerator into a sum, then align denominators — and none of the four costs a
cancellation hypothesis.
-/

noncomputable section

open DirectSum SetLike

namespace GradedModule

universe u v

variable {ι A M σA σM : Type*}
variable [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ι → σA) (𝓜 : ι → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
variable (S : Submonoid A)

/-! ## Homogeneous fractions -/

/-- A module fraction whose numerator and denominator lie in matching graded pieces. -/
structure NumDenSameDeg where
  /-- The common grading index of the numerator and denominator. -/
  deg : ι
  /-- The homogeneous numerator. -/
  num : 𝓜 deg
  /-- The homogeneous denominator. -/
  den : 𝒜 deg
  /-- The denominator belongs to the submonoid being localized. -/
  den_mem : (den : A) ∈ S

namespace NumDenSameDeg

variable {𝒜 𝓜 S}

/-- Forget the grading certificate and view a homogeneous module fraction in the ordinary
localized module. -/
def embedding (c : NumDenSameDeg 𝒜 𝓜 S) : LocalizedModule S M :=
  LocalizedModule.mk (S := S) (c.num : M) (⟨(c.den : A), c.den_mem⟩ : S)

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σA A]
    [AddSubgroupClass σM M] [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
@[simp]
theorem embedding_eq (c : NumDenSameDeg 𝒜 𝓜 S) :
    c.embedding = LocalizedModule.mk (S := S) (c.num : M)
      (⟨(c.den : A), c.den_mem⟩ : S) :=
  rfl

end NumDenSameDeg

/-! ## The degree-zero submodule -/

/-- Restrict scalars on the ordinary localized module along the inclusion of the degree-zero
homogeneous localization into the full localization. -/
noncomputable instance localizedModuleModule :
    Module (HomogeneousLocalization 𝒜 S) (LocalizedModule S M) :=
  Module.compHom _ (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))

/-- An ordinary localized-module element is degree zero if it has a representative whose module
numerator and ring denominator lie in matching graded pieces. -/
def IsDegreeZero (z : LocalizedModule S M) : Prop :=
  ∃ c : NumDenSameDeg 𝒜 𝓜 S, c.embedding = z

omit [SetLike.GradedSMul 𝒜 𝓜] in
theorem isDegreeZero_zero : IsDegreeZero 𝒜 𝓜 S (0 : LocalizedModule S M) := by
  refine ⟨⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, one_mem S⟩, ?_⟩
  simp [NumDenSameDeg.embedding]

theorem IsDegreeZero.add {x y : LocalizedModule S M}
    (hx : IsDegreeZero 𝒜 𝓜 S x) (hy : IsDegreeZero 𝒜 𝓜 S y) :
    IsDegreeZero 𝒜 𝓜 S (x + y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  refine ⟨
    { deg := p.deg + q.deg
      num := ⟨(q.den : A) • (p.num : M) + (p.den : A) • (q.num : M), ?_⟩
      den := ⟨(p.den : A) * (q.den : A), SetLike.mul_mem_graded p.den.2 q.den.2⟩
      den_mem := S.mul_mem p.den_mem q.den_mem }, ?_⟩
  · exact add_mem
      (add_comm q.deg p.deg ▸ SetLike.GradedSMul.smul_mem q.den.2 p.num.2)
      (SetLike.GradedSMul.smul_mem p.den.2 q.num.2)
  · simp only [NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_add_mk]
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σA A]
    [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜] in
theorem IsDegreeZero.neg {x : LocalizedModule S M} (hx : IsDegreeZero 𝒜 𝓜 S x) :
    IsDegreeZero 𝒜 𝓜 S (-x) := by
  obtain ⟨p, rfl⟩ := hx
  refine ⟨
    { deg := p.deg
      num := ⟨-(p.num : M), neg_mem p.num.2⟩
      den := p.den
      den_mem := p.den_mem }, ?_⟩
  simpa only [NumDenSameDeg.embedding] using
    (LocalizedModule.mk_neg
      (S := S) (M := M) (m := (p.num : M))
      (s := (⟨(p.den : A), p.den_mem⟩ : S)))

omit [AddSubgroupClass σM M] in
theorem IsDegreeZero.smul (a : HomogeneousLocalization 𝒜 S) {x : LocalizedModule S M}
    (hx : IsDegreeZero 𝒜 𝓜 S x) : IsDegreeZero 𝒜 𝓜 S (a • x) := by
  obtain ⟨p, rfl⟩ := hx
  refine ⟨
    { deg := a.deg + p.deg
      num := ⟨a.num • (p.num : M), SetLike.GradedSMul.smul_mem a.num_mem_deg p.num.2⟩
      den := ⟨a.den * (p.den : A), SetLike.mul_mem_graded a.den_mem_deg p.den.2⟩
      den_mem := S.mul_mem a.den_mem p.den_mem }, ?_⟩
  change LocalizedModule.mk (S := S) (a.num • (p.num : M))
    (⟨a.den * (p.den : A), S.mul_mem a.den_mem p.den_mem⟩ : S) =
      (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S) a) •
        LocalizedModule.mk (S := S) (p.num : M) (⟨(p.den : A), p.den_mem⟩ : S)
  rw [HomogeneousLocalization.algebraMap_apply]
  rw [a.eq_num_div_den]
  rw [LocalizedModule.mk_smul_mk]
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp⟩

/-- The degree-zero homogeneous localization as a submodule of the ordinary localized module. -/
def degreeZeroSubmodule :
    Submodule (HomogeneousLocalization 𝒜 S) (LocalizedModule S M) where
  carrier := IsDegreeZero 𝒜 𝓜 S
  zero_mem' := isDegreeZero_zero 𝒜 𝓜 S
  add_mem' := fun hx hy ↦
    IsDegreeZero.add (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) hx hy
  smul_mem' := fun a _ hx ↦
    IsDegreeZero.smul (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) a hx

/-- The degree-zero homogeneous localization of the graded module `M`. -/
abbrev DegreeZeroLocalization := degreeZeroSubmodule (𝓜 := 𝓜) 𝒜 S

namespace DegreeZeroLocalization

variable {𝒜 𝓜 S}

/-- Construct a degree-zero localized element from a certified homogeneous fraction. -/
def mk (c : NumDenSameDeg 𝒜 𝓜 S) : DegreeZeroLocalization 𝒜 𝓜 S :=
  ⟨c.embedding, ⟨c, rfl⟩⟩

@[simp]
theorem coe_mk (c : NumDenSameDeg 𝒜 𝓜 S) :
    ((mk c : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = c.embedding :=
  rfl

/-- Every degree-zero localized element has a homogeneous numerator and denominator. -/
theorem mk_surjective :
    Function.Surjective (mk : NumDenSameDeg 𝒜 𝓜 S → DegreeZeroLocalization 𝒜 𝓜 S) := by
  rintro ⟨z, ⟨c, hc⟩⟩
  exact ⟨c, Subtype.ext hc⟩

@[ext]
theorem ext {x y : DegreeZeroLocalization 𝒜 𝓜 S}
    (h : (x : LocalizedModule S M) = y) : x = y :=
  Subtype.ext h

/-- Equality of homogeneous fractions is the ordinary localized-module equality criterion. -/
theorem mk_eq_mk_iff (p q : NumDenSameDeg 𝒜 𝓜 S) :
    mk p = mk q ↔
      ∃ u : S,
        (u : A) • (q.den : A) • (p.num : M) =
          (u : A) • (p.den : A) • (q.num : M) := by
  constructor
  · intro h
    have h' : p.embedding = q.embedding := congr_arg Subtype.val h
    simp only [NumDenSameDeg.embedding] at h'
    rw [LocalizedModule.mk_eq] at h'
    simpa only [Submonoid.smul_def, Submonoid.coe_mul] using h'
  · intro h
    apply ext
    simp only [coe_mk, NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_eq]
    simpa only [Submonoid.smul_def, Submonoid.coe_mul] using h

@[simp]
theorem coe_zero :
    ((0 : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = 0 :=
  rfl

@[simp]
theorem coe_add (x y : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((x + y : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = x + y :=
  rfl

@[simp]
theorem coe_neg (x : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((-x : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = -x :=
  rfl

@[simp]
theorem coe_smul (a : HomogeneousLocalization 𝒜 S)
    (x : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((a • x : DegreeZeroLocalization 𝒜 𝓜 S) : LocalizedModule S M) = a • (x : LocalizedModule S M) :=
  rfl

/-- **The scalar action in explicit fractions**: `(p/q) • (m/s) = (p • m)/(q * s)`.

The companion of `twistMul_mk` for the module action, and the rule a caller
needs to rebuild a local-fraction certificate after multiplying by a scalar.
Without it the action is opaque at a use site: `coe_smul` moves the problem into
`LocalizedModule` but says nothing about which fraction comes out.

The proof is the one already inside `IsDegreeZero.smul`, which constructs exactly
this `NumDenSameDeg` in order to show the action stays degree zero; naming the
computation separately means a caller no longer has to re-derive it.

**Not `@[simp]`.** Its right-hand side is stated with `a.num` and `a.den`, the
representative `HomogeneousLocalization` chooses, which is the *less* usable
form — see `mk_smul_mk` below. Marking both would also be a `simpNF` conflict,
since this one rewrites that one's left-hand side. -/
theorem smul_mk (a : HomogeneousLocalization 𝒜 S) (c : NumDenSameDeg 𝒜 𝓜 S) :
    a • (mk c : DegreeZeroLocalization 𝒜 𝓜 S) =
      mk { deg := a.deg + c.deg
           num := ⟨a.num • (c.num : M),
             SetLike.GradedSMul.smul_mem a.num_mem_deg c.num.2⟩
           den := ⟨a.den * (c.den : A),
             SetLike.mul_mem_graded a.den_mem_deg c.den.2⟩
           den_mem := S.mul_mem a.den_mem c.den_mem } := by
  apply DegreeZeroLocalization.ext
  rw [coe_smul, coe_mk, coe_mk]
  show (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S) a) •
    LocalizedModule.mk (S := S) (c.num : M) (⟨(c.den : A), c.den_mem⟩ : S) = _
  rw [HomogeneousLocalization.algebraMap_apply, a.eq_num_div_den,
    LocalizedModule.mk_smul_mk]
  rfl

/-- **The scalar action on two explicit fractions.**

`smul_mk` leaves the scalar as `a.num / a.den`, which are the representative
`HomogeneousLocalization` chooses — *not* the fields of whatever
`NumDenSameDeg` the caller built `a` from. When the scalar is itself written as
`HomogeneousLocalization.mk c'`, that gap has to be closed again at every use
site. This states the rule with both sides explicit, so it does not. -/
@[simp]
theorem mk_smul_mk (c' : HomogeneousLocalization.NumDenSameDeg 𝒜 S)
    (c : NumDenSameDeg 𝒜 𝓜 S) :
    HomogeneousLocalization.mk c' • (mk c : DegreeZeroLocalization 𝒜 𝓜 S) =
      mk { deg := c'.deg + c.deg
           num := ⟨(c'.num : A) • (c.num : M),
             SetLike.GradedSMul.smul_mem c'.num.2 c.num.2⟩
           den := ⟨(c'.den : A) * (c.den : A),
             SetLike.mul_mem_graded c'.den.2 c.den.2⟩
           den_mem := S.mul_mem c'.den_mem c.den_mem } := by
  apply DegreeZeroLocalization.ext
  rw [coe_smul, coe_mk, coe_mk]
  show (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S)
      (HomogeneousLocalization.mk c')) •
    LocalizedModule.mk (S := S) (c.num : M) (⟨(c.den : A), c.den_mem⟩ : S) = _
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
    LocalizedModule.mk_smul_mk]
  rfl

/-! ### Maps induced by enlarging the denominator submonoid -/

/-- Enlarging the denominator submonoid sends degree-zero homogeneous module fractions to
degree-zero homogeneous module fractions. -/
noncomputable def mapOfLE {T : Submonoid A} (h : S ≤ T) :
    DegreeZeroLocalization 𝒜 𝓜 S →+ DegreeZeroLocalization 𝒜 𝓜 T where
  toFun z := by
    refine ⟨LocalizedModule.liftOfLE S T h z, ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := c.num
        den := c.den
        den_mem := h c.den_mem }, ?_⟩
    rw [← hc]
    change LocalizedModule.mk (c.num : M) (⟨c.den, h c.den_mem⟩ : T) =
      LocalizedModule.liftOfLE S T h
        (LocalizedModule.mk (c.num : M) (⟨c.den, c.den_mem⟩ : S))
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
    exact (IsLocalizedModule.liftOfLE_mk' S T h
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap T M)
        (c.num : M) (⟨c.den, c.den_mem⟩ : S)).symm
  map_zero' := by
    apply ext
    exact (LocalizedModule.liftOfLE S T h).map_zero
  map_add' x y := by
    apply ext
    exact (LocalizedModule.liftOfLE S T h).map_add
      (x : LocalizedModule S M) (y : LocalizedModule S M)

@[simp]
theorem mapOfLE_mk {T : Submonoid A} (h : S ≤ T) (c : NumDenSameDeg 𝒜 𝓜 S) :
    mapOfLE (𝒜 := 𝒜) (𝓜 := 𝓜) h (mk c) = mk
      { deg := c.deg
        num := c.num
        den := c.den
        den_mem := h c.den_mem } := by
  apply ext
  change LocalizedModule.liftOfLE S T h
      (LocalizedModule.mk (c.num : M) (⟨c.den, c.den_mem⟩ : S)) =
    LocalizedModule.mk (c.num : M) (⟨c.den, h c.den_mem⟩ : T)
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.liftOfLE_mk' S T h
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap T M)
        (c.num : M) (⟨c.den, c.den_mem⟩ : S)

/-! ### Inverting an element that is not a power of the new denominator

`mapOfLE` covers enlarging the denominator submonoid along an inclusion `S ≤ T`. The Čech
differential needs a case it does not reach: along a face the denominators are
`.powers g₁` and `.powers g₂` with `g₁ * h = g₂`, and `Submonoid.powers g₁ ≤ Submonoid.powers g₂`
is false — `powers a ≤ powers b` needs `a` to be a *power* of `b`, and divisibility is weaker.

The map still exists, because `g₁` is already invertible once `g₂` is. These two lemmas supply
exactly that, in the form `LocalizedModule.lift` consumes, and are what a face map must be built
from. They are stated for a bare module because nothing about them is graded. -/

/-- If `g₁ * h` is a power of `g₂`, then `g₁` is already invertible after inverting `g₂`.

`g₁ * h` is invertible there, and in a commutative ring a factor of a unit is a unit. -/
theorem isUnit_algebraMap_localization_of_mul_mem {g₁ g₂ h : A}
    (hgh : g₁ * h ∈ Submonoid.powers g₂) :
    IsUnit (algebraMap A (Localization (Submonoid.powers g₂)) g₁) := by
  have h1 : IsUnit (algebraMap A (Localization (Submonoid.powers g₂)) (g₁ * h)) :=
    IsLocalization.map_units _ ⟨g₁ * h, hgh⟩
  rw [map_mul] at h1
  exact isUnit_of_mul_isUnit_left h1

/-- Every power of `g₁` therefore acts invertibly on the module localized at `g₂`.

This is the hypothesis of `LocalizedModule.lift`, so it is what turns the previous lemma into an
actual map out of the localization at `g₁`. The scalar action factors through
`Localization (Submonoid.powers g₂)`, where the inverse is available. -/
theorem isUnit_algebraMap_end_of_mul_mem {g₁ g₂ h : A}
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (s : Submonoid.powers g₁) :
    IsUnit (algebraMap A
      (Module.End A (LocalizedModule (Submonoid.powers g₂) M)) (s : A)) := by
  obtain ⟨N, hN⟩ := s.2
  obtain ⟨u, hu⟩ := (isUnit_algebraMap_localization_of_mul_mem (A := A) hgh).pow N
  have hu' : (u : Localization (Submonoid.powers g₂)) =
      algebraMap A (Localization (Submonoid.powers g₂)) (s : A) := by
    rw [hu, ← hN, map_pow]
  rw [Module.End.isUnit_iff]
  have key : ∀ x : LocalizedModule (Submonoid.powers g₂) M,
      (algebraMap A (Module.End A (LocalizedModule (Submonoid.powers g₂) M)) (s : A)) x =
        (u : Localization (Submonoid.powers g₂)) • x := fun x => by
    rw [hu', Module.algebraMap_end_apply, algebraMap_smul]
  constructor
  · intro x y hxy
    have h2 := congrArg (fun z => (↑u⁻¹ : Localization (Submonoid.powers g₂)) • z) hxy
    simpa [key, smul_smul] using h2
  · intro y
    exact ⟨(↑u⁻¹ : Localization (Submonoid.powers g₂)) • y, by simp [key, smul_smul]⟩

/-- The map of ordinary localized modules along a Čech face.

`g₁` is already invertible after inverting `g₂`, so the universal property of
`LocalizedModule (Submonoid.powers g₁) M` produces this map without any inclusion of
denominator submonoids. This is the underlying map of `faceMap`; it carries no grading. -/
noncomputable def faceLift {g₁ g₂ h : A} (hgh : g₁ * h ∈ Submonoid.powers g₂) :
    LocalizedModule (Submonoid.powers g₁) M →ₗ[A]
      LocalizedModule (Submonoid.powers g₂) M :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap (Submonoid.powers g₂) M)
    (isUnit_algebraMap_end_of_mul_mem (M := M) hgh)

/-- Along a face, clearing the denominator `g₁ⁿ` multiplies numerator and denominator by `hⁿ`.

This is the formula the graded face map is defined by: the abstract `LocalizedModule.lift` is
inverted here into an explicit fraction, which is what the degree-zero certificate needs.

Both sides are pinned by multiplying through by `g₁ ⁿ`, which acts invertibly on the target --
that is the whole content of `isUnit_algebraMap_end_of_mul_mem`. -/
theorem faceLift_mk {g₁ g₂ h : A} (hgh : g₁ * h ∈ Submonoid.powers g₂)
    (hg : g₁ * h = g₂) (m : M) (n : ℕ) :
    faceLift (M := M) hgh
        (LocalizedModule.mk m (⟨g₁ ^ n, n, rfl⟩ : Submonoid.powers g₁)) =
      LocalizedModule.mk (h ^ n • m) (⟨g₂ ^ n, n, rfl⟩ : Submonoid.powers g₂) := by
  have hunit := isUnit_algebraMap_end_of_mul_mem (M := M) hgh
    (⟨g₁ ^ n, n, rfl⟩ : Submonoid.powers g₁)
  rw [Module.End.isUnit_iff] at hunit
  apply hunit.1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
  have hleft : (g₁ ^ n) • faceLift (M := M) hgh
      (LocalizedModule.mk m ⟨g₁ ^ n, n, rfl⟩) =
      LocalizedModule.mk (S := Submonoid.powers g₂) m 1 := by
    rw [← LinearMap.map_smul, LocalizedModule.smul'_mk]
    have hcancel : LocalizedModule.mk ((g₁ ^ n) • m)
        (⟨g₁ ^ n, n, rfl⟩ : Submonoid.powers g₁) =
        LocalizedModule.mk (S := Submonoid.powers g₁) m 1 :=
      LocalizedModule.mk_cancel (⟨g₁ ^ n, n, rfl⟩ : Submonoid.powers g₁) m
    rw [hcancel, faceLift, LocalizedModule.lift_mk_one]
    rfl
  have hright : (g₁ ^ n) • LocalizedModule.mk (h ^ n • m)
      (⟨g₂ ^ n, n, rfl⟩ : Submonoid.powers g₂) =
      LocalizedModule.mk (S := Submonoid.powers g₂) m 1 := by
    rw [LocalizedModule.smul'_mk, ← mul_smul, ← mul_pow, hg]
    exact LocalizedModule.mk_cancel (⟨g₂ ^ n, n, rfl⟩ : Submonoid.powers g₂) m
  rw [hleft, hright]

omit [AddSubgroupClass σM M] in
/-- A face map preserves the degree-zero condition.

Clearing `g₁ⁿ` costs `hⁿ` in both numerator and denominator, so the matching-degree certificate
survives with its degree raised by `n • e`. -/
theorem isDegreeZero_faceLift {g₁ g₂ h : A} {e : ι} (hh : h ∈ 𝒜 e)
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (hg : g₁ * h = g₂)
    {z : LocalizedModule (Submonoid.powers g₁) M}
    (hz : IsDegreeZero 𝒜 𝓜 (Submonoid.powers g₁) z) :
    IsDegreeZero 𝒜 𝓜 (Submonoid.powers g₂) (faceLift (M := M) hgh z) := by
  obtain ⟨c, rfl⟩ := hz
  obtain ⟨n, hn⟩ := c.den_mem
  -- `Submonoid.powers` membership arrives unreduced; pin the beta-reduced form.
  have hn' : g₁ ^ n = (c.den : A) := hn
  have hden : (⟨(c.den : A), c.den_mem⟩ : Submonoid.powers g₁) = ⟨g₁ ^ n, n, rfl⟩ :=
    Subtype.ext hn'.symm
  have hpow : g₂ ^ n = h ^ n * (c.den : A) := by
    rw [← hg, mul_pow, mul_comm (g₁ ^ n) (h ^ n), hn']
  refine ⟨
    { deg := n • e + c.deg
      num := ⟨h ^ n • (c.num : M),
        SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n hh) c.num.2⟩
      den := ⟨g₂ ^ n, hpow ▸ SetLike.mul_mem_graded (SetLike.pow_mem_graded n hh) c.den.2⟩
      den_mem := ⟨n, rfl⟩ }, ?_⟩
  show LocalizedModule.mk _ _ = _
  rw [NumDenSameDeg.embedding, hden, faceLift_mk (M := M) hgh hg]

/-- The Čech face map on degree-zero homogeneous localizations.

`mapOfLE` cannot supply this: along a face the denominator submonoids are `Submonoid.powers g₁`
and `Submonoid.powers g₂` with `g₁ * h = g₂`, and divisibility does not nest powers submonoids.
The map exists anyway because `g₁` is invertible once `g₂` is. -/
noncomputable def faceMap {g₁ g₂ h : A} {e : ι} (hh : h ∈ 𝒜 e)
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (hg : g₁ * h = g₂) :
    DegreeZeroLocalization 𝒜 𝓜 (.powers g₁) →+
      DegreeZeroLocalization 𝒜 𝓜 (.powers g₂) where
  toFun z := ⟨faceLift (M := M) hgh (z : LocalizedModule (Submonoid.powers g₁) M),
    isDegreeZero_faceLift hh hgh hg z.2⟩
  map_zero' := by
    apply ext
    exact (faceLift (M := M) hgh).map_zero
  map_add' x y := by
    apply ext
    exact (faceLift (M := M) hgh).map_add
      (x : LocalizedModule (Submonoid.powers g₁) M)
      (y : LocalizedModule (Submonoid.powers g₁) M)

@[simp]
theorem coe_faceMap {g₁ g₂ h : A} {e : ι} (hh : h ∈ 𝒜 e)
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (hg : g₁ * h = g₂)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers g₁)) :
    ((faceMap (𝓜 := 𝓜) hh hgh hg z : DegreeZeroLocalization 𝒜 𝓜 (.powers g₂)) :
        LocalizedModule (Submonoid.powers g₂) M) =
      faceLift (M := M) hgh (z : LocalizedModule (Submonoid.powers g₁) M) :=
  rfl

/-- The face map in explicit fractions: `m / g₁ⁿ ↦ hⁿ m / g₂ⁿ`. -/
theorem faceMap_mk {g₁ g₂ h : A} {e : ι} (hh : h ∈ 𝒜 e)
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (hg : g₁ * h = g₂)
    (c : NumDenSameDeg 𝒜 𝓜 (.powers g₁)) (n : ℕ) (hn : g₁ ^ n = (c.den : A)) :
    faceMap (𝓜 := 𝓜) hh hgh hg (mk c) =
      mk ({ deg := n • e + c.deg
            num := ⟨h ^ n • (c.num : M),
              SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n hh) c.num.2⟩
            den := ⟨g₂ ^ n, by
              rw [show g₂ ^ n = h ^ n * (c.den : A) by
                rw [← hg, mul_pow, mul_comm (g₁ ^ n) (h ^ n), hn]]
              exact SetLike.mul_mem_graded (SetLike.pow_mem_graded n hh) c.den.2⟩
            den_mem := ⟨n, rfl⟩ } : NumDenSameDeg 𝒜 𝓜 (.powers g₂)) := by
  apply ext
  have hden : (⟨(c.den : A), c.den_mem⟩ : Submonoid.powers g₁) = ⟨g₁ ^ n, n, rfl⟩ :=
    Subtype.ext hn.symm
  show faceLift (M := M) hgh (NumDenSameDeg.embedding c) = _
  rw [NumDenSameDeg.embedding, hden, faceLift_mk (M := M) hgh hg]
  rfl

/-! ### Changing the grading by a membership equivalence

Two gradings with the same members present the same degree-zero localization. The underlying
element of `LocalizedModule S M` does not move at all; only the certificate is rebuilt. This is
the localization-level counterpart of `associatedIsoOfPiecewiseIff`, and it is what lets a
statement about `intShift 𝒜 0` be read as one about `𝒜`. -/

/-- Degree-zero localizations depend only on the membership predicates of the graded pieces. -/
noncomputable def linearEquivOfMemIff {σN : Type*} [SetLike σN M] [AddSubgroupClass σN M]
    (𝓝 : ι → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) :
    DegreeZeroLocalization 𝒜 𝓜 S ≃ₗ[HomogeneousLocalization 𝒜 S]
      DegreeZeroLocalization 𝒜 𝓝 S where
  toFun z := ⟨(z : LocalizedModule S M), by
    obtain ⟨c, hc⟩ := z.property
    exact ⟨{ deg := c.deg
             num := ⟨(c.num : M), (hmem c.deg (c.num : M)).mp c.num.2⟩
             den := c.den
             den_mem := c.den_mem }, hc⟩⟩
  invFun z := ⟨(z : LocalizedModule S M), by
    obtain ⟨c, hc⟩ := z.property
    exact ⟨{ deg := c.deg
             num := ⟨(c.num : M), (hmem c.deg (c.num : M)).mpr c.num.2⟩
             den := c.den
             den_mem := c.den_mem }, hc⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_linearEquivOfMemIff {σN : Type*} [SetLike σN M] [AddSubgroupClass σN M]
    (𝓝 : ι → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((linearEquivOfMemIff (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) 𝓝 hmem z :
        DegreeZeroLocalization 𝒜 𝓝 S) : LocalizedModule S M) =
      (z : LocalizedModule S M) :=
  rfl

@[simp]
theorem linearEquivOfMemIff_mk {σN : Type*} [SetLike σN M] [AddSubgroupClass σN M]
    (𝓝 : ι → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) (c : NumDenSameDeg 𝒜 𝓜 S) :
    linearEquivOfMemIff (𝒜 := 𝒜) (𝓜 := 𝓜) (S := S) 𝓝 hmem (mk c) =
      mk { deg := c.deg
           num := ⟨(c.num : M), (hmem c.deg (c.num : M)).mp c.num.2⟩
           den := c.den
           den_mem := c.den_mem } :=
  rfl

/-! ### Localization away from one homogeneous element -/

/-- The degree-zero fraction `m / fⁿ` when `f` has degree `d` and `m` has degree `n • d`. -/
def awayMk {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (m : M)
    (hm : m ∈ 𝓜 (n • d)) : DegreeZeroLocalization 𝒜 𝓜 (.powers f) :=
  mk
    { deg := n • d
      num := ⟨m, hm⟩
      den := ⟨f ^ n, SetLike.pow_mem_graded n hf⟩
      den_mem := ⟨n, rfl⟩ }

@[simp]
theorem coe_awayMk {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (m : M)
    (hm : m ∈ 𝓜 (n • d)) :
    ((awayMk hf n m hm : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
      LocalizedModule (.powers f) M) =
        LocalizedModule.mk m (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) :=
  rfl

/-- **`awayMk` is a normal form.** Every degree-zero fraction away from `f` is `m / fⁿ` for some
`n` and some `m` of degree `n • deg f`.

The denominator is a power of `f` because that is what `Submonoid.powers f` means; the content is
that the `NumDenSameDeg` degree certificate has no freedom left. It is pinned by
`DirectSum.degree_eq_of_mem_mem`: the denominator lies both in the certified piece and, as `fⁿ`,
in `n • deg f`, and a nonzero homogeneous element lies in exactly one piece.

The hypothesis is `∀ n, fⁿ ≠ 0` rather than `f ≠ 0` so that no domain assumption is needed here;
in a domain `pow_ne_zero` supplies it. It cannot be dropped: over a ring where `f` is nilpotent
the localization is trivial and the degree is genuinely unconstrained. -/
theorem exists_awayMk {f : A} {e : ι} (hf : f ∈ 𝒜 e) (hf0 : ∀ n : ℕ, f ^ n ≠ 0)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    ∃ (n : ℕ) (m : M) (hm : m ∈ 𝓜 (n • e)), z = awayMk hf n m hm := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  obtain ⟨deg, num, den, den_mem⟩ := c
  obtain ⟨n, hn⟩ := den_mem
  have hden : (den : A) ∈ 𝒜 (n • e) := hn ▸ SetLike.pow_mem_graded n hf
  have hdeg : deg = n • e :=
    DirectSum.degree_eq_of_mem_mem 𝒜 den.2 hden (hn ▸ hf0 n)
  subst hdeg
  refine ⟨n, (num : M), num.2, ext ?_⟩
  exact congrArg (fun s : Submonoid.powers f => LocalizedModule.mk (num : M) s)
    (Subtype.ext hn.symm : (⟨(den : A), ⟨n, hn⟩⟩ : Submonoid.powers f) = ⟨f ^ n, ⟨n, rfl⟩⟩)

/-- **Cross-multiplication decides equality of `awayMk`s.** `p / fⁿ = q / fᵐ` exactly when
`fᵐ • p = fⁿ • q`, with no surviving `∃ u`.

`mk_eq_mk_iff` is the general criterion and it leaves an unknown `u ∈ Submonoid.powers f`
behind. Cancelling that `u` is the whole point of this lemma and the only place the two
hypotheses are used: `IsDomain A` makes every `fᵗ` regular, and `Module.IsTorsionFree A M`
turns a regular ring element into an injective scalar action on `M`. For `M = A` the latter is
an instance, so the polynomial case needs neither supplied by hand.

Without torsion-freeness the statement is false, not merely unproved: an `f`-torsion element of
`M` is a nonzero numerator whose fraction is zero. -/
theorem awayMk_eq_awayMk_iff [IsDomain A] [Module.IsTorsionFree A M] {f : A} {e : ι}
    (hf : f ∈ 𝒜 e) (hf0 : f ≠ 0) {n m : ℕ} {p q : M} (hp : p ∈ 𝓜 (n • e))
    (hq : q ∈ 𝓜 (m • e)) :
    awayMk hf n p hp = awayMk hf m q hq ↔ f ^ m • p = f ^ n • q := by
  rw [awayMk, awayMk, mk_eq_mk_iff]
  constructor
  · rintro ⟨⟨u, t, rfl⟩, hu⟩
    exact Module.IsTorsionFree.isSMulRegular (M := M)
      (IsRegular.of_ne_zero (pow_ne_zero t hf0)) hu
  · intro h
    exact ⟨1, by simpa using h⟩

/-- The zero numerator gives the zero fraction. -/
theorem awayMk_zero {f : A} {e : ι} (hf : f ∈ 𝒜 e) (n : ℕ) :
    awayMk (𝓜 := 𝓜) hf n (0 : M) (zero_mem (𝓜 (n • e))) = 0 := by
  apply ext
  rw [coe_awayMk, coe_zero]
  simp

/-- `awayMk` is additive in the numerator at a fixed denominator. -/
theorem awayMk_add {f : A} {e : ι} (hf : f ∈ 𝒜 e) (n : ℕ) (p q : M)
    (hp : p ∈ 𝓜 (n • e)) (hq : q ∈ 𝓜 (n • e)) :
    awayMk hf n (p + q) (add_mem hp hq) = awayMk hf n p hp + awayMk hf n q hq := by
  apply ext
  rw [coe_awayMk, coe_add, coe_awayMk, coe_awayMk, LocalizedModule.mk_add_mk,
    LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, ← mul_smul]

/-- `awayMk` is additive over a finite sum of numerators.

The membership hypothesis is total (`∀ b`) rather than restricted to `s`, because the summands on
the right have to carry their own certificates and a `∀ b ∈ s` hypothesis is not available inside
`Finset.sum`. In practice the summands are monomials of a fixed degree, so nothing is lost.

The proof descends into `LocalizedModule` before inducting. That is not incidental: the numerator
appears in the type of `awayMk`'s membership argument, so rewriting `Finset.sum_insert` in the
goal directly fails on a non-type-correct motive. `coe_awayMk` discharges the certificate first,
and the induction then runs over an ordinary equation. -/
theorem awayMk_sum {f : A} {e : ι} (hf : f ∈ 𝒜 e) (n : ℕ) {β : Type*} (s : Finset β)
    (p : β → M) (hp : ∀ b, p b ∈ 𝓜 (n • e)) :
    awayMk hf n (∑ b ∈ s, p b) (sum_mem fun b _ => hp b) =
      ∑ b ∈ s, awayMk hf n (p b) (hp b) := by
  classical
  apply ext
  rw [coe_awayMk]
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, coe_add, coe_awayMk, ← ih,
        LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
      exact ⟨1, by
        simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, ← mul_smul]⟩

/-- Raising the denominator by `fᵗ` and the numerator with it leaves the fraction alone.

This is what puts two `awayMk`s over a common denominator, which every argument about sums of
fractions with different denominators needs. It holds over any ring: no cancellation is
performed, so neither `IsDomain` nor torsion-freeness appears. -/
theorem awayMk_shift {f : A} {e : ι} (hf : f ∈ 𝒜 e) (n t : ℕ) (p : M)
    (hp : p ∈ 𝓜 (n • e)) (hfp : f ^ t • p ∈ 𝓜 ((n + t) • e)) :
    awayMk hf (n + t) (f ^ t • p) hfp = awayMk hf n p hp := by
  rw [awayMk, awayMk, mk_eq_mk_iff]
  exact ⟨1, by simp [← mul_smul, ← pow_add]⟩

/-- **Two fractions share a denominator.** Any two degree-zero fractions away from `f` have
`awayMk` representatives over one common power `fⁿ`.

This is `exists_awayMk` on each fraction followed by `awayMk_shift` to align the two exponents
at their sum. It is the move every statement about a *sum* of fractions opens with — additivity
of `awayMk` exists only at a fixed denominator — and it is what the additivity of the sign
projection (#340's contracting homotopy) reduces to. Like `exists_awayMk`, it costs no domain
or torsion-freeness hypothesis: no cancellation is performed. -/
theorem exists_awayMk_pair {f : A} {e : ι} (hf : f ∈ 𝒜 e) (hf0 : ∀ n : ℕ, f ^ n ≠ 0)
    (z₁ z₂ : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    ∃ (n : ℕ) (p₁ p₂ : M) (hp₁ : p₁ ∈ 𝓜 (n • e)) (hp₂ : p₂ ∈ 𝓜 (n • e)),
      z₁ = awayMk hf n p₁ hp₁ ∧ z₂ = awayMk hf n p₂ hp₂ := by
  obtain ⟨n₁, q₁, hq₁, rfl⟩ := exists_awayMk hf hf0 z₁
  obtain ⟨n₂, q₂, hq₂, rfl⟩ := exists_awayMk hf hf0 z₂
  have hp₁ : f ^ n₂ • q₁ ∈ 𝓜 ((n₁ + n₂) • e) := by
    have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n₂ hf) hq₁
    rwa [vadd_eq_add, show n₂ • e + n₁ • e = (n₁ + n₂) • e by rw [add_nsmul, add_comm]] at h
  have hp₂ : f ^ n₁ • q₂ ∈ 𝓜 ((n₁ + n₂) • e) := by
    have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n₁ hf) hq₂
    rwa [vadd_eq_add, show n₁ • e + n₂ • e = (n₁ + n₂) • e by rw [add_nsmul]] at h
  -- Transport an `awayMk` across `n₂ + n₁ = n₁ + n₂`; the exponent sits in the membership
  -- certificate, so `rw` cannot reach it and proof irrelevance has to do the move.
  have hcongr : ∀ (a b : ℕ) (q : M) (hqa : q ∈ 𝓜 (a • e)) (hqb : q ∈ 𝓜 (b • e)), a = b →
      awayMk hf a q hqa = awayMk hf b q hqb := by
    rintro a b q hqa hqb rfl; rfl
  refine ⟨n₁ + n₂, f ^ n₂ • q₁, f ^ n₁ • q₂, hp₁, hp₂,
    (awayMk_shift hf n₁ n₂ q₁ hq₁ hp₁).symm, ?_⟩
  have hp₂' : f ^ n₁ • q₂ ∈ 𝓜 ((n₂ + n₁) • e) := by
    rwa [show (n₂ + n₁) • e = (n₁ + n₂) • e by rw [Nat.add_comm]]
  exact ((awayMk_shift hf n₂ n₁ q₂ hq₂ hp₂').symm.trans
    (hcongr (n₂ + n₁) (n₁ + n₂) _ hp₂' hp₂ (Nat.add_comm n₂ n₁)))

/-- **A fraction vanishes exactly when its numerator does.**

This is `awayMk_eq_awayMk_iff` against the zero fraction, and it is what makes the numerator a
faithful record of the element: any independence statement about fractions reduces to one about
numerators. The hypotheses are inherited from that lemma and are needed for the same reason —
without torsion-freeness an `f`-torsion numerator is a nonzero numerator with a zero fraction. -/
theorem awayMk_eq_zero_iff [IsDomain A] [Module.IsTorsionFree A M] {f : A} {e : ι}
    (hf : f ∈ 𝒜 e) (hf0 : f ≠ 0) {n : ℕ} {p : M} (hp : p ∈ 𝓜 (n • e)) :
    awayMk hf n p hp = 0 ↔ p = 0 := by
  rw [← awayMk_zero (𝓜 := 𝓜) hf 0, awayMk_eq_awayMk_iff hf hf0]
  simp
/-- Two equal degree indices give the same `awayMk`.

`awayMk` records the degree of its denominator in the `NumDenSameDeg` certificate, so two
certificates that are propositionally equal still need transporting. Every caller that meets this
has the same shape: one side names the degree as `(γ' + single i₀ c).degree` and the other as
`c + γ'.degree`. -/
theorem awayMk_deg_congr {f : A} {e₁ e₂ : ι} (h : e₁ = e₂) (hf₁ : f ∈ 𝒜 e₁) (hf₂ : f ∈ 𝒜 e₂)
    (n : ℕ) (p : M) (hp₁ : p ∈ 𝓜 (n • e₁)) (hp₂ : p ∈ 𝓜 (n • e₂)) :
    awayMk hf₁ n p hp₁ = awayMk hf₂ n p hp₂ := by
  subst h; rfl

set_option maxHeartbeats 1200000 in
/-- **The face map in `awayMk` normal form.** Restricting `p / g₁ⁿ` along `g₁ * h = g₂` multiplies
the numerator by `hⁿ` and leaves the exponent alone.

This is `faceMap_mk` with the denominator already known to be a power, which is the shape every
caller has: the face of a Čech intersection is a restriction between two `awayMk`s, not between
two arbitrary `NumDenSameDeg`s. The target degree is written `e + e₁` rather than `e₁ + e` so that
`n • (e + e₁)` matches the `n • e + n • e₁` that `faceMap_mk` produces. -/
theorem faceMap_awayMk {g₁ g₂ h : A} {e e₁ : ι} (hh : h ∈ 𝒜 e) (hg₁ : g₁ ∈ 𝒜 e₁)
    (hgh : g₁ * h ∈ Submonoid.powers g₂) (hg : g₁ * h = g₂)
    (hg₂ : g₂ ∈ 𝒜 (e + e₁)) (n : ℕ) (p : M) (hp : p ∈ 𝓜 (n • e₁))
    (hres : h ^ n • p ∈ 𝓜 (n • (e + e₁))) :
    faceMap (𝓜 := 𝓜) hh hgh hg (awayMk hg₁ n p hp) = awayMk hg₂ n (h ^ n • p) hres := by
  rw [awayMk, faceMap_mk (𝓜 := 𝓜) hh hgh hg _ n rfl, awayMk]
  apply ext
  simp only [coe_mk, NumDenSameDeg.embedding]

end DegreeZeroLocalization

/-! ## Functoriality -/

/-- An `A`-linear map which preserves every graded piece. Mathlib has a bundled graded ring map,
but currently no corresponding bundled map for internally graded modules. -/
@[ext]
structure GradedLinearMap {N σN : Type*} [AddCommGroup N] [Module A N]
    [SetLike σN N] [AddSubgroupClass σN N] (𝓝 : ι → σN) where
  /-- The underlying linear map. -/
  toLinearMap : M →ₗ[A] N
  /-- The map preserves every homogeneous component. -/
  map_mem : ∀ i (m : M), m ∈ 𝓜 i → toLinearMap m ∈ 𝓝 i

namespace GradedLinearMap

variable {N σN : Type*} [AddCommGroup N] [Module A N]
variable [SetLike σN N] [AddSubgroupClass σN N]
variable (𝓝 : ι → σN) [SetLike.GradedSMul 𝒜 𝓝]

/-- The ordinary localized map underlying a grading-preserving linear map. -/
noncomputable def localized (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    LocalizedModule S M →ₗ[Localization S] LocalizedModule S N :=
  LocalizedModule.map S f.toLinearMap

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σM M] in
@[simp]
theorem localized_mk (f : GradedLinearMap (A := A) 𝓜 𝓝) (m : M) (s : S) :
    localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f (LocalizedModule.mk m s) =
      LocalizedModule.mk (f.toLinearMap m) s := by
  exact LocalizedModule.map_mk S f.toLinearMap m s

/-- A grading-preserving linear map sends degree-zero homogeneous localizations to degree-zero
homogeneous localizations. -/
noncomputable def map (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    DegreeZeroLocalization 𝒜 𝓜 S →ₗ[HomogeneousLocalization 𝒜 S]
      DegreeZeroLocalization 𝒜 𝓝 S where
  toFun z := by
    refine ⟨localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f z, ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨f.toLinearMap c.num, f.map_mem c.deg c.num c.num.2⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    rw [← hc]
    simp only [NumDenSameDeg.embedding]
    rw [localized_mk (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S)]
  map_add' x y := by
    apply DegreeZeroLocalization.ext
    exact (localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f).map_add x y
  map_smul' a x := by
    apply DegreeZeroLocalization.ext
    exact (localized (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f).map_smul (algebraMap _ _ a) x

@[simp]
theorem map_mk (f : GradedLinearMap (A := A) 𝓜 𝓝) (c : NumDenSameDeg 𝒜 𝓜 S) :
    map (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨f.toLinearMap c.num, f.map_mem c.deg c.num c.num.2⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply DegreeZeroLocalization.ext
  exact localized_mk (𝓜 := 𝓜) (𝓝 := 𝓝) (S := S) f c.num ⟨c.den, c.den_mem⟩

end GradedLinearMap

/-! ## The graded ring as a module

When the graded module is the graded ring itself, the construction above recovers Mathlib's
degree-zero homogeneous localization.  Keeping this comparison explicit is useful for identifying
the associated sheaf of the graded ring with the structure sheaf on `Proj`.
-/

namespace DegreeZeroLocalization

variable (𝒜 : ι → σA) [GradedRing 𝒜] (S : Submonoid A)

/-- Regard a homogeneous localization element as a degree-zero element of the localization of the
graded ring considered as a module over itself. -/
noncomputable def homogeneousLocalizationLinearMap :
    HomogeneousLocalization 𝒜 S →ₗ[HomogeneousLocalization 𝒜 S]
      DegreeZeroLocalization 𝒜 𝒜 S where
  toFun z := by
    refine ⟨z.val, ?_⟩
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    exact ⟨
      { deg := c.deg
        num := c.num
        den := c.den
        den_mem := c.den_mem }, rfl⟩
  map_add' x y := by
    apply ext
    exact HomogeneousLocalization.val_add x y
  map_smul' x y := by
    apply ext
    simp only [coe_smul]
    exact HomogeneousLocalization.val_mul x y

@[simp]
theorem coe_homogeneousLocalizationLinearMap (z : HomogeneousLocalization 𝒜 S) :
    ((homogeneousLocalizationLinearMap 𝒜 S z : DegreeZeroLocalization 𝒜 𝒜 S) :
      LocalizedModule S A) = z.val :=
  rfl

theorem homogeneousLocalizationLinearMap_injective :
    Function.Injective (homogeneousLocalizationLinearMap 𝒜 S) := by
  intro x y h
  apply HomogeneousLocalization.val_injective S
  exact congrArg Subtype.val h

theorem homogeneousLocalizationLinearMap_surjective :
    Function.Surjective (homogeneousLocalizationLinearMap 𝒜 S) := by
  rintro ⟨z, hz⟩
  obtain ⟨c, hc⟩ := hz
  let c' : HomogeneousLocalization.NumDenSameDeg 𝒜 S :=
    { deg := c.deg
      num := c.num
      den := c.den
      den_mem := c.den_mem }
  refine ⟨HomogeneousLocalization.mk c', ?_⟩
  apply ext
  exact hc

/-- The degree-zero localization of the graded ring as a module is canonically linearly
equivalent to Mathlib's homogeneous localization ring. -/
noncomputable def selfLinearEquiv :
    HomogeneousLocalization 𝒜 S ≃ₗ[HomogeneousLocalization 𝒜 S]
      DegreeZeroLocalization 𝒜 𝒜 S :=
  LinearEquiv.ofBijective (homogeneousLocalizationLinearMap 𝒜 S)
    ⟨homogeneousLocalizationLinearMap_injective 𝒜 S,
      homogeneousLocalizationLinearMap_surjective 𝒜 S⟩

@[simp]
theorem coe_selfLinearEquiv (z : HomogeneousLocalization 𝒜 S) :
    ((selfLinearEquiv 𝒜 S z : DegreeZeroLocalization 𝒜 𝒜 S) :
      LocalizedModule S A) = z.val :=
  rfl

@[simp]
theorem selfLinearEquiv_apply_mk
    (c : HomogeneousLocalization.NumDenSameDeg 𝒜 S) :
    selfLinearEquiv 𝒜 S (HomogeneousLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := c.num
          den := c.den
          den_mem := c.den_mem } := by
  apply ext
  rfl

@[simp]
theorem selfLinearEquiv_symm_apply_mk (c : NumDenSameDeg 𝒜 𝒜 S) :
    (selfLinearEquiv 𝒜 S).symm (DegreeZeroLocalization.mk c) =
      HomogeneousLocalization.mk
        { deg := c.deg
          num := c.num
          den := c.den
          den_mem := c.den_mem } := by
  apply (selfLinearEquiv 𝒜 S).injective
  simp only [LinearEquiv.apply_symm_apply, selfLinearEquiv_apply_mk]

end DegreeZeroLocalization

end GradedModule
