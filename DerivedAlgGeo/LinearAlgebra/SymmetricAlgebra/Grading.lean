/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Grading
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# The grading of the symmetric algebra

The symmetric algebra `Sym(M)` of a module `M` over a commutative semiring `R` is graded by
degree: its degree-`n` part `Symⁿ(M)` is the `n`-th power of the image of `M`.

## Main definitions

* `SymmetricAlgebra.gradedPiece R M n`: the degree-`n` part `Symⁿ(M)`, the `n`-th power of the
  range of `SymmetricAlgebra.ι R M`.
* `SymmetricAlgebra.map R' g`: for an `R`-algebra `R'`, an `R'`-module `M'` and an `R`-linear
  map `g : M →ₗ[R] M'`, the `R`-algebra map `Sym_R(M) → Sym_{R'}(M')` sending `ι x` to
  `ι (g x)`.

## Main results

* `SymmetricAlgebra.gradedAlgebra`: `Sym(M)` is a graded algebra over `gradedPiece R M`.
* `SymmetricAlgebra.gradedPiece_eq_map`: `Symⁿ(M)` is the image of the degree-`n` part of the
  tensor algebra.
* `SymmetricAlgebra.map_mem_gradedPiece`: `SymmetricAlgebra.map R' g` preserves degree.
* `SymmetricAlgebra.isLocalization_map`: the symmetric algebra commutes with localization. If
  `R'` is the localization of `R` at a submonoid `S` and `g : M →ₗ[R] M'` is the localization of
  `M` at `S`, then `Sym_{R'}(M')` is the localization of `Sym_R(M)` at the image of `S`;
  `SymmetricAlgebra.isLocalization_away_map` is the case `S = {rⁿ}`.

## Implementation notes

`SymmetricAlgebra R M` is Mathlib's quotient of the tensor algebra by `TensorAlgebra.symRingCon`.
The grading is not built from a second construction of `Symⁿ(M)` as a quotient of `⨂ⁿ M`: it is
the image of the tensor grading under the quotient map, written as the power of the range of
`SymmetricAlgebra.ι`, exactly as Mathlib grades `TensorAlgebra` and `ExteriorAlgebra`. The
decomposition is the lift of the degree-one inclusion into the internal direct sum, which is
commutative because `Sym(M)` is.

## References

* [Stacks, Tag 00DM: the symmetric algebra and its grading](https://stacks.math.columbia.edu/tag/00DM).
* [Stacks, Tag 01CF: the symmetric algebra of a sheaf of modules](https://stacks.math.columbia.edu/tag/01CF).

## Tags

symmetric algebra, grading, graded algebra, localization
-/

open scoped DirectSum

namespace SymmetricAlgebra

section Grading

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` part `Symⁿ(M)` of the symmetric algebra: the `n`-th power of the range of
`SymmetricAlgebra.ι R M`. -/
def gradedPiece (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (ι R M) ^ n

instance : SetLike.GradedMonoid (gradedPiece R M) :=
  Submodule.nat_power_gradedMonoid _

variable {R M} in
theorem ι_mem_gradedPiece_one (x : M) : ι R M x ∈ gradedPiece R M 1 := by
  simpa only [gradedPiece, pow_one] using LinearMap.mem_range_self _ x

theorem gradedPiece_zero : gradedPiece R M 0 = 1 :=
  pow_zero _

variable {R} in
theorem algebraMap_mem_gradedPiece_zero (r : R) :
    algebraMap R (SymmetricAlgebra R M) r ∈ gradedPiece R M 0 := by
  rw [gradedPiece_zero]
  exact Submodule.algebraMap_mem r

/-- `Symⁿ(M)` is the image of the degree-`n` part of the tensor algebra under the quotient map
`TensorAlgebra R M → SymmetricAlgebra R M`. -/
theorem gradedPiece_eq_map (n : ℕ) :
    gradedPiece R M n =
      (LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n).map
        (algHom R M).toLinearMap := by
  rw [Submodule.map_pow, gradedPiece, ι, LinearMap.range_comp]
  rfl

/-- `SymmetricAlgebra.ι` as a map into degree one of the internal direct sum. This is an
auxiliary construction for `SymmetricAlgebra.gradedAlgebra`. -/
nonrec def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, gradedPiece R M i :=
  DirectSum.lof R ℕ (fun i ↦ gradedPiece R M i) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ ι_mem_gradedPiece_one

theorem GradedAlgebra.ι_apply (x : M) :
    GradedAlgebra.ι R M x =
      DirectSum.of (fun i ↦ gradedPiece R M i) 1
        ⟨SymmetricAlgebra.ι R M x, ι_mem_gradedPiece_one x⟩ :=
  rfl

/-- The symmetric algebra is graded by degree. -/
instance gradedAlgebra : GradedAlgebra (gradedPiece R M) :=
  GradedAlgebra.ofAlgHom _ (lift (GradedAlgebra.ι R M))
    (by
      ext x
      simp [GradedAlgebra.ι_apply])
    fun i x ↦ by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end Grading

section RingHomExt

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Semiring A]

/-- Two ring maps out of the symmetric algebra agree once they agree on the scalars and on the
generators `ι x`. -/
theorem ringHom_ext {F G : SymmetricAlgebra R M →+* A}
    (halg : F.comp (algebraMap R _) = G.comp (algebraMap R _))
    (hι : ∀ x, F (ι R M x) = G (ι R M x)) : F = G := by
  refine RingHom.ext fun a ↦ ?_
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact congr($halg r)
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end RingHomExt

section Map

variable {R : Type*} (R' : Type*) {M M' : Type*} [CommSemiring R] [CommSemiring R']
  [Algebra R R'] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] [Module R' M']
  [IsScalarTower R R' M']

/-- The `R`-algebra map `Sym_R(M) → Sym_{R'}(M')` induced by an `R`-linear map `g : M →ₗ[R] M'`
into an `R'`-module, sending `ι x` to `ι (g x)`. -/
def map (g : M →ₗ[R] M') : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R' M' :=
  lift ((ι R' M').restrictScalars R ∘ₗ g)

variable {R'} (g : M →ₗ[R] M')

@[simp]
theorem map_ι (x : M) : map R' g (ι R M x) = ι R' M' (g x) :=
  lift_ι_apply _ x

theorem map_algebraMap (r : R) :
    map R' g (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (SymmetricAlgebra R' M')]

/-- `SymmetricAlgebra.map R' g` preserves degree. -/
theorem map_mem_gradedPiece {n : ℕ} {x : SymmetricAlgebra R M} (hx : x ∈ gradedPiece R M n) :
    map R' g x ∈ gradedPiece R' M' n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (SymmetricAlgebra R' M')]
    exact algebraMap_mem_gradedPiece_zero M' _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x _ ih =>
    obtain ⟨y, rfl⟩ := hm
    rw [map_mul, map_ι]
    have := SetLike.GradedMul.mul_mem (ι_mem_gradedPiece_one (g y)) ih
    rwa [add_comm] at this

end Map

section Localization

variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (S : Submonoid R) (g : M →ₗ[R] M')

/-- **The symmetric algebra commutes with localization** (Stacks 00DM, 01CF). If `R'` is the
localization of `R` at `S` and `g : M →ₗ[R] M'` is the localization of `M` at `S`, then
`Sym_{R'}(M')` is the localization of `Sym_R(M)` at the image of `S`, through
`SymmetricAlgebra.map R' g`. -/
theorem isLocalization_map [IsLocalization S R'] [IsLocalizedModule S g] :
    letI := (map R' g).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (SymmetricAlgebra R M) S)
      (SymmetricAlgebra R' M') := by
  let _ : Algebra (SymmetricAlgebra R M) (SymmetricAlgebra R' M') :=
    (map R' g).toRingHom.toAlgebra
  let A := SymmetricAlgebra R M
  let T := SymmetricAlgebra R' M'
  let S' := Algebra.algebraMapSubmonoid A S
  let L := Localization S'
  have hAT (a : A) : algebraMap A T a = map R' g a := rfl
  have hRT (r : R) : algebraMap R T r = algebraMap R' T (algebraMap R R' r) :=
    IsScalarTower.algebraMap_apply R R' T r
  -- The elements of `S` act invertibly on `L` and on `T`.
  have hunitL (s : S) : IsUnit (algebraMap R L s) := by
    rw [IsScalarTower.algebraMap_apply R A L]
    exact IsLocalization.map_units L (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ : S')
  have hunitT (s : S') : IsUnit (algebraMap A T s) := by
    obtain ⟨_, ⟨s, hs, rfl⟩⟩ := s
    rw [hAT, map_algebraMap]
    exact (IsLocalization.map_units R' ⟨s, hs⟩).map _
  -- `R'` acts on `L`.
  let _ : Algebra R' L := (IsLocalization.lift (M := S) (S := R') hunitL).toAlgebra
  have : IsScalarTower R R' L := .of_algebraMap_eq fun r ↦
    (IsLocalization.lift_eq (M := S) (S := R') hunitL r).symm
  -- The map `M' → L` given by the universal property of `g`.
  let f : M →ₗ[R] L := (IsScalarTower.toAlgHom R A L).toLinearMap ∘ₗ ι R M
  have hunitEnd (s : S) : IsUnit (algebraMap R (Module.End R L) s) := by
    rw [← (Algebra.lmul R L).commutes]
    exact (hunitL s).map _
  let ψ : M' →ₗ[R'] L :=
    (IsLocalizedModule.lift S g f hunitEnd).extendScalarsOfIsLocalization S R'
  have hψ (x : M) : ψ (g x) = algebraMap A L (ι R M x) :=
    IsLocalizedModule.lift_apply S g f hunitEnd x
  let φ₂ : T →ₐ[R'] L := lift ψ
  let φ₁ : L →+* T := IsLocalization.lift (M := S') (g := algebraMap A T) hunitT
  have hφ₁ (a : A) : φ₁ (algebraMap A L a) = algebraMap A T a := IsLocalization.lift_eq hunitT a
  -- `φ₂ ∘ φ₁` is the identity of `L`.
  have h₂₁ : (φ₂ : T →+* L).comp φ₁ = RingHom.id L := by
    refine IsLocalization.ringHom_ext S' ?_
    rw [RingHom.id_comp, RingHom.comp_assoc, IsLocalization.lift_comp]
    refine ringHom_ext (RingHom.ext fun r ↦ ?_) fun x ↦ ?_
    · change φ₂ (algebraMap A T (algebraMap R A r)) = algebraMap A L (algebraMap R A r)
      rw [hAT, map_algebraMap, φ₂.commutes, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    · change φ₂ (map R' g (ι R M x)) = _
      rw [map_ι, lift_ι_apply, hψ]
  -- `φ₁ ∘ φ₂` is the identity of `T`.
  let F : T →+* T := φ₁.comp φ₂
  have hFalg : F.comp (algebraMap R' T) = algebraMap R' T := by
    refine IsLocalization.ringHom_ext S (RingHom.ext fun r ↦ ?_)
    change φ₁ (φ₂ (algebraMap R' T (algebraMap R R' r))) = algebraMap R' T (algebraMap R R' r)
    rw [φ₂.commutes, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L, hφ₁,
      hAT, map_algebraMap]
  have hFR (r : R) : F (algebraMap R T r) = algebraMap R T r := by
    rw [hRT]; exact congr($hFalg (algebraMap R R' r))
  have h₁₂ : F = RingHom.id T := by
    refine ringHom_ext (by rw [hFalg, RingHom.id_comp]) fun x ↦ ?_
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S g x
    have hgm : F (ι R' M' (g m)) = ι R' M' (g m) := by
      change φ₁ (φ₂ (ι R' M' (g m))) = _
      rw [lift_ι_apply, hψ, hφ₁, hAT, map_ι]
    have hsx : ι R' M' (g m) = algebraMap R T s * ι R' M' x := by
      rw [← hs, ← Algebra.smul_def, LinearMap.map_smul_of_tower]
      rfl
    rw [hsx, map_mul, hFR, hRT] at hgm
    exact ((IsLocalization.map_units R' s).map (algebraMap R' T)).mul_left_cancel hgm
  let e : L ≃ₐ[A] T :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom φ₁ (φ₂ : T →+* L) h₁₂ h₂₁) hφ₁
  exact IsLocalization.isLocalization_of_algEquiv S' e

/-- `SymmetricAlgebra.isLocalization_map` for the localization away from one element: if
`R' = R[1/r]` and `M' = M[1/r]`, then `Sym_{R'}(M') = Sym_R(M)[1/r]`. -/
theorem isLocalization_away_map (r : R) [IsLocalization.Away r R']
    [IsLocalizedModule (Submonoid.powers r) g] :
    letI := (map R' g).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (SymmetricAlgebra R M) r) (SymmetricAlgebra R' M') := by
  let _ : Algebra (SymmetricAlgebra R M) (SymmetricAlgebra R' M') :=
    (map R' g).toRingHom.toAlgebra
  have := isLocalization_map (R' := R') (Submonoid.powers r) g
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at this

end Localization

end SymmetricAlgebra
