/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Linear cohomology classes of the Hom complex

Mathlib defines `HomComplex.CohomologyClass` as an additive quotient. For an
`R`-linear category, the coboundaries are stable under `R`, so the concrete
kernel/range quotient supplies a compatible `R`-module structure and an
`R`-linear equivalence. The instance is scoped: callers opt in to this scalar
structure rather than changing Mathlib's additive interface globally.

This is an adapter for cohomology classes, not a derived-Hom base-change result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
  (P Q : CochainComplex C ℤ) (n : ℤ)

/-- Cycles expressed as the kernel of the Hom-complex differential agree
linearly with Mathlib's cocycle subtype. -/
def cyclesLinearEquiv :
    (δ_hom R P Q n (n + 1)).ker ≃ₗ[R] Cocycle P Q n where
  toFun z := ⟨z.1, by
    change δ n (n + 1) z.1 = 0
    exact z.2⟩
  invFun z := ⟨z.1, by
    change δ n (n + 1) z.1 = 0
    exact z.2⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def coboundariesSubmodule : Submodule R (Cocycle P Q n) where
  __ := coboundaries P Q n
  smul_mem' r z hz := by
    rcases hz with ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, r • β, by
      rw [δ_smul, hβ]
      rfl⟩

private theorem delta_comp_delta :
    (δ_hom R P Q n (n + 1)).comp (δ_hom R P Q (n - 1) n) = 0 := by
  apply LinearMap.ext
  intro γ
  change δ n (n + 1) (δ (n - 1) n γ) = 0
  exact δ_δ (n - 1) n (n + 1) γ

/-- The preceding Hom-complex differential, restricted to cycles. -/
def boundaryToCyclesLinear :
    Cochain P Q (n - 1) →ₗ[R] (δ_hom R P Q n (n + 1)).ker :=
  (δ_hom R P Q (n - 1) n).codRestrict _ (fun β => by
    have h := LinearMap.congr_fun (delta_comp_delta (R := R) P Q n) β
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.mem_ker] using h)

private theorem boundary_map_eq_coboundaries :
    (boundaryToCyclesLinear (R := R) P Q n).range.map
      (cyclesLinearEquiv (R := R) P Q n).toLinearMap =
      coboundariesSubmodule (R := R) P Q n := by
  ext z
  constructor
  · rintro ⟨y, ⟨β, hβ⟩, rfl⟩
    subst y
    change (cyclesLinearEquiv (R := R) P Q n)
      ((boundaryToCyclesLinear (R := R) P Q n) β) ∈ coboundaries P Q n
    exact ⟨n - 1, by omega, β, rfl⟩
  · intro hz
    obtain ⟨β, hβ⟩ :=
      (mem_coboundaries_iff z (n - 1) (by omega)).mp hz
    refine ⟨(boundaryToCyclesLinear (R := R) P Q n) β, ⟨β, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hβ

private theorem boundary_addSubgroup_map_eq :
    (boundaryToCyclesLinear (R := R) P Q n).range.toAddSubgroup.map
      (cyclesLinearEquiv (R := R) P Q n).toAddEquiv = coboundaries P Q n := by
  ext z
  have h := congrArg (fun T : Submodule R (Cocycle P Q n) => z ∈ T)
    (boundary_map_eq_coboundaries (R := R) P Q n)
  change z ∈ (boundaryToCyclesLinear (R := R) P Q n).range.map
      (cyclesLinearEquiv (R := R) P Q n).toLinearMap ↔
    z ∈ coboundariesSubmodule (R := R) P Q n
  exact Iff.of_eq h

private def quotientAddEquiv :
    ((δ_hom R P Q n (n + 1)).ker ⧸
      (boundaryToCyclesLinear (R := R) P Q n).range) ≃+
      CohomologyClass P Q n :=
  QuotientAddGroup.congr _ _ (cyclesLinearEquiv (R := R) P Q n).toAddEquiv
    (boundary_addSubgroup_map_eq (R := R) P Q n)

/-- The scalar action on Hom-complex cohomology classes, transported from
the concrete kernel/range quotient. This instance is deliberately scoped. -/
scoped instance cohomologyClassModule : Module R (CohomologyClass P Q n) :=
  (quotientAddEquiv (R := R) P Q n).symm.module R

/-- The concrete kernel/range quotient identifies linearly with Mathlib's
cohomology classes. -/
def cohomologyClassLinearEquiv :
    ((δ_hom R P Q n (n + 1)).ker ⧸
      (boundaryToCyclesLinear (R := R) P Q n).range) ≃ₗ[R]
      CohomologyClass P Q n :=
  ((quotientAddEquiv (R := R) P Q n).symm.linearEquiv R).symm

@[simp] theorem cohomologyClassLinearEquiv_mk
    (z : (δ_hom R P Q n (n + 1)).ker) :
    cohomologyClassLinearEquiv (R := R) P Q n (Submodule.Quotient.mk z) =
      CohomologyClass.mk ((cyclesLinearEquiv (R := R) P Q n) z) := rfl

@[simp] theorem cohomologyClass_mk_smul (r : R) (z : Cocycle P Q n) :
    CohomologyClass.mk (r • z) = r • CohomologyClass.mk z := by
  apply (quotientAddEquiv (R := R) P Q n).symm.injective
  change (quotientAddEquiv (R := R) P Q n).symm
      (CohomologyClass.mk (r • z)) =
    r • (quotientAddEquiv (R := R) P Q n).symm (CohomologyClass.mk z)
  rfl

end

end CochainComplex.HomComplex
