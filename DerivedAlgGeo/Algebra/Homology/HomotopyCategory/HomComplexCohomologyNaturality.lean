/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyLinear

/-!
# Naturality of linear Hom-complex cohomology classes

Three degreewise `R`-linear maps commuting with the two adjacent Hom-complex
differentials induce maps on the concrete kernel/range quotient and on Mathlib's
`CohomologyClass`. The linear equivalence between those presentations commutes
with the induced maps. The source and target complexes may live in different
`R`-linear preadditive categories.

This is a generic cochain-complex statement; no localization or derived-Hom
comparison is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace CochainComplex.HomComplex

open scoped CochainComplex.HomComplex

universe u v w v' w'

noncomputable section

variable {R : Type u} [CommRing R]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
  (P Q : CochainComplex C ℤ) (n : ℤ)
  {C' : Type v'} [Category.{w'} C'] [Preadditive C'] [Linear R C']
  (P' Q' : CochainComplex C' ℤ)
  (fprev : Cochain P Q (n - 1) →ₗ[R] Cochain P' Q' (n - 1))
  (fcur : Cochain P Q n →ₗ[R] Cochain P' Q' n)
  (fnext : Cochain P Q (n + 1) →ₗ[R] Cochain P' Q' (n + 1))
  (hprev : (δ_hom R P' Q' (n - 1) n).comp fprev =
    fcur.comp (δ_hom R P Q (n - 1) n))
  (hcur : (δ_hom R P' Q' n (n + 1)).comp fcur =
    fnext.comp (δ_hom R P Q n (n + 1)))

private def cocycleMapLinear : Cocycle P Q n →ₗ[R] Cocycle P' Q' n where
  toFun z := Cocycle.mk (fcur z.1) (n + 1) rfl (by
    have h := LinearMap.congr_fun hcur z.1
    change δ n (n + 1) (fcur z.1) = fnext (δ n (n + 1) z.1) at h
    simpa only [Cocycle.δ_eq_zero, map_zero] using h)
  map_add' z w := by
    apply Subtype.ext
    exact map_add fcur z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul fcur r z.1

include fprev hprev in
private theorem cocycleMapLinear_mem_coboundaries (z : Cocycle P Q n)
    (hz : z ∈ coboundaries P Q n) :
    cocycleMapLinear P Q n P' Q' fcur fnext hcur z ∈ coboundaries P' Q' n := by
  obtain ⟨β, hβ⟩ := (mem_coboundaries_iff z (n - 1) (by omega)).mp hz
  apply (mem_coboundaries_iff _ (n - 1) (by omega)).mpr
  refine ⟨fprev β, ?_⟩
  change δ (n - 1) n (fprev β) = fcur z.1
  have h := LinearMap.congr_fun hprev β
  change δ (n - 1) n (fprev β) = fcur (δ (n - 1) n β) at h
  rw [hβ] at h
  exact h

/-- The map on Mathlib cohomology classes induced by degreewise linear maps
commuting with both adjacent Hom-complex differentials. -/
def cohomologyClassMapLinear :
    CohomologyClass P Q n →ₗ[R] CohomologyClass P' Q' n := by
  let g : Cocycle P Q n →+ CohomologyClass P' Q' n :=
    (CohomologyClass.mkAddMonoidHom P' Q' n).comp
      (cocycleMapLinear P Q n P' Q' fcur fnext hcur).toAddMonoidHom
  have hg : coboundaries P Q n ≤ g.ker := by
    intro z hz
    change CohomologyClass.mk (cocycleMapLinear P Q n P' Q' fcur fnext hcur z) = 0
    apply (CohomologyClass.mk_eq_zero_iff _).mpr
    exact cocycleMapLinear_mem_coboundaries P Q n P' Q'
      fprev fcur fnext hprev hcur z hz
  let e := CohomologyClass.descAddMonoidHom g hg
  refine { toFun := e, map_add' := e.map_add, map_smul' := ?_ }
  intro r x
  induction x using Quotient.inductionOn with
  | _ z =>
    change e (r • CohomologyClass.mk z) = r • e (CohomologyClass.mk z)
    rw [← cohomologyClass_mk_smul P Q n r z]
    change CohomologyClass.mk (cocycleMapLinear P Q n P' Q' fcur fnext hcur (r • z)) =
      r • CohomologyClass.mk (cocycleMapLinear P Q n P' Q' fcur fnext hcur z)
    rw [← cohomologyClass_mk_smul P' Q' n r
      (cocycleMapLinear P Q n P' Q' fcur fnext hcur z)]
    rw [map_smul]

/-- On a cocycle class, the induced map applies `fcur` to its representative. -/
@[simp] theorem cohomologyClassMapLinear_mk (z : Cocycle P Q n) :
    cohomologyClassMapLinear P Q n P' Q' fprev fcur fnext hprev hcur
      (CohomologyClass.mk z) =
    CohomologyClass.mk (Cocycle.mk (fcur z.1) (n + 1) rfl (by
      have h := LinearMap.congr_fun hcur z.1
      change δ n (n + 1) (fcur z.1) = fnext (δ n (n + 1) z.1) at h
      simpa only [Cocycle.δ_eq_zero, map_zero] using h)) := rfl

private def cyclesMapLinear :
    (δ_hom R P Q n (n + 1)).ker →ₗ[R] (δ_hom R P' Q' n (n + 1)).ker where
  toFun z := ⟨fcur z.1, by
    have h := LinearMap.congr_fun hcur z.1
    change δ n (n + 1) (fcur z.1) = fnext (δ n (n + 1) z.1) at h
    have hz : δ n (n + 1) z.1 = 0 := z.2
    rw [hz, map_zero] at h
    exact h⟩
  map_add' z w := Subtype.ext (map_add fcur z.1 w.1)
  map_smul' r z := Subtype.ext (map_smul fcur r z.1)

include fprev hprev in
private theorem cyclesMapLinear_mem_boundary (z :
    (boundaryToCyclesLinear (R := R) P Q n).range) :
    cyclesMapLinear P Q n P' Q' fcur fnext hcur z.1 ∈
      (boundaryToCyclesLinear (R := R) P' Q' n).range := by
  obtain ⟨β, hβ⟩ := z.2
  refine ⟨fprev β, ?_⟩
  apply Subtype.ext
  change δ (n - 1) n (fprev β) = fcur z.1
  have h := LinearMap.congr_fun hprev β
  change δ (n - 1) n (fprev β) = fcur (δ (n - 1) n β) at h
  have hβ' : δ (n - 1) n β = z.1 := congrArg Subtype.val hβ
  simpa only [hβ'] using h

/-- The induced linear map on the concrete kernel/range presentation of
Hom-complex cohomology. -/
def concreteCohomologyMap :
    ((δ_hom R P Q n (n + 1)).ker ⧸
      (boundaryToCyclesLinear (R := R) P Q n).range) →ₗ[R]
      ((δ_hom R P' Q' n (n + 1)).ker ⧸
        (boundaryToCyclesLinear (R := R) P' Q' n).range) :=
  Submodule.mapQ _ _ (cyclesMapLinear P Q n P' Q' fcur fnext hcur)
    (by
      intro z hz
      exact cyclesMapLinear_mem_boundary P Q n P' Q'
        fprev fcur fnext hprev hcur ⟨z, hz⟩)

/-- On a concrete quotient class, the induced map applies `fcur` to its cycle. -/
@[simp] theorem concreteCohomologyMap_mk (z : (δ_hom R P Q n (n + 1)).ker) :
    concreteCohomologyMap (R := R) P Q n P' Q' fprev fcur fnext hprev hcur
      (Submodule.Quotient.mk z) =
    Submodule.Quotient.mk
      (⟨fcur z.1, by
        have h := LinearMap.congr_fun hcur z.1
        change δ n (n + 1) (fcur z.1) = fnext (δ n (n + 1) z.1) at h
        have hz : δ n (n + 1) z.1 = 0 := z.2
        rw [hz, map_zero] at h
        exact h⟩ : (δ_hom R P' Q' n (n + 1)).ker) := rfl

/-- The linear class/quotient adapter is natural for degreewise maps commuting
with the Hom-complex differential. -/
theorem cohomologyClassLinearEquiv_naturality :
    (cohomologyClassMapLinear P Q n P' Q' fprev fcur fnext hprev hcur).comp
      (cohomologyClassLinearEquiv (R := R) P Q n).toLinearMap =
    (cohomologyClassLinearEquiv (R := R) P' Q' n).toLinearMap.comp
      (concreteCohomologyMap (R := R) P Q n P' Q'
        fprev fcur fnext hprev hcur) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    simp only [LinearMap.comp_apply, concreteCohomologyMap_mk]
    rfl

end

end CochainComplex.HomComplex
