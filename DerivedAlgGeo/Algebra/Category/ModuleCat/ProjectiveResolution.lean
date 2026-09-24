/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Projective
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
# Finite-term projective resolutions of finite modules

Over a noetherian commutative ring, a finite module admits a projective resolution whose
terms remain finite. Construct the resolution in `FGModuleCat`, where Mathlib's
`ProjectiveResolution.of` applies after the finite-free epimorphisms give enough projectives.
The inclusion into `ModuleCat` preserves homology; its preservation of projectives follows
because a projective finite module is a retract of a finite free module.

The same witness, extended to integer-indexed cochain degrees, is strictly bounded above
by zero, termwise finite and projective, with a quasi-isomorphism to the degree-zero complex
of the input module. The strict bound, projectivity and quasi-isomorphism are supplied by
Mathlib's `ProjectiveResolution` API; the theorem below supplies finiteness in both indexings.
The negative-degree tail is not asserted to terminate. This is a resolution of one module,
not a finite-projective model of an arbitrary bounded complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

noncomputable section

/-- A finite module over a noetherian commutative ring has a projective resolution
with finite terms in both the natural-number chain indexing and its integer cochain
extension. The latter is strictly supported in degrees at most zero. -/
theorem exists_finite_projectiveResolution {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : ProjectiveResolution M,
      (∀ n : ℕ, Module.Finite R (P.complex.X n)) ∧
      (∀ i : ℤ, Module.Finite R (P.cochainComplex.X i)) := by
  classical
  letI : EnoughProjectives (FGModuleCat.{u} R) := by
    constructor
    intro X
    obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi X
    exact ⟨{ p := FGModuleCat.of R (Fin k → R)
             projective := FGModuleCat.projective_of_finFree k
             f := q
             epi := hq }⟩
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have hProjective (X : FGModuleCat.{u} R) (hX : Projective X) :
      Projective (F.obj X) := by
    letI : Projective X := hX
    obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi X
    letI : Epi q := hq
    let s := Projective.factorThru (𝟙 X) q
    have hs : s ≫ q = 𝟙 X := Projective.factorThru_comp (𝟙 X) q
    have hFree : Projective (F.obj (FGModuleCat.of R (Fin k → R))) := by
      change Projective (ModuleCat.of R (Fin k → R))
      exact ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    letI : Projective (F.obj (FGModuleCat.of R (Fin k → R))) := hFree
    exact ((Retract.mk s q hs).map F).projective
  letI : F.PreservesProjectiveObjects := ⟨fun {X} hX => hProjective X hX⟩
  letI : F.PreservesHomology := by infer_instance
  let Mfg : FGModuleCat.{u} R := ⟨M, by change Module.Finite R M; infer_instance⟩
  let Q : ProjectiveResolution Mfg := ProjectiveResolution.of Mfg
  let P : ProjectiveResolution M := F.mapProjectiveResolution Q
  have hfinite (n : ℕ) : Module.Finite R (P.complex.X n) := by
    change Module.Finite R (Q.complex.X n).obj
    exact (Q.complex.X n).property
  refine ⟨P, hfinite, ?_⟩
  intro i
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    exact (Module.Finite.equiv_iff (P.cochainComplexXIso (-k) k).toLinearEquiv).mpr
      (hfinite k)
  · have hzero : IsZero (P.cochainComplex.X i) :=
      P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)
    letI : Subsingleton (P.cochainComplex.X i) := ModuleCat.isZero_iff_subsingleton.mp hzero
    infer_instance

end

end ModuleCat
