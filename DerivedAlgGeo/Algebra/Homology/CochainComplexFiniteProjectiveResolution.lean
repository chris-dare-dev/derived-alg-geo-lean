/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Projective
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.FullSubcategory

/-!
# Finite-term bounded-above projective replacements

Mathlib constructs strictly bounded-below injective replacements. Opposing a cochain
complex and negating its integer degrees gives a strictly bounded-above projective
replacement in `FGModuleCat R`, where finite-free epimorphisms supply enough projectives.
The `ModuleCat` version below transfers the resulting complex and quasi-isomorphism
through the finite-module inclusion. No finite lower bound or derived-arrow comparison
is asserted.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Reindexing an opposite-category cochain complex by negation preserves a
quasi-isomorphism. The short complexes in degree `n` and `-n` are definitionally
the same after choosing their adjacent indices explicitly. -/
private lemma quasiIso_restrictionNeg {C : Type*} [Category* C] [Abelian C]
    {J L : CochainComplex Cᵒᵖ ℤ} (i : J ⟶ L) (hi : QuasiIso i) :
    QuasiIso (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt) := by
  letI : QuasiIso i := hi
  rw [quasiIso_iff]
  intro n
  have hi' : QuasiIsoAt i (-n) := (quasiIso_iff i).mp inferInstance (-n)
  have hsc := (quasiIsoAt_iff' i (- (n + 1)) (-n) (- (n - 1))
    (by simp; omega) (by simp; omega)).mp hi'
  apply (quasiIsoAt_iff'
    (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt)
    (n + 1) n (n - 1) (by simp) (by simp)).mpr
  exact hsc

namespace FGModuleCat

/-- A strictly bounded-above complex of finite modules over a noetherian
commutative ring has a strictly bounded-above quasi-isomorphic complex of
projective finite modules. Its negative-degree tail may be infinite. -/
theorem exists_boundedAbove_projective_replacement {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : CochainComplex (FGModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex (FGModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p := by
  classical
  letI : EnoughProjectives (FGModuleCat.{u} R) := by
    constructor
    intro X
    obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi X
    exact ⟨{ p := FGModuleCat.of R (Fin k → R)
             projective := FGModuleCat.projective_of_finFree k
             f := q
             epi := hq }⟩
  let E := CochainComplex.opEquivalence (FGModuleCat.{u} R)
  let J := E.functor.obj (Opposite.op K)
  have hJ : J.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hzero : IsZero (K.X (-i)) := K.isZero_of_isStrictlyLE b (-i) (by omega)
    change IsZero (Opposite.op (K.X (-i)))
    exact hzero.op
  letI : J.IsStrictlyGE (-b) := hJ
  obtain ⟨L, i, hqi, hInj, hL⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective J (-b)
  let P : CochainComplex (FGModuleCat.{u} R) ℤ := Opposite.unop (E.inverse.obj L)
  let p : P ⟶ K := (E.inverse.map i).unop ≫
    (E.unitIso.app (Opposite.op K)).unop.hom
  have hBound : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    change IsZero (Opposite.unop (L.X (-n)))
    have hzero : IsZero (L.X (-n)) := by
      letI : L.IsStrictlyGE (-b) := hL
      exact L.isZero_of_isStrictlyGE (-b) (-n) (by omega)
    exact hzero.unop
  have hProj (n : ℤ) : Projective (P.X n) := by
    change Projective (Opposite.unop (L.X (-n)))
    letI : Injective (L.X (-n)) := hInj (-n)
    infer_instance
  have hRestrict : QuasiIso
      (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt) :=
    quasiIso_restrictionNeg i hqi
  have hUnop : QuasiIso (E.inverse.map i).unop := by
    change QuasiIso ((HomologicalComplex.unopFunctor (FGModuleCat.{u} R)
      (ComplexShape.down ℤ)).map
        (HomologicalComplex.restrictionMap i ComplexShape.embeddingDownIntUpInt).op)
    exact (HomologicalComplex.quasiIso_unopFunctor_map_iff _).mpr hRestrict
  letI : QuasiIso (E.inverse.map i).unop := hUnop
  refine ⟨P, p, hBound, hProj, ?_⟩
  dsimp [p]
  infer_instance

end FGModuleCat

namespace ModuleCat

/-- A strictly bounded-above complex of finite modules over a noetherian
commutative ring has a strictly bounded-above, termwise finite-projective
replacement in `ModuleCat`. The quasi-isomorphism is an actual complex map to
the supplied complex. No strict lower bound is claimed for the replacement. -/
theorem exists_finite_projective_replacement {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b]
    (hfinite : ∀ i : ℤ, Module.Finite R (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (p : P ⟶ K),
      P.IsStrictlyLE b ∧ (∀ i : ℤ, Module.Finite R (P.X i)) ∧
      (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso p := by
  classical
  let F := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  let Kfg : CochainComplex (FGModuleCat.{u} R) ℤ :=
    HomologicalComplex.liftObjectProperty (ModuleCat.isFG R) K
      (by intro i; change Module.Finite R (K.X i); exact hfinite i)
  have hKfg : Kfg.IsStrictlyLE b := by
    apply (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff Kfg F b).mp
    change K.IsStrictlyLE b
    infer_instance
  letI : Kfg.IsStrictlyLE b := hKfg
  obtain ⟨Pfg, pfg, hPbound, hPproj, hpfg⟩ :=
    FGModuleCat.exists_boundedAbove_projective_replacement Kfg b
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
  letI : F.Additive := by infer_instance
  letI : F.PreservesHomology := by infer_instance
  let P : CochainComplex (ModuleCat.{u} R) ℤ := (F.mapHomologicalComplex (.up ℤ)).obj Pfg
  let p : P ⟶ K := (F.mapHomologicalComplex (.up ℤ)).map pfg
  have hBound : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff Pfg F b).mpr hPbound
  have hFinite (i : ℤ) : Module.Finite R (P.X i) := by
    change Module.Finite R (Pfg.X i).obj
    exact (Pfg.X i).property
  have hProj (i : ℤ) : Projective (P.X i) := by
    change Projective (F.obj (Pfg.X i))
    exact hProjective (Pfg.X i) (hPproj i)
  have hQuasi : QuasiIso p := by
    letI : QuasiIso pfg := hpfg
    exact HomologicalComplex.quasiIso_map_of_preservesHomology pfg F
  exact ⟨P, p, hBound, hFinite, hProj, hQuasi⟩

end ModuleCat

end
