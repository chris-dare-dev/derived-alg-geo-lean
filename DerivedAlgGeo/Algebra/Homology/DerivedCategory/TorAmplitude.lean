/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ModuleCatTensor

/-!
# Tor amplitude of bounded-above complexes of modules

For a commutative ring `R`, an object `K` of `D(R)` has Tor amplitude in `[a, b]` if it is
bounded above and `Hⁱ(K ⊗^L_R M) = 0` for every `R`-module `M` and every `i ∉ [a, b]`
(Stacks 0652). It has finite Tor dimension if it has Tor amplitude in some `[a, b]`.

## Main definitions

* `ModuleCat.torAmplitude`: Stacks 0652 (1), on bounded-above objects.
* `ModuleCat.finiteTorDimension`: Stacks 0652 (2).

## Main results

* `ModuleCat.isZero_homology_of_torAmplitude`: Tor amplitude in `[a, b]` forces the
  cohomology to vanish outside `[a, b]`.
* `ModuleCat.flat_cokernel_of_torAmplitude`: Stacks 0653. For a strictly bounded-above
  complex `K` of flat modules with Tor amplitude in `[a, b]`, `Coker(d^{a-1})` is flat.
* `ModuleCat.torAmplitude_iff_exists_flat`: Stacks 0654. Tor amplitude in `[a, b]` holds iff
  `K` is quasi-isomorphic to a complex of flat modules vanishing outside `[a, b]`.
* `ModuleCat.torAmplitude_obj₃`, `ModuleCat.torAmplitude_obj₂`, `ModuleCat.torAmplitude_obj₁`:
  Stacks 0655 (1), (2) and (3), Tor amplitude in a distinguished triangle.

## Implementation notes

* **`D⁻` instead of `D`.** `ModuleCat.derivedTensorRight` is defined on the bounded-above
  derived category, so `torAmplitude` carries a `D⁻` witness. This agrees with Stacks'
  definition on all of `D(R)`, because Tor amplitude in `[a, b]` forces
  `Hⁱ(K) = Hⁱ(K ⊗^L R) = 0` outside `[a, b]`; stating that agreement would need the
  unbounded derived tensor product, which is not constructed here.
* **Flat terms in 0653.** The flatness hypothesis on the terms is needed: the complex
  `ℤ/2 → ℤ/4`, `1 ↦ 2`, in degrees `0, 1`, is quasi-isomorphic to `(ℤ/2)[-1]`, which has Tor
  amplitude in `[0, 1]`, but its cokernel in degree `0` is `ℤ/2`, not flat over `ℤ`.
* **Proof of 0653.** Stacks reads `Tor₁(Coker(d^{a-1}), M)` off a flat resolution. Here the
  flatness criterion of `Module.Flat.iff_lTensor_preserves_injective_linearMap` is checked
  directly by a diagram chase on `K^{a-2} ⊗ - → K^{a-1} ⊗ - → K^a ⊗ -`, which only uses that
  `K^a` is flat and that `K ⊗ N` is exact in degree `a - 1` for every `N`.
* **Proof of 0655.** Stacks derives it from `- ⊗^L M` preserving distinguished triangles. Here
  a distinguished triangle of bounded-above objects is realized as the mapping-cone triangle of
  a map of strictly bounded-above complexes of projectives, and tensoring that map with `M`
  gives a distinguished triangle on the vertices of `- ⊗^L M`. No triangulated structure on
  `ModuleCat.derivedTensorRight` is asserted.

## References

* [Stacks: Tag 0651](https://stacks.math.columbia.edu/tag/0651)
* [Stacks: Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks: Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks: Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks: Tag 0655](https://stacks.math.columbia.edu/tag/0655)
-/

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Stacks 0652 (1), on bounded-above objects: `K` has Tor amplitude in `[a, b]` if it is
bounded above and `Hⁱ(K ⊗^L_R M) = 0` for every `R`-module `M` and every `i ∉ [a, b]`. -/
def torAmplitude (R : Type u) [CommRing R] (a b : ℤ) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ ∃ hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K,
    ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((derivedTensorRight M).obj ⟨K, hK⟩))

/-- Stacks 0652 (2): `K` has finite Tor dimension if it has Tor amplitude in some
`[a, b]`. -/
def finiteTorDimension (R : Type u) [CommRing R] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ ∃ a b : ℤ, torAmplitude R a b K

instance (a b : ℤ) : (torAmplitude R a b).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨hK, h⟩
    exact ⟨DerivedCategory.TStructure.t.minus.prop_of_iso e hK, fun M i hi ↦
      (h M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        ((derivedTensorRight M).mapIso (ObjectProperty.isoMk _ e.symm)))⟩

instance : (finiteTorDimension R).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨a, b, h⟩ ↦ ⟨a, b, (torAmplitude R a b).prop_of_iso e h⟩

/-- Tor amplitude in `[a, b]` implies Tor amplitude in any larger interval. -/
theorem torAmplitude_mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {K : DerivedCategory (ModuleCat.{u} R)} (h : torAmplitude R a b K) :
    torAmplitude R a' b' K :=
  ⟨h.1, fun M i hi ↦ h.2 M i (by omega)⟩

/-- The cohomology of a localized complex vanishes in degree `i` iff the complex is exact
there. -/
private lemma isZero_homology_Q_obj_iff (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj K)) ↔
      K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((DerivedCategory.homologyFunctorFactors _ i).app K).isZero_iff

/-- A projective module is flat. -/
private lemma flat_of_projective (X : ModuleCat.{u} R) [Projective X] : Module.Flat R X := by
  have : Module.Projective R X := (IsProjective.iff_projective X).mpr ‹_›
  infer_instance

/-- A bounded-above object of `D(R)` is the localization of a strictly bounded-above complex
of projective modules. -/
private lemma exists_projective_model {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : DerivedCategory.TStructure.t.minus K) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (_ : P.IsStrictlyLE n)
      (_ : ∀ i, Projective (P.X i)), Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨n, hn⟩ := hK
  letI : K.IsLE n := hn
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE n
  obtain ⟨P, p, hP, hProj, hp⟩ :=
    CochainComplex.exists_boundedAbove_projective_replacement L n
  exact ⟨P, n, hP, hProj, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e.symm⟩⟩

/-- On a strictly bounded-above complex of flat modules, Tor amplitude is read off the
degreewise tensor products. -/
theorem torAmplitude_Q_obj_iff_of_flat (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [P.IsStrictlyLE n] (hP : ∀ i, Module.Flat R (P.X i)) (a b : ℤ) :
    torAmplitude R a b (DerivedCategory.Q.obj P) ↔
      ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
        (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt i := by
  constructor
  · rintro ⟨hK, h⟩ M i hi
    obtain ⟨e⟩ := nonempty_derivedTensorRight_obj_iso_of_flat M P n hP
    exact (isZero_homology_Q_obj_iff _ i).mp
      ((h M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm))
  · intro h
    refine ⟨⟨n, inferInstance⟩, fun M i hi ↦ ?_⟩
    obtain ⟨e⟩ := nonempty_derivedTensorRight_obj_iso_of_flat M P n hP
    exact ((isZero_homology_Q_obj_iff _ i).mpr (h M i hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)

/-- Tensoring a cochain complex of modules with the unit is the identity. -/
private def tensorUnitIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tensorRight (𝟙_ (ModuleCat.{u} R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      P :=
  (NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{u} R)) _).app P ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app P

/-- A strictly bounded-above complex of flat modules with Tor amplitude in `[a, b]` is exact
outside `[a, b]`. -/
private lemma exactAt_of_torAmplitude (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [P.IsStrictlyLE n] (hP : ∀ i, Module.Flat R (P.X i)) {a b : ℤ}
    (h : torAmplitude R a b (DerivedCategory.Q.obj P)) (i : ℤ) (hi : i < a ∨ b < i) :
    P.ExactAt i :=
  ((torAmplitude_Q_obj_iff_of_flat P n hP a b).mp h (𝟙_ _) i hi).of_iso (tensorUnitIso P)

/-- Tor amplitude in `[a, b]` forces the cohomology to vanish outside `[a, b]`: take
`M = R`. -/
theorem isZero_homology_of_torAmplitude {a b : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (h : torAmplitude R a b K) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  obtain ⟨P, n, _, hProj, ⟨e⟩⟩ := exists_projective_model h.1
  have hflat (j : ℤ) : Module.Flat R (P.X j) := by
    have := hProj j
    exact flat_of_projective _
  exact ((isZero_homology_Q_obj_iff P i).mpr (exactAt_of_torAmplitude P n hflat
    ((torAmplitude R a b).prop_of_iso e.symm h) i hi)).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e.symm)

/-- `id ⊗ f` and `φ ⊗ id` commute. -/
private lemma lTensor_rTensor_comm {A B N N' : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (φ : A →ₗ[R] B) (f : N →ₗ[R] N') (y : TensorProduct R A N) :
    f.lTensor B (φ.rTensor N y) = φ.rTensor N' (f.lTensor A y) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-- The degreewise tensor product of a cochain complex of modules with `N`, in degrees
`i → j → k`, as exactness of linear maps. -/
private lemma function_exact_rTensor_of_exactAt (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : Type u) [AddCommGroup N] [Module R N] (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k)
    (h : (((tensorRight (ModuleCat.of R N)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).ExactAt j) :
    Function.Exact ((P.d i j).hom.rTensor N) ((P.d j k).hom.rTensor N) := by
  have := (exactAt_iff_function_exact _ i j k hij hjk).mp h
  change Function.Exact (P.d i j ▷ ModuleCat.of R N).hom (P.d j k ▷ ModuleCat.of R N).hom at this
  rwa [ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerRight] at this

/-- The flatness criterion behind Stacks 0653 (Algebra 00M5): if `P^a` is flat and every
degreewise tensor product `P ⊗ N` is exact in degree `a - 1`, then `Coker(d^{a-1})` is flat. -/
theorem flat_cokernel_of_exactAt_tensorRight (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hPa : Module.Flat R (P.X a))
    (h : ∀ N : ModuleCat.{u} R,
      (((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt (a - 1)) :
    Module.Flat R (cokernel (P.d (a - 1) a) : ModuleCat.{u} R) := by
  let π := (cokernel.π (P.d (a - 1) a)).hom
  have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hex : Function.Exact (P.d (a - 1) a).hom π :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (ShortComplex.exact_cokernel (P.d (a - 1) a))
  refine Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
    fun N N' _ _ _ _ f hf ↦ ?_
  let g := (LinearMap.range f).mkQ
  have hg : Function.Surjective g := Submodule.mkQ_surjective _
  have hfg : Function.Exact f g := LinearMap.exact_map_mkQ_range f
  have hN := function_exact_rTensor_of_exactAt P (N' ⧸ LinearMap.range f) (a - 1 - 1) (a - 1) a
    (by omega) (by omega) (h (ModuleCat.of R (N' ⧸ LinearMap.range f)))
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective N hπ x
  rw [lTensor_rTensor_comm] at hx
  obtain ⟨z, hz⟩ := (rTensor_exact N' hex hπ (f.lTensor _ y)).mp hx
  have h₂ : (P.d (a - 1) a).hom.rTensor _ (g.lTensor _ z) = 0 := by
    rw [← lTensor_rTensor_comm, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      hfg.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w'', hw''⟩ := (hN (g.lTensor _ z)).mp h₂
  obtain ⟨w', rfl⟩ := LinearMap.lTensor_surjective _ hg w''
  have h₃ : g.lTensor _ (z - (P.d (a - 1 - 1) (a - 1)).hom.rTensor N' w') = 0 := by
    rw [map_sub, lTensor_rTensor_comm, hw'', sub_self]
  obtain ⟨v, hv⟩ := (lTensor_exact (P.X (a - 1)) hfg hg _).mp h₃
  have hdd : (P.d (a - 1) a).hom ∘ₗ (P.d (a - 1 - 1) (a - 1)).hom = 0 := by
    ext x
    exact d_comp_d_apply P _ _ _ x
  have h₄ : f.lTensor _ (y - (P.d (a - 1) a).hom.rTensor N v) = 0 := by
    rw [map_sub, lTensor_rTensor_comm, hv, map_sub, hz, sub_sub_cancel, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, hdd, LinearMap.rTensor_zero, LinearMap.zero_apply]
  have hy := Module.Flat.lTensor_preserves_injective_linearMap f hf
    (h₄.trans (map_zero _).symm)
  rw [sub_eq_zero] at hy
  rw [hy, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hex.linearMap_comp_eq_zero,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- Stacks 0653: for a strictly bounded-above complex `P` of flat modules with Tor amplitude in
`[a, b']`, the cokernel of `d^{a-1}` is flat. Only the lower bound `a` matters. -/
theorem flat_cokernel_of_torAmplitude (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (hP : ∀ i, Module.Flat R (P.X i)) {a b' : ℤ}
    (h : torAmplitude R a b' (DerivedCategory.Q.obj P)) :
    Module.Flat R (cokernel (P.d (a - 1) a) : ModuleCat.{u} R) :=
  flat_cokernel_of_exactAt_tensorRight P a (hP a) fun N ↦
    (torAmplitude_Q_obj_iff_of_flat P b hP a b').mp h N (a - 1) (Or.inl (by omega))

/-- Stacks 0654: `K` has Tor amplitude in `[a, b]` iff it is quasi-isomorphic to a complex of
flat modules vanishing outside `[a, b]`. The flat model is `τ_{≥ a} τ_{≤ b}` of a
bounded-above projective replacement: its top term is a kernel, flat because the complex is
exact above `b`, and its bottom term is the cokernel of 0653. -/
theorem torAmplitude_iff_exists_flat (a b : ℤ) (K : DerivedCategory (ModuleCat.{u} R)) :
    torAmplitude R a b K ↔ ∃ E : CochainComplex (ModuleCat.{u} R) ℤ,
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ (∀ i, Module.Flat R (E.X i)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  constructor
  · intro h
    obtain ⟨P, n, _, hProj, ⟨e⟩⟩ := exists_projective_model h.1
    have hflat (j : ℤ) : Module.Flat R (P.X j) := by
      have := hProj j
      exact flat_of_projective _
    have hP : torAmplitude R a b (DerivedCategory.Q.obj P) :=
      (torAmplitude R a b).prop_of_iso e.symm h
    have hPex := exactAt_of_torAmplitude P n hflat hP
    have : P.IsLE b := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      exact hPex i (Or.inr hi)
    let P' := P.truncLE b
    have hP'flat (i : ℤ) : Module.Flat R (P'.X i) := by
      rcases lt_trichotomy i b with hi | rfl | hi
      · have := hflat i
        exact Module.Flat.of_linearEquiv (P.truncLEXIso b i hi).toLinearEquiv
      · have := flat_ker_d_of_exactAt P n i (fun j _ ↦ hflat j) fun j hj ↦ hPex j (Or.inr hj)
        exact (Module.Flat.equiv_iff ((P.truncLEXIsoCycles i) ≪≫
          P.cyclesIsoSc' (i - 1) i (i + 1) (by simp) (by simp) ≪≫
          (P.sc' (i - 1) i (i + 1)).cyclesIsoKernel ≪≫
            ModuleCat.kernelIsoKer _).toLinearEquiv.symm).mp this
      · have : Subsingleton (P'.X i) :=
          ModuleCat.isZero_iff_subsingleton.mp (P'.isZero_of_isStrictlyLE b i hi)
        infer_instance
    let eP' : DerivedCategory.Q.obj P' ≅ DerivedCategory.Q.obj P :=
      asIso (DerivedCategory.Q.map (P.ιTruncLE b))
    have hP' : torAmplitude R a b (DerivedCategory.Q.obj P') :=
      (torAmplitude R a b).prop_of_iso eP'.symm hP
    have hcoker := flat_cokernel_of_torAmplitude P' b hP'flat hP'
    have hP'ex := exactAt_of_torAmplitude P' b hP'flat hP'
    have : P'.IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro i hi
      exact hP'ex i (Or.inl hi)
    refine ⟨P'.truncGE a, inferInstance, inferInstance, fun i ↦ ?_,
      ⟨(asIso (DerivedCategory.Q.map (P'.πTruncGE a))).symm ≪≫ eP' ≪≫ e⟩⟩
    rcases lt_trichotomy i a with hi | rfl | hi
    · have : Subsingleton ((P'.truncGE a).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp ((P'.truncGE a).isZero_of_isStrictlyGE a i hi)
      infer_instance
    · exact (Module.Flat.equiv_iff ((P'.truncGEXIsoOpcycles i) ≪≫
        P'.opcyclesIsoSc' (i - 1) i (i + 1) (by simp) (by simp) ≪≫
        (P'.sc' (i - 1) i (i + 1)).opcyclesIsoCokernel).toLinearEquiv.symm).mp hcoker
    · have := hP'flat i
      exact Module.Flat.of_linearEquiv (P'.truncGEXIso a i hi).toLinearEquiv
  · rintro ⟨E, _, _, hE, ⟨e⟩⟩
    refine (torAmplitude R a b).prop_of_iso e
      ((torAmplitude_Q_obj_iff_of_flat E b hE a b).mpr fun M i hi ↦ ?_)
    rcases hi with hi | hi
    · exact CochainComplex.exactAt_of_isGE _ a i hi
    · exact CochainComplex.exactAt_of_isLE _ b i hi

/-- A distinguished triangle of bounded-above objects is carried by `- ⊗^L M` to the vertices of
a distinguished triangle. It is realized as the mapping-cone triangle of a map between strictly
bounded-above complexes of projectives, and that map is tensored with `M`. -/
private lemma exists_distTriang_derivedTensorRight (M : ModuleCat.{u} R)
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : DerivedCategory.TStructure.t.minus T.obj₁)
    (h₂ : DerivedCategory.TStructure.t.minus T.obj₂)
    (h₃ : DerivedCategory.TStructure.t.minus T.obj₃) :
    ∃ T' ∈ distTriang (DerivedCategory (ModuleCat.{u} R)),
      Nonempty (T'.obj₁ ≅ (derivedTensorRight M).obj ⟨T.obj₁, h₁⟩) ∧
      Nonempty (T'.obj₂ ≅ (derivedTensorRight M).obj ⟨T.obj₂, h₂⟩) ∧
      Nonempty (T'.obj₃ ≅ (derivedTensorRight M).obj ⟨T.obj₃, h₃⟩) := by
  obtain ⟨P₁, n₁, _, hP₁, ⟨e₁⟩⟩ := exists_projective_model h₁
  obtain ⟨P₂, n₂, _, hP₂, ⟨e₂⟩⟩ := exists_projective_model h₂
  have : P₁.IsStrictlyLE (max n₁ n₂) := P₁.isStrictlyLE_of_le n₁ _ (le_max_left _ _)
  have : P₂.IsStrictlyLE (max n₁ n₂) := P₂.isStrictlyLE_of_le n₂ _ (le_max_right _ _)
  have : P₁.IsKProjective := CochainComplex.isKProjective_of_projective P₁ (max n₁ n₂)
  let qQ := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P₁
    ((HomotopyCategory.quotient _ _).obj P₂)).2
      ((qQ.app P₁).hom ≫ e₁.hom ≫ T.mor₁ ≫ e₂.inv ≫ (qQ.app P₂).inv)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
  have hφ : DerivedCategory.Q.map φ = e₁.hom ≫ T.mor₁ ≫ e₂.inv := by
    have hnat := qQ.hom.naturality φ
    dsimp at hnat
    rw [← cancel_epi (qQ.hom.app P₁), ← hnat, hψ]
    simp
  obtain ⟨E, -, -⟩ := exists_iso_of_arrow_iso _ _ hT
    (DerivedCategory.mappingCone_triangle_distinguished φ)
    (Arrow.isoMk e₁.symm e₂.symm (by
      change e₁.inv ≫ DerivedCategory.Q.map φ = T.mor₁ ≫ e₂.inv
      rw [hφ, Iso.inv_hom_id_assoc]))
  have : (CochainComplex.mappingCone φ).IsStrictlyLE (max n₁ n₂) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff φ i).mpr
      ⟨P₁.isZero_of_isStrictlyLE (max n₁ n₂) (i + 1) (by omega),
        P₂.isZero_of_isStrictlyLE (max n₁ n₂) i hi⟩
  have (i : ℤ) : Projective ((CochainComplex.mappingCone φ).X i) := by
    have := hP₁ (i + 1)
    have := hP₂ i
    exact Projective.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm inferInstance
  have := hP₁
  have := hP₂
  refine ⟨DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)),
    DerivedCategory.mappingCone_triangle_distinguished _, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact (derivedTensorRightObjIso M P₁ (max n₁ n₂)).symm ≪≫
      (derivedTensorRight M).mapIso (ObjectProperty.isoMk _ e₁)
  · exact (derivedTensorRightObjIso M P₂ (max n₁ n₂)).symm ≪≫
      (derivedTensorRight M).mapIso (ObjectProperty.isoMk _ e₂)
  · exact DerivedCategory.Q.mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso φ (tensorRight M)).symm ≪≫
      (derivedTensorRightObjIso M (CochainComplex.mappingCone φ) (max n₁ n₂)).symm ≪≫
      (derivedTensorRight M).mapIso (ObjectProperty.isoMk _ (Triangle.π₃.mapIso E).symm)

/-- Stacks 0655 (1): in a distinguished triangle `K → L → M → K[1]`, if `K` has Tor amplitude
in `[a + 1, b + 1]` and `L` in `[a, b]`, then `M` has Tor amplitude in `[a, b]`. -/
theorem torAmplitude_obj₃ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {a b : ℤ} (h₁ : torAmplitude R (a + 1) (b + 1) T.obj₁)
    (h₂ : torAmplitude R a b T.obj₂) : torAmplitude R a b T.obj₃ := by
  have h₃ := DerivedCategory.TStructure.t.minus.ext_of_isTriangulatedClosed₃ T hT h₁.1 h₂.1
  refine ⟨h₃, fun M i hi ↦ ?_⟩
  obtain ⟨T', hT', ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ :=
    exists_distTriang_derivedTensorRight M T hT h₁.1 h₂.1 h₃
  have hex := DerivedCategory.HomologySequence.exact₃ T' hT' i (i + 1)
  refine (hex.isZero_X₂ ?_ ?_).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₃.symm)
  · exact ((h₂.2 M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₂)).eq_of_src _ _
  · exact ((h₁.2 M (i + 1) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor _ (i + 1)).mapIso f₁)).eq_of_tgt _ _

/-- Stacks 0655 (2): in a distinguished triangle `K → L → M → K[1]`, if `K` and `M` have Tor
amplitude in `[a, b]`, then so does `L`. -/
theorem torAmplitude_obj₂ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {a b : ℤ} (h₁ : torAmplitude R a b T.obj₁)
    (h₃ : torAmplitude R a b T.obj₃) : torAmplitude R a b T.obj₂ := by
  have h₂ := DerivedCategory.TStructure.t.minus.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1
  refine ⟨h₂, fun M i hi ↦ ?_⟩
  obtain ⟨T', hT', ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ :=
    exists_distTriang_derivedTensorRight M T hT h₁.1 h₂ h₃.1
  have hex := DerivedCategory.HomologySequence.exact₂ T' hT' i
  refine (hex.isZero_X₂ ?_ ?_).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₂.symm)
  · exact ((h₁.2 M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₁)).eq_of_src _ _
  · exact ((h₃.2 M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₃)).eq_of_tgt _ _

/-- Stacks 0655 (3): in a distinguished triangle `K → L → M → K[1]`, if `L` has Tor amplitude
in `[a + 1, b + 1]` and `M` in `[a, b]`, then `K` has Tor amplitude in `[a + 1, b + 1]`. -/
theorem torAmplitude_obj₁ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {a b : ℤ} (h₂ : torAmplitude R (a + 1) (b + 1) T.obj₂)
    (h₃ : torAmplitude R a b T.obj₃) : torAmplitude R (a + 1) (b + 1) T.obj₁ := by
  have h₁ := DerivedCategory.TStructure.t.minus.ext_of_isTriangulatedClosed₁ T hT h₂.1 h₃.1
  refine ⟨h₁, fun M i hi ↦ ?_⟩
  obtain ⟨T', hT', ⟨f₁⟩, ⟨f₂⟩, ⟨f₃⟩⟩ :=
    exists_distTriang_derivedTensorRight M T hT h₁ h₂.1 h₃.1
  have hex := DerivedCategory.HomologySequence.exact₁ T' hT' (i - 1) i
  refine (hex.isZero_X₂ ?_ ?_).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₁.symm)
  · exact ((h₃.2 M (i - 1) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor _ (i - 1)).mapIso f₃)).eq_of_src _ _
  · exact ((h₂.2 M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso f₂)).eq_of_tgt _ _

end ModuleCat
