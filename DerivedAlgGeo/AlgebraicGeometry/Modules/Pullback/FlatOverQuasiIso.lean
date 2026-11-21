/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Pullback of quasi-isomorphisms between complexes flat over the base

Let `P = Y ×_T T'` be a pullback square with projections `fst : P ⟶ Y` and `snd : P ⟶ T'`.
Degreewise pullback along `fst` keeps a quasi-isomorphism between strictly bounded-above
complexes of module sheaves on `Y` a quasi-isomorphism, as soon as every term of both complexes
is flat over `T`. This is the Tor-independence that makes degreewise pullback compute derived
base change on such complexes.

## Main definitions

None.

## Main results

* `AlgebraicGeometry.Scheme.Modules.acyclic_pullback_of_isPullback` — the pullback of a strictly
  bounded-above acyclic complex with terms flat over `T` is acyclic.
* `AlgebraicGeometry.Scheme.Modules.quasiIso_pullback_of_isPullback` — the pullback of a
  quasi-isomorphism between strictly bounded-above complexes with terms flat over `T` is a
  quasi-isomorphism.

## Implementation notes

The homological algebra is stated for an additive functor `F` and an object property `𝒫`
containing zero, closed under kernels of epimorphisms, isomorphisms and biproducts, such that
`F` keeps short exact sequences with quotient in `𝒫` short exact. For pullback along `fst` and
flatness over `T`, these are `IsFlatOver.of_isZero`, `IsFlatOver.of_shortExact`,
`IsFlatOver.of_iso`, `IsFlatOver.biprod` and `pullback_shortExact_of_isPullback`.

For a strictly bounded-above acyclic complex `K`, the cycles `Zⁱ` are in `𝒫` by descending
induction along the short exact sequences `Zⁱ → Kⁱ → Zⁱ⁺¹`. These sequences stay short exact
after `F`, which gives exactness of `F K` in every degree. A quasi-isomorphism is reduced to its
mapping cone, which is acyclic, strictly bounded above, with terms `Kⁱ⁺¹ ⊞ Lⁱ`.

The upper bound is needed. Termwise flatness does not keep an unbounded acyclic complex acyclic
under tensor products, so the statement is not claimed for unbounded complexes.

## References

* [Stacks, Tag 0DI5](https://stacks.math.columbia.edu/tag/0DI5), the base-change lemma for
  relatively perfect objects that this result serves.

## Tags

pullback, base change, flat module, quasi-isomorphism, Tor-independence
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Generic

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- The short complex `Zⁱ → Kⁱ → Zʲ` of cycles. -/
private noncomputable abbrev cyclesSC (K : CochainComplex C ℤ) (i j : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

private lemma cyclesSC_shortExact (K : CochainComplex C ℤ) (i j : ℤ) (hij : i + 1 = j)
    (hK : K.ExactAt j) : (cyclesSC K i j).ShortExact := by
  have hexact : (cyclesSC K i j).Exact := by
    let S' := ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)
    have hS' : S'.Exact :=
      ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j (by simp [← hij]))
    let φ : cyclesSC K i j ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := K.iCycles j
        comm₁₂ := by simp [S']
        comm₂₃ := by simp [S'] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS'
  have hepi : Epi (K.toCycles i j) := by
    have h := (K.exactAt_iff' i j (j + 1) (by simp [← hij]) (by simp)).1 hK
    have := h.epi_toCycles
    have e := K.toCycles_cyclesIsoSc'_hom i j (j + 1) (by simp [← hij]) (by simp)
    have : K.toCycles i j = (K.sc' i j (j + 1)).toCycles ≫
        (K.cyclesIsoSc' i j (j + 1) (by simp [← hij]) (by simp)).inv := by
      rw [← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  exact { exact := hexact, mono_f := by dsimp; infer_instance, epi_g := hepi }

variable (F : C ⥤ D) (P : C → Prop)

/-- A functor that keeps short exact sequences with quotient in `P` short exact keeps
strictly bounded-above acyclic complexes with terms in `P` acyclic, when `P` contains the zero
objects and is closed under kernels of epimorphisms. -/
private theorem acyclic_map_of_isStrictlyLE [F.PreservesZeroMorphisms]
    (hP0 : ∀ X, IsZero X → P X)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₃ → (S.map F).ShortExact)
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b] (hK : K.Acyclic)
    (hKP : ∀ i, P (K.X i)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  have hZ : ∀ n : ℕ, ∀ i : ℤ, b + 1 - n ≤ i → P (K.cycles i) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      exact hP0 _ ((K.isZero_of_isStrictlyLE b i (by omega)).of_mono (K.iCycles i))
    | succ n ih =>
      intro i hi
      by_cases hi' : b + 1 - n ≤ i
      · exact ih i hi'
      · exact hP _ (cyclesSC_shortExact K i (i + 1) rfl (hK _)) (hKP i) (ih (i + 1) (by omega))
  have hZ' : ∀ i, P (K.cycles i) := fun i ↦ by
    by_cases hi : b + 1 ≤ i
    · exact hZ 0 i (by simpa using hi)
    · exact hZ (b + 1 - i).toNat i (by omega)
  have hSES : ∀ i j, i + 1 = j → ((cyclesSC K i j).map F).ShortExact := fun i j hij ↦
    hF _ (cyclesSC_shortExact K i j hij (hK _)) (hZ' j)
  intro i
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  let S₃ := ShortComplex.mk (F.map (K.toCycles (i - 1) i) ≫ F.map (K.iCycles i))
    (F.map (K.toCycles i (i + 1))) (by
      rw [Category.assoc, ← F.map_comp, ← F.map_comp, (cyclesSC K i (i + 1)).zero,
        comp_zero, Functor.map_zero])
  have h1 := hSES (i - 1) i (by omega)
  have h2 := hSES i (i + 1) rfl
  have h3 := hSES (i + 1) (i + 1 + 1) rfl
  let φ₁ : S₃ ⟶ ((F.mapHomologicalComplex _).obj K).sc' (i - 1) i (i + 1) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (K.iCycles (i + 1))
      comm₁₂ := by
        dsimp [S₃]
        rw [← F.map_comp, HomologicalComplex.toCycles_i, Category.id_comp, Category.comp_id]
      comm₂₃ := by
        dsimp [S₃]
        rw [← F.map_comp, HomologicalComplex.toCycles_i, Category.id_comp] }
  let φ₂ : S₃ ⟶ (cyclesSC K i (i + 1)).map F :=
    { τ₁ := F.map (K.toCycles (i - 1) i)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by dsimp [S₃]; rw [Category.comp_id]
      comm₂₃ := by dsimp [S₃]; rw [Category.comp_id, Category.id_comp] }
  have : Mono φ₁.τ₃ := h3.mono_f
  have : Epi φ₂.τ₁ := h1.epi_g
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁,
    ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂]
  exact h2.exact

private lemma quasiIso_iff_acyclic_mappingCone {M N : CochainComplex C ℤ} (g : M ⟶ N) :
    QuasiIso g ↔ (CochainComplex.mappingCone g).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh g)
    (HomotopyCategory.mappingCone_triangleh_distinguished g)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

private theorem quasiIso_map_of_isStrictlyLE [F.Additive]
    (hP0 : ∀ X, IsZero X → P X)
    (hPi : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hPb : ∀ X Y : C, P X → P Y → P (X ⊞ Y))
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₃ → (S.map F).ShortExact)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b]
    (hg : QuasiIso g) (hK : ∀ i, P (K.X i)) (hL : ∀ i, P (L.X i)) :
    QuasiIso ((F.mapHomologicalComplex _).map g) := by
  rw [quasiIso_iff_acyclic_mappingCone] at hg ⊢
  have hcone : (CochainComplex.mappingCone g).IsStrictlyLE (max a b) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff g i).2
      ⟨K.isZero_of_isStrictlyLE a (i + 1) (by omega), L.isZero_of_isStrictlyLE b i (by omega)⟩
  have hP' : ∀ i, P ((CochainComplex.mappingCone g).X i) := fun i ↦
    hPi (HomologicalComplex.homotopyCofiber.XIsoBiprod g i (i + 1) rfl).symm
      (hPb _ _ (hK _) (hL _))
  have h := acyclic_map_of_isStrictlyLE F P hP0 hP hF _ (max a b) hg hP'
  exact fun i ↦ (h i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso g F)

end Generic

variable {P Y T T' : Scheme.{u}} {fst : P ⟶ Y} {snd : P ⟶ T'} {q : Y ⟶ T} {h : T' ⟶ T}

/-- Degreewise pullback along `fst` keeps a strictly bounded-above acyclic complex of module
sheaves acyclic when its terms are flat over `T`. No flatness of `q` is used. -/
theorem acyclic_pullback_of_isPullback (H : IsPullback fst snd q h)
    (K : CochainComplex Y.Modules ℤ) (b : ℤ) [K.IsStrictlyLE b] (hK : K.Acyclic)
    (hKq : ∀ i, IsFlatOver q (K.X i)) :
    (((pullback fst).mapHomologicalComplex _).obj K).Acyclic :=
  acyclic_map_of_isStrictlyLE (pullback fst) (IsFlatOver q) (fun _ hX ↦ IsFlatOver.of_isZero hX)
    (fun _ hS h₂ h₃ ↦ IsFlatOver.of_shortExact hS h₂ h₃)
    (fun _ hS h₃ ↦ pullback_shortExact_of_isPullback H hS h₃) K b hK hKq

/-- **Tor-independence for complexes flat over the base.** Degreewise pullback along `fst`
keeps a quasi-isomorphism between strictly bounded-above complexes of module sheaves a
quasi-isomorphism when every term of both complexes is flat over `T`. No flatness of `q` is
used; the bounds are on the terms, not on cohomology. -/
theorem quasiIso_pullback_of_isPullback (H : IsPullback fst snd q h)
    {K L : CochainComplex Y.Modules ℤ} (g : K ⟶ L) (a b : ℤ) [K.IsStrictlyLE a]
    [L.IsStrictlyLE b] (hg : QuasiIso g) (hK : ∀ i, IsFlatOver q (K.X i))
    (hL : ∀ i, IsFlatOver q (L.X i)) :
    QuasiIso (((pullback fst).mapHomologicalComplex _).map g) :=
  quasiIso_map_of_isStrictlyLE (pullback fst) (IsFlatOver q)
    (fun _ hX ↦ IsFlatOver.of_isZero hX) (fun e hX ↦ IsFlatOver.of_iso e hX)
    (fun _ _ hX hY ↦ IsFlatOver.biprod hX hY) (fun _ hS h₂ h₃ ↦ IsFlatOver.of_shortExact hS h₂ h₃)
    (fun _ hS h₃ ↦ pullback_shortExact_of_isPullback H hS h₃) g a b hg hK hL

end AlgebraicGeometry.Scheme.Modules
