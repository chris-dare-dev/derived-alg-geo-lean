/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectCorrespondence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.HomVanishing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.Noetherian
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Finite
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Local

/-!
# Terminating chains for weak stability functions (Lemmas 14.8 and 14.11)

Two chain-termination results of §14 of arXiv:1902.08184v4 for a weak
stability function `W` on the heart of a t-structure with the
Harder--Narasimhan property, whose zero-charge subcategory `A⁰` satisfies the
chain condition of Remark 14.7.

* **Lemma 14.8** ([PT19, Lemma 2.17]): if the charges of heart objects lie in a
  finitely generated subgroup of `ℂ` and are Gaussian rational, the heart is
  noetherian.
* **Lemma 14.11**: under the support property, an increasing chain of
  subobjects of a fixed heart object whose slopes are bounded below by a fixed
  `μ ∈ ℝ ∪ {+∞}` terminates.

## Main results

All in the namespace `CategoryTheory.Triangulated.WeakStabilityCondition`.

* `WeakStabilityFunction.isNoetherian_of_zeroCharge_gaussian` — Lemma 14.8.
* `WeakStabilityFunction.terminates_of_slope_ge` — Lemma 14.11.

## Implementation notes

### The common input

Both proofs rest on one consequence of the HN property: **the real parts of
the charges of the subobjects of a fixed heart object are bounded below.**
For a semistable object `S` of finite slope `s`, a subobject `G` has slope at
most `s`, so `-Re Z(G) ≤ s · Im Z(G)`; when `S` has slope `+∞` every subobject
lies on the real axis to the right of `Z(S)`.  The bound passes to extensions,
hence along an HN filtration to every object.

From there, if the charges along an increasing chain `E₁ ⊆ E₂ ⊆ ⋯ ⊆ E` become
constant from `E_N` on, the quotients `E_i / E_N` are zero-charge subobjects of
`E / E_N`, and the chain condition on `A⁰` stops them.  The two lemmas differ
only in why the charges stabilize.

### Lemma 14.8: what "defined over `ℚ[i]`" has to mean

The source's charge is a homomorphism `Z : Λ → ℂ` on a free abelian group of
finite rank (Definition 12.2), and "defined over `ℚ[i]`" means
`Z(Λ) ⊆ ℚ ⊕ iℚ`.  Finite rank is what makes the image discrete, and the
proof's first sentence uses that discreteness.  Here the charge lives on the
ambient `K₀ C`, which need not be finitely generated, and Gaussian-rational
values on `K₀ C` alone do **not** suffice.  The finitely generated projective
modules over the von Neumann regular ring `R = colim M_{2ⁿ}(k)` form an abelian
category with a faithful additive rank valued in `ℤ[1/2]`; `i · rank` is a
stability function with values in `iℤ[1/2]` for which every object is
semistable, and `R` has a strictly increasing chain of direct summands of
ranks `1 - 2⁻ⁿ`.  So the hypotheses are that the charges of heart objects lie
in the image of a finitely generated group `Λ` and are Gaussian rational.  For
a charge factoring through `v : K₀ C → Λ`, as in the source, the first holds
with the class `v E`.

The proof follows the source.  The imaginary parts along the chain are
nondecreasing, bounded by `Im Z(E)` and lie in `(1/N)ℤ`, so they stabilize.
After that the real parts are nonincreasing, bounded below by the common input
and lie in `(1/N)ℤ`, so they stabilize too.  This replaces the source's
maximal subobjects `Mᵢ` with `Im Z = 0`; the lower bound on the real parts is
what those subobjects supplied.

### Lemma 14.11: the mass of an HN filtration

The support property bounds the class of a *semistable* object by its charge,
so the class of `Eᵢ` is bounded by the sum of `|Z|` over its HN factors.  The
HN factors of slope `> 0` come first and those of slope `≤ 0` last, so the
absolute values of their real parts sum to `Re Z(Eᵢ) - 2 Re Z(F)`, where `F` is
the HN step at which the slopes become nonpositive.  The common input bounds
`-Re Z(F)`, since `F ⊆ Eᵢ ⊆ E`, and `μ(Eᵢ) ≥ μ` bounds `Re Z(Eᵢ)` above.  The
classes of the `Eᵢ` are therefore bounded, hence finitely many by the
discreteness of the lattice, and so are their charges.  This replaces the
source's compact parallelogram of HN-factor charges and its count of integral
combinations of finitely many classes; both arguments reach the same finite
set of charges.

### Hypotheses

* The zero-charge chain condition is Remark 14.7's characterisation, the form
  in which `NoetherianTorsionSubcategory` records Definition 14.6.  It follows
  from `IsNoetherianTorsionSubcategory t W.zeroCharge` by
  `IsNoetherianTorsionSubcategory.terminates`, and conversely produces the
  torsion pair `(A⁰, (A⁰)⊥)` by
  `WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition`.
* The support property is the norm-bound form of Definition 12.2(ii), on the
  classes of nonzero semistable objects in a finite-dimensional real space
  where the classes form a discrete subgroup; a quadratic form gives it by
  `HasQuadraticSupportProperty.hasSupportProperty`.  The charge is required to
  be realized by `Zlin` only on classes of heart objects.

## References

* arXiv:1902.08184v4 (Bayer, Lahoz, Macrì, Nuer, Perry, Stellari), Definitions
  12.2 and 14.6, Remarks 12.3 and 14.7, Lemmas 14.8 and 14.11.
* [PT19] D. Piyaratne, Y. Toda, *Moduli of Bridgeland semistable objects on
  3-folds and Donaldson--Thomas invariants*, J. Reine Angew. Math. 747 (2019),
  Lemma 2.17.

## Tags

noetherian heart, weak stability function, support property, ascending chain
condition, Harder--Narasimhan filtration
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  {t : TStructure C}

attribute [local instance] TStructure.heartFullSubcategoryAbelian

/-! ### Real sequences -/

/-- A monotone sequence with finitely many values is eventually constant. -/
private theorem exists_eventually_eq_of_monotone_of_finite {α : Type*} [PartialOrder α]
    {f : ℕ → α} (hf : Monotone f) (hfin : (Set.range f).Finite) :
    ∃ N, ∀ i, N ≤ i → f i = f N := by
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := hfin.exists_maximal ⟨f 0, 0, rfl⟩
  exact ⟨N, fun i hi => le_antisymm (hmax ⟨i, rfl⟩ (hf hi)) (hf hi)⟩

/-- A monotone real sequence bounded above with values in `(1/N)ℤ` is eventually
constant. -/
private theorem exists_eventually_eq_of_monotone_of_intMul {f : ℕ → ℝ} (hf : Monotone f)
    {N : ℕ} (hN : 0 < N) (hint : ∀ i, ∃ k : ℤ, (N : ℝ) * f i = k) {c : ℝ}
    (hc : ∀ i, f i ≤ c) : ∃ M, ∀ i, M ≤ i → f i = f M := by
  refine exists_eventually_eq_of_monotone_of_finite hf
    (((Finset.Icc ⌈(N : ℝ) * f 0⌉ ⌊(N : ℝ) * c⌋).image
      fun k : ℤ => (k : ℝ) / N).finite_toSet.subset ?_)
  rintro _ ⟨i, rfl⟩
  obtain ⟨k, hk⟩ := hint i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc]
  refine ⟨k, ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩, ?_⟩
  · rw [← hk]
    exact mul_le_mul_of_nonneg_left (hf (Nat.zero_le i)) hNpos.le
  · rw [← hk]
    exact mul_le_mul_of_nonneg_left (hc i) hNpos.le
  · rw [← hk]
    field_simp

/-- **The real parts along an HN polygon.** If the terms of a finite sequence
with nonpositive real part form an initial segment, and every partial sum has
real part at least `-B`, then the absolute values of the real parts sum to at
most the real part of the total plus `2B`. -/
private theorem sum_abs_re_le {n : ℕ} (z : ℕ → ℂ) (P : ℕ → Prop)
    (hP : ∀ i j, i ≤ j → j < n → P j → P i)
    (hPre : ∀ j, j < n → P j → (z j).re ≤ 0) (hnPre : ∀ j, j < n → ¬P j → 0 ≤ (z j).re)
    {B : ℝ} (hB : ∀ k, k ≤ n → -(∑ j ∈ Finset.range k, z j).re ≤ B) :
    ∑ j ∈ Finset.range n, |(z j).re| ≤ (∑ j ∈ Finset.range n, z j).re + 2 * B := by
  have key : ∀ m, m ≤ n →
      (∑ j ∈ Finset.range m, |(z j).re| ≤ (∑ j ∈ Finset.range m, z j).re + 2 * B) ∧
      ((m = 0 ∨ P (m - 1)) →
        ∑ j ∈ Finset.range m, |(z j).re| = -(∑ j ∈ Finset.range m, z j).re) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 := hB 0 (Nat.zero_le _)
      simp only [Finset.range_zero, Finset.sum_empty, Complex.zero_re, neg_zero] at h0
      refine ⟨?_, fun _ => by simp⟩
      simp only [Finset.range_zero, Finset.sum_empty, Complex.zero_re]
      linarith
    | succ m ih =>
      intro hm
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      have hBm := hB (m + 1) hm
      rw [Finset.sum_range_succ, Complex.add_re] at hBm
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Complex.add_re]
      by_cases hPm : P m
      · have hprev : m = 0 ∨ P (m - 1) := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exact Or.inl h
          · exact Or.inr (hP (m - 1) m (by omega) (by omega) hPm)
        rw [abs_of_nonpos (hPre m (by omega) hPm), ih₂ hprev]
        exact ⟨by linarith, fun _ => by ring⟩
      · rw [abs_of_nonneg (hnPre m (by omega) hPm)]
        refine ⟨by linarith, fun h => ?_⟩
        rcases h with h | h
        · omega
        · exact absurd (by simpa using h) hPm
  exact (key n le_rfl).1

/-! ### Subobject chains as chains of subobjects of the abelian heart -/

namespace SubobjectChain

variable {B : ObjectProperty C} {E : C} (c : SubobjectChain t B E)

/-- The ambient object of a subobject chain, as an object of the abelian heart. -/
private abbrev heartTarget : t.heart.FullSubcategory := ⟨E, (c.toAmbient_mono 0).2.1⟩

/-- A chain object, as an object of the abelian heart. -/
private abbrev heartObj (i : ℕ) : t.heart.FullSubcategory := ⟨c.obj i, (c.toAmbient_mono i).1⟩

/-- The inclusion of a chain object into the ambient object, in the abelian heart. -/
private def heartArrow (i : ℕ) : c.heartObj i ⟶ c.heartTarget :=
  ObjectProperty.homMk (c.toAmbient i)

private instance (i : ℕ) : Mono (c.heartArrow i) :=
  mono_of_isHeartMono t _ (c.toAmbient_mono i)

/-- The subobjects of the abelian heart traced out by a subobject chain. -/
private def subobjects : ℕ →o Subobject c.heartTarget :=
  ⟨fun i => Subobject.mk (c.heartArrow i), monotone_nat_of_le_succ fun i =>
    Subobject.mk_le_mk_of_comm (ObjectProperty.homMk (c.step i) : c.heartObj i ⟶ c.heartObj (i + 1))
      (by ext; exact c.comm i)⟩

/-- A chain whose traced subobjects are eventually constant terminates. -/
private theorem terminates_of_subobjects
    (h : ∃ M, ∀ i, M ≤ i → c.subobjects M = c.subobjects i) : c.Terminates := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun i hi => ?_⟩
  have heq : Subobject.mk (c.heartArrow i) = Subobject.mk (c.heartArrow (i + 1)) :=
    (hM i hi).symm.trans (hM (i + 1) (by omega))
  let s : c.heartObj i ⟶ c.heartObj (i + 1) := ObjectProperty.homMk (c.step i)
  have hs : s = (Subobject.isoOfMkEqMk _ _ heq).hom := by
    apply (cancel_mono (c.heartArrow (i + 1))).1
    rw [show (Subobject.isoOfMkEqMk _ _ heq).hom = Subobject.ofMkLEMk _ _ heq.le from rfl,
      Subobject.ofMkLEMk_comp]
    ext
    exact c.comm i
  haveI : IsIso s := by rw [hs]; infer_instance
  exact (inferInstance : IsIso ((t.heart).ι.map s))

/-- The traced subobjects have the slopes of the chain objects. -/
private theorem slope_subobjects (W : WeakStabilityFunction t) (i : ℕ) :
    W.slope (c.subobjects i : t.heart.FullSubcategory).obj = W.slope (c.obj i) :=
  W.slope_eq_of_iso ((t.heart).ι.mapIso (Subobject.underlyingIso (c.heartArrow i)))

end SubobjectChain

namespace WeakStabilityFunction

variable (W : WeakStabilityFunction t)

/-! ### Charges in the abelian heart -/

/-- Classes are additive on short exact sequences of the abelian heart. -/
private theorem K₀_of_shortExact {S : ShortComplex t.heart.FullSubcategory}
    (hS : S.ShortExact) :
    K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle (C := C) t S.f S.g
    S.zero fun {A} a ha => ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
      hS.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩
  exact K₀.of_triangle C _ hd

/-- Charges are additive on short exact sequences of the abelian heart. -/
private theorem charge_shortExact {S : ShortComplex t.heart.FullSubcategory}
    (hS : S.ShortExact) :
    W.charge S.X₂.obj = W.charge S.X₁.obj + W.charge S.X₃.obj := by
  simp only [charge, K₀_of_shortExact hS, map_add]

omit [IsTriangulated C] in
private theorem charge_im_nonneg {E : C} (hE : t.heart E) : 0 ≤ (W.charge E).im := by
  by_cases h : IsZero E
  · simp [W.charge_isZero h]
  · rcases W.upper E hE h with h | h
    · exact h.le
    · exact h.1.ge

omit [IsTriangulated C] in
private theorem charge_re_nonpos_of_im_eq_zero {E : C} (hE : t.heart E)
    (him : (W.charge E).im = 0) : (W.charge E).re ≤ 0 := by
  by_cases h : IsZero E
  · simp [W.charge_isZero h]
  · rcases W.upper E hE h with h | h
    · exact absurd him h.ne'
    · exact h.2

omit [IsTriangulated C] in
private theorem charge_eq_zero_of_isZero {G : t.heart.FullSubcategory} (hG : IsZero G) :
    W.charge G.obj = 0 :=
  W.charge_isZero ((t.heart).ι.map_isZero hG)

private theorem charge_mono {X Y : t.heart.FullSubcategory} (g : X ⟶ Y) [Mono g] :
    W.charge Y.obj = W.charge X.obj + W.charge (cokernel g).obj :=
  W.charge_shortExact (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel g)
    inferInstance inferInstance)

/-- The imaginary part of the charge does not decrease from a subobject to the
object. -/
private theorem im_charge_le_of_mono {X Y : t.heart.FullSubcategory} (g : X ⟶ Y) [Mono g] :
    (W.charge X.obj).im ≤ (W.charge Y.obj).im := by
  have h := congrArg Complex.im (W.charge_mono g)
  rw [Complex.add_im] at h
  linarith [W.charge_im_nonneg (cokernel g).property]

/-- With equal imaginary parts, the real part of the charge does not increase
from a subobject to the object. -/
private theorem re_charge_le_of_mono_of_im_eq {X Y : t.heart.FullSubcategory} (g : X ⟶ Y)
    [Mono g] (him : (W.charge X.obj).im = (W.charge Y.obj).im) :
    (W.charge Y.obj).re ≤ (W.charge X.obj).re := by
  have h := W.charge_mono g
  have hQ : (W.charge (cokernel g).obj).im = 0 := by
    have := congrArg Complex.im h
    rw [Complex.add_im] at this
    linarith
  have := congrArg Complex.re h
  rw [Complex.add_re] at this
  linarith [W.charge_re_nonpos_of_im_eq_zero (cokernel g).property hQ]

/-! ### The real parts of subobjects are bounded below -/

/-- A semistable heart object bounds the real parts of the charges of its
subobjects from below. -/
private theorem exists_neg_re_le_of_semistable {S : t.heart.FullSubcategory}
    (hS : W.IsSemistable S.obj) :
    ∃ c : ℝ, ∀ (G : t.heart.FullSubcategory) (g : G ⟶ S), Mono g →
      -(W.charge G.obj).re ≤ c := by
  by_cases him : 0 < (W.charge S.obj).im
  · set s := -(W.charge S.obj).re / (W.charge S.obj).im
    refine ⟨max s 0 * (W.charge S.obj).im, fun G g hg => ?_⟩
    have hGS : (W.charge G.obj).im ≤ (W.charge S.obj).im := W.im_charge_le_of_mono g
    by_cases hG : IsZero G
    · rw [W.charge_eq_zero_of_isZero hG, Complex.zero_re, neg_zero]
      exact mul_nonneg (le_max_right _ _) him.le
    · have hle := W.heart_subobject_slope_le g hS hG
      rw [W.slope_of_im_pos him] at hle
      have hGim : 0 < (W.charge G.obj).im := by
        by_contra h
        rw [W.slope_of_im_nonpos h] at hle
        exact absurd hle (by simp)
      rw [W.slope_of_im_pos hGim] at hle
      have hle' : -(W.charge G.obj).re / (W.charge G.obj).im ≤ s := by exact_mod_cast hle
      calc -(W.charge G.obj).re ≤ s * (W.charge G.obj).im := (div_le_iff₀ hGim).1 hle'
        _ ≤ max s 0 * (W.charge G.obj).im :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hGim.le
        _ ≤ max s 0 * (W.charge S.obj).im := mul_le_mul_of_nonneg_left hGS (le_max_right _ _)
  · refine ⟨-(W.charge S.obj).re, fun G g hg => ?_⟩
    have hSim : (W.charge S.obj).im = 0 :=
      le_antisymm (not_lt.1 him) (W.charge_im_nonneg S.property)
    have hGim : (W.charge G.obj).im = (W.charge S.obj).im :=
      le_antisymm (W.im_charge_le_of_mono g) (hSim ▸ W.charge_im_nonneg G.property)
    linarith [W.re_charge_le_of_mono_of_im_eq g hGim]

/-- Lower bounds on the real parts of the charges of subobjects add along a
short exact sequence. -/
private theorem neg_re_le_of_shortExact {S : ShortComplex t.heart.FullSubcategory}
    (hS : S.ShortExact) {cA cB : ℝ}
    (hA : ∀ (G : t.heart.FullSubcategory) (g : G ⟶ S.X₁), Mono g →
      -(W.charge G.obj).re ≤ cA)
    (hB : ∀ (G : t.heart.FullSubcategory) (g : G ⟶ S.X₃), Mono g →
      -(W.charge G.obj).re ≤ cB)
    (G : t.heart.FullSubcategory) (g : G ⟶ S.X₂) [Mono g] :
    -(W.charge G.obj).re ≤ cA + cB := by
  let φ := g ≫ S.g
  have hk : (kernel.ι φ ≫ g) ≫ S.g = 0 := by simp [φ]
  let u : kernel φ ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι _ hk)
  have hu : u ≫ S.f = kernel.ι φ ≫ g :=
    hS.fIsKernel.fac (KernelFork.ofι _ hk) WalkingParallelPair.zero
  haveI : Mono (u ≫ S.f) := by rw [hu]; infer_instance
  haveI : Mono u := mono_of_mono u S.f
  have hsum := W.charge_mono (kernel.ι φ)
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  have h₁ := hA _ u inferInstance
  have h₂ := hB _ (Abelian.factorThruCoimage φ) inferInstance
  change -(W.charge (cokernel (kernel.ι φ)).obj).re ≤ cB at h₂
  linarith

/-- **The real parts of the charges of the subobjects of a heart object are
bounded below**, under the HN property. -/
private theorem exists_neg_re_le (hHN : W.HasHNProperty) (E : t.heart.FullSubcategory) :
    ∃ c : ℝ, ∀ (G : t.heart.FullSubcategory) (g : G ⟶ E), Mono g →
      -(W.charge G.obj).re ≤ c := by
  by_cases hE : IsZero E
  · refine ⟨0, fun G g hg => ?_⟩
    have hG : IsZero G := IsZero.of_mono g hE
    rw [W.charge_eq_zero_of_isZero hG, Complex.zero_re, neg_zero]
  obtain ⟨F⟩ := hHN E hE
  have key : ∀ k (hk : k ≤ F.n), ∃ c : ℝ, ∀ (G : t.heart.FullSubcategory)
      (g : G ⟶ (F.chain ⟨k, by omega⟩ : t.heart.FullSubcategory)), Mono g →
        -(W.charge G.obj).re ≤ c := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, fun G g hg => ?_⟩
      have hZ : IsZero ((F.chain ⟨0, by omega⟩ : Subobject E) : t.heart.FullSubcategory) := by
        rw [F.chain_bot]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      have hG : IsZero G := IsZero.of_mono g hZ
      rw [W.charge_eq_zero_of_isZero hG, Complex.zero_re, neg_zero]
    | succ k ih =>
      intro hk
      obtain ⟨cA, hA⟩ := ih (by omega)
      let j : Fin F.n := ⟨k, by omega⟩
      obtain ⟨cB, hB⟩ := W.exists_neg_re_le_of_semistable (F.factor_semistable j)
      refine ⟨cA + cB, fun G g hg => ?_⟩
      exact W.neg_re_le_of_shortExact
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel
          (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))) inferInstance inferInstance)
        hA hB G g
  obtain ⟨c, hc⟩ := key F.n le_rfl
  let e : (F.chain ⟨F.n, by omega⟩ : t.heart.FullSubcategory) ≅ E :=
    Subobject.isoOfEq _ _ F.chain_top ≪≫ asIso (⊤ : Subobject E).arrow
  exact ⟨c, fun G g hg => hc G (g ≫ e.inv) inferInstance⟩

/-! ### Stabilizing charges stop the chain -/

/-- If the charges along an increasing chain of subobjects of a heart object
are constant from `N` on, the chain is eventually constant, provided
zero-charge subobject chains terminate.

The quotients `S i / S N` are zero-charge subobjects of `E / S N`, and the
subobject correspondence recovers `S i` from them. -/
private theorem exists_eq_of_charge_eventually_eq
    (h0 : ∀ E : C, t.heart E → ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates)
    {E : t.heart.FullSubcategory} (S : ℕ →o Subobject E) (N : ℕ)
    (hN : ∀ i, N ≤ i → W.charge (S i : t.heart.FullSubcategory).obj =
      W.charge (S N : t.heart.FullSubcategory).obj) :
    ∃ M, ∀ i, M ≤ i → S M = S i := by
  let Q : t.heart.FullSubcategory := cokernel (S N).arrow
  let π : E ⟶ Q := cokernel.π (S N).arrow
  let T : ℕ → Subobject Q := fun i => imageSubobject ((S (N + i)).arrow ≫ π)
  have hpb : ∀ i, (Subobject.pullback π).obj (T i) = S (N + i) := fun i =>
    Abelian.pullback_imageSubobject_eq (S.monotone (Nat.le_add_right N i))
  have hzero : ∀ i, W.heartZeroCharge t (T i : t.heart.FullSubcategory) := by
    intro i
    refine ⟨(T i : t.heart.FullSubcategory).property, ?_⟩
    have hses : W.charge (((Subobject.pullback π).obj (T i) : Subobject E) :
          t.heart.FullSubcategory).obj =
        W.charge (S N : t.heart.FullSubcategory).obj +
          W.charge (T i : t.heart.FullSubcategory).obj :=
      W.charge_shortExact (Abelian.shortExact_ofLE_pullbackπ (S N) (T i))
    rw [hpb i, hN (N + i) (Nat.le_add_right N i)] at hses
    linear_combination -hses
  let ZSub := {P : Subobject Q // W.heartZeroCharge t (P : t.heart.FullSubcategory)}
  haveI : WellFoundedGT ZSub := W.wellFoundedGT_zeroChargeSubobject t Q (h0 Q.obj Q.property)
  let T' : ℕ →o ZSub :=
    ⟨fun i => ⟨T i, hzero i⟩, fun i j hij => by
      change T i ≤ T j
      have h : (S (N + i)).arrow ≫ π =
          Subobject.ofLE _ _ (S.monotone (show N + i ≤ N + j by omega)) ≫
            ((S (N + j)).arrow ≫ π) := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      change imageSubobject ((S (N + i)).arrow ≫ π) ≤ imageSubobject ((S (N + j)).arrow ≫ π)
      rw [h]
      exact imageSubobject_comp_le _ _⟩
  obtain ⟨K, hK⟩ := WellFoundedGT.monotone_chain_condition T'
  refine ⟨N + K, fun i hi => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ i by omega)
  rw [← hpb K, ← hpb k, show T K = T k from congrArg Subtype.val (hK k (by omega))]

/-- The imaginary parts of the charges increase along a chain of subobjects. -/
private theorem monotone_im_charge {E : t.heart.FullSubcategory} (S : ℕ →o Subobject E) :
    Monotone fun i => (W.charge (S i : t.heart.FullSubcategory).obj).im :=
  fun _ _ hij => W.im_charge_le_of_mono (Subobject.ofLE _ _ (S.monotone hij))

/-- Once the imaginary parts are constant, the real parts decrease along a
chain of subobjects. -/
private theorem monotone_neg_re_charge {E : t.heart.FullSubcategory} (S : ℕ →o Subobject E)
    {N₁ : ℕ} (hN₁ : ∀ i, N₁ ≤ i → (W.charge (S i : t.heart.FullSubcategory).obj).im =
      (W.charge (S N₁ : t.heart.FullSubcategory).obj).im) :
    Monotone fun i => -(W.charge (S (N₁ + i) : t.heart.FullSubcategory).obj).re := by
  intro i j hij
  have h := W.re_charge_le_of_mono_of_im_eq
    (Subobject.ofLE _ _ (S.monotone (show N₁ + i ≤ N₁ + j by omega)))
    (by rw [hN₁ (N₁ + i) (by omega), hN₁ (N₁ + j) (by omega)])
  simpa using h

omit [IsTriangulated C] in
/-- Constant imaginary parts from `N₁` on and constant real parts from
`N₁ + N₂` on make the charges constant from `N₁ + N₂` on. -/
private theorem charge_eq_of_im_re {E : t.heart.FullSubcategory} (S : ℕ →o Subobject E)
    {N₁ N₂ : ℕ} (hN₁ : ∀ i, N₁ ≤ i → (W.charge (S i : t.heart.FullSubcategory).obj).im =
      (W.charge (S N₁ : t.heart.FullSubcategory).obj).im)
    (hN₂ : ∀ i, N₂ ≤ i → -(W.charge (S (N₁ + i) : t.heart.FullSubcategory).obj).re =
      -(W.charge (S (N₁ + N₂) : t.heart.FullSubcategory).obj).re) :
    ∀ i, N₁ + N₂ ≤ i → W.charge (S i : t.heart.FullSubcategory).obj =
      W.charge (S (N₁ + N₂) : t.heart.FullSubcategory).obj := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N₁ ≤ i by omega)
  apply Complex.ext
  · exact neg_inj.1 (hN₂ k (by omega))
  · rw [hN₁ (N₁ + k) (by omega), hN₁ (N₁ + N₂) (by omega)]

/-! ### Lemma 14.8 -/

/-- The Gaussian-rational values of an additive map on a finitely generated
group have a common denominator. -/
private theorem exists_nat_mul_mem_gaussian {Λ : Type*} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (Z : Λ →+ ℂ) : ∃ N : ℕ, 0 < N ∧ ∀ a : Λ, (∃ p q : ℚ, Z a = p + q * Complex.I) →
      ∃ x y : ℤ, (N : ℂ) * Z a = x + y * Complex.I := by
  let L : Submodule ℤ Λ :=
    { carrier := {a | ∃ p q : ℚ, Z a = p + q * Complex.I}
      add_mem' := by
        rintro a b ⟨p, q, hp⟩ ⟨p', q', hp'⟩
        exact ⟨p + p', q + q', by rw [map_add, hp, hp']; push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro n a ⟨p, q, hp⟩
        exact ⟨n * p, n * q, by rw [map_zsmul, hp, zsmul_eq_mul]; push_cast; ring⟩ }
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian L
  have hmem : ∀ a ∈ s, ∃ p q : ℚ, Z a = p + q * Complex.I := fun a ha =>
    (hs ▸ Submodule.subset_span ha : a ∈ L)
  choose! p q hpq using hmem
  let N : ℕ := ∏ a ∈ s, (p a).den * (q a).den
  have hN : 0 < N := Finset.prod_pos fun a _ => Nat.mul_pos (p a).den_pos (q a).den_pos
  have hint : ∀ (r : ℚ) (k : ℕ), r.den ∣ k → ∃ x : ℤ, (k : ℚ) * r = x := by
    rintro r _ ⟨m, rfl⟩
    exact ⟨m * r.num, by push_cast; rw [mul_comm (r.den : ℚ), mul_assoc, Rat.den_mul_eq_num]⟩
  let L' : Submodule ℤ Λ :=
    { carrier := {a | ∃ x y : ℤ, (N : ℂ) * Z a = x + y * Complex.I}
      add_mem' := by
        rintro a b ⟨x, y, hx⟩ ⟨x', y', hx'⟩
        exact ⟨x + x', y + y', by rw [map_add, mul_add, hx, hx']; push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro n a ⟨x, y, hx⟩
        refine ⟨n * x, n * y, ?_⟩
        rw [map_zsmul, zsmul_eq_mul, mul_left_comm, hx]
        push_cast
        ring }
  have hsL' : (s : Set Λ) ⊆ L' := by
    intro a ha
    obtain ⟨x, hx⟩ := hint (p a) N
      ((dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem (fun a => (p a).den * (q a).den) ha))
    obtain ⟨y, hy⟩ := hint (q a) N
      ((dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem (fun a => (p a).den * (q a).den) ha))
    refine ⟨x, y, ?_⟩
    rw [hpq a ha, mul_add, ← mul_assoc]
    have hx' : ((N : ℚ) * p a : ℂ) = (x : ℂ) := by exact_mod_cast hx
    have hy' : ((N : ℚ) * q a : ℂ) = (y : ℂ) := by exact_mod_cast hy
    push_cast at hx' hy'
    rw [hx', hy']
  refine ⟨N, hN, fun a ha => ?_⟩
  have haL : a ∈ L := ha
  rw [← hs] at haL
  exact Submodule.span_le.2 hsL' haL

/-- Lemma 14.8 with the discreteness made explicit: charges of heart objects in
`(1/N)ℤ[i]`. -/
private theorem isNoetherianObject_of_intMul (hHN : W.HasHNProperty)
    (h0 : ∀ E : C, t.heart E → ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates)
    {N : ℕ} (hN : 0 < N)
    (hint : ∀ X : C, t.heart X → ∃ x y : ℤ, (N : ℂ) * W.charge X = x + y * Complex.I)
    (E : t.heart.FullSubcategory) : IsNoetherianObject E := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro S
  obtain ⟨B, hB⟩ := W.exists_neg_re_le hHN E
  have hre : ∀ X : C, t.heart X → ∃ x : ℤ, (N : ℝ) * (W.charge X).re = x := fun X hX => by
    obtain ⟨x, y, h⟩ := hint X hX
    exact ⟨x, by simpa using congrArg Complex.re h⟩
  have him : ∀ X : C, t.heart X → ∃ y : ℤ, (N : ℝ) * (W.charge X).im = y := fun X hX => by
    obtain ⟨x, y, h⟩ := hint X hX
    exact ⟨y, by simpa using congrArg Complex.im h⟩
  obtain ⟨N₁, hN₁⟩ := exists_eventually_eq_of_monotone_of_intMul (W.monotone_im_charge S) hN
    (fun i => him _ (S i : t.heart.FullSubcategory).property)
    (fun i => W.im_charge_le_of_mono (S i).arrow)
  obtain ⟨N₂, hN₂⟩ := exists_eventually_eq_of_monotone_of_intMul
    (W.monotone_neg_re_charge S hN₁) hN
    (fun i => by
      obtain ⟨x, hx⟩ := hre _ (S (N₁ + i) : t.heart.FullSubcategory).property
      exact ⟨-x, by push_cast; rw [mul_neg, hx]⟩)
    (fun i => hB _ (S (N₁ + i)).arrow inferInstance)
  exact W.exists_eq_of_charge_eventually_eq h0 S _ (W.charge_eq_of_im_re S hN₁ hN₂)

/-- **Lemma 14.8** ([PT19, Lemma 2.17]): let `W` be a weak stability function
with the HN property whose zero-charge subobject chains terminate (Remark
14.7's form of "`A⁰` is a noetherian torsion subcategory").  If the charges of
heart objects lie in the image of a finitely generated group `Λ` and are
Gaussian rational, the heart is noetherian.

The source's charge is `Z : Λ → ℂ` on a lattice of finite rank with
`Z(Λ) ⊆ ℚ ⊕ iℚ`; for a charge factoring through `v : K₀ C → Λ`, `hZ` holds with
the class `v E`.  Gaussian-rational values on `K₀ C` alone would not do; see
the module docstring. -/
theorem isNoetherian_of_zeroCharge_gaussian (hHN : W.HasHNProperty)
    (h0 : ∀ E : C, t.heart E → ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates)
    {Λ : Type*} [AddCommGroup Λ] [Module.Finite ℤ Λ] (Z : Λ →+ ℂ)
    (hZ : ∀ E : C, t.heart E → W.charge E ∈ Set.range Z)
    (hQ : ∀ E : C, t.heart E → ∃ p q : ℚ, W.charge E = p + q * Complex.I) :
    t.IsNoetherian := by
  obtain ⟨N, hN, hNZ⟩ := exists_nat_mul_mem_gaussian Z
  refine fun E => W.isNoetherianObject_of_intMul hHN h0 hN (fun X hX => ?_) E
  obtain ⟨a, ha⟩ := hZ X hX
  have hq := hQ X hX
  rw [← ha] at hq ⊢
  exact hNZ a hq

/-! ### Lemma 14.11 -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **The class of a heart object is bounded by the mass of its HN
filtration.** Under the support property, if `-Re Z` is at most `B` on the
subobjects of `F`, the class of `F` has norm at most
`K (Im Z(F) + Re Z(F) + 2B)`. -/
private theorem norm_class_le_of_hn (w : K₀ C →+ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ E : C, t.heart E → Zlin (w (K₀.of C E)) = W.charge E) {K : ℝ} (hK : 0 ≤ K)
    (hsupp : ∀ x ∈ {x | ∃ E : C, W.IsSemistable E ∧ ¬IsZero E ∧ x = w (K₀.of C E)},
      ‖x‖ ≤ K * ‖Zlin x‖)
    {F : t.heart.FullSubcategory} (HF : WeakAbelianHNFiltration W F) {B : ℝ}
    (hB : ∀ (G : t.heart.FullSubcategory) (g : G ⟶ F), Mono g → -(W.charge G.obj).re ≤ B) :
    ‖w (K₀.of C F.obj)‖ ≤
      K * ((W.charge F.obj).im + (W.charge F.obj).re + 2 * B) := by
  classical
  let κ : ℕ → K₀ C := fun j =>
    if h : j < HF.n then K₀.of C (HF.factor ⟨j, h⟩).obj else 0
  have htel : ∀ k (hk : k ≤ HF.n), K₀.of C (HF.chain ⟨k, by omega⟩ :
      t.heart.FullSubcategory).obj = ∑ j ∈ Finset.range k, κ j := by
    intro k
    induction k with
    | zero =>
      intro _
      have hZ0 : IsZero ((HF.chain ⟨0, by omega⟩ : Subobject F) :
          t.heart.FullSubcategory) := by
        rw [HF.chain_bot]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      rw [Finset.range_zero, Finset.sum_empty]
      exact K₀.of_isZero C ((t.heart).ι.map_isZero hZ0)
    | succ k ih =>
      intro hk
      let j : Fin HF.n := ⟨k, by omega⟩
      rw [Finset.sum_range_succ, ← ih (by omega)]
      have h := K₀_of_shortExact (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel
        (Subobject.ofLE (HF.chain j.castSucc) (HF.chain j.succ)
          (le_of_lt (HF.chain_strictMono j.castSucc_lt_succ)))) inferInstance inferInstance)
      have hk' : k < HF.n := by omega
      simp only [κ, hk', ↓reduceDIte]
      exact h
  have hF : K₀.of C F.obj = ∑ j ∈ Finset.range HF.n, κ j := by
    rw [← htel HF.n le_rfl]
    exact K₀.of_iso C ((t.heart).ι.mapIso
      (Subobject.isoOfEq _ _ HF.chain_top ≪≫ asIso (⊤ : Subobject F).arrow)).symm
  let z : ℕ → ℂ := fun j => W.Z (κ j)
  have hzsum : ∀ k (hk : k ≤ HF.n), ∑ j ∈ Finset.range k, z j =
      W.charge (HF.chain ⟨k, by omega⟩ : t.heart.FullSubcategory).obj := fun k hk => by
    simp only [z, charge, htel k hk, map_sum]
  have hzF : ∑ j ∈ Finset.range HF.n, z j = W.charge F.obj := by
    simp only [z, charge, hF, map_sum]
  have hzslope : ∀ j (hj : j < HF.n), W.slope (HF.factor ⟨j, hj⟩).obj = HF.μ ⟨j, hj⟩ :=
    fun j hj => HF.factor_slope ⟨j, hj⟩
  have hzj : ∀ j (hj : j < HF.n), z j = W.charge (HF.factor ⟨j, hj⟩).obj := fun j hj => by
    simp only [z, κ, hj, ↓reduceDIte, charge]
  -- the HN factors of positive slope come first
  let P : ℕ → Prop := fun j => ∃ hj : j < HF.n, (0 : WithTop ℝ) < HF.μ ⟨j, hj⟩
  have hP : ∀ i j, i ≤ j → j < HF.n → P j → P i := by
    rintro i j hij hj ⟨_, hμ⟩
    exact ⟨by omega, hμ.trans_le (HF.μ_anti.antitone (Fin.mk_le_mk.2 hij))⟩
  have hPre : ∀ j, j < HF.n → P j → (z j).re ≤ 0 := by
    rintro j hj ⟨_, hμ⟩
    rw [hzj j hj]
    rw [← hzslope j hj] at hμ
    by_cases him : 0 < (W.charge (HF.factor ⟨j, hj⟩).obj).im
    · rw [W.slope_of_im_pos him] at hμ
      have : (0 : ℝ) < -(W.charge (HF.factor ⟨j, hj⟩).obj).re /
          (W.charge (HF.factor ⟨j, hj⟩).obj).im := by exact_mod_cast hμ
      have := (div_pos_iff_of_pos_right him).1 this
      linarith
    · exact W.charge_re_nonpos_of_im_eq_zero (HF.factor ⟨j, hj⟩).property
        (le_antisymm (not_lt.1 him) (W.charge_im_nonneg (HF.factor ⟨j, hj⟩).property))
  have hnPre : ∀ j, j < HF.n → ¬P j → 0 ≤ (z j).re := by
    intro j hj hPj
    have hμ : HF.μ ⟨j, hj⟩ ≤ 0 := not_lt.1 fun h => hPj ⟨hj, h⟩
    rw [hzj j hj]
    rw [← hzslope j hj] at hμ
    have him : 0 < (W.charge (HF.factor ⟨j, hj⟩).obj).im := by
      by_contra h
      rw [W.slope_of_im_nonpos h] at hμ
      exact absurd hμ (by simp)
    rw [W.slope_of_im_pos him] at hμ
    have : -(W.charge (HF.factor ⟨j, hj⟩).obj).re /
        (W.charge (HF.factor ⟨j, hj⟩).obj).im ≤ 0 := by exact_mod_cast hμ
    have := (div_le_iff₀ him).1 this
    linarith
  have hBk : ∀ k, k ≤ HF.n → -(∑ j ∈ Finset.range k, z j).re ≤ B := fun k hk => by
    rw [hzsum k hk]
    exact hB _ (HF.chain _).arrow inferInstance
  have hre := sum_abs_re_le z P hP hPre hnPre hBk
  calc ‖w (K₀.of C F.obj)‖ = ‖∑ j ∈ Finset.range HF.n, w (κ j)‖ := by
        simp only [hF, map_sum]
    _ ≤ ∑ j ∈ Finset.range HF.n, ‖w (κ j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range HF.n, K * ‖z j‖ := Finset.sum_le_sum fun j hj => by
        have hj' := Finset.mem_range.1 hj
        have h := hsupp _ ⟨_, HF.factor_semistable ⟨j, hj'⟩,
          HF.factor_obj_not_isZero ⟨j, hj'⟩, rfl⟩
        simp only [κ, hj', ↓reduceDIte, z]
        rwa [hZ _ (HF.factor ⟨j, hj'⟩).property] at h
    _ ≤ ∑ j ∈ Finset.range HF.n, K * (|(z j).re| + (z j).im) := Finset.sum_le_sum fun j hj => by
        refine mul_le_mul_of_nonneg_left ?_ hK
        have him : 0 ≤ (z j).im := by
          rw [hzj j (Finset.mem_range.1 hj)]
          exact W.charge_im_nonneg (HF.factor _).property
        simpa [abs_of_nonneg him] using Complex.norm_le_abs_re_add_abs_im (z j)
    _ = K * (∑ j ∈ Finset.range HF.n, |(z j).re| + (∑ j ∈ Finset.range HF.n, z j).im) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Complex.im_sum]
    _ ≤ K * ((W.charge F.obj).im + (W.charge F.obj).re + 2 * B) := by
        rw [hzF] at hre ⊢
        exact mul_le_mul_of_nonneg_left (by linarith) hK

/-- Lemma 14.11 for a chain of subobjects in the abelian heart. -/
private theorem exists_eq_of_slope_ge (hHN : W.HasHNProperty) (w : K₀ C →+ V)
    (hw : DiscreteTopology (Set.range w)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ E : C, t.heart E → Zlin (w (K₀.of C E)) = W.charge E)
    (hsupp : Support.HasSupportProperty Zlin
      {x | ∃ E : C, W.IsSemistable E ∧ ¬IsZero E ∧ x = w (K₀.of C E)})
    (h0 : ∀ E : C, t.heart E → ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates)
    (μ : WithTop ℝ) {E : t.heart.FullSubcategory} (S : ℕ →o Subobject E)
    (hS : ∀ i, μ ≤ W.slope (S i : t.heart.FullSubcategory).obj) :
    ∃ M, ∀ i, M ≤ i → S M = S i := by
  obtain ⟨B, hB⟩ := W.exists_neg_re_le hHN E
  obtain ⟨K, hK, hsupp⟩ := hsupp
  have hImE : 0 ≤ (W.charge E.obj).im := W.charge_im_nonneg E.property
  -- the slope bound bounds the real parts from above
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧
      ∀ i, (W.charge (S i : t.heart.FullSubcategory).obj).re ≤ r := by
    induction μ using WithTop.recTopCoe with
    | top =>
      refine ⟨0, le_rfl, fun i => ?_⟩
      have him : ¬0 < (W.charge (S i : t.heart.FullSubcategory).obj).im := fun h => by
        have := hS i
        rw [W.slope_of_im_pos h] at this
        exact absurd this (by simp)
      exact W.charge_re_nonpos_of_im_eq_zero (S i : t.heart.FullSubcategory).property
        (le_antisymm (not_lt.1 him)
          (W.charge_im_nonneg (S i : t.heart.FullSubcategory).property))
    | coe m =>
      refine ⟨max (-m) 0 * (W.charge E.obj).im, mul_nonneg (le_max_right _ _) hImE,
        fun i => ?_⟩
      have hIm := W.im_charge_le_of_mono (S i).arrow
      by_cases him : 0 < (W.charge (S i : t.heart.FullSubcategory).obj).im
      · have h := hS i
        rw [W.slope_of_im_pos him] at h
        have h' : m ≤ -(W.charge (S i : t.heart.FullSubcategory).obj).re /
            (W.charge (S i : t.heart.FullSubcategory).obj).im := by exact_mod_cast h
        have h'' := (le_div_iff₀ him).1 h'
        calc (W.charge (S i : t.heart.FullSubcategory).obj).re
            ≤ -m * (W.charge (S i : t.heart.FullSubcategory).obj).im := by linarith
          _ ≤ max (-m) 0 * (W.charge (S i : t.heart.FullSubcategory).obj).im :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) him.le
          _ ≤ max (-m) 0 * (W.charge E.obj).im :=
            mul_le_mul_of_nonneg_left hIm (le_max_right _ _)
      · have := W.charge_re_nonpos_of_im_eq_zero (S i : t.heart.FullSubcategory).property
          (le_antisymm (not_lt.1 him)
            (W.charge_im_nonneg (S i : t.heart.FullSubcategory).property))
        linarith [mul_nonneg (le_max_right (-m) 0) hImE]
  -- the classes along the chain are bounded
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hcls : ∀ i, ‖w (K₀.of C (S i : t.heart.FullSubcategory).obj)‖ ≤
      K * ((W.charge E.obj).im + r + 2 * max B 0) := by
    intro i
    by_cases hz : IsZero (S i : t.heart.FullSubcategory)
    · have h0' : K₀.of C (S i : t.heart.FullSubcategory).obj = 0 :=
        K₀.of_isZero C ((t.heart).ι.map_isZero hz)
      rw [h0', map_zero, norm_zero]
      exact mul_nonneg hK.le (by linarith)
    obtain ⟨HF⟩ := hHN _ hz
    have hBi : ∀ (G : t.heart.FullSubcategory) (g : G ⟶ (S i : t.heart.FullSubcategory)),
        Mono g → -(W.charge G.obj).re ≤ max B 0 := fun G g _ =>
      (hB G (g ≫ (S i).arrow) inferInstance).trans (le_max_left _ _)
    refine (W.norm_class_le_of_hn w Zlin hZ hK.le hsupp HF hBi).trans
      (mul_le_mul_of_nonneg_left ?_ hK.le)
    linarith [W.im_charge_le_of_mono (S i).arrow, hr i]
  -- hence finitely many classes, and finitely many charges
  have hfin : (Set.range fun i => W.charge (S i : t.heart.FullSubcategory).obj).Finite := by
    have hball := Support.HasSupportProperty.finite_classes (Z := (LinearMap.id : V →ₗ[ℝ] V))
      (S := Set.univ) ⟨1, one_pos, fun v _ => by simp⟩ w hw
      (K * ((W.charge E.obj).im + r + 2 * max B 0) + 1)
    refine (hball.image Zlin).subset ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨w (K₀.of C (S i : t.heart.FullSubcategory).obj), ⟨⟨_, rfl⟩, trivial, ?_⟩,
      hZ _ (S i : t.heart.FullSubcategory).property⟩
    simp only [LinearMap.id_apply]
    linarith [hcls i]
  -- the charges stabilize, and with them the chain
  obtain ⟨N₁, hN₁⟩ := exists_eventually_eq_of_monotone_of_finite (W.monotone_im_charge S)
    ((hfin.image Complex.im).subset (by rintro _ ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩))
  obtain ⟨N₂, hN₂⟩ := exists_eventually_eq_of_monotone_of_finite
    (W.monotone_neg_re_charge S hN₁)
    ((hfin.image fun z => -z.re).subset (by rintro _ ⟨i, rfl⟩; exact ⟨_, ⟨N₁ + i, rfl⟩, rfl⟩))
  exact W.exists_eq_of_charge_eventually_eq h0 S _ (W.charge_eq_of_im_re S hN₁ hN₂)

/-- **Lemma 14.11.** Let `W` be a weak stability function with the HN property,
the support property, and terminating zero-charge subobject chains (Remark
14.7's form of "`A⁰` is a noetherian torsion subcategory").  Then for every
`μ ∈ ℝ ∪ {+∞}`, an increasing chain of subobjects of a fixed heart object, each
of slope at least `μ`, terminates.

The support property is the norm-bound form of Definition 12.2(ii) for the
classes `w E ∈ V` of nonzero semistable objects, where the classes of all
objects form a discrete subgroup and `Zlin` realizes the charge on classes of
heart objects.  For a lattice `ι : Λ →+ V` with discrete image and a class map
`v : K₀ C →+ Λ`, take `w = ι.comp v`. -/
theorem terminates_of_slope_ge (hHN : W.HasHNProperty) (w : K₀ C →+ V)
    (hw : DiscreteTopology (Set.range w)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ E : C, t.heart E → Zlin (w (K₀.of C E)) = W.charge E)
    (hsupp : Support.HasSupportProperty Zlin
      {x | ∃ E : C, W.IsSemistable E ∧ ¬IsZero E ∧ x = w (K₀.of C E)})
    (h0 : ∀ E : C, t.heart E → ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates)
    (μ : WithTop ℝ) {E : C} (c : SubobjectChain t (fun F => μ ≤ W.slope F) E) :
    c.Terminates :=
  c.terminates_of_subobjects (W.exists_eq_of_slope_ge hHN w hw Zlin hZ hsupp h0 μ c.subobjects
    fun i => by rw [c.slope_subobjects W i]; exact c.prop i)

end WeakStabilityFunction

end

end CategoryTheory.Triangulated.WeakStabilityCondition
