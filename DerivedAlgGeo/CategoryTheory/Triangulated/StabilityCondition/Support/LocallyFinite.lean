/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.FirstStrictSES
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.Semistable
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Finite

/-!
# Local finiteness from the support property

The second paragraph of Remark 12.3 of arXiv:1902.08184v4 (after
[BMS16, Appendix A] and [KS08]): a pre-stability condition with the support
property is locally finite, hence a Bridgeland stability condition.

Classes reach a finite-dimensional real space `V` through an additive map out
of `K₀` with discrete image, which is the lattice hypothesis of Remark 12.3.
Two presentations are provided: a class map `v : K₀ → Λ` followed by
`ι : Λ →+ V` (the source's convention), and a class map straight into `V`
together with `QuadraticSupportData`. Local finiteness is concluded, never
assumed: the `locallyFinite` field of `StabilityCondition.WithClassMap` is
filled by these theorems.

## Main definitions

* `toStabilityCondition_of_quadraticSupport`: the Bridgeland stability
  condition underlying a pre-stability condition with quadratic support.
* `QuadraticSupportData.toStabilityCondition`: the same for a class map into
  `V` with discrete image.

## Main results

* `isLocallyFinite_of_hasSupportProperty`: the norm-bound form.
* `isLocallyFinite_of_quadraticSupport`: Remark 12.3, second paragraph, with
  a genuine quadratic form.
* `QuadraticSupportData.isLocallyFinite`: the same for a class map into `V`.

Semistable objects of the resulting stability condition have Jordan--Hölder
filtrations by `Slicing.IsLocallyFinite.hasJordanHolderFiltrations`.

## Implementation notes

Fix a phase `t` and rotate the charge so that `t` points along the positive
real axis. On a nonzero semistable object of phase within `1/4` of `t` the
real part of the rotated charge is at least half its norm. Summing over
Harder--Narasimhan factors, every object `F` of the thin interval
`P((t - 1/4, t + 1/4))` therefore has nonnegative rotated real part `ρ F`,
positive when `F` is nonzero, and the support property gives
`‖class F‖ ≤ 2 K ρ F`.

Strict subobjects `A` of an interval object `E` fit into strict short exact
sequences inside the interval, so `ρ` is additive along them. Hence `ρ A ≤ ρ E`
bounds the classes of strict subobjects in a ball, finitely many by
discreteness, and `ρ` strictly increases along a strictly increasing pair of
strict subobjects. A strictly monotone map with finite range forces both chain
conditions. This bounds strict chains in the interval category itself; it is
not a bound on the HN factors of a single object.

## References

* arXiv:1902.08184v4 (Bayer, Lahoz, Macrì, Nuer, Perry, Stellari), Definition
  12.2 and Remark 12.3.
* Bayer, Macrì, Stellari, *The space of stability conditions on abelian
  threefolds, and on some Calabi-Yau threefolds* (2016), Appendix A.
* Kontsevich, Soibelman, *Stability structures, motivic Donaldson-Thomas
  invariants and cluster transformations* (2008).

## Tags

stability condition, support property, local finiteness, quadratic form
-/

noncomputable section

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ V : Type*} [AddCommGroup Λ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {v : K₀ C →+ Λ}

/-- The real part of the charge rotated so that phase `t` points along the
positive real axis. -/
private def sectorRe (σ : WithClassMap C v) (t : ℝ) : K₀ C →+ ℝ :=
  Complex.reAddGroupHom.comp
    ((AddMonoidHom.mulLeft (Complex.exp (-((Real.pi * t : ℝ) * Complex.I)))).comp
      (σ.Z.comp v))

private theorem sectorRe_apply (σ : WithClassMap C v) (t : ℝ) (x : K₀ C) :
    sectorRe σ t x = (Complex.exp (-((Real.pi * t : ℝ) * Complex.I)) * σ.Z (v x)).re :=
  rfl

/-- A nonzero semistable object of phase within `1/3` of `t` has nonzero
charge, and the rotated real part of that charge is at least half its norm. -/
private theorem sectorRe_of_semistable (σ : WithClassMap C v) {t φ : ℝ}
    (hφ : |φ - t| ≤ 1 / 3) {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    0 < ‖σ.Z (v (K₀.of C E))‖ ∧
      ‖σ.Z (v (K₀.of C E))‖ ≤ 2 * sectorRe σ t (K₀.of C E) := by
  obtain ⟨m, hm, hZ⟩ := σ.compatible φ E hP hE
  have hrot : Complex.exp (-((Real.pi * t : ℝ) * Complex.I)) *
      ((m : ℂ) * Complex.exp ((Real.pi * φ : ℝ) * Complex.I)) =
        (m : ℂ) * Complex.exp ((Real.pi * (φ - t) : ℝ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hnorm : ‖σ.Z (v (K₀.of C E))‖ = m := by
    rw [hZ, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_of_nonneg hm.le, mul_one]
  have hre : sectorRe σ t (K₀.of C E) = m * Real.cos (Real.pi * (φ - t)) := by
    rw [sectorRe_apply, hZ, hrot, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hθ : |Real.pi * (φ - t)| ≤ Real.pi / 3 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hcos : 1 / 2 ≤ Real.cos (Real.pi * (φ - t)) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [Real.pi_pos]) hθ
    rwa [Real.cos_abs, Real.cos_pi_div_three] at h
  rw [hnorm, hre]
  exact ⟨hm, by nlinarith⟩

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The sector estimate.** Every object of the thin interval of radius
`1/4` around `t` has nonnegative rotated real part, positive when the object
is nonzero, and the support bound controls the norm of its class by that real
part. -/
private theorem sectorRe_of_intervalProp (σ : WithClassMap C v) (w : K₀ C →+ V)
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ φ E, σ.slicing.P φ E → ¬IsZero E →
      ‖w (K₀.of C E)‖ ≤ K * ‖σ.Z (v (K₀.of C E))‖)
    (t : ℝ) {E : C} (hE : σ.slicing.intervalProp C (t - 1 / 4) (t + 1 / 4) E) :
    0 ≤ sectorRe σ t (K₀.of C E) ∧
      ‖w (K₀.of C E)‖ ≤ 2 * K * sectorRe σ t (K₀.of C E) ∧
      (¬IsZero E → 0 < sectorRe σ t (K₀.of C E)) := by
  rcases hE with hzero | ⟨F, hF⟩
  · rw [K₀.of_isZero C hzero]
    exact ⟨by simp, by simp, fun h => absurd hzero h⟩
  have hfac : ∀ j, 0 ≤ sectorRe σ t (K₀.of C (F.factor j)) ∧
      ‖w (K₀.of C (F.factor j))‖ ≤ 2 * K * sectorRe σ t (K₀.of C (F.factor j)) ∧
      (¬IsZero (F.factor j) → 0 < sectorRe σ t (K₀.of C (F.factor j))) := by
    intro j
    by_cases hj : IsZero (F.factor j)
    · rw [K₀.of_isZero C hj]
      exact ⟨by simp, by simp, fun h => absurd hj h⟩
    have hφ : |F.φ j - t| ≤ 1 / 3 := by
      rw [abs_le]
      constructor <;> linarith [(hF j).1, (hF j).2]
    obtain ⟨hpos, hle⟩ := sectorRe_of_semistable σ hφ (F.semistable j) hj
    have hw := hb _ _ (F.semistable j) hj
    refine ⟨by linarith, ?_, fun _ => by linarith⟩
    calc ‖w (K₀.of C (F.factor j))‖ ≤ K * ‖σ.Z (v (K₀.of C (F.factor j)))‖ := hw
      _ ≤ K * (2 * sectorRe σ t (K₀.of C (F.factor j))) :=
        mul_le_mul_of_nonneg_left hle hK
      _ = 2 * K * sectorRe σ t (K₀.of C (F.factor j)) := by ring
  rw [K₀.of_postnikovTower_eq_sum C F.toPostnikovTower, map_sum, map_sum]
  refine ⟨Finset.sum_nonneg fun j _ => (hfac j).1, ?_, fun hEz => ?_⟩
  · calc ‖∑ j, w (K₀.of C (F.factor j))‖ ≤ ∑ j, ‖w (K₀.of C (F.factor j))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, 2 * K * sectorRe σ t (K₀.of C (F.factor j)) :=
          Finset.sum_le_sum fun j _ => (hfac j).2.1
      _ = 2 * K * ∑ j, sectorRe σ t (K₀.of C (F.factor j)) := by
          rw [Finset.mul_sum]
  · obtain ⟨j, hj⟩ := HNFiltration.exists_nonzero_factor C F hEz
    exact Finset.sum_pos' (fun j _ => (hfac j).1) ⟨j, Finset.mem_univ _, (hfac j).2.2 hj⟩

variable [IsTriangulated C]

open WeakStabilityCondition.StabilityCondition in
/-- **Local finiteness from the support property**, norm-bound form.

`w` sends `K₀` to a finite-dimensional real space with discrete image, `Zlin`
is a real-linear charge on that space realizing `σ.Z`, and the support
property bounds `‖w E‖` by a multiple of `‖Zlin (w E)‖` on nonzero semistable
objects. Then every thin interval of radius `1/4` has finite length. -/
theorem isLocallyFinite_of_hasSupportProperty (σ : WithClassMap C v)
    (w : K₀ C →+ V) (hw : DiscreteTopology (Set.range w)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ x, Zlin (w x) = σ.Z (v x))
    (h : WeakStabilityCondition.Support.HasSupportProperty Zlin
      {x | ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = w (K₀.of C E)}) :
    σ.slicing.IsLocallyFinite C := by
  obtain ⟨K, hK, hbound⟩ := h
  have hb : ∀ φ E, σ.slicing.P φ E → ¬IsZero E →
      ‖w (K₀.of C E)‖ ≤ K * ‖σ.Z (v (K₀.of C E))‖ := fun φ E hP hE => by
    rw [← hZ]
    exact hbound _ ⟨φ, E, hP, hE, rfl⟩
  refine Slicing.IsLocallyFinite.of_strictFiniteLength C σ.slicing (η := 1 / 4)
    (by norm_num) (by norm_num) fun t E => ?_
  have : Fact (t - 1 / 4 < t + 1 / 4) := ⟨by linarith⟩
  have : Fact ((t + 1 / 4) - (t - 1 / 4) ≤ 1) := ⟨by linarith⟩
  have hest := fun {F : C} (hF : σ.slicing.intervalProp C (t - 1 / 4) (t + 1 / 4) F) =>
    sectorRe_of_intervalProp σ w hK.le hb t hF
  let ρ := sectorRe σ t
  let cls : StrictSubobject E → K₀ C := fun A =>
    K₀.of C (A.1 : σ.slicing.IntervalCat C (t - 1 / 4) (t + 1 / 4)).obj
  have hses : ∀ {X Y : σ.slicing.IntervalCat C (t - 1 / 4) (t + 1 / 4)} (f : X ⟶ Y),
      IsStrictMono f → K₀.of C Y.obj = K₀.of C X.obj + K₀.of C (cokernel f).obj :=
    fun f hf => Slicing.IntervalCat.K₀_of_strictShortExact C σ.slicing
      (Deformation.Slicing.IntervalCat.strictShortExact_cokernel C f hf)
  have hmono : StrictMono fun A => ρ (cls A) := by
    intro A B hAB
    have hle : A.1 ≤ B.1 := hAB.le
    let i := Subobject.ofLE A.1 B.1 hle
    have hi : IsStrictMono i := by
      let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := σ.slicing)
        (t - 1 / 4) (t + 1 / 4) (Fact.out : (t + 1 / 4) - (t - 1 / 4) ≤ 1)
      have : Mono (FR.map A.1.arrow) :=
        Slicing.IntervalCat.mono_toRightHeart_of_strictMono C σ.slicing _ A.2
      have : Mono (FR.map i) := mono_of_mono_fac (f := FR.map B.1.arrow) (by
        rw [← FR.map_comp, Subobject.ofLE_arrow])
      exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart C σ.slicing i
    have hne : ¬IsZero (cokernel i).obj := by
      intro hz
      have : Epi i := Preadditive.epi_of_isZero_cokernel i
        (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hz)
      have : IsIso i := hi.isIso
      exact hAB.ne (Subtype.ext (Subobject.eq_of_comm (asIso i) (Subobject.ofLE_arrow hle)))
    have hpos := (hest (cokernel i).property).2.2 hne
    change ρ (cls A) < ρ (cls B)
    rw [show cls B = cls A + K₀.of C (cokernel i).obj from hses i hi, map_add]
    linarith
  have hρE : ∀ A, ρ (cls A) ≤ ρ (K₀.of C E.obj) := fun A => by
    rw [hses A.1.arrow A.2, map_add]
    linarith [(hest (cokernel A.1.arrow).property).1]
  have hfin : (Set.range fun A => ρ (cls A)).Finite := by
    refine ((finite_range_inter_closedBall w hw (2 * K * ρ (K₀.of C E.obj))).image
      fun x => (Complex.exp (-((Real.pi * t : ℝ) * Complex.I)) * Zlin x).re).subset ?_
    rintro _ ⟨A, rfl⟩
    refine ⟨w (cls A), ⟨⟨cls A, rfl⟩, ?_⟩, ?_⟩
    · exact (hest (A.1 : σ.slicing.IntervalCat C (t - 1 / 4) (t + 1 / 4)).property).2.1.trans
        (mul_le_mul_of_nonneg_left (hρE A) (by positivity))
    · simp only [ρ, sectorRe_apply, hZ]
  have : Finite (Set.range fun A => ρ (cls A)) := hfin.to_subtype
  have hg : StrictMono (Set.rangeFactorization fun A => ρ (cls A)) :=
    fun _ _ hAB => hmono hAB
  exact ⟨ObjectProperty.is_of_prop _ hg.wellFoundedLT,
    ObjectProperty.is_of_prop _ hg.wellFoundedGT⟩

/-- **Remark 12.3, second paragraph.** A pre-stability condition whose
classes, pushed into `V` along `ι` with discrete image, satisfy the support
property for a genuine quadratic form is locally finite.

`Zlin` realizes the central charge on `Λ` through `ι`, and the selected locus
is `ι` applied to the classes of nonzero semistable objects. -/
theorem isLocallyFinite_of_quadraticSupport (σ : WithClassMap C v)
    (ι : Λ →+ V) (hι : DiscreteTopology (Set.range ι)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ x, Zlin (ι x) = σ.Z x)
    (h : HasQuadraticSupportProperty Zlin
      {x | ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = ι (v (K₀.of C E))}) :
    σ.slicing.IsLocallyFinite C :=
  isLocallyFinite_of_hasSupportProperty σ (ι.comp v)
    (DiscreteTopology.of_subset hι (Set.range_comp_subset_range v ι)) Zlin
    (fun x => hZ (v x)) h.hasSupportProperty

/-- **A pre-stability condition with the support property is a stability
condition.**

Definition 12.2(iii) of arXiv:1902.08184v4 calls a pre-stability condition
with the support property a *stability condition*. This maps such data into
the repository's Bridgeland `StabilityCondition.WithClassMap`, whose
`locallyFinite` field is filled by `isLocallyFinite_of_quadraticSupport`. -/
def toStabilityCondition_of_quadraticSupport (σ : WithClassMap C v)
    (ι : Λ →+ V) (hι : DiscreteTopology (Set.range ι)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ x, Zlin (ι x) = σ.Z x)
    (h : HasQuadraticSupportProperty Zlin
      {x | ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = ι (v (K₀.of C E))}) :
    StabilityCondition.WithClassMap C v where
  toWithClassMap := σ
  locallyFinite := isLocallyFinite_of_quadraticSupport σ ι hι Zlin hZ h

@[simp]
theorem toStabilityCondition_of_quadraticSupport_toWithClassMap (σ : WithClassMap C v)
    (ι : Λ →+ V) (hι : DiscreteTopology (Set.range ι)) (Zlin : V →ₗ[ℝ] ℂ)
    (hZ : ∀ x, Zlin (ι x) = σ.Z x)
    (h : HasQuadraticSupportProperty Zlin
      {x | ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = ι (v (K₀.of C E))}) :
    (σ.toStabilityCondition_of_quadraticSupport ι hι Zlin hZ h).toWithClassMap = σ :=
  rfl

/-- Ordinary quadratic support for a class map into `V` with discrete image
gives local finiteness. -/
theorem QuadraticSupportData.isLocallyFinite {u : K₀ C →+ V}
    {σ : WithClassMap C u} {Zlin : V →ₗ[ℝ] ℂ} (h : σ.QuadraticSupportData Zlin)
    (hu : DiscreteTopology (Set.range u)) : σ.slicing.IsLocallyFinite C :=
  isLocallyFinite_of_hasSupportProperty σ u hu Zlin
    (fun x => h.charge_compatible (u x)) h.hasSupportProperty

/-- The Bridgeland stability condition carried by ordinary quadratic support
over a class map with discrete image. -/
def QuadraticSupportData.toStabilityCondition {u : K₀ C →+ V}
    {σ : WithClassMap C u} {Zlin : V →ₗ[ℝ] ℂ} (h : σ.QuadraticSupportData Zlin)
    (hu : DiscreteTopology (Set.range u)) : StabilityCondition.WithClassMap C u where
  toWithClassMap := σ
  locallyFinite := h.isLocallyFinite hu

@[simp]
theorem QuadraticSupportData.toStabilityCondition_toWithClassMap {u : K₀ C →+ V}
    {σ : WithClassMap C u} {Zlin : V →ₗ[ℝ] ℂ} (h : σ.QuadraticSupportData Zlin)
    (hu : DiscreteTopology (Set.range u)) :
    (h.toStabilityCondition hu).toWithClassMap = σ :=
  rfl

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
