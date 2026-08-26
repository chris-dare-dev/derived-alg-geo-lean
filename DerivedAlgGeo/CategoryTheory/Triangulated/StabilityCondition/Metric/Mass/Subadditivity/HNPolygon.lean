/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.FiniteSums
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.Uniqueness
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.Interval.Set.Monotone

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Harder--Narasimhan polygon paths for mass subadditivity

This file supplies the algebraic path underlying the HN polygon of an object in
an abelian category with a stability function.  Its vertices are the charges of
the subobjects in an abelian HN filtration.  Consecutive edge vectors are
proved to be the charges of the semistable factors, so the polygonal path
length is exactly the usual sum of factor masses.

Convex-hull containment under monomorphisms, strict support of interior path
vertices, and the semistable-descent/maximal-phase algebra needed for the
ambient boundary theorem are proved separately below; none is hidden inside
the path representation.  The support-completeness theorem for every
positive-angle direction is stated explicitly and avoids identifying the
whole ambient polygon with the closed HN vertex hull, which is false in
general.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits Complex
open scoped BigOperators

namespace CategoryTheory.Triangulated

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The HN polygon of an object: the convex hull of the charges of all its
subobjects.  This is the paper's ambient polygon; a chosen HN filtration below
provides its distinguished decreasing-phase boundary path. -/
def StabilityFunction.hnPolygon (Z : StabilityFunction A) (E : A) : Set ℂ :=
  convexHull ℝ (Set.range fun S : Subobject E ↦ Z.charge (S : A))

/-- Every subobject charge is a point of the HN polygon. -/
theorem StabilityFunction.subobjectCharge_mem_hnPolygon
    (Z : StabilityFunction A) (E : A) (S : Subobject E) :
    Z.charge (S : A) ∈ Z.hnPolygon E :=
  subset_convexHull ℝ (Set.range fun T : Subobject E ↦ Z.charge (T : A))
    (Set.mem_range_self S)

/-- A monomorphism induces inclusion of HN polygons: pushing a subobject
forward along the monomorphism does not change its underlying object up to
isomorphism, hence does not change its charge. -/
theorem StabilityFunction.hnPolygon_mono {X Y : A} (Z : StabilityFunction A)
    (f : X ⟶ Y) [Mono f] : Z.hnPolygon X ⊆ Z.hnPolygon Y := by
  apply convexHull_mono
  rintro _ ⟨S, rfl⟩
  let T : Subobject Y := (Subobject.map f).obj S
  have hmap : T = Subobject.mk (S.arrow ≫ f) := by
    calc
      (Subobject.map f).obj S =
          (Subobject.map f).obj (Subobject.mk S.arrow) := by
        rw [Subobject.mk_arrow]
      _ = Subobject.mk (S.arrow ≫ f) := Subobject.map_mk S.arrow f
  let e : (T : A) ≅ (S : A) :=
    Subobject.isoOfEqMk T (S.arrow ≫ f) hmap
  refine ⟨T, ?_⟩
  exact Z.charge_eq_of_iso e

namespace ComplexPolygonalPath

/-- The oriented area functional `z ↦ r × z`, regarded as a continuous
real-linear functional on the complex plane. -/
def crossFunctional (r : ℂ) : ℂ →L[ℝ] ℝ :=
  r.re • Complex.imCLM - r.im • Complex.reCLM

@[simp]
theorem crossFunctional_apply (r z : ℂ) :
    crossFunctional r z = r.re * z.im - r.im * z.re := by
  simp [crossFunctional]

/-- The unit complex vector at angle `θ`. -/
def unitRay (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

@[simp]
theorem unitRay_re (θ : ℝ) : (unitRay θ).re = Real.cos θ := by
  simp only [unitRay, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, add_zero]

@[simp]
theorem unitRay_im (θ : ℝ) : (unitRay θ).im = Real.sin θ := by
  simp only [unitRay, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, zero_add, add_zero]

/-- A unit ray at an angle strictly between `0` and `π` lies in the open
upper half-plane. -/
theorem unitRay_mem_semiClosedUpperHalfPlane {θ : ℝ} (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) : unitRay θ ∈ semiClosedUpperHalfPlane := by
  rw [semiClosedUpperHalfPlane]
  exact Or.inl (by
    change 0 < (unitRay θ).im
    rw [unitRay_im]
    exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ)

/-- On the principal upper-half-plane branch, the argument of `unitRay θ` is
literally `θ`. -/
theorem arg_unitRay {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    Complex.arg (unitRay θ) = θ := by
  unfold unitRay
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hθπ.le⟩

/-- The cross functional is positive on a vector of strictly larger
upper-half-plane argument. -/
theorem crossFunctional_pos_of_arg_lt {r z : ℂ}
    (hr : r ∈ semiClosedUpperHalfPlane) (hz : z ∈ semiClosedUpperHalfPlane)
    (harg : Complex.arg r < Complex.arg z) :
    0 < crossFunctional r z := by
  rw [crossFunctional_apply]
  exact cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hr)
    (semiClosedUpperHalfPlane_ne_zero hr) (semiClosedUpperHalfPlane_ne_zero hz) harg

/-- The cross functional is negative on a vector of strictly smaller
upper-half-plane argument. -/
theorem crossFunctional_neg_of_arg_lt {r z : ℂ}
    (hr : r ∈ semiClosedUpperHalfPlane) (hz : z ∈ semiClosedUpperHalfPlane)
    (harg : Complex.arg z < Complex.arg r) :
    crossFunctional r z < 0 := by
  have hpos := cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    (semiClosedUpperHalfPlane_ne_zero hz) (semiClosedUpperHalfPlane_ne_zero hr) harg
  rw [crossFunctional_apply]
  linarith

/-- At every interior vertex of a finite path whose upper-half-plane edge
arguments strictly decrease, some real-linear functional has a strict unique
maximum among the path vertices.  This is the supporting-hyperplane form of
strict clockwise convexity. -/
theorem exists_strict_support_at_interior {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ j, j ≠ k → l (z j) < l (z k) := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by omega⟩
  have hiPrev_lt_iNext : iPrev < iNext := by
    simp only [iPrev, iNext, Fin.mk_lt_mk]
    omega
  have hargNext_lt_argPrev :
      Complex.arg (z iNext.succ - z iNext.castSucc) <
        Complex.arg (z iPrev.succ - z iPrev.castSucc) :=
    harg hiPrev_lt_iNext
  let θ : ℝ :=
    (Complex.arg (z iPrev.succ - z iPrev.castSucc) +
      Complex.arg (z iNext.succ - z iNext.castSucc)) / 2
  have hargNext_lt_θ : Complex.arg (z iNext.succ - z iNext.castSucc) < θ := by
    dsimp [θ]
    linarith
  have hθ_lt_argPrev : θ < Complex.arg (z iPrev.succ - z iPrev.castSucc) := by
    dsimp [θ]
    linarith
  have hθ₀ : 0 < θ :=
    (arg_pos_of_mem_semiClosedUpperHalfPlane (hedge iNext)).trans hargNext_lt_θ
  have hθπ : θ < Real.pi :=
    hθ_lt_argPrev.trans_le (Complex.arg_le_pi _)
  let r : ℂ := unitRay θ
  let l : ℂ →L[ℝ] ℝ := crossFunctional r
  have hr : r ∈ semiClosedUpperHalfPlane := by
    exact unitRay_mem_semiClosedUpperHalfPlane hθ₀ hθπ
  have hr_arg : Complex.arg r = θ := by
    exact arg_unitRay hθ₀ hθπ
  have hstep_before : ∀ m : Fin (n + 1), m < k →
      l (z m) < l (z (Order.succ m)) := by
    intro m hm
    let i : Fin n := ⟨m.1, by omega⟩
    have hi_le : i ≤ iPrev := by
      simp only [i, iPrev, Fin.mk_le_mk]
      omega
    have hθ_lt_arg_i : θ < Complex.arg (z i.succ - z i.castSucc) :=
      hθ_lt_argPrev.trans_le (harg.antitone hi_le)
    have hpos : 0 < l (z i.succ - z i.castSucc) := by
      exact crossFunctional_pos_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact hθ_lt_arg_i)
    have hm_eq : m = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hm_eq, Fin.orderSucc_castSucc]
    rw [map_sub] at hpos
    linarith
  have hstep_after : ∀ m : Fin (n + 1), k < m →
      l (z m) < l (z (Order.pred m)) := by
    intro m hm
    let i : Fin n := ⟨m.1 - 1, by omega⟩
    have hi_ge : iNext ≤ i := by
      simp only [iNext, i, Fin.mk_le_mk]
      omega
    have harg_i_lt_θ : Complex.arg (z i.succ - z i.castSucc) < θ :=
      (harg.antitone hi_ge).trans_lt hargNext_lt_θ
    have hneg : l (z i.succ - z i.castSucc) < 0 := by
      exact crossFunctional_neg_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact harg_i_lt_θ)
    have hm_eq : m = i.succ := by
      apply Fin.ext
      simp only [i, Fin.succ_mk]
      omega
    rw [hm_eq, Fin.orderPred_succ]
    rw [map_sub] at hneg
    linarith
  have hmono : StrictMonoOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Iic k) :=
    strictMonoOn_Iic_of_lt_succ hstep_before
  have hanti : StrictAntiOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Ici k) :=
    strictAntiOn_Ici_of_lt_pred hstep_after
  refine ⟨l, fun j hj ↦ ?_⟩
  rcases lt_or_gt_of_ne hj with hjk | hkj
  · exact hmono (Set.mem_Iic.mpr hjk.le) (Set.mem_Iic.mpr le_rfl) hjk
  · exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hkj.le) hkj

/-- The sum of the directed edges of a finite path is its endpoint
displacement. -/
theorem sum_edges_eq_last_sub_zero {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ∑ i : Fin n, (z i.succ - z i.castSucc) = z (Fin.last n) - z 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      rw [Fin.sum_univ_castSucc]
      rw [show (∑ x : Fin n, (z x.castSucc.succ - z x.castSucc.castSucc)) =
        z' (Fin.last n) - z' 0 by simpa [z'] using ih z']
      change z (Fin.last n).castSucc - z 0 +
          (z (Fin.last n).succ - z (Fin.last n).castSucc) =
        z (Fin.last (n + 1)) - z 0
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hlast]
      ring

/-- For an upper-half-plane path with decreasing edge arguments, the
argument of its total displacement is bounded above by the argument of its
first edge. -/
theorem arg_last_sub_zero_le_arg_first {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hn : 0 < n)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : Antitone (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc))) :
    Complex.arg (z (Fin.last n) - z 0) ≤
      Complex.arg (z (Fin.succ ⟨0, hn⟩) - z (Fin.castSucc ⟨0, hn⟩)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← sum_edges_eq_last_sub_zero]
  refine (arg_sum_le_sup_of_semiClosedUpperHalfPlane hs (fun i _ ↦ hedge i)).trans ?_
  apply Finset.sup'_le hs
  intro i _
  exact harg (Fin.zero_le i)

/-- For an upper-half-plane path with decreasing edge arguments, the
argument of its last edge is bounded above by the argument of its total
displacement. -/
theorem arg_last_edge_le_arg_last_sub_zero {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hn : 0 < n)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : Antitone (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc))) :
    Complex.arg
        (z (Fin.succ ⟨n - 1, by omega⟩) - z (Fin.castSucc ⟨n - 1, by omega⟩)) ≤
      Complex.arg (z (Fin.last n) - z 0) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← sum_edges_eq_last_sub_zero]
  have hlast_le_inf :
      Complex.arg (z (Fin.succ ⟨n - 1, by omega⟩) -
          z (Fin.castSucc ⟨n - 1, by omega⟩)) ≤
        s.inf' hs (Complex.arg ∘ fun i : Fin n ↦
          z i.succ - z i.castSucc) := by
    apply Finset.le_inf'
    intro i _
    exact harg (Fin.mk_le_mk.mpr (by omega))
  exact hlast_le_inf.trans
    (inf_le_arg_sum_of_semiClosedUpperHalfPlane hs (fun i _ ↦ hedge i))

/-- The Euclidean length of a finite path in the complex plane.  A path with
`n` edges is represented by its `n + 1` vertices. -/
def length {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin n, ‖z i.succ - z i.castSucc‖

/-- The straight chord between the endpoints of a finite complex path is no
longer than the path.  This is the metric primitive used when an HN polygonal
boundary is refined by inserting further vertices. -/
theorem norm_last_sub_zero_le_length {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ‖z (Fin.last n) - z 0‖ ≤ length z := by
  induction n with
  | zero => simp [length]
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      have htriangle :
          ‖z (Fin.last (n + 1)) - z 0‖ ≤
            ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
              ‖z (Fin.last n).castSucc - z 0‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (z (Fin.last (n + 1)) - z (Fin.last n).castSucc)
          (z (Fin.last n).castSucc - z 0)
      calc
        ‖z (Fin.last (n + 1)) - z 0‖
            ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
                ‖z (Fin.last n).castSucc - z 0‖ := htriangle
        _ ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ + length z' :=
          by
            simpa [z'] using add_le_add_left (ih z')
              ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖
        _ = length z := by
          unfold length
          rw [Fin.sum_univ_castSucc]
          simp [z', add_comm]

end ComplexPolygonalPath

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E : A} (F : AbelianHNFiltration Z E)

/-- Pulling the image of `S → E/M` back to `E` recovers `S` when
`M ≤ S`.  This is the subobject correspondence needed to transport an HN
tail to a quotient. -/
private theorem pullback_image_to_quotient_eq (Z : StabilityFunction A)
    {M S : Subobject E}
    (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  exact CategoryTheory.Triangulated.AbelianHNFiltration.pullback_imageSubobject_eq
    Z hMS

/-- The image subobject of an epimorphism is the top subobject. -/
private theorem imageSubobject_eq_top_of_epi {X Y : A} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = ⊤ := by
  haveI : Epi (imageSubobject f).arrow := epi_of_epi_fac (imageSubobject_arrow_comp f)
  haveI : IsIso (imageSubobject f).arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

/-- The tail of an HN filtration after the `k`-th vertex, transported to the
quotient by that vertex.  Its factors are precisely the original factors at
indices `k, ..., n - 1`. -/
noncomputable def quotientHNFiltration {k : ℕ} (hk : k < F.n) :
    AbelianHNFiltration Z
      (cokernel (F.chain ⟨k, by omega⟩).arrow) where
  n := F.n - k
  nonempty := Nat.sub_pos_of_lt hk
  chain := fun ⟨j, _⟩ ↦ imageSubobject
    ((F.chain ⟨k + j, by omega⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by omega⟩).arrow)
  chain_strictMono := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro ⟨j, hj⟩
    change imageSubobject ((F.chain ⟨k + j, by omega⟩).arrow ≫
        cokernel.π (F.chain ⟨k, by omega⟩).arrow) <
      imageSubobject ((F.chain ⟨k + (j + 1), by omega⟩).arrow ≫
        cokernel.π (F.chain ⟨k, by omega⟩).arrow)
    have hM₁ : F.chain ⟨k, by omega⟩ ≤ F.chain ⟨k + j, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hM₂ : F.chain ⟨k, by omega⟩ ≤ F.chain ⟨k + (j + 1), by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hS₁S₂ : F.chain ⟨k + j, by omega⟩ <
        F.chain ⟨k + (j + 1), by omega⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
    have hle : imageSubobject ((F.chain ⟨k + j, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by omega⟩).arrow) ≤
        imageSubobject ((F.chain ⟨k + (j + 1), by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by omega⟩).arrow) := by
      rw [show (F.chain ⟨k + j, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨k, by omega⟩).arrow =
          Subobject.ofLE _ _ hS₁S₂.le ≫
            ((F.chain ⟨k + (j + 1), by omega⟩).arrow ≫
              cokernel.π (F.chain ⟨k, by omega⟩).arrow) from by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact lt_of_le_of_ne hle (fun heq ↦ absurd
      ((pullback_image_to_quotient_eq Z hM₁).symm.trans
        (heq ▸ pullback_image_to_quotient_eq Z hM₂))
      (ne_of_lt hS₁S₂))
  chain_bot := by
    change imageSubobject ((F.chain ⟨k, by omega⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by omega⟩).arrow) = ⊥
    rw [cokernel.condition, imageSubobject_zero]
  chain_top := by
    change imageSubobject ((F.chain ⟨k + (F.n - k), by omega⟩).arrow ≫
      cokernel.π (F.chain ⟨k, by omega⟩).arrow) = ⊤
    have hidx : k + (F.n - k) = F.n := Nat.add_sub_of_le hk.le
    have htop : F.chain ⟨k + (F.n - k), by omega⟩ = ⊤ := by
      have hi : (⟨k + (F.n - k), by omega⟩ : Fin (F.n + 1)) =
          ⟨F.n, Nat.lt_succ_self F.n⟩ := Fin.ext hidx
      rw [hi, F.chain_top]
    rw [htop]
    haveI : IsIso (⊤ : Subobject E).arrow := inferInstance
    rw [imageSubobject_iso_comp]
    exact imageSubobject_eq_top_of_epi _
  phase := fun ⟨j, _⟩ ↦ F.phase ⟨k + j, by omega⟩
  phase_strictAnti := by
    intro ⟨j₁, _⟩ ⟨j₂, _⟩ h
    exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by
      simp only [Fin.lt_def] at h
      omega))
  factor_phase := by
    intro ⟨j, hj⟩
    exact ((AbelianHNFiltration.phase_cokernel_pullback_eq Z (F.chain ⟨k, by omega⟩) _).symm.trans
      ((StabilityFunction.phase_cokernel_ofLE_congr Z
        (pullback_image_to_quotient_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))))
        (pullback_image_to_quotient_eq Z
          (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))))).trans
      (F.factor_phase ⟨k + j, by omega⟩)))
  factor_semistable := by
    intro ⟨j, hj⟩
    have hM₁ : F.chain ⟨k, by omega⟩ ≤ F.chain ⟨k + j, by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hM₂ : F.chain ⟨k, by omega⟩ ≤ F.chain ⟨k + (j + 1), by omega⟩ :=
      F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by omega))
    have hS₁S₂ : F.chain ⟨k + j, by omega⟩ <
        F.chain ⟨k + (j + 1), by omega⟩ :=
      F.chain_strictMono (Fin.mk_lt_mk.mpr (by omega))
    have hle : imageSubobject ((F.chain ⟨k + j, by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by omega⟩).arrow) ≤
        imageSubobject ((F.chain ⟨k + (j + 1), by omega⟩).arrow ≫
          cokernel.π (F.chain ⟨k, by omega⟩).arrow) := by
      rw [show (F.chain ⟨k + j, by omega⟩).arrow ≫
            cokernel.π (F.chain ⟨k, by omega⟩).arrow =
          Subobject.ofLE _ _ hS₁S₂.le ≫
            ((F.chain ⟨k + (j + 1), by omega⟩).arrow ≫
              cokernel.π (F.chain ⟨k, by omega⟩).arrow) from by
        rw [← Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_comp_le _ _
    exact Z.isSemistable_of_iso
      (AbelianHNFiltration.cokernelPullbackIso Z (F.chain ⟨k, by omega⟩)
        (lt_of_le_of_ne hle (fun heq ↦ absurd
          ((pullback_image_to_quotient_eq Z hM₁).symm.trans
            (heq ▸ pullback_image_to_quotient_eq Z hM₂))
          (ne_of_lt hS₁S₂))))
      (StabilityFunction.isSemistable_cokernel_ofLE_congr Z
        (pullback_image_to_quotient_eq Z hM₁)
        (pullback_image_to_quotient_eq Z hM₂)
        (F.factor_semistable ⟨k + j, by omega⟩))

/-- The quotient of `S` by `S ∩ K` maps canonically into `E / K`. -/
noncomputable def quotientInfToCokernel (S K : Subobject E) :
    cokernel (Subobject.ofLE (S ⊓ K) S inf_le_left) ⟶ cokernel K.arrow :=
  cokernel.desc (Subobject.ofLE (S ⊓ K) S inf_le_left)
    (S.arrow ≫ cokernel.π K.arrow) (by
      rw [← Category.assoc, Subobject.inf_comp_left]
      rw [← Subobject.inf_comp_right S K, Category.assoc, cokernel.condition,
        comp_zero])

/-- The canonical map `S / (S ∩ K) → E / K` is a monomorphism. -/
instance quotientInfToCokernel_mono (S K : Subobject E) :
    Mono (quotientInfToCokernel S K) := by
  let i : ((S ⊓ K : Subobject E) : A) ⟶ (S : A) :=
    Subobject.ofLE (S ⊓ K) S inf_le_left
  let q : (S : A) ⟶ cokernel K.arrow := S.arrow ≫ cokernel.π K.arrow
  have hiq : i ≫ q = 0 := by
    dsimp [i, q]
    rw [← Category.assoc, Subobject.inf_comp_left]
    rw [← Subobject.inf_comp_right S K, Category.assoc, cokernel.condition,
      comp_zero]
  let T : ShortComplex A := ShortComplex.mk i q hiq
  have hK : IsLimit (KernelFork.ofι K.arrow (cokernel.condition K.arrow)) :=
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel K.arrow)
      inferInstance inferInstance).fIsKernel
  have hiKernel : IsLimit (KernelFork.ofι i hiq) := by
    apply KernelFork.IsLimit.ofι'
    intro X g hg
    have hgK : (g ≫ S.arrow) ≫ cokernel.π K.arrow = 0 := by
      simpa [q, Category.assoc] using hg
    let u : X ⟶ (K : A) := hK.lift (KernelFork.ofι (g ≫ S.arrow) hgK)
    have hu : u ≫ K.arrow = g ≫ S.arrow :=
      hK.fac (KernelFork.ofι (g ≫ S.arrow) hgK) WalkingParallelPair.zero
    let c : PullbackCone S.arrow K.arrow := PullbackCone.mk g u hu.symm
    let l : X ⟶ ((S ⊓ K : Subobject E) : A) :=
      (Subobject.inf_isPullback S K).isLimit.lift c
    refine ⟨l, ?_⟩
    exact (Subobject.inf_isPullback S K).isLimit.fac c WalkingCospan.left
  have hExact : T.Exact := T.exact_of_f_is_kernel hiKernel
  change Mono (cokernel.desc i q hiq)
  exact T.exact_iff_mono_cokernel_desc.mp hExact

/-- A semistable subobject whose phase is strictly larger than every HN
factor from index `k` onward is contained in the `k`-th filtration step.
This public descent lemma is the algebraic engine behind the left boundary of
the HN polygon. -/
theorem semistable_le_chain_of_phase_gt {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) {k : ℕ} (hk : k ≤ F.n)
    (hphase : ∀ j : Fin F.n, k ≤ j.1 → F.phase j < Z.phase (B : A)) :
    B ≤ F.chain ⟨k, by omega⟩ := by
  suffices h : ∀ d m (hm : m < F.n + 1), F.n - m = d → k ≤ m →
      B ≤ F.chain ⟨m, hm⟩ from
    h (F.n - k) k (by omega) rfl le_rfl
  intro d
  induction d with
  | zero =>
      intro m hm hd _
      have hmn : m = F.n := by omega
      subst m
      rw [F.chain_top]
      exact le_top
  | succ d ih =>
      intro m hm hd hkm
      have hstep : B ≤ F.chain ⟨m + 1, by omega⟩ :=
        ih (m + 1) (by omega) (by omega) (by omega)
      let j : Fin F.n := ⟨m, by omega⟩
      have hj_succ_eq : (j.succ : Fin (F.n + 1)) = ⟨m + 1, by omega⟩ := by
        apply Fin.ext
        simp [j]
      have hle_jsucc : B ≤ F.chain j.succ := hj_succ_eq ▸ hstep
      have hcomp : Subobject.ofLE B (F.chain j.succ) hle_jsucc ≫
          cokernel.π (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
            (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))) = 0 :=
        StabilityFunction.hom_eq_zero_of_semistable_phase_gt Z hB (F.factor_semistable j)
          (F.factor_phase j ▸ hphase j (by omega)) _
      exact le_of_ofLE_comp_cokernel_zero hle_jsucc
        (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)) hcomp

/-- No nonzero semistable subobject has phase strictly above the first HN
factor. -/
theorem semistable_phase_le_first {B : Subobject E}
    (hB : Z.IsSemistable (B : A)) :
    Z.phase (B : A) ≤ F.phase ⟨0, F.nonempty⟩ := by
  by_contra hnot
  have hgt : F.phase ⟨0, F.nonempty⟩ < Z.phase (B : A) := lt_of_not_ge hnot
  have hle : B ≤ F.chain ⟨0, by omega⟩ :=
    F.semistable_le_chain_of_phase_gt hB (Nat.zero_le _) (fun j _ ↦
      lt_of_le_of_lt (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))) hgt)
  rw [F.chain_bot] at hle
  have hBbot : B = ⊥ := le_bot_iff.mp hle
  exact hB.1 ((StabilityFunction.subobject_isZero_iff_eq_bot B).2 hBbot)

/-- The object represented by the `i`-th successive quotient in an abelian HN
filtration. -/
abbrev factorObj (i : Fin F.n) : A :=
  cokernel (Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
    (le_of_lt (F.chain_strictMono i.castSucc_lt_succ)))

/-- The charge vertices of the HN polygonal path. -/
def polygonVertex (j : Fin (F.n + 1)) : ℂ := Z.charge (F.chain j : A)

/-- A directed edge of the distinguished HN polygonal path. -/
def polygonEdge (i : Fin F.n) : ℂ :=
  F.polygonVertex i.succ - F.polygonVertex i.castSucc

/-- The length of the distinguished, decreasing-phase boundary path of the HN
polygon. -/
def polygonLength : ℝ :=
  ComplexPolygonalPath.length F.polygonVertex

/-- The abelian HN mass: the sum of the norms of the factor charges. -/
def mass : ℝ := ∑ i : Fin F.n, ‖Z.charge (F.factorObj i)‖

/-- A consecutive HN polygon edge is the charge of the corresponding
semistable factor. -/
theorem polygonVertex_succ_sub (i : Fin F.n) :
    F.polygonEdge i = Z.charge (F.factorObj i) := by
  let f : (F.chain i.castSucc : A) ⟶ (F.chain i.succ : A) :=
    Subobject.ofLE (F.chain i.castSucc) (F.chain i.succ)
      (le_of_lt (F.chain_strictMono i.castSucc_lt_succ))
  haveI : Mono f := by dsimp [f]; infer_instance
  let S : ShortComplex A := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := StabilityFunction.shortExact_of_mono f
  have hadd := Z.additive S hS
  change Z.charge (F.chain i.succ : A) - Z.charge (F.chain i.castSucc : A) =
    Z.charge (cokernel f)
  change Z.charge (F.chain i.succ : A) =
    Z.charge (F.chain i.castSucc : A) + Z.charge (cokernel f) at hadd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hadd)

/-- Every HN polygon edge lies in Bridgeland's semi-closed upper
half-plane. -/
theorem polygonEdge_mem_semiClosedUpperHalfPlane (i : Fin F.n) :
    F.polygonEdge i ∈ semiClosedUpperHalfPlane := by
  rw [F.polygonVertex_succ_sub i]
  exact Z.nonzero_mem (F.factorObj i) (F.factor_semistable i).1

/-- The argument of an HN polygon edge is `π` times the phase of its
factor. -/
theorem polygonEdge_arg (i : Fin F.n) :
    Complex.arg (F.polygonEdge i) = Real.pi * F.phase i := by
  rw [F.polygonVertex_succ_sub i]
  calc
    Complex.arg (Z.charge (F.factorObj i)) =
        Real.pi * Z.phase (F.factorObj i) := by
      unfold CategoryTheory.Triangulated.StabilityFunction.phase
      field_simp
    _ = Real.pi * F.phase i := by rw [F.factor_phase i]

/-- HN polygon edges turn strictly clockwise: their arguments strictly
decrease along the filtration. -/
theorem polygonEdge_arg_strictAnti :
    StrictAnti (fun i : Fin F.n ↦ Complex.arg (F.polygonEdge i)) := by
  intro i j hij
  change Complex.arg (F.polygonEdge j) < Complex.arg (F.polygonEdge i)
  rw [F.polygonEdge_arg j, F.polygonEdge_arg i]
  exact mul_lt_mul_of_pos_left (F.phase_strictAnti hij) Real.pi_pos

/-- Every interior HN vertex is a strict supporting point of the distinguished
HN path: a continuous real-linear functional has a unique maximum there among
all path vertices.  This is the path-level extremality input used by HN-polygon
containment arguments. -/
theorem polygonVertex_exists_strict_support (k : Fin (F.n + 1)) (hk₀ : 0 < k)
    (hkn : k < Fin.last F.n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ j, j ≠ k →
      l (F.polygonVertex j) < l (F.polygonVertex k) := by
  apply ComplexPolygonalPath.exists_strict_support_at_interior F.polygonVertex
    (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
    F.polygonEdge_arg_strictAnti k hk₀ hkn

/-- The length of the HN polygonal boundary is exactly its factor mass. -/
theorem polygonLength_eq_mass : F.polygonLength = F.mass := by
  unfold polygonLength ComplexPolygonalPath.length mass
  apply Finset.sum_congr rfl
  intro i _
  rw [show F.polygonVertex i.succ - F.polygonVertex i.castSucc =
    F.polygonEdge i from rfl, F.polygonVertex_succ_sub i]

/-- The initial HN polygon vertex is the origin. -/
@[simp]
theorem polygonVertex_zero : F.polygonVertex 0 = 0 := by
  unfold polygonVertex
  have hbot : F.chain 0 = ⊥ := by
    simpa using F.chain_bot
  rw [hbot]
  exact Z.map_zero _ ((StabilityFunction.subobject_isZero_iff_eq_bot _).2 rfl)

/-- The terminal HN polygon vertex is the charge of the filtered object. -/
@[simp]
theorem polygonVertex_last :
    F.polygonVertex ⟨F.n, Nat.lt_succ_self F.n⟩ = Z.charge E := by
  unfold polygonVertex
  rw [F.chain_top]
  exact Z.charge_eq_of_iso (asIso (⊤ : Subobject E).arrow)

/-- The phase of the filtered object is at most the phase of the first HN
factor. -/
theorem phase_le_first : Z.phase E ≤ F.phase ⟨0, F.nonempty⟩ := by
  have harg := ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
    F.polygonVertex F.nonempty (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
    F.polygonEdge_arg_strictAnti.antitone
  have hlast : F.polygonVertex (Fin.last F.n) = Z.charge E := by
    exact F.polygonVertex_last
  rw [hlast, F.polygonVertex_zero, sub_zero,
    show F.polygonVertex (Fin.succ ⟨0, F.nonempty⟩) -
        F.polygonVertex (Fin.castSucc ⟨0, F.nonempty⟩) =
      F.polygonEdge ⟨0, F.nonempty⟩ from rfl,
    F.polygonVertex_succ_sub] at harg
  change Z.phase E ≤ F.phase ⟨0, F.nonempty⟩
  rw [← F.factor_phase ⟨0, F.nonempty⟩]
  unfold CategoryTheory.Triangulated.StabilityFunction.phase
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2 harg

/-- The phase of the last HN factor is at most the phase of the filtered
object. -/
theorem last_le_phase :
    F.phase ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩ ≤ Z.phase E := by
  have harg := ComplexPolygonalPath.arg_last_edge_le_arg_last_sub_zero
    F.polygonVertex F.nonempty (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
    F.polygonEdge_arg_strictAnti.antitone
  have hlast : F.polygonVertex (Fin.last F.n) = Z.charge E := by
    exact F.polygonVertex_last
  rw [hlast, F.polygonVertex_zero, sub_zero,
    show F.polygonVertex
        (Fin.succ ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩) -
        F.polygonVertex
          (Fin.castSucc ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩) =
      F.polygonEdge ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩ from rfl,
    F.polygonVertex_succ_sub] at harg
  change F.phase ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩ ≤ Z.phase E
  rw [← F.factor_phase ⟨F.n - 1, Nat.sub_lt F.nonempty Nat.one_pos⟩]
  unfold CategoryTheory.Triangulated.StabilityFunction.phase
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2 harg

/-- A nonzero map from a filtration prefix to a semistable object cannot land
strictly below the phase of the prefix's last factor.  The proof extends
zero-vanishing one HN factor at a time. -/
theorem phase_last_prefix_le_of_ne_zero_to_semistable {Q : A}
    (hQ : Z.IsSemistable Q) {k : ℕ} (hk₀ : 0 < k) (hkn : k ≤ F.n)
    (q : (F.chain ⟨k, by omega⟩ : A) ⟶ Q) (hq : q ≠ 0) :
    F.phase ⟨k - 1, by omega⟩ ≤ Z.phase Q := by
  by_contra hnot
  have hphaseQ : Z.phase Q < F.phase ⟨k - 1, by omega⟩ :=
    lt_of_not_ge hnot
  have hzero : ∀ m (hm : m ≤ k),
      Subobject.ofLE (F.chain ⟨m, by omega⟩) (F.chain ⟨k, by omega⟩)
        (F.chain_strictMono.monotone (Fin.mk_le_mk.mpr hm)) ≫ q = 0 := by
    intro m hm
    induction m with
    | zero =>
        have hbot : F.chain ⟨0, by omega⟩ = ⊥ := by
          simpa using F.chain_bot
        have hz : IsZero (F.chain ⟨0, by omega⟩ : A) :=
          (StabilityFunction.subobject_isZero_iff_eq_bot _).2 hbot
        exact zero_of_source_iso_zero _ hz.isoZero
    | succ m ih =>
        have hmk : m ≤ k := by omega
        have hmn : m < F.n := by omega
        let j : Fin F.n := ⟨m, hmn⟩
        let M : Subobject E := F.chain j.castSucc
        let N : Subobject E := F.chain j.succ
        let K : Subobject E := F.chain ⟨k, by omega⟩
        have hMN : M ≤ N := le_of_lt (F.chain_strictMono j.castSucc_lt_succ)
        have hNK : N ≤ K :=
          F.chain_strictMono.monotone (Fin.mk_le_mk.mpr (by
            omega))
        let r : (N : A) ⟶ Q := Subobject.ofLE N K hNK ≫ q
        have hfr : Subobject.ofLE M N hMN ≫ r = 0 := by
          dsimp [r, M, N, K]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
          simpa [j] using ih hmk
        let d : cokernel (Subobject.ofLE M N hMN) ⟶ Q :=
          cokernel.desc (Subobject.ofLE M N hMN) r hfr
        have hd : d = 0 := by
          dsimp [d, M, N]
          apply StabilityFunction.hom_eq_zero_of_semistable_phase_gt Z (F.factor_semistable j) hQ
          rw [F.factor_phase j]
          exact hphaseQ.trans_le (F.phase_strictAnti.antitone (Fin.mk_le_mk.mpr (by
            omega)))
        have hr : r = 0 := by
          calc
            r = cokernel.π (Subobject.ofLE M N hMN) ≫ d := by
              dsimp [d]
              exact (cokernel.π_desc (Subobject.ofLE M N hMN) r hfr).symm
            _ = 0 := by rw [hd, comp_zero]
        simpa [r, N, K, j] using hr
  have htop := hzero k le_rfl
  apply hq
  simpa only [Subobject.ofLE_refl, Category.id_comp] using htop

/-- Assuming the HN property, every nonzero subobject has phase at most the
first phase of a chosen HN filtration.  The proof takes the first HN factor of
the subobject, embeds its first filtration step into the ambient object, and
applies semistable descent. -/
theorem subobject_phase_le_first (hHN : Z.HasHNProperty) {B : Subobject E}
    (hB : B ≠ ⊥) : Z.phase (B : A) ≤ F.phase ⟨0, F.nonempty⟩ := by
  have hBzero : ¬IsZero (B : A) :=
    StabilityFunction.subobject_not_isZero_of_ne_bot hB
  obtain ⟨G⟩ := hHN (B : A) hBzero
  let i₀ : Fin G.n := ⟨0, G.nonempty⟩
  let C₁ : Subobject (B : A) := G.chain i₀.succ
  have hchainBot : G.chain i₀.castSucc = ⊥ := by
    simpa [i₀] using G.chain_bot
  have hC₁ss : Z.IsSemistable (C₁ : A) := by
    have hfactorBot :
        Z.IsSemistable (cokernel (Subobject.ofLE ⊥ C₁ bot_le)) :=
      StabilityFunction.isSemistable_cokernel_ofLE_congr Z hchainBot.symm rfl
        (G.factor_semistable i₀)
    exact Z.isSemistable_of_iso
      (StabilityFunction.subobjectCokernelBotIso C₁ bot_le) hfactorBot
  have hC₁phase : Z.phase (C₁ : A) = G.phase i₀ := by
    change Z.phase (C₁ : A) = G.phase i₀
    rw [← G.factor_phase i₀]
    exact ((StabilityFunction.phase_cokernel_ofLE_congr Z hchainBot rfl).trans
      (Z.phase_eq_of_iso
        (StabilityFunction.subobjectCokernelBotIso C₁ bot_le))).symm
  let D : Subobject E := (Subobject.map B.arrow).obj C₁
  have hmap : D = Subobject.mk (C₁.arrow ≫ B.arrow) := by
    calc
      (Subobject.map B.arrow).obj C₁ =
          (Subobject.map B.arrow).obj (Subobject.mk C₁.arrow) := by
        rw [Subobject.mk_arrow]
      _ = Subobject.mk (C₁.arrow ≫ B.arrow) :=
        Subobject.map_mk C₁.arrow B.arrow
  let e : (D : A) ≅ (C₁ : A) :=
    Subobject.isoOfEqMk D (C₁.arrow ≫ B.arrow) hmap
  have hDss : Z.IsSemistable (D : A) :=
    Z.isSemistable_of_iso e.symm hC₁ss
  calc
    Z.phase (B : A) ≤ G.phase i₀ := phase_le_first G
    _ = Z.phase (C₁ : A) := hC₁phase.symm
    _ = Z.phase (D : A) := (Z.phase_eq_of_iso e).symm
    _ ≤ F.phase ⟨0, F.nonempty⟩ := F.semistable_phase_le_first hDss

/-- Every nonzero quotient of a filtration prefix has phase at least the
phase of the prefix's last HN factor.  We compose with the last semistable
factor of an HN filtration of the quotient and use factor-by-factor
vanishing on the prefix. -/
theorem last_prefix_le_quotient_phase (hHN : Z.HasHNProperty)
    {k : ℕ} (hk₀ : 0 < k) (hkn : k ≤ F.n) {Q : A}
    (q : (F.chain ⟨k, by omega⟩ : A) ⟶ Q) [Epi q]
    (hQ : ¬IsZero Q) :
    F.phase ⟨k - 1, by omega⟩ ≤ Z.phase Q := by
  obtain ⟨G⟩ := hHN Q hQ
  let j : Fin G.n := ⟨G.n - 1, Nat.sub_lt G.nonempty Nat.one_pos⟩
  have htop : G.chain j.succ = ⊤ := by
    have hj : j.succ = ⟨G.n, Nat.lt_succ_self G.n⟩ := by
      apply Fin.ext
      simp only [j, Fin.succ_mk]
      have := G.nonempty
      omega
    rw [hj, G.chain_top]
  haveI : IsIso (G.chain j.succ).arrow := by
    rw [htop]
    infer_instance
  let p : Q ⟶ factorObj G j :=
    inv (G.chain j.succ).arrow ≫
      cokernel.π (Subobject.ofLE (G.chain j.castSucc) (G.chain j.succ)
        (le_of_lt (G.chain_strictMono j.castSucc_lt_succ)))
  haveI : Epi p := by
    dsimp [p]
    infer_instance
  have hp : p ≠ 0 := by
    intro hp
    exact (G.factor_semistable j).1 (IsZero.of_epi_eq_zero p hp)
  have hqp : q ≫ p ≠ 0 := by
    intro h
    apply hp
    exact (cancel_epi q).1 (by simpa using h)
  calc
    F.phase ⟨k - 1, by omega⟩ ≤ Z.phase (factorObj G j) :=
      F.phase_last_prefix_le_of_ne_zero_to_semistable
        (G.factor_semistable j) hk₀ hkn (q ≫ p) hqp
    _ = G.phase j := G.factor_phase j
    _ ≤ Z.phase Q := last_le_phase G

/-- The quotient `S / (S ∩ E_k)` lies in the phase range of the HN tail:
its phase is at most the phase of the next factor. -/
theorem quotient_inf_phase_le (hHN : Z.HasHNProperty) {k : ℕ}
    (hk : k < F.n) (S : Subobject E)
    (hQ : ¬IsZero (cokernel (Subobject.ofLE (S ⊓ F.chain ⟨k, by omega⟩) S
      inf_le_left))) :
    Z.phase (cokernel (Subobject.ofLE (S ⊓ F.chain ⟨k, by omega⟩) S
      inf_le_left)) ≤ F.phase ⟨k, hk⟩ := by
  let K : Subobject E := F.chain ⟨k, by omega⟩
  let Q : A := cokernel (Subobject.ofLE (S ⊓ K) S inf_le_left)
  let f : Q ⟶ cokernel K.arrow := quotientInfToCokernel S K
  let D : Subobject (cokernel K.arrow) := Subobject.mk f
  have hD : D ≠ ⊥ := by
    intro hDbot
    have hf : f = 0 := by
      rw [← Subobject.mk_eq_bot_iff_zero]
      exact hDbot
    exact hQ (IsZero.of_mono_eq_zero f hf)
  let G := F.quotientHNFiltration hk
  have hphaseD : Z.phase (D : A) ≤ G.phase ⟨0, G.nonempty⟩ :=
    G.subobject_phase_le_first hHN hD
  have e : (D : A) ≅ Q := Subobject.underlyingIso f
  calc
    Z.phase (cokernel (Subobject.ofLE (S ⊓ F.chain ⟨k, by omega⟩) S
      inf_le_left)) = Z.phase Q := rfl
    _ = Z.phase (D : A) := (Z.phase_eq_of_iso e).symm
    _ ≤ G.phase ⟨0, G.nonempty⟩ := hphaseD
    _ = F.phase ⟨k, hk⟩ := by rfl

/-- A proper inclusion of subobjects has a nonzero cokernel. -/
private theorem cokernel_ofLE_not_isZero {I S : Subobject E} (hIS : I ≤ S)
    (hne : I ≠ S) : ¬IsZero (cokernel (Subobject.ofLE I S hIS)) := by
  intro hzero
  haveI : Epi (Subobject.ofLE I S hIS) :=
    Preadditive.epi_of_isZero_cokernel _ hzero
  haveI : IsIso (Subobject.ofLE I S hIS) := isIso_of_mono_of_epi _
  exact hne (Subobject.eq_of_comm (asIso (Subobject.ofLE I S hIS))
    (Subobject.ofLE_arrow hIS))

/-- A vertex which maximizes a cross-product support functional on the
distinguished HN path also maximizes it against every subobject charge.

This is the support-function form of the statement that the HN path is the
left boundary of the ambient HN polygon.  Unlike the stronger (and generally
false) assertion that the whole ambient polygon is the convex hull of the HN
vertices, it only controls support directions with angle in `(0, π)`.  Those
are exactly the directions used by the polygon-perimeter comparison.

The proof cuts an arbitrary subobject `S` at the maximizing filtration vertex
`K = E_k`.  The quotient `S / (S ∩ K)` lies no higher than the next HN ray,
while `K / (S ∩ K)` lies no lower than the preceding HN ray.  Maximality on
the two neighboring path vertices places the support ray between them, so the
two quotient contributions have opposite signs. -/
theorem subobjectCharge_le_of_polygonVertex_isMax
    (hHN : Z.HasHNProperty) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (k : Fin (F.n + 1))
    (hmax : ∀ j, ComplexPolygonalPath.crossFunctional
      (ComplexPolygonalPath.unitRay θ) (F.polygonVertex j) ≤
        ComplexPolygonalPath.crossFunctional
          (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k))
    (S : Subobject E) :
    ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (Z.charge (S : A)) ≤
      ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k) := by
  let r : ℂ := ComplexPolygonalPath.unitRay θ
  let l : ℂ →L[ℝ] ℝ := ComplexPolygonalPath.crossFunctional r
  have hr : r ∈ semiClosedUpperHalfPlane :=
    ComplexPolygonalPath.unitRay_mem_semiClosedUpperHalfPlane hθ.1 hθ.2
  have hrne : r ≠ 0 := semiClosedUpperHalfPlane_ne_zero hr
  have hrarg : Complex.arg r = θ :=
    ComplexPolygonalPath.arg_unitRay hθ.1 hθ.2
  let K : Subobject E := F.chain k
  let I : Subobject E := S ⊓ K
  let Qₛ : A := cokernel (Subobject.ofLE I S inf_le_left)
  let Qₖ : A := cokernel (Subobject.ofLE I K inf_le_right)
  have hZₛ : Z.charge (S : A) = Z.charge (I : A) + Z.charge Qₛ :=
    Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE I S inf_le_left))
      inferInstance inferInstance)
  have hZₖ : Z.charge (K : A) = Z.charge (I : A) + Z.charge Qₖ :=
    Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE I K inf_le_right))
      inferInstance inferInstance)
  have hdiff : Z.charge (S : A) - Z.charge (K : A) =
      Z.charge Qₛ - Z.charge Qₖ := by
    linear_combination hZₛ - hZₖ
  have hleft : l (Z.charge Qₛ) ≤ 0 := by
    by_cases hkn : k < Fin.last F.n
    · let iNext : Fin F.n := ⟨k.1, by omega⟩
      have hkNext : iNext.castSucc = k := by apply Fin.ext; rfl
      have hpath : l (F.polygonVertex iNext.succ) ≤
          l (F.polygonVertex iNext.castSucc) := by
        simpa [l, r, hkNext] using hmax iNext.succ
      have hedge_nonpos : l (F.polygonEdge iNext) ≤ 0 := by
        rw [polygonEdge, map_sub]
        linarith
      have hargNext : Complex.arg (F.polygonEdge iNext) ≤ θ := by
        have hcross : 0 ≤
            (F.polygonEdge iNext).re * r.im -
              (F.polygonEdge iNext).im * r.re := by
          dsimp [l] at hedge_nonpos
          rw [ComplexPolygonalPath.crossFunctional_apply] at hedge_nonpos
          linarith
        have harg := arg_le_of_cross_nonneg
          (semiClosedUpperHalfPlane_ne_zero
            (F.polygonEdge_mem_semiClosedUpperHalfPlane iNext)) hrne
          (by rw [hrarg]; exact hθ.1) hcross
        simpa [hrarg] using harg
      by_cases hIS : I = S
      · have hZzero : Z.charge Qₛ = 0 := by
          rw [hIS] at hZₛ
          exact (add_left_cancel (show Z.charge (S : A) + 0 =
            Z.charge (S : A) + Z.charge Qₛ by simpa using hZₛ)).symm
        rw [hZzero, map_zero]
      · have hQₛ : ¬IsZero Qₛ := cokernel_ofLE_not_isZero inf_le_left hIS
        have hphase : Z.phase Qₛ ≤ F.phase iNext := by
          simpa [Qₛ, I, K, iNext] using
            F.quotient_inf_phase_le hHN (k := k.1) (by omega) S hQₛ
        have hargQ : Complex.arg (Z.charge Qₛ) ≤ θ := by
          apply le_trans _ hargNext
          rw [F.polygonEdge_arg iNext]
          calc
            Complex.arg (Z.charge Qₛ) = Real.pi * Z.phase Qₛ := by
              unfold CategoryTheory.Triangulated.StabilityFunction.phase
              field_simp
            _ ≤ Real.pi * F.phase iNext :=
              mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
        have hcross := cross_nonneg_of_arg_le
          (im_nonneg_of_mem_semiClosedUpperHalfPlane (Z.nonzero_mem Qₛ hQₛ))
          (semiClosedUpperHalfPlane_ne_zero (Z.nonzero_mem Qₛ hQₛ)) hrne
          (by simpa [hrarg] using hargQ)
        simp only [CategoryTheory.Triangulated.abelianDatum_cl] at hcross
        dsimp [l]
        rw [ComplexPolygonalPath.crossFunctional_apply]
        linarith
    · have hk : k = Fin.last F.n :=
        le_antisymm (Fin.le_last k) (not_lt.mp hkn)
      have hKtop : K = ⊤ := by
        dsimp [K]
        rw [hk]
        exact F.chain_top
      have hIS : I = S := by
        simp [I, hKtop]
      have hZzero : Z.charge Qₛ = 0 := by
        rw [hIS] at hZₛ
        exact (add_left_cancel (show Z.charge (S : A) + 0 =
          Z.charge (S : A) + Z.charge Qₛ by simpa using hZₛ)).symm
      rw [hZzero, map_zero]
  have hright : 0 ≤ l (Z.charge Qₖ) := by
    by_cases hk₀ : 0 < k
    · let iPrev : Fin F.n := ⟨k.1 - 1, by omega⟩
      have hkPrev : iPrev.succ = k := by apply Fin.ext; simp [iPrev]; omega
      have hpath : l (F.polygonVertex iPrev.castSucc) ≤
          l (F.polygonVertex iPrev.succ) := by
        simpa [l, r, hkPrev] using hmax iPrev.castSucc
      have hedge_nonneg : 0 ≤ l (F.polygonEdge iPrev) := by
        rw [polygonEdge, map_sub]
        linarith
      have hθargPrev : θ ≤ Complex.arg (F.polygonEdge iPrev) := by
        have harg := arg_le_of_cross_nonneg hrne
          (semiClosedUpperHalfPlane_ne_zero
            (F.polygonEdge_mem_semiClosedUpperHalfPlane iPrev))
          (arg_pos_of_mem_semiClosedUpperHalfPlane
            (F.polygonEdge_mem_semiClosedUpperHalfPlane iPrev)) (by
              dsimp [l] at hedge_nonneg
              simpa [ComplexPolygonalPath.crossFunctional_apply] using hedge_nonneg)
        simpa [hrarg] using harg
      by_cases hIK : I = K
      · have hZzero : Z.charge Qₖ = 0 := by
          rw [hIK] at hZₖ
          exact (add_left_cancel (show Z.charge (K : A) + 0 =
            Z.charge (K : A) + Z.charge Qₖ by simpa using hZₖ)).symm
        rw [hZzero, map_zero]
      · have hQₖ : ¬IsZero Qₖ := cokernel_ofLE_not_isZero inf_le_right hIK
        have hphase : F.phase iPrev ≤ Z.phase Qₖ := by
          simpa [Qₖ, I, K, iPrev] using
            F.last_prefix_le_quotient_phase hHN (k := k.1) (by omega)
              (by omega) (cokernel.π (Subobject.ofLE I K inf_le_right)) hQₖ
        have hargQ : θ ≤ Complex.arg (Z.charge Qₖ) := by
          apply hθargPrev.trans
          rw [F.polygonEdge_arg iPrev]
          calc
            Real.pi * F.phase iPrev ≤ Real.pi * Z.phase Qₖ :=
              mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
            _ = Complex.arg (Z.charge Qₖ) := by
              unfold CategoryTheory.Triangulated.StabilityFunction.phase
              field_simp
        exact cross_nonneg_of_arg_le (im_nonneg_of_mem_semiClosedUpperHalfPlane hr)
          hrne (semiClosedUpperHalfPlane_ne_zero (Z.nonzero_mem Qₖ hQₖ)) (by
            simpa [hrarg] using hargQ)
    · have hk : k = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hk₀
      have hKbot : K = ⊥ := by
        dsimp [K]
        rw [hk]
        exact F.chain_bot
      have hIK : I = K := by
        simp [I, hKbot]
      have hZzero : Z.charge Qₖ = 0 := by
        rw [hIK] at hZₖ
        exact (add_left_cancel (show Z.charge (K : A) + 0 =
          Z.charge (K : A) + Z.charge Qₖ by simpa using hZₖ)).symm
      rw [hZzero, map_zero]
  have hmapdiff : l (Z.charge (S : A)) - l (Z.charge (K : A)) =
      l (Z.charge Qₛ) - l (Z.charge Qₖ) := by
    rw [← map_sub, hdiff, map_sub]
  change l (Z.charge (S : A)) ≤ l (F.polygonVertex k)
  rw [show F.polygonVertex k = Z.charge (K : A) by rfl]
  linarith

/-- Every positive-angle support functional reaches its ambient HN-polygon
maximum on the distinguished HN path. -/
theorem hnPolygon_le_of_polygonVertex_isMax
    (hHN : Z.HasHNProperty) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (k : Fin (F.n + 1))
    (hmax : ∀ j, ComplexPolygonalPath.crossFunctional
      (ComplexPolygonalPath.unitRay θ) (F.polygonVertex j) ≤
        ComplexPolygonalPath.crossFunctional
          (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k))
    {z : ℂ} (hz : z ∈ Z.hnPolygon E) :
    ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) z ≤
      ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k) := by
  let l : ℂ →L[ℝ] ℝ := ComplexPolygonalPath.crossFunctional
    (ComplexPolygonalPath.unitRay θ)
  obtain ⟨y, ⟨S, rfl⟩, hy⟩ :=
    (l.toLinearMap.convexOn (convex_univ : Convex ℝ (Set.univ : Set ℂ))).exists_ge_of_mem_convexHull
      (Set.subset_univ _) hz
  exact hy.trans (F.subobjectCharge_le_of_polygonVertex_isMax hHN hθ k hmax S)

/-- A strict linear maximum on a generating set remains a strict unique
maximum on its convex hull. -/
private theorem strict_support_convexHull {s : Set ℂ} {v : ℂ}
    (l : ℂ →L[ℝ] ℝ) (h : ∀ x ∈ s, x ≠ v → l x < l v) :
    ∀ x ∈ convexHull ℝ s, x ≠ v → l x < l v := by
  let T : Set ℂ := {x | l x < l v ∨ x = v}
  have hsT : s ⊆ T := by
    intro x hx
    by_cases hxv : x = v
    · exact Or.inr hxv
    · exact Or.inl (h x hx hxv)
  have hTconvex : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · left
      simp only [map_add, map_smul, smul_eq_mul]
      by_cases ha₀ : a = 0
      · have hb₁ : b = 1 := by linarith
        simpa [ha₀, hb₁] using hy
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha₀)
        calc
          a * l x + b * l y < a * l v + b * l v :=
            add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left hx ha')
              (mul_le_mul_of_nonneg_left hy.le hb)
          _ = l v := by rw [← add_mul, hab, one_mul]
    · by_cases ha₀ : a = 0
      · right
        have hb₁ : b = 1 := by linarith
        simp [ha₀, hb₁]
      · left
        simp only [map_add, map_smul, smul_eq_mul]
        have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha₀)
        calc
          a * l x + b * l y < a * l y + b * l y :=
            add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha') le_rfl
          _ = l y := by rw [← add_mul, hab, one_mul]
    · by_cases hb₀ : b = 0
      · right
        have ha₁ : a = 1 := by linarith
        simp [hb₀, ha₁]
      · left
        simp only [map_add, map_smul, smul_eq_mul]
        have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb₀)
        calc
          a * l x + b * l y < a * l x + b * l x :=
            add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hy hb')
          _ = l x := by rw [← add_mul, hab, one_mul]
    · right
      calc
        a • y + b • y = (a + b) • y := (add_smul a b y).symm
        _ = y := by rw [hab]; exact one_smul ℝ y
  have hhull : convexHull ℝ s ⊆ T := convexHull_min hsT hTconvex
  intro x hx hxv
  rcases hhull hx with hlt | heq
  · exact hlt
  · exact (hxv heq).elim

/-- Every interior HN vertex is strictly supported against the charge of
every other subobject.  At the cut `K = E_k`, the charge difference splits as

`Z(S) - Z(K) = Z(S / (S ∩ K)) - Z(K / (S ∩ K))`.

The first quotient lies below the next HN ray and the second lies above the
preceding HN ray, so the cross-product functional at an intermediate angle is
strictly smaller on `S`. -/
theorem subobjectCharge_exists_strict_support (hHN : Z.HasHNProperty)
    (k : Fin (F.n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last F.n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ S : Subobject E, S ≠ F.chain k →
      l (Z.charge (S : A)) < l (F.polygonVertex k) := by
  let iPrev : Fin F.n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin F.n := ⟨k.1, by omega⟩
  have hiPrevNext : iPrev < iNext := by
    simp only [iPrev, iNext, Fin.mk_lt_mk]
    omega
  have hargNextPrev : Complex.arg (F.polygonEdge iNext) <
      Complex.arg (F.polygonEdge iPrev) :=
    F.polygonEdge_arg_strictAnti hiPrevNext
  let θ : ℝ :=
    (Complex.arg (F.polygonEdge iPrev) + Complex.arg (F.polygonEdge iNext)) / 2
  have hargNextθ : Complex.arg (F.polygonEdge iNext) < θ := by
    dsimp [θ]
    linarith
  have hθargPrev : θ < Complex.arg (F.polygonEdge iPrev) := by
    dsimp [θ]
    linarith
  have hθ₀ : 0 < θ :=
    (arg_pos_of_mem_semiClosedUpperHalfPlane
      (F.polygonEdge_mem_semiClosedUpperHalfPlane iNext)).trans hargNextθ
  have hθπ : θ < Real.pi :=
    hθargPrev.trans_le (Complex.arg_le_pi _)
  let r : ℂ := ComplexPolygonalPath.unitRay θ
  let l : ℂ →L[ℝ] ℝ := ComplexPolygonalPath.crossFunctional r
  have hr : r ∈ semiClosedUpperHalfPlane :=
    ComplexPolygonalPath.unitRay_mem_semiClosedUpperHalfPlane hθ₀ hθπ
  have hrarg : Complex.arg r = θ :=
    ComplexPolygonalPath.arg_unitRay hθ₀ hθπ
  refine ⟨l, fun S hSK ↦ ?_⟩
  let K : Subobject E := F.chain k
  let I : Subobject E := S ⊓ K
  let Qₛ : A := cokernel (Subobject.ofLE I S inf_le_left)
  let Qₖ : A := cokernel (Subobject.ofLE I K inf_le_right)
  have hZₛ : Z.charge (S : A) = Z.charge (I : A) + Z.charge Qₛ :=
    Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE I S inf_le_left))
      inferInstance inferInstance)
  have hZₖ : Z.charge (K : A) = Z.charge (I : A) + Z.charge Qₖ :=
    Z.additive _ (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel (Subobject.ofLE I K inf_le_right))
      inferInstance inferInstance)
  have hdiff : Z.charge (S : A) - Z.charge (K : A) =
      Z.charge Qₛ - Z.charge Qₖ := by
    linear_combination hZₛ - hZₖ
  have hleft : l (Z.charge Qₛ) ≤ 0 := by
    by_cases hIS : I = S
    · have hZzero : Z.charge Qₛ = 0 := by
        rw [hIS] at hZₛ
        exact (add_left_cancel (show Z.charge (S : A) + 0 =
          Z.charge (S : A) + Z.charge Qₛ by simpa using hZₛ)).symm
      rw [hZzero, map_zero]
    · have hQₛ : ¬IsZero Qₛ := cokernel_ofLE_not_isZero inf_le_left hIS
      have hphase : Z.phase Qₛ ≤ F.phase iNext := by
        simpa [Qₛ, I, K, iNext] using
          F.quotient_inf_phase_le hHN (k := k.1) (by omega) S hQₛ
      have hargQ : Complex.arg (Z.charge Qₛ) ≤
          Complex.arg (F.polygonEdge iNext) := by
        rw [F.polygonEdge_arg iNext]
        calc
          Complex.arg (Z.charge Qₛ) = Real.pi * Z.phase Qₛ := by
            unfold CategoryTheory.Triangulated.StabilityFunction.phase
            field_simp
          _ ≤ Real.pi * F.phase iNext :=
            mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
      exact (ComplexPolygonalPath.crossFunctional_neg_of_arg_lt hr
        (Z.nonzero_mem Qₛ hQₛ) (by
          rw [hrarg]
          exact hargQ.trans_lt hargNextθ)).le
  have hright : 0 ≤ l (Z.charge Qₖ) := by
    by_cases hIK : I = K
    · have hZzero : Z.charge Qₖ = 0 := by
        rw [hIK] at hZₖ
        exact (add_left_cancel (show Z.charge (K : A) + 0 =
          Z.charge (K : A) + Z.charge Qₖ by simpa using hZₖ)).symm
      rw [hZzero, map_zero]
    · have hQₖ : ¬IsZero Qₖ := cokernel_ofLE_not_isZero inf_le_right hIK
      have hphase : F.phase iPrev ≤ Z.phase Qₖ := by
        simpa [Qₖ, I, K, iPrev] using
          F.last_prefix_le_quotient_phase hHN (k := k.1) (by omega)
            (by omega) (cokernel.π (Subobject.ofLE I K inf_le_right)) hQₖ
      have hargQ : Complex.arg (F.polygonEdge iPrev) ≤
          Complex.arg (Z.charge Qₖ) := by
        rw [F.polygonEdge_arg iPrev]
        calc
          Real.pi * F.phase iPrev ≤ Real.pi * Z.phase Qₖ :=
            mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
          _ = Complex.arg (Z.charge Qₖ) := by
            unfold CategoryTheory.Triangulated.StabilityFunction.phase
            field_simp
      exact (ComplexPolygonalPath.crossFunctional_pos_of_arg_lt hr
        (Z.nonzero_mem Qₖ hQₖ) (by
          rw [hrarg]
          exact hθargPrev.trans_le hargQ)).le
  have hstrict : l (Z.charge Qₛ) - l (Z.charge Qₖ) < 0 := by
    by_cases hIS : I = S
    · have hIK : I ≠ K := by
        intro h
        apply hSK
        change S = K
        exact hIS.symm.trans h
      have hQₖ : ¬IsZero Qₖ := cokernel_ofLE_not_isZero inf_le_right hIK
      have hright' : 0 < l (Z.charge Qₖ) := by
        have hphase : F.phase iPrev ≤ Z.phase Qₖ := by
          simpa [Qₖ, I, K, iPrev] using
            F.last_prefix_le_quotient_phase hHN (k := k.1) (by omega)
              (by omega) (cokernel.π (Subobject.ofLE I K inf_le_right)) hQₖ
        apply ComplexPolygonalPath.crossFunctional_pos_of_arg_lt hr
          (Z.nonzero_mem Qₖ hQₖ)
        rw [hrarg]
        refine hθargPrev.trans_le ?_
        rw [F.polygonEdge_arg iPrev]
        calc
          Real.pi * F.phase iPrev ≤ Real.pi * Z.phase Qₖ :=
            mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
          _ = Complex.arg (Z.charge Qₖ) := by
            unfold CategoryTheory.Triangulated.StabilityFunction.phase
            field_simp
      linarith
    · have hQₛ : ¬IsZero Qₛ := cokernel_ofLE_not_isZero inf_le_left hIS
      have hleft' : l (Z.charge Qₛ) < 0 := by
        have hphase : Z.phase Qₛ ≤ F.phase iNext := by
          simpa [Qₛ, I, K, iNext] using
            F.quotient_inf_phase_le hHN (k := k.1) (by omega) S hQₛ
        apply ComplexPolygonalPath.crossFunctional_neg_of_arg_lt hr
          (Z.nonzero_mem Qₛ hQₛ)
        rw [hrarg]
        have hargQ : Complex.arg (Z.charge Qₛ) ≤
            Complex.arg (F.polygonEdge iNext) := by
          rw [F.polygonEdge_arg iNext]
          calc
            Complex.arg (Z.charge Qₛ) = Real.pi * Z.phase Qₛ := by
              unfold CategoryTheory.Triangulated.StabilityFunction.phase
              field_simp
            _ ≤ Real.pi * F.phase iNext :=
              mul_le_mul_of_nonneg_left hphase Real.pi_pos.le
        exact hargQ.trans_lt hargNextθ
      linarith
  have hmapdiff : l (Z.charge (S : A)) - l (Z.charge (K : A)) =
      l (Z.charge Qₛ) - l (Z.charge Qₖ) := by
    rw [← map_sub, hdiff, map_sub]
  change l (Z.charge (S : A)) < l (Z.charge (K : A))
  linarith

/-- Every interior HN path vertex is an exposed point of the full ambient HN
polygon: it is the strict unique maximizer of a continuous real-linear
functional over the convex hull of all subobject charges. -/
theorem polygonVertex_exists_strict_support_hnPolygon
    (hHN : Z.HasHNProperty) (k : Fin (F.n + 1)) (hk₀ : 0 < k)
    (hkn : k < Fin.last F.n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ z ∈ Z.hnPolygon E, z ≠ F.polygonVertex k →
      l z < l (F.polygonVertex k) := by
  obtain ⟨l, hl⟩ := F.subobjectCharge_exists_strict_support hHN k hk₀ hkn
  refine ⟨l, strict_support_convexHull l ?_⟩
  rintro z ⟨S, rfl⟩ hz
  exact hl S (by
    intro hSK
    apply hz
    simp [polygonVertex, hSK])

/-- Every vertex of the distinguished HN path lies in the ambient HN
polygon. -/
theorem polygonVertex_mem_hnPolygon (j : Fin (F.n + 1)) :
    F.polygonVertex j ∈ Z.hnPolygon E :=
  Z.subobjectCharge_mem_hnPolygon E (F.chain j)

/-- The norm of the total charge is bounded by the HN polygon length. -/
theorem norm_charge_le_polygonLength : ‖Z.charge E‖ ≤ F.polygonLength := by
  have h := ComplexPolygonalPath.norm_last_sub_zero_le_length F.polygonVertex
  change ‖F.polygonVertex (Fin.last F.n) - F.polygonVertex 0‖ ≤
    F.polygonLength at h
  have hlast : F.polygonVertex (Fin.last F.n) = Z.charge E := by
    simp [Fin.last]
  have hzero : F.polygonVertex 0 = 0 := by
    exact F.polygonVertex_zero
  simpa [hlast, hzero] using h

/-- The norm of the total charge is bounded by the sum of the HN factor
masses. -/
theorem norm_charge_le_mass : ‖Z.charge E‖ ≤ F.mass := by
  rw [← F.polygonLength_eq_mass]
  exact F.norm_charge_le_polygonLength

end AbelianHNFiltration

end

end CategoryTheory.Triangulated
