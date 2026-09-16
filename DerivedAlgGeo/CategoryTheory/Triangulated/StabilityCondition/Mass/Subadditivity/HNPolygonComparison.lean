/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Analysis.Convex.ComplexPolygonalPath.Perimeter
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.HNPolygon

/-!
# Perimeter comparison for Harder--Narasimhan polygons

The Harder--Narasimhan reading of the neutral perimeter comparison in
`Analysis/Convex/ComplexPolygonalPath/Perimeter.lean`: the vertices are
subobject charges, the edges are semistable-factor charges, and the path length
is the mass.

## Main declarations

* `polygonLength_le_of_vertexHull_subset`, for applications that already have
  containment of the two closed finite vertex polygons.
* `polygonLength_le_add_norm_charge_sub_of_mono`, the boundary-cut comparison
  along a monomorphism, and its `mass_le_add_norm_cokernel_of_mono` and
  `mass_le_add_norm_of_shortExact` mass forms.
* `mass_eq_mass`, independence of the mass of the chosen HN filtration.

## Source

Ikeda, *A phase limit formula and the space of stability conditions*,
Lemmas 3.7 and 3.8, at `t = 0`. Lemma 3.8 is strengthened at that parameter by
not requiring the cokernel to have phase one: that hypothesis controls the
exponential weight for general `t` and disappears when `t = 0`. No claim that
the full ambient HN polygon is the closed HN vertex hull is used -- it is false
in general; positive-angle support maxima of the ambient polygon come from
`HNPolygon` instead.

## Placement

This file is the stability adapter half of what was
`StabilityCondition/Metric/Mass/Subadditivity/PolygonPerimeter.lean`. MO1.13
(#1324) sent the Euclidean half to its neutral owner and gave what stayed a
name for its subject -- the HN polygon comparison -- rather than for the shape
of its proof. The citation above travels with it unchanged.
-/

namespace CategoryTheory.Triangulated

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E E' : A}

/-- HN-path specialization of the finite perimeter comparison for
applications which already have containment of the two closed finite vertex
polygons.  The monomorphism comparison below uses the more precise ambient
support theorem instead of trying to derive this hypothesis from full ambient
HN-polygon containment. -/
theorem polygonLength_le_of_vertexHull_subset
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hcharge : Z.charge E = Z.charge E')
    (hcontain : convexHull ℝ (Set.range F.polygonVertex) ⊆
      convexHull ℝ (Set.range G.polygonVertex)) :
    F.polygonLength ≤ G.polygonLength := by
  apply ComplexPolygonalPath.length_le_of_convexHull_subset F.nonempty
  · rw [F.polygonVertex_zero, G.polygonVertex_zero]
  · calc
      F.polygonVertex (Fin.last F.n) = Z.charge E := F.polygonVertex_last
      _ = Z.charge E' := hcharge
      _ = G.polygonVertex (Fin.last G.n) := G.polygonVertex_last.symm
  · exact fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i
  · exact fun i ↦ G.polygonEdge_mem_semiClosedUpperHalfPlane i
  · exact F.polygonEdge_arg_strictAnti
  · exact hcontain

/-- **Boundary-cut HN polygon comparison.** If `E ⟶ E'` is monic, the HN
path of `E` is no longer than the HN path of `E'` followed by the single edge
from `Z(E')` back to `Z(E)`.

This is the `t = 0` comparison used in Ikeda's Lemma 3.8, strengthened at that
parameter by not requiring the cokernel to have phase one.  (That phase
hypothesis controls the exponential weight for general `t`; it disappears
when `t = 0`.)  The final edge is allowed to lie on the positive real boundary
when the cokernel does have phase one.  No false claim that the full ambient HN
polygon is the closed HN vertex hull is used.  Instead, positive-angle support
maxima of the ambient polygon are supplied by `HNPolygon` and the finite
support-fan perimeter theorem closes the argument. -/
theorem polygonLength_le_add_norm_charge_sub_of_mono
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hHN : Z.HasHNProperty) (f : E ⟶ E') [Mono f] :
    F.polygonLength ≤ G.polygonLength + ‖Z.charge E - Z.charge E'‖ := by
  let w : Fin (G.n + 2) → ℂ := Fin.snoc G.polygonVertex (Z.charge E)
  let q : Fin (F.n + 1) → Fin (G.n + 2) := fun k ↦
    if hk₀ : k = 0 then 0
    else if hkl : k = Fin.last F.n then Fin.last (G.n + 1)
    else (ComplexPolygonalPath.crossMaxIndex G.polygonVertex
      (ComplexPolygonalPath.interiorBisector F.polygonVertex k
        (Fin.pos_iff_ne_zero.mpr hk₀)
        (lt_of_le_of_ne (Fin.le_last k) hkl))).castSucc
  have hq₀ : q 0 = 0 := by simp [q]
  have hq_last : q (Fin.last F.n) = Fin.last (G.n + 1) := by
    have hne : (Fin.last F.n : Fin (F.n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      have := F.nonempty
      omega
    unfold q
    rw [dif_neg hne, dif_pos rfl]
  have hq : Monotone q := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · by_cases ha₀ : a = 0
      · simp [q, ha₀]
      · by_cases hbl : b = Fin.last F.n
        · rw [hbl, hq_last]
          exact Fin.le_last _
        · have hal : a ≠ Fin.last F.n := by
            intro h
            subst a
            exact (not_lt_of_ge (Fin.le_last b)) hab
          have hb₀ : b ≠ 0 := by
            intro h
            subst b
            exact Fin.not_lt_zero a hab
          have ha_pos : 0 < a := Fin.pos_iff_ne_zero.mpr ha₀
          have hb_pos : 0 < b := Fin.pos_iff_ne_zero.mpr hb₀
          have ha_last : a < Fin.last F.n :=
            lt_of_le_of_ne (Fin.le_last a) hal
          have hb_last : b < Fin.last F.n :=
            lt_of_le_of_ne (Fin.le_last b) hbl
          simp only [q, dif_neg ha₀, dif_neg hal, dif_neg hb₀, dif_neg hbl,
            Fin.castSucc_le_castSucc_iff]
          exact ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
            G.polygonVertex (fun i ↦ G.polygonEdge_mem_semiClosedUpperHalfPlane i)
            (ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
              (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
              F.polygonEdge_arg_strictAnti a ha_pos ha_last)
            (ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
              (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
              F.polygonEdge_arg_strictAnti b hb_pos hb_last)
            (ComplexPolygonalPath.interiorBisector_strictAnti F.polygonVertex
              F.polygonEdge_arg_strictAnti ha_pos ha_last hb_pos hb_last hab)
  have hsupport : ∀ k, ComplexPolygonalPath.turningFunctional
      F.polygonVertex k (F.polygonVertex k) ≤
        ComplexPolygonalPath.turningFunctional
          F.polygonVertex k (w (q k)) := by
    intro k
    by_cases hk₀ : k = 0
    · subst k
      rw [hq₀]
      simp [w, F.polygonVertex_zero, G.polygonVertex_zero]
    by_cases hkl : k = Fin.last F.n
    · subst k
      rw [hq_last]
      have hw : w (Fin.last (G.n + 1)) =
          F.polygonVertex (Fin.last F.n) := by
        rw [show w (Fin.last (G.n + 1)) = Z.charge E by simp [w]]
        exact F.polygonVertex_last.symm
      rw [hw]
    have hk_pos : 0 < k := Fin.pos_iff_ne_zero.mpr hk₀
    have hk_last : k < Fin.last F.n :=
      lt_of_le_of_ne (Fin.le_last k) hkl
    let θ := ComplexPolygonalPath.interiorBisector
      F.polygonVertex k hk_pos hk_last
    let j := ComplexPolygonalPath.crossMaxIndex G.polygonVertex θ
    have hθ : θ ∈ Set.Ioo 0 Real.pi :=
      ComplexPolygonalPath.interiorBisector_mem_Ioo F.polygonVertex
        (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        F.polygonEdge_arg_strictAnti k hk_pos hk_last
    have hzB : F.polygonVertex k ∈ Z.hnPolygon E' :=
      Z.hnPolygon_mono f (F.polygonVertex_mem_hnPolygon k)
    have hcross : ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (F.polygonVertex k) ≤
      ComplexPolygonalPath.crossFunctional
        (ComplexPolygonalPath.unitRay θ) (G.polygonVertex j) :=
      G.hnPolygon_le_of_polygonVertex_isMax hHN hθ j
        (fun i ↦ ComplexPolygonalPath.crossMaxIndex_max
          G.polygonVertex θ i) hzB
    have hqk : q k = j.castSucc := by
      simp [q, hk₀, hkl, θ, j]
    rw [ComplexPolygonalPath.turningFunctional_interior_eq_cross
        F.polygonVertex (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        k hk_pos hk_last,
      ComplexPolygonalPath.turningFunctional_interior_eq_cross
        F.polygonVertex (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        k hk_pos hk_last, hqk]
    simp only [w, Fin.snoc_castSucc]
    exact mul_le_mul_of_nonneg_left hcross
      (le_of_lt (ComplexPolygonalPath.interiorTurnScale_pos F.polygonVertex
        (fun i ↦ F.polygonEdge_mem_semiClosedUpperHalfPlane i)
        F.polygonEdge_arg_strictAnti k hk_pos hk_last))
  have hclosed := ComplexPolygonalPath.closedLength_le_of_monotone_support
    F.polygonVertex w q hq hq₀ hq_last hsupport
  rw [ComplexPolygonalPath.closedLength_eq_length_add_chord,
    ComplexPolygonalPath.closedLength_eq_length_add_chord] at hclosed
  have hw₀ : w 0 = F.polygonVertex 0 := by
    simp [w, F.polygonVertex_zero, G.polygonVertex_zero]
  have hwlast : w (Fin.last (G.n + 1)) = F.polygonVertex (Fin.last F.n) := by
    rw [show w (Fin.last (G.n + 1)) = Z.charge E by simp [w]]
    exact F.polygonVertex_last.symm
  rw [hw₀, hwlast] at hclosed
  have hopen : F.polygonLength ≤ ComplexPolygonalPath.length w := by
    exact le_of_add_le_add_right hclosed
  rw [ComplexPolygonalPath.length_snoc] at hopen
  have hGlast : G.polygonVertex (Fin.last G.n) = Z.charge E' :=
    G.polygonVertex_last
  rw [hGlast] at hopen
  simpa [w, polygonLength] using hopen

/-- Mass form of the boundary-cut comparison.  The closing-edge charge is
the negative of the cokernel charge, by additivity of the stability
function. -/
theorem mass_le_add_norm_cokernel_of_mono
    (F : AbelianHNFiltration Z E) (G : AbelianHNFiltration Z E')
    (hHN : Z.HasHNProperty) (f : E ⟶ E') [Mono f] :
    F.mass ≤ G.mass + ‖Z.charge (Limits.cokernel f)‖ := by
  have hse : (ShortComplex.mk f (Limits.cokernel.π f)
      (Limits.cokernel.condition f)).ShortExact :=
    StabilityFunction.shortExact_of_mono f
  have hadd := Z.additive _ hse
  have hsub : Z.charge E - Z.charge E' = -Z.charge (Limits.cokernel f) := by
    linear_combination -hadd
  rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass, ← norm_neg,
    ← hsub]
  exact F.polygonLength_le_add_norm_charge_sub_of_mono G hHN f

/-- Short-exact-sequence form of the boundary-cut comparison. -/
theorem mass_le_add_norm_of_shortExact (S : ShortComplex A)
    (hS : S.ShortExact) (F : AbelianHNFiltration Z S.X₁)
    (G : AbelianHNFiltration Z S.X₂) (hHN : Z.HasHNProperty) :
    F.mass ≤ G.mass + ‖Z.charge S.X₃‖ := by
  letI := hS.mono_f
  have hmass := F.mass_le_add_norm_cokernel_of_mono G hHN S.f
  let e : Limits.cokernel S.f ≅ S.X₃ :=
    Limits.IsColimit.coconePointUniqueUpToIso (Limits.cokernelIsCokernel S.f)
      hS.gIsCokernel
  have hcharge : Z.charge (Limits.cokernel S.f) = Z.charge S.X₃ :=
    Z.charge_eq_of_iso e
  rwa [hcharge] at hmass

/-- The mass of an abelian HN filtration is independent of the chosen
filtration.  This is the identity-monomorphism specialization of the
boundary-cut comparison. -/
theorem mass_eq_mass (F G : AbelianHNFiltration Z E)
    (hHN : Z.HasHNProperty) :
    F.mass = G.mass := by
  apply le_antisymm
  · rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass]
    simpa using F.polygonLength_le_add_norm_charge_sub_of_mono G hHN (𝟙 E)
  · rw [← F.polygonLength_eq_mass, ← G.polygonLength_eq_mass]
    simpa using G.polygonLength_le_add_norm_charge_sub_of_mono F hHN (𝟙 E)

end AbelianHNFiltration

end

end CategoryTheory.Triangulated
