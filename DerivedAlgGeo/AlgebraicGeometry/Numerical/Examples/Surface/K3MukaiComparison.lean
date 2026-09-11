/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3Mukai
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.RankOneWalls

/-!
# The integral and real Mukai structures of the K3 model agree

The degree-`2d` K3 model carries two Mukai structures that had nothing to do
with each other.

* `K3Mukai.lean` builds the **integral** one: `k3IntegralMukaiData`, with
  lattice `ℤ`, form `⟪x, y⟫ = 2d·x·y`, and `mukaiVector E = (r, c, χ − r)` in
  `Mukai.MukaiLattice ℤ`.  Sphericality there is `⟪v, v⟫ = -2` over `ℤ`, and
  `isSpherical_mukaiVector_iff` characterises it.
* `RankOneRealization.lean` builds the **real** one: the divisor line `ℝ` with
  form `2d·x·y`, whose real Mukai extension is where every wall statement of
  `Divisorial/Signature.lean` and `Divisorial/Region.lean` lives.  Sphericality
  there is `PeriodDomain.IsSphericalClass`.

`Mukai/IntegralBridge.lean` has carried the general comparison for some time —
`extendMap`, `realPairing_extendMap`, `isSphericalClass_extendMap` — waiting on
a lattice map that respects both forms.  On this model that map is the inclusion
`ℤ → ℝ`, and the forms agree on the nose.

## Why this matters beyond tidiness

Every wall-finiteness statement proved for this model counts *real* spherical
classes.  The geometric content is about *integral* ones: `⟪v, v⟫ = -2` in the
Mukai lattice, which `GrothendieckGroup/MukaiVector.lean` relates to `χ₂` and
to the expected dimension of a moduli space.  `k3_isSphericalClass_of_isSpherical`
is the link, so `k3_finite_walls_meeting_box` and its siblings become statements
about the classes the geometry cares about rather than about a real
approximation of them.

`k3_mukaiVector_eq_extendMap` is the identification that carries it: the real
Mukai vector of a numerical class **is** the integral one, extended.

## What is not claimed

Nothing here identifies either carrier with `K_num(X)` for a geometric K3, and
no Riemann--Roch input is added: `mukaiVector_k3` already evaluated the integral
vector, and this file only compares.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

variable {d : ℕ}

/-! ### The lattice map -/

/-- The inclusion of the rank-one Néron--Severi lattice `ℤ·H` into the real
divisor line, sending `H` to the unit vector. -/
def k3LatticeMap : ℤ →ₗ[ℤ] SurfaceDivisor where
  toFun n := (n : ℝ)
  map_add' _ _ := by push_cast; ring
  map_smul' m n := by
    simp only [smul_eq_mul, zsmul_eq_mul, eq_intCast, Int.cast_mul]
    push_cast
    ring

@[simp]
theorem k3LatticeMap_apply (n : ℤ) : k3LatticeMap n = (n : ℝ) := rfl

/-- **The two forms agree.**  This is the hypothesis every theorem of
`Mukai/IntegralBridge.lean` waits on, and on this model it is a cast. -/
theorem k3LatticeMap_pairing (d : ℕ) (x y : ℤ) :
    (surfaceDivisorSpace (2 * (d : ℝ))).intersection (k3LatticeMap x) (k3LatticeMap y)
      = ((k3MukaiForm d x y : ℤ) : ℝ) := by
  show 2 * (d : ℝ) * (x : ℝ) * (y : ℝ) = ((2 * (d : ℤ) * x * y : ℤ) : ℝ)
  push_cast
  ring

/-! ### The two pairings, and the two Mukai vectors -/

/-- **The integral Mukai pairing is the real one.** -/
theorem k3_realPairing_extendMap (d : ℕ) (u w : Mukai.MukaiLattice ℤ) :
    Mukai.realPairing (surfaceDivisorSpace (2 * (d : ℝ))).intersection
        (Mukai.extendMap k3LatticeMap u) (Mukai.extendMap k3LatticeMap w)
      = ((Mukai.pairing (k3MukaiForm d) u w : ℤ) : ℝ) :=
  Mukai.realPairing_extendMap _ _ _ (k3LatticeMap_pairing d) u w

/-- **The real Mukai vector is the integral one, extended.**

The left side is `Walls/Divisorial/Mukai.lean` read through the realization of
`RankOneRealization.lean`; the right side is `GrothendieckGroup/MukaiVector.lean`
read through `k3IntegralMukaiData`.  They are the same triple. -/
theorem k3_mukaiVector_eq_extendMap (d : ℕ) (hd : d ≠ 0) (E : SurfaceNum) :
    (k3Realization d).chernCharacter.mukaiVector (k3Realization d).divisorSpace
        ((k3Realization d).sqrtTodd (V := k3NumericalVariety d)) E
      = Mukai.extendMap k3LatticeMap ((k3IntegralMukaiData d).mukaiVector E) := by
  rw [k3Realization_sqrtTodd d hd, ChernCharacter.mukaiVector_k3, mukaiVector_k3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact k3Realization_chernCharacter_rank d E
  · exact k3Realization_chernCharacter_chOne d E
  · show (k3Realization d).chernCharacter.chTwo E + (k3Realization d).chernCharacter.rank E
      = ((E 0 + 2 * (d : ℤ) * E 2 : ℤ) : ℝ)
    rw [k3Realization_chernCharacter_chTwo d E, k3Realization_chernCharacter_rank d E]
    push_cast
    ring

/-! ### Integral sphericality is real sphericality -/

/-- **An integral spherical class of the Mukai lattice is a spherical class of
the real form.**

The `-2` reads the same on both sides, which is what the halving convention of
`Mukai/RealForm.lean` exists for.  This is the link that makes the wall
statements about integral classes. -/
theorem k3_isSphericalClass_of_isSpherical (d : ℕ) {δ : Mukai.MukaiLattice ℤ}
    (hδ : Mukai.IsSpherical (k3MukaiForm d) δ) :
    PeriodDomain.IsSphericalClass
      (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection)
      (Mukai.extendMap k3LatticeMap δ) :=
  Mukai.isSphericalClass_extendMap _ _ _ (k3LatticeMap_pairing d)
    (fun x y => (surfaceDivisorSpace (2 * (d : ℝ))).pair_comm x y) hδ

/-- **The Mukai vector of a numerical class is a real spherical class exactly
when the integral criterion holds.**

`isSpherical_mukaiVector_iff` states that criterion in terms of `χ₂`, so this is
where the real wall theory meets the numerical invariants. -/
theorem k3_isSphericalClass_mukaiVector (d : ℕ) (hd : d ≠ 0) {E : SurfaceNum}
    (hE : Mukai.IsSpherical (k3MukaiForm d) ((k3IntegralMukaiData d).mukaiVector E)) :
    PeriodDomain.IsSphericalClass
      (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection)
      ((k3Realization d).chernCharacter.mukaiVector (k3Realization d).divisorSpace
        ((k3Realization d).sqrtTodd (V := k3NumericalVariety d)) E) := by
  rw [k3_mukaiVector_eq_extendMap d hd E]
  exact k3_isSphericalClass_of_isSpherical d hE

/-! ### The integral Mukai extension is the lattice of the wall statements -/

/-- The extension of an integral class lands in the integral Mukai extension of
`ℤ·H`, which is the lattice `k3_finite_walls_integral` and
`k3_finite_walls_meeting_box` are stated against. -/
theorem k3_extendMap_mem_integralExtension (δ : Mukai.MukaiLattice ℤ) :
    Mukai.extendMap k3LatticeMap δ ∈
      Mukai.integralExtension (Submodule.span ℤ (Set.range surfaceDivisorBasis)) := by
  have hone : ∀ n : ℤ, ((n : ℝ)) ∈ Submodule.span ℤ ({(1 : ℝ)} : Set ℝ) := by
    intro n
    refine Submodule.mem_span_singleton.mpr ⟨n, ?_⟩
    simp
  have hrange : Set.range (surfaceDivisorBasis : Unit → SurfaceDivisor)
      = ({(1 : ℝ)} : Set ℝ) := by
    simp [surfaceDivisorBasis, Module.Basis.singleton, Set.range_unique]
  refine ⟨hone δ.1, ?_, hone δ.2.2⟩
  show k3LatticeMap δ.2.1 ∈ Submodule.span ℤ (Set.range surfaceDivisorBasis)
  rw [hrange, k3LatticeMap_apply]
  exact hone δ.2.1

/-! ### The spherical chart's integral comparison -/

/-- **The first witness for `Spherical.IntegralComparison`.**

`Walls/Spherical/Basic.lean` says of that structure: "it is supplied, never
constructed — producing one is the geometric obligation of exhibiting `NS(X)`
with its intersection form", and nothing in the tree constructed one, so
`pairing_map`, `selfPairing_map` and `isSpherical_map_iff` were all vacuous.

On the degree-`2d` K3 the obligation is discharged by the rank-one lattice
`ℤ·H`: the map is the inclusion of `ℤ` into the divisor line and the forms agree
by `k3LatticeMap_pairing`.

Note this is a **different** structure from the Mukai comparison above.  Its
`compat` field is stated on all of `ℤ`, not on the image of a first Chern class,
so it is a genuine comparison of forms rather than a constraint on one map. -/
def k3IntegralComparison (d : ℕ) :
    Wall.Spherical.IntegralComparison
      (surfaceDivisorSpace (2 * (d : ℝ))).intersection (k3MukaiForm d) where
  toFun := (k3LatticeMap : ℤ →ₗ[ℤ] SurfaceDivisor).toAddMonoidHom
  compat := k3LatticeMap_pairing d

@[simp]
theorem k3IntegralComparison_toFun (d : ℕ) (n : ℤ) :
    (k3IntegralComparison d).toFun n = ((n : ℤ) : ℝ) := rfl

/-- **Integral and real sphericality agree in the `(β, ω)` chart**, on the K3
model.  This is `isSpherical_map_iff` with the witness supplied. -/
theorem k3_isSpherical_map_iff (d : ℕ) (v : Mukai.MukaiLattice ℤ) :
    Wall.Spherical.IsSpherical (surfaceDivisorSpace (2 * (d : ℝ))).intersection
        ((k3IntegralComparison d).map v)
      ↔ Mukai.IsSpherical (k3MukaiForm d) v :=
  Wall.Spherical.isSpherical_map_iff (k3IntegralComparison d) v

/-- The spherical chart's comparison agrees with the period-domain one: both
send an integral class to the same real triple. -/
theorem k3IntegralComparison_map_eq_extendMap (d : ℕ) (v : Mukai.MukaiLattice ℤ) :
    (k3IntegralComparison d).map v = Mukai.extendMap k3LatticeMap v := rfl

/-! ### Wall finiteness, over integral classes -/

/-- The extension map is injective, because the integer cast is. -/
theorem extendMap_k3LatticeMap_injective :
    Function.Injective (Mukai.extendMap k3LatticeMap) := by
  intro u w h
  have h1 : ((u.1 : ℝ)) = ((w.1 : ℝ)) := congrArg Prod.fst h
  have h2 : ((u.2.1 : ℝ)) = ((w.2.1 : ℝ)) := congrArg (fun z => z.2.1) h
  have h3 : ((u.2.2 : ℝ)) = ((w.2.2 : ℝ)) := congrArg (fun z => z.2.2) h
  exact Prod.ext (Int.cast_injective h1)
    (Prod.ext (Int.cast_injective h2) (Int.cast_injective h3))

/-- **Only finitely many integral spherical classes of the Mukai lattice have a
wall meeting the parameter box.**

This is `k3_finite_walls_meeting_box` said over `Mukai.MukaiLattice ℤ` instead of
over the real extension.  It is the statement the geometry wants: the classes
counted are those with `⟪v, v⟫ = -2` in the integral lattice, which
`isSpherical_mukaiVector_iff` reads off `χ₂`.

Nothing new is assumed — only `d > 0` and `t₀ > 0`, as before. -/
theorem k3_finite_integral_spherical_walls (d : ℕ) (hd : d ≠ 0)
    (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    {δ : Mukai.MukaiLattice ℤ |
        Mukai.IsSpherical (k3MukaiForm d) δ ∧
        ∃ p ∈ parameterBox b₀ t₀ t₁,
          DivisorSpace.expPlane (surfaceDivisorSpace (2 * (d : ℝ))) p.1 p.2 ∈
            PeriodDomain.wall
              (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection)
              (Mukai.extendMap k3LatticeMap δ)}.Finite := by
  refine Set.Finite.of_finite_image ?_
    (Set.injOn_of_injective extendMap_k3LatticeMap_injective)
  refine (k3_finite_walls_meeting_box hd b₀ t₀ t₁ ht₀).subset ?_
  rintro _ ⟨δ, ⟨hsph, p, hp, hw⟩, rfl⟩
  exact ⟨k3_isSphericalClass_of_isSpherical d hsph, ⟨p, hp, hw⟩,
    k3_extendMap_mem_integralExtension δ⟩

end

end Examples

end AlgebraicGeometry.Numerical
