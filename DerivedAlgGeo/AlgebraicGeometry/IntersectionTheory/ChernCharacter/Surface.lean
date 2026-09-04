/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Surface.Number
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant

/-!
# Numerical Chern-character data on surfaces

This file constructs the surface components which can be recovered from determinants,
intersection numbers, and Euler characteristics without introducing a Chow group.

For a two-term perfect determinant package, the virtual rank is the difference of the ranks in
the resolution and `c₁` is its determinant class in `Pic X`.  An `IntersectionContext` in
dimension two supplies the structure-sheaf Euler function and the symmetric Picard intersection
pairing.  These determine the degree-level Todd terms by

`td₁ · L = χ(L) - χ(O_X) - L² / 2`,  `deg td₂ = χ(O_X)`,

and hence

`deg ch₂(F) = χ(F) - rank(F) deg td₂ - td₁ · c₁(F)`.

The output is deliberately degree-level in codimension two.  Recovering an element of an
arbitrary Layer A ring `A²` from its degree requires an explicit representability or
nondegeneracy hypothesis; no such assumption is hidden here.

As in `Divisors.Determinant`, arbitrary coherent sheaves are not silently declared perfect.
The API applies to coherent sheaves carrying explicit two-term perfect determinant data, and
rank additivity for three independently chosen resolutions remains an explicit hypothesis in
the short-exact theorem.
-/

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.IntersectionTheory.Number

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

noncomputable section

/-! ## Rank and first Chern class -/

/-- The virtual rank of a coherent sheaf presented by a two-term finite locally free
resolution. -/
def virtualRank {F : Coh X} (P : Coh.TwoTermPerfectDeterminantData F) : ℤ :=
  (P.middle.rank : ℤ) - (P.left.rank : ℤ)

/-- The determinant first Chern class, in the additive form of the Picard group. -/
def picardFirstChernClass {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) : Additive (Pic X) :=
  P.firstChernClassAdd

/-- The numerical first Chern class as the functional obtained by intersecting the determinant
class with every Picard class. -/
noncomputable def numericalFirstChernClass
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) :
    Additive (Pic X) →ₗ[ℤ] ℤ :=
  I.surfaceIntersectionPairing (picardFirstChernClass P)

@[simp]
theorem virtualRank_ofIso {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    virtualRank (P.ofIso e) = virtualRank P :=
  rfl

@[simp]
theorem picardFirstChernClass_ofIso {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    picardFirstChernClass (P.ofIso e) = picardFirstChernClass P :=
  rfl

@[simp]
theorem numericalFirstChernClass_ofIso
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    numericalFirstChernClass I (P.ofIso e) = numericalFirstChernClass I P :=
  rfl

/-! ## Todd pairings extracted from the structure-sheaf polynomial -/

/-- The degree-one Todd contribution paired with a Picard class:
`td₁ · L = χ(L) - χ(O_X) - L²/2`.

The polarization identity for the degree-two Picard Euler function proves that this expression
is additive in `L`. -/
noncomputable def toddOnePairing
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) : Additive (Pic X) →+ ℚ where
  toFun L :=
    ((I.eulerPic L.toMul - I.eulerPic 1 : ℤ) : ℚ) -
      (I.surfaceIntersectionPairing L L : ℤ) / 2
  map_zero' := by
    simp
  map_add' L M := by
    have hcross :
        I.surfaceIntersectionPairing L M =
          I.eulerPic (L.toMul * M.toMul) - I.eulerPic L.toMul -
            I.eulerPic M.toMul + I.eulerPic 1 := by
      change I.surfaceIntersectionPairing (Additive.ofMul L.toMul)
          (Additive.ofMul M.toMul) = _
      rw [I.surfaceIntersectionPairing_apply, I.surfaceIntersectionNumber_eq]
    have hsymm : I.surfaceIntersectionPairing M L =
        I.surfaceIntersectionPairing L M := by
      change I.surfaceIntersectionPairing (Additive.ofMul M.toMul)
          (Additive.ofMul L.toMul) =
        I.surfaceIntersectionPairing (Additive.ofMul L.toMul)
          (Additive.ofMul M.toMul)
      exact I.surfaceIntersectionPairing_symm M.toMul L.toMul
    change
      ((I.eulerPic (L.toMul * M.toMul) - I.eulerPic 1 : ℤ) : ℚ) -
          (I.surfaceIntersectionPairing (L + M) (L + M) : ℤ) / 2 =
        (((I.eulerPic L.toMul - I.eulerPic 1 : ℤ) : ℚ) -
          (I.surfaceIntersectionPairing L L : ℤ) / 2) +
        (((I.eulerPic M.toMul - I.eulerPic 1 : ℤ) : ℚ) -
          (I.surfaceIntersectionPairing M M : ℤ) / 2)
    simp only [map_add, LinearMap.add_apply]
    rw [hsymm]
    push_cast [hcross]
    ring

@[simp]
theorem toddOnePairing_apply
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) (L : Additive (Pic X)) :
    toddOnePairing I L =
      ((I.eulerPic L.toMul - I.eulerPic 1 : ℤ) : ℚ) -
        (I.surfaceIntersectionPairing L L : ℤ) / 2 :=
  rfl

/-- The top Todd degree on a surface is the Euler characteristic of its structure sheaf. -/
noncomputable def toddTwoDegree
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) : ℚ :=
  D.eulerCharacteristic (structureSheafObject I.structureSheafCoherent)

/-! ## Surface Chern character -/

/-- The numerical degree of `ch₂(F)`, recovered from Euler characteristic, rank, determinant,
and the structure-sheaf Todd data. -/
noncomputable def chernCharacterTwoDegree
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) : ℚ :=
  (D.eulerCharacteristic F : ℚ) -
    (virtualRank P : ℚ) * toddTwoDegree I -
      toddOnePairing I (picardFirstChernClass P)

variable (k) in
/-- The three surface Chern-character coordinates recovered without a Chow ring. -/
@[ext]
structure SurfaceChernCharacter (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsVariety k X] where
  rank : ℤ
  first : Additive (Pic X)
  secondDegree : ℚ

/-- Package the virtual rank, determinant first Chern class, and degree of `ch₂`. -/
noncomputable def surfaceChernCharacter
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) : SurfaceChernCharacter k X where
  rank := virtualRank P
  first := picardFirstChernClass P
  secondDegree := chernCharacterTwoDegree I P

/-- The defining surface Riemann--Roch identity for the recovered degree-level components. -/
theorem eulerCharacteristic_eq_rank_mul_toddTwo_add_toddOne_add_chernCharacterTwo
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) :
    (D.eulerCharacteristic F : ℚ) =
      (virtualRank P : ℚ) * toddTwoDegree I +
        toddOnePairing I (picardFirstChernClass P) +
          chernCharacterTwoDegree I P := by
  simp only [chernCharacterTwoDegree]
  ring

/-! ## Isomorphism invariance and exact-sequence additivity -/

@[simp]
theorem chernCharacterTwoDegree_ofIso
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    chernCharacterTwoDegree I (P.ofIso e) = chernCharacterTwoDegree I P := by
  simp only [chernCharacterTwoDegree, virtualRank_ofIso,
    picardFirstChernClass_ofIso]
  rw [D.eulerCharacteristic_iso e]

@[simp]
theorem surfaceChernCharacter_ofIso
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    surfaceChernCharacter I (P.ofIso e) = surfaceChernCharacter I P := by
  ext <;> simp [surfaceChernCharacter]

/-- Numerical first Chern classes are additive for a determinant-compatible short exact
sequence. -/
theorem numericalFirstChernClass_shortExact
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {S : ShortComplex (Coh X)}
    (P : Coh.PerfectShortExactDeterminantData S) :
    numericalFirstChernClass I P.middle =
      numericalFirstChernClass I P.left + numericalFirstChernClass I P.right := by
  unfold numericalFirstChernClass picardFirstChernClass
  rw [P.firstChernClassAdd_eq_add, map_add]

/-- Picard-valued first Chern classes are additive for a determinant-compatible short exact
sequence. -/
theorem picardFirstChernClass_shortExact
    {S : ShortComplex (Coh X)}
    (P : Coh.PerfectShortExactDeterminantData S) :
    picardFirstChernClass P.middle =
      picardFirstChernClass P.left + picardFirstChernClass P.right :=
  P.firstChernClassAdd_eq_add

/-- `ch₂` is additive on a determinant-compatible coherent short exact sequence once the
independently chosen two-term resolutions are also known to have additive virtual ranks. -/
theorem chernCharacterTwoDegree_shortExact
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {S : ShortComplex (Coh X)}
    (P : Coh.PerfectShortExactDeterminantData S)
    (hrank : virtualRank P.middle = virtualRank P.left + virtualRank P.right) :
    chernCharacterTwoDegree I P.middle =
      chernCharacterTwoDegree I P.left + chernCharacterTwoDegree I P.right := by
  have hchi := D.eulerCharacteristic_additive (C S P.shortExact)
  have hc₁ := P.firstChernClassAdd_eq_add
  unfold chernCharacterTwoDegree picardFirstChernClass
  rw [hchi, hrank, hc₁, map_add]
  push_cast
  ring

/-! ## Structure sheaves and line bundles -/

/-- The structure sheaf has `ch₂ = 0` for any explicit determinant presentation with rank one
and trivial determinant class. -/
theorem chernCharacterTwoDegree_structureSheaf
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2)
    (P : Coh.TwoTermPerfectDeterminantData
      (structureSheafObject I.structureSheafCoherent))
    (hrank : virtualRank P = 1)
    (hc₁ : picardFirstChernClass P = 0) :
    chernCharacterTwoDegree I P = 0 := by
  unfold chernCharacterTwoDegree toddTwoDegree
  rw [hrank, hc₁, map_zero]
  norm_num

/-- The Picard Euler function takes the trivial class to the actual Euler characteristic of the
structure sheaf. -/
theorem eulerPic_one_eq_eulerCharacteristic_structureSheaf
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) :
    I.eulerPic 1 =
      D.eulerCharacteristic (structureSheafObject I.structureSheafCoherent) := by
  let L : Fin 0 → Pic X := fun i ↦ Fin.elim0 i
  have h := I.twists.realization 0 L (0 : Fin 0 → ℤ)
  rw [picardMonomial_zero] at h
  calc
    I.eulerPic 1 = D.eulerCharacteristic ((I.twists.twistFamily 0 L).obj 0) := h
    _ = D.eulerCharacteristic (structureSheafObject I.structureSheafCoherent) := by
      apply D.eulerCharacteristic_iso
      apply ObjectProperty.isoMk (Scheme.coherent X)
      simpa [Snapper.CoherentTwistFamily.obj, Snapper.twistModules,
        Snapper.twistModulesAlong] using
        (Iso.refl (structureSheafObject I.structureSheafCoherent).1)

/-- The two equivalent descriptions of the top Todd degree: `χ(O_X)` and the Picard Euler
function at the trivial class. -/
theorem toddTwoDegree_eq_eulerPic_one
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) :
    toddTwoDegree I = (I.eulerPic 1 : ℚ) := by
  rw [toddTwoDegree, eulerPic_one_eq_eulerCharacteristic_structureSheaf I]

/-- A rank-one coherent sheaf whose determinant class is `L` and whose Euler characteristic is
the Picard Euler value of `L` has the usual line-bundle formula `deg ch₂ = L²/2`.

The Euler-value hypothesis is supplied, for actual representatives in the intersection context,
by its `TwistContext.realization` field and is explicit for any independently chosen coherent
representative. -/
theorem chernCharacterTwoDegree_lineBundle
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (L : Pic X)
    (hrank : virtualRank P = 1)
    (hc₁ : picardFirstChernClass P = Additive.ofMul L)
    (hchi : D.eulerCharacteristic F = I.eulerPic L) :
    chernCharacterTwoDegree I P =
      (I.surfaceIntersectionNumber L L : ℚ) / 2 := by
  rw [chernCharacterTwoDegree, hrank, hc₁, hchi, toddTwoDegree,
    ← eulerPic_one_eq_eulerCharacteristic_structureSheaf I]
  simp only [toddOnePairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    I.surfaceIntersectionPairing_apply, toMul_ofMul]
  push_cast
  ring

/-! ## Discriminant and Layer A compatibility -/

/-- The degree of the surface discriminant `Δ(F) = c₁(F)² - 2 rank(F) ch₂(F)`. -/
noncomputable def discriminantDegree
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) : ℚ :=
  (I.surfaceIntersectionPairing (picardFirstChernClass P)
      (picardFirstChernClass P) : ℤ) -
    2 * (virtualRank P : ℚ) * chernCharacterTwoDegree I P

@[simp]
theorem discriminantDegree_ofIso
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F G : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    discriminantDegree I (P.ofIso e) = discriminantDegree I P := by
  simp [discriminantDegree]

/-- Compatibility with the degree of the Layer A numerical discriminant.  The hypotheses state
exactly that a proposed Layer A class realizes the rank, `c₁²`, and degree-level `ch₂`
constructed here. -/
theorem discriminantDegree_eq_numericalVariety
    {D : FiniteCohomology k X} {C : D.LinearConnectingSystem}
    (I : IntersectionContext D C 2) {F : Coh X}
    (P : Coh.TwoTermPerfectDeterminantData F)
    {A : Type v} {N : Type w} [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] (V : NumericalVarietyData 2 A N) (E : N)
    (hrank : V.rank E = virtualRank P)
    (hc₁ : V.ring.degree (V.chComp E 1 * V.chComp E 1) =
      (I.surfaceIntersectionPairing (picardFirstChernClass P)
        (picardFirstChernClass P) : ℤ))
    (hch₂ : V.ring.degree (V.chComp E 2) =
      chernCharacterTwoDegree I P) :
    discriminantDegree I P = V.ring.degree (V.discriminant E) := by
  rw [V.degree_discriminant, hrank, hc₁, hch₂]
  simp only [discriminantDegree]

end

end AlgebraicGeometry.IntersectionTheory.ChernCharacterSurface
