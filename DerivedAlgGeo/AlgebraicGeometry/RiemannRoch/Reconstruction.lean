/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.ChernCharacter.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.CharacteristicClasses
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Reconstruction systems, in any dimension

A `ReconstructionSystem` picks reconstruction data for every coherent sheaf,
compatibly with isomorphism and with short exact sequences, and thereby descends
rank and the Chern-character components to `K₀Ab (Coh X)`.

Nothing here mentions a dimension: the structure is stated over
`PairingContext D C d A` for an arbitrary `d`.

## Why this file exists

It was declared twice. `HigherDimension/Hirzebruch.lean` had it at `d`, and
`Surface/NumericalVariety.lean` had it again at `d = 2` -- eleven declarations,
identical to the token across roughly eighty lines of code, differing only in
line wrapping and two docstring phrasings. The surface case is the general case
at `d = 2`, so it is now obtained rather than restated.

Placing it here rather than in `HigherDimension/` is the point: a
dimension-general structure does not belong in a namespace named for one range
of dimensions, and `Surface` should not have to import `HigherDimension` to
reach it.
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.IntersectionTheory.Number
open scoped BigOperators

noncomputable section

variable {k : Type u} [Field k]
variable {X : Variety k}
variable {D : FiniteCohomology X}
variable {C : D.LinearConnectingSystem}
variable {d : ℕ}
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {P : PairingContext D C d A}
variable {O : Coh X.toScheme}

/-! ## Dimension-general descent through `K₀(Coh X)` -/

/-- A compatible choice of reconstruction data for every coherent sheaf in dimension `d`. -/
structure ReconstructionSystem where
  /-- Reconstruction data for every coherent sheaf. -/
  reconstruction : ∀ F : Coh X.toScheme, P.ReconstructionData F
  /-- Rank is invariant under coherent-sheaf isomorphism. -/
  rank_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).rank = (reconstruction G).rank
  /-- Twist Euler functions are invariant under coherent-sheaf isomorphism. -/
  eulerPic_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).twists.eulerPic = (reconstruction G).twists.eulerPic
  /-- Rank is additive in a short exact sequence. -/
  rank_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).rank =
      (reconstruction S.X₁).rank + (reconstruction S.X₃).rank
  /-- Twist Euler functions are additive in a short exact sequence. -/
  eulerPic_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).twists.eulerPic =
      (reconstruction S.X₁).twists.eulerPic +
        (reconstruction S.X₃).twists.eulerPic

namespace ReconstructionSystem

/-- Reconstructed rank as an additive coherent-sheaf invariant. -/
noncomputable def rankInvariant (R : ReconstructionSystem (P := P)) :
    K₀Ab (Coh X.toScheme) →+ ℤ :=
  K₀Ab.liftOf (fun F => (R.reconstruction F).rank)
    (fun S hS => R.rank_shortExact S hS)

/-- The reconstructed `i`-th Chern-character component as an additive coherent-sheaf
invariant valued in the certified graded piece. -/
noncomputable def chernCharacterInvariant (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    K₀Ab (Coh X.toScheme) →+ (P.ring.piece i) :=
  K₀Ab.liftOf
    (fun F => ⟨chernCharacterComponent RO (R.reconstruction F) i,
      chernCharacterComponent_mem RO (R.reconstruction F) i⟩)
    (by
      intro S hS
      apply Subtype.ext
      exact chernCharacterComponent_add RO (R.reconstruction S.X₁)
        (R.reconstruction S.X₃) (R.reconstruction S.X₂)
        (R.rank_shortExact S hS) (R.eulerPic_shortExact S hS) i)

/-- Reconstructed rank on `K₀(Coh X)`. -/
noncomputable def rankHom (R : ReconstructionSystem (P := P)) :
    K₀Ab (Coh X.toScheme) →+ ℤ :=
  R.rankInvariant

/-- The reconstructed `i`-th Chern-character component on `K₀(Coh X)`. -/
noncomputable def chernCharacterHom (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    K₀Ab (Coh X.toScheme) →+ A :=
  (P.ring.piece i).subtype.toAddMonoidHom.comp
    (R.chernCharacterInvariant RO i)

@[simp]
theorem rankHom_class (R : ReconstructionSystem (P := P)) (F : Coh X.toScheme) :
    R.rankHom (K₀Ab.of F) = (R.reconstruction F).rank := by
  simp [rankHom, rankInvariant]

@[simp]
theorem chernCharacterHom_class (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (F : Coh X.toScheme) (i : ℕ) :
    R.chernCharacterHom RO i (K₀Ab.of F) =
      chernCharacterComponent RO (R.reconstruction F) i := by
  simp [chernCharacterHom, chernCharacterInvariant]

/-- Every descended Chern-character component remains in its graded piece. -/
theorem chernCharacterHom_mem (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E : K₀Ab (Coh X.toScheme)) (i : ℕ) :
    R.chernCharacterHom RO i E ∈ P.ring.piece i :=
  (R.chernCharacterInvariant RO i E).property

/-- The rational algebra map restricted to integral ranks. -/
noncomputable def intAlgebraMap : ℤ →+ A where
  toFun r := algebraMap ℚ A (r : ℚ)
  map_zero' := by simp
  map_add' r s := by simp

/-- The descended zeroth Chern character is the algebra image of rank. -/
theorem chernCharacterHom_zero (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (E : K₀Ab (Coh X.toScheme)) :
    R.chernCharacterHom RO 0 E = algebraMap ℚ A (R.rankHom E : ℚ) := by
  have hhom : R.chernCharacterHom RO 0 =
      (intAlgebraMap (A := A)).comp R.rankHom := by
    apply K₀Ab.hom_ext
    intro F
    simp [intAlgebraMap]
  exact DFunLike.congr_fun hhom E

theorem chernCharacterHom_add (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E F : K₀Ab (Coh X.toScheme)) (i : ℕ) :
    R.chernCharacterHom RO i (E + F) =
      R.chernCharacterHom RO i E + R.chernCharacterHom RO i F :=
  map_add _ _ _

end ReconstructionSystem

end

end AlgebraicGeometry.RiemannRoch
