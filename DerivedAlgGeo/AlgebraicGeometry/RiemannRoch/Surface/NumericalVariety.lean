/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Variety.Numerical
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.ChernCharacter.Basic
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Lattice
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-!
# A geometric numerical variety for surfaces

This file is the assembly point from the geometric surface theory to Layer A.  It does two
things which should not be hidden behind instances:

* an invariant of coherent sheaves which respects isomorphisms and short exact sequences is
  descended through the explicit Grothendieck group `K₀(Coh X)`;
* reconstructed surface Chern characters, geometric Todd components, and geometric
  Hirzebruch--Riemann--Roch are packaged as a genuine `NumericalVarietyData`.

The construction uses `K₀(Coh X)` as its input group.  The numerical Grothendieck group is then
the Euler-radical quotient from `Numerical/GrothendieckGroup/Lattice.lean`; in particular the
quotient and sign conventions are shared with Layer A rather than reconstructed here.

`GeometricData.sheaf_hirzebruch_riemannRoch` is a theorem about every coherent sheaf, not a
Layer A axiom about arbitrary Grothendieck classes.  The latter is proved below by descending
both sides as additive invariants. Thus `toNumericalVariety` selects the data, while
`toNumericalVariety_satisfiesHRR` supplies its separate HRR witness.
-/

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.RiemannRoch.Surface

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.IntersectionTheory.Number
open scoped BigOperators

variable {k : Type u} [Field k]
variable {X : Variety k}

noncomputable section

/-! ## Reconstructed Chern characters on `K₀` -/

variable {D : FiniteCohomology X}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {P : PairingContext D C 2 A}
variable {O : Coh X.toScheme}
variable (RO : P.ReconstructionData O)

/-- A compatible choice of reconstruction data for every coherent sheaf.

The comparison fields are the exact hypotheses needed by the reconstruction theorems.  They
are separated from `GeometricData` because they already suffice to descend rank and Chern
character to the coherent Grothendieck group. -/
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

/-- Rank as an additive invariant of coherent sheaves. -/
noncomputable def rankInvariant (R : ReconstructionSystem (P := P)) :
    K₀Ab (Coh X.toScheme) →+ ℤ :=
  K₀Ab.liftOf (fun F => (R.reconstruction F).rank)
    (fun S hS => R.rank_shortExact S hS)

/-- The reconstructed `i`-th Chern-character component, valued in its certified graded piece,
as an additive invariant of coherent sheaves. -/
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

/-- Rank on `K₀(Coh X)`. -/
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
    (RO : P.ReconstructionData O)
    (F : Coh X.toScheme) (i : ℕ) :
    R.chernCharacterHom RO i (K₀Ab.of F) =
      chernCharacterComponent RO (R.reconstruction F) i := by
  simp [chernCharacterHom, chernCharacterInvariant]

/-- Every descended Chern-character component remains in the correct graded piece. -/
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

/-- The reconstructed zeroth Chern character is the algebra image of numerical rank on every
Grothendieck class, not only on sheaf generators. -/
theorem chernCharacterHom_zero (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E : K₀Ab (Coh X.toScheme)) :
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

/-! ## Surface assembly and Hirzebruch--Riemann--Roch -/

/-- Geometric input which assembles the coherent Grothendieck group into a Layer A numerical
surface.

The sheaf-level HRR property is deliberately kept separate from this selected data. Its proof
for every virtual Grothendieck class is `GeometricData.hirzebruch_riemannRoch` below. -/
structure GeometricData (RO : P.ReconstructionData O)
    (R : ReconstructionSystem (P := P)) where
  /-- The geometrically constructed Todd components. -/
  toddComponent : ℕ → A
  /-- Todd components carry their geometric grading. -/
  toddComponent_mem : ∀ i,
    toddComponent i ∈ P.ring.piece i
  /-- The degree-zero Todd component is normalized to one. -/
  toddComponent_zero : toddComponent 0 = 1

/-- Geometric surface HRR for coherent sheaves, as a proposition-valued
property of the selected geometric data. -/
structure GeometricData.SatisfiesSheafHRR
    {R : ReconstructionSystem (P := P)} (G : GeometricData RO R) : Prop where
  /-- Geometric surface HRR for coherent sheaves. -/
  eq : ∀ F : Coh X.toScheme,
    (D.eulerCharacteristic F : ℚ) = P.ring.degree
      ((∑ i ∈ Finset.range 3,
          chernCharacterComponent RO (R.reconstruction F) i) *
        (∑ j ∈ Finset.range 3, G.toddComponent j))

namespace GeometricData

variable {R : ReconstructionSystem (P := P)}

/-- The total reconstructed Chern character as an additive homomorphism on `K₀`. -/
noncomputable def totalChernCharacterHom (_G : GeometricData RO R) :
    K₀Ab (Coh X.toScheme) →+ A :=
  ∑ i ∈ Finset.range 3, R.chernCharacterHom RO i

/-- The total geometric Todd class of the surface. -/
noncomputable def totalTodd (G : GeometricData RO R) : A :=
  ∑ j ∈ Finset.range 3, G.toddComponent j

/-- The right side of HRR, as an additive homomorphism on `K₀`. -/
noncomputable def riemannRochHom (G : GeometricData RO R) :
    K₀Ab (Coh X.toScheme) →+ ℚ where
  toFun E := P.ring.degree
    (totalChernCharacterHom (RO := RO) G E * totalTodd (RO := RO) G)
  map_zero' := by simp [totalChernCharacterHom]
  map_add' E F := by
    rw [map_add, add_mul, map_add]

/-- Cast the cohomological Euler homomorphism from `ℤ` to `ℚ`. -/
noncomputable def rationalEulerHom (_G : GeometricData RO R) :
    K₀Ab (Coh X.toScheme) →+ ℚ where
  toFun E := (D.grothendieckEulerHom C E : ℚ)
  map_zero' := by simp
  map_add' E F := by simp

@[simp]
theorem totalChernCharacterHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    totalChernCharacterHom (RO := RO) G (K₀Ab.of F) =
      ∑ i ∈ Finset.range 3,
        chernCharacterComponent RO (R.reconstruction F) i := by
  simp [totalChernCharacterHom]

@[simp]
theorem riemannRochHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    riemannRochHom (RO := RO) G (K₀Ab.of F) =
      P.ring.degree
        ((∑ i ∈ Finset.range 3,
            chernCharacterComponent RO (R.reconstruction F) i) *
          (∑ j ∈ Finset.range 3, G.toddComponent j)) := by
  simp [riemannRochHom, totalTodd]

@[simp]
theorem rationalEulerHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    rationalEulerHom (RO := RO) G (K₀Ab.of F) =
      (D.eulerCharacteristic F : ℚ) := by
  simp [rationalEulerHom]

/-- Geometric HRR descends from coherent sheaves to every virtual Grothendieck class. -/
theorem hirzebruch_riemannRoch (G : GeometricData RO R)
    (hG : G.SatisfiesSheafHRR)
    (E : K₀Ab (Coh X.toScheme)) :
    (D.grothendieckEulerHom C E : ℚ) = P.ring.degree
      ((∑ i ∈ Finset.range 3, R.chernCharacterHom RO i E) *
        (∑ j ∈ Finset.range 3, G.toddComponent j)) := by
  have hhom : rationalEulerHom (RO := RO) G = riemannRochHom (RO := RO) G := by
    apply K₀Ab.hom_ext
    intro F
    rw [rationalEulerHom_class (RO := RO) G,
      riemannRochHom_class (RO := RO) G]
    exact hG.eq F
  change rationalEulerHom (RO := RO) G E = riemannRochHom (RO := RO) G E
  exact DFunLike.congr_fun hhom E

/-- The selected scheme-derived numerical surface. Its separate HRR witness is
`toNumericalVariety_satisfiesHRR`, proved by Grothendieck descent. -/
@[reducible]
noncomputable def toNumericalVariety (G : GeometricData RO R) :
    NumericalVarietyData 2 A (K₀Ab (Coh X.toScheme)) where
  ring := P.ring
  rank := R.rankHom
  chComp E i := R.chernCharacterHom RO i E
  chComp_mem := R.chernCharacterHom_mem RO
  chComp_zero := R.chernCharacterHom_zero RO
  chComp_add := R.chernCharacterHom_add RO
  toddComp := G.toddComponent
  toddComp_mem := G.toddComponent_mem
  toddComp_zero := G.toddComponent_zero
  chi := D.grothendieckEulerHom C

/-- The descended coherent-sheaf HRR proof supplies numerical HRR. -/
theorem toNumericalVariety_satisfiesHRR (G : GeometricData RO R)
    (hG : G.SatisfiesSheafHRR) : G.toNumericalVariety.SatisfiesHRR :=
  ⟨hirzebruch_riemannRoch (RO := RO) G hG⟩

theorem toNumericalVariety_rank_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    G.toNumericalVariety.rank (K₀Ab.of F) =
      (R.reconstruction F).rank := by
  change R.rankHom (K₀Ab.of F) = (R.reconstruction F).rank
  exact R.rankHom_class F

theorem toNumericalVariety_chComp_class (G : GeometricData RO R)
    (F : Coh X.toScheme) (i : ℕ) :
    G.toNumericalVariety.chComp (K₀Ab.of F) i =
      chernCharacterComponent RO (R.reconstruction F) i := by
  change R.chernCharacterHom RO i (K₀Ab.of F) =
    chernCharacterComponent RO (R.reconstruction F) i
  exact R.chernCharacterHom_class RO F i

@[simp]
theorem toNumericalVariety_toddComp (G : GeometricData RO R) (i : ℕ) :
    G.toNumericalVariety.toddComp i = G.toddComponent i :=
  rfl

theorem toNumericalVariety_chi_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    G.toNumericalVariety.chi (K₀Ab.of F) =
      D.eulerCharacteristic F := by
  change D.grothendieckEulerHom C (K₀Ab.of F) =
    D.eulerCharacteristic F
  exact D.grothendieckEulerHom_class C F

/-- On a coherent-sheaf class, the Layer A surface expansion is exactly the geometric
rank/`ch₁`/`ch₂` expansion used to construct the presentation. -/
theorem surface_chi_class_eq (G : GeometricData RO R)
    (hG : G.SatisfiesSheafHRR)
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      ((R.reconstruction F).rank : ℚ) *
          P.ring.degree (G.toddComponent 2) +
        P.ring.degree
          (chernCharacterComponent RO (R.reconstruction F) 1 *
            G.toddComponent 1) +
        P.ring.degree
          (chernCharacterComponent RO (R.reconstruction F) 2) := by
  have h := AlgebraicGeometry.Numerical.Surface.chi_eq G.toNumericalVariety
    (toNumericalVariety_satisfiesHRR (RO := RO) G hG) (K₀Ab.of F)
  rw [toNumericalVariety_chi_class (RO := RO) G F,
    toNumericalVariety_rank_class (RO := RO) G F,
    toNumericalVariety_toddComp (RO := RO) G 2,
    toNumericalVariety_chComp_class (RO := RO) G F 1,
    toNumericalVariety_toddComp (RO := RO) G 1,
    toNumericalVariety_chComp_class (RO := RO) G F 2] at h
  exact h

/-- The geometric K3 hypotheses give the existing Layer A K3 structure on the assembled
surface. -/
theorem toIsK3 (G : GeometricData RO R)
    (htoddOne : G.toddComponent 1 = 0)
    (htoddTwo : P.ring.degree (G.toddComponent 2) = 2) :
    K3.IsK3 G.toNumericalVariety := by
  exact
    { toddComp_one := htoddOne
      degree_toddComp_two := htoddTwo }

/-- Under the geometric K3 hypotheses, the existing Layer A K3 Riemann--Roch theorem becomes
the corresponding statement for every coherent sheaf. -/
theorem k3_eulerCharacteristic_eq (G : GeometricData RO R)
    (hG : G.SatisfiesSheafHRR)
    (htoddOne : G.toddComponent 1 = 0)
    (htoddTwo : P.ring.degree (G.toddComponent 2) = 2)
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      2 * ((R.reconstruction F).rank : ℚ) +
        P.ring.degree
          (chernCharacterComponent RO (R.reconstruction F) 2) := by
  have h := K3.chi_eq G.toNumericalVariety
    (toNumericalVariety_satisfiesHRR (RO := RO) G hG)
    (toIsK3 (RO := RO) G htoddOne htoddTwo) (K₀Ab.of F)
  rw [toNumericalVariety_chi_class (RO := RO) G F,
    toNumericalVariety_rank_class (RO := RO) G F,
    toNumericalVariety_chComp_class (RO := RO) G F 2] at h
  exact h

/-- The numerical class of a coherent sheaf: first its coherent-Grothendieck class, then the
Euler-radical quotient fixed by Layer A. -/
noncomputable def numericalClass (G : GeometricData RO R) (F : Coh X.toScheme) :
    NumericalVarietyData.NumericalQuotient G.toNumericalVariety :=
  Submodule.Quotient.mk (K₀Ab.of F)

end GeometricData

end

end AlgebraicGeometry.RiemannRoch.Surface
