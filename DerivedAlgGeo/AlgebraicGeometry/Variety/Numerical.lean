/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Variety.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Basic
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.CharacteristicClasses
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.Definitions

/-!
# Realizing a geometric variety numerically

`Variety.NumericalData` is the first explicit bridge from the geometric half of DerivedAlgGeo to
the numerical half. Its source is a genuine `Variety k` and coherent sheaves on its underlying
scheme. Its target is a numerical intersection ring `A`, a numerical Grothendieck group `N`,
and ultimately a `NumericalVarietyData n A N`.

The important direction of construction is encoded in the fields:

* coherent sheaves map to numerical classes, invariant under isomorphism and additive in
  short exact sequences;
* Chern classes are primary data;
* `chComp` is computed from those Chern classes by the universal formulas in
  `AlgebraicGeometry/Numerical/Core/CharacteristicClasses.lean`;
* `toddComp` is computed from the Chern classes of the tangent bundle;
* geometric Chern classes and Euler characteristics agree with their numerical descendants.

The remaining hard mathematics is visible rather than hidden. A realization must still prove
gradedness, additivity of the computed Chern character, and Hirzebruch--Riemann--Roch. Those
proofs will be supplied by the future geometric Chern-class and Riemann--Roch developments.

The current characteristic-class API is complete through codimension four, so this first
constructor records `n ≤ 4`. Extending the universal power-series implementation removes that
bound without changing the realization structure conceptually.
-/

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace Variety

open Numerical Numerical.NumericalRingData

variable {k : Type w} [Field k]

/-- Certified data exhibiting how a geometric variety descends to a numerical variety.

`NumericalRingData n A` is an input because constructing the numerical intersection ring is a
separate geometric task. This structure then derives the numerical Chern character and Todd
components from Chern-class data and packages all compatibility obligations needed for
`NumericalVarietyData`. -/
structure NumericalData (X : Variety k) (n : ℕ) (A : Type u) (N : Type v)
    [CommRing A] [Algebra ℚ A] [AddCommGroup N] where
  /-- The selected numerical intersection-ring presentation. -/
  ring : NumericalRingData n A
  /-- The component formulas currently supplied cover every codimension of `X`. -/
  dimension_le_four : n ≤ 4
  /-- The numerical class, as a hom out of the Grothendieck group of `Coh X`.

  This was a function together with `classOf_iso` and `classOf_shortExact`. Those
  two laws say exactly that the function factors through `K₀Ab`, so they are not
  data: they are `K₀Ab.of_iso` and `K₀Ab.of_shortExact` composed with this hom,
  and they survive as theorems of the same names and argument shapes below. -/
  classOfHom : K₀Ab (Coh X.toScheme) →+ N
  /-- Rank on the numerical Grothendieck group. -/
  rank : N →+ ℤ
  /-- Chern classes of a numerical class. -/
  chernClasses : N → ChernClassData A
  /-- The rank stored with the Chern classes agrees with numerical rank. -/
  chernClasses_rank : ∀ E : N, (chernClasses E).rank = rank E
  /-- Chern classes constructed geometrically for coherent sheaves. -/
  coherentChernClasses : Coh X.toScheme → ChernClassData A
  /-- Geometric Chern classes descend through the numerical class map. -/
  coherentChernClasses_classOf : ∀ F : Coh X.toScheme,
    chernClasses (classOfHom (K₀Ab.of F)) = coherentChernClasses F
  /-- The universally computed Chern-character components have the expected grading. -/
  chernCharacter_mem : ∀ (E : N) (i : ℕ),
    ChernClassData.chernCharacterComponent (chernClasses E) i ∈ ring.piece i
  /-- The universally computed Chern character is additive on numerical classes. -/
  chernCharacter_add : ∀ (E F : N) (i : ℕ),
    ChernClassData.chernCharacterComponent (chernClasses (E + F)) i =
      ChernClassData.chernCharacterComponent (chernClasses E) i +
        ChernClassData.chernCharacterComponent (chernClasses F) i
  /-- Chern classes of the tangent bundle, used to compute the Todd class. -/
  tangentChernClasses : ChernClassData A
  /-- The universally computed Todd components have the expected grading. -/
  todd_mem : ∀ i : ℕ,
    ChernClassData.toddComponent tangentChernClasses i ∈ ring.piece i
  /-- Euler characteristic on numerical classes. -/
  chi : N →+ ℤ
  /-- Finite-dimensional derived cohomology from which the geometric Euler characteristic is
  constructed. -/
  finiteCohomology : Cohomology.FiniteCohomology X
  /-- The cohomological Euler characteristic descends through the numerical class map. -/
  coherentEulerCharacteristic_classOf : ∀ F : Coh X.toScheme,
    chi (classOfHom (K₀Ab.of F)) = finiteCohomology.eulerCharacteristic F

namespace NumericalData

variable {X : Variety k} {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

/-- Hirzebruch--Riemann--Roch as a property of geometric numerical data, kept
separate from the selected realization. -/
structure SatisfiesHRR (D : NumericalData X n A N) : Prop where
  eq : ∀ E : N, (D.chi E : ℚ) = D.ring.degree
    ((∑ i ∈ Finset.range (n + 1),
        ChernClassData.chernCharacterComponent (D.chernClasses E) i) *
      (∑ j ∈ Finset.range (n + 1),
        ChernClassData.toddComponent D.tangentChernClasses j))

/-- The geometric Euler characteristic used by a numerical realization, constructed from its
finite-dimensional derived cohomology. -/
noncomputable abbrev coherentEulerCharacteristic (D : NumericalData X n A N) :
    Coh X.toScheme → ℤ :=
  D.finiteCohomology.eulerCharacteristic

/-- Construct the numerical variety certified by geometric `NumericalData`.

Unlike the original direct model definitions, the Chern-character and Todd components are not
independent fields here: they are definitionally the universal expressions in the supplied
Chern classes. -/
@[reducible]
noncomputable def toNumericalVariety (D : NumericalData X n A N) : NumericalVarietyData n A N where
  ring := D.ring
  rank := D.rank
  chComp := fun E i => ChernClassData.chernCharacterComponent (D.chernClasses E) i
  chComp_mem := D.chernCharacter_mem
  chComp_zero := by
    intro E
    rw [ChernClassData.chernCharacterComponent_zero, D.chernClasses_rank]
  chComp_add := D.chernCharacter_add
  toddComp := ChernClassData.toddComponent D.tangentChernClasses
  toddComp_mem := D.todd_mem
  toddComp_zero := ChernClassData.toddComponent_zero _
  chi := D.chi

/-- A geometric HRR proof induces the proposition-valued numerical HRR witness. -/
theorem toNumericalVariety_satisfiesHRR (D : NumericalData X n A N)
    (hD : SatisfiesHRR D) : D.toNumericalVariety.SatisfiesHRR :=
  ⟨hD.eq⟩

@[simp] theorem toNumericalVariety_rank (D : NumericalData X n A N) :
    D.toNumericalVariety.rank = D.rank := rfl

@[simp] theorem toNumericalVariety_chComp (D : NumericalData X n A N) (E : N) (i : ℕ) :
    D.toNumericalVariety.chComp E i =
      ChernClassData.chernCharacterComponent (D.chernClasses E) i := rfl

@[simp] theorem toNumericalVariety_toddComp (D : NumericalData X n A N) (i : ℕ) :
    D.toNumericalVariety.toddComp i =
      ChernClassData.toddComponent D.tangentChernClasses i := rfl

/-- The second Chern-character component produced by a realization. -/
theorem toNumericalVariety_chComp_two (D : NumericalData X n A N) (E : N) :
    D.toNumericalVariety.chComp E 2 = algebraMap ℚ A (1 / 2) *
      ((D.chernClasses E).c 1 ^ 2 - 2 * (D.chernClasses E).c 2) := rfl

/-- The third Chern-character component produced by a realization. -/
theorem toNumericalVariety_chComp_three (D : NumericalData X n A N) (E : N) :
    D.toNumericalVariety.chComp E 3 = algebraMap ℚ A (1 / 6) *
      ((D.chernClasses E).c 1 ^ 3
        - 3 * (D.chernClasses E).c 1 * (D.chernClasses E).c 2
        + 3 * (D.chernClasses E).c 3) := rfl

/-- The fourth Chern-character component produced by a realization. -/
theorem toNumericalVariety_chComp_four (D : NumericalData X n A N) (E : N) :
    D.toNumericalVariety.chComp E 4 = algebraMap ℚ A (1 / 24) *
      ((D.chernClasses E).c 1 ^ 4
        - 4 * (D.chernClasses E).c 1 ^ 2 * (D.chernClasses E).c 2
        + 2 * (D.chernClasses E).c 2 ^ 2
        + 4 * (D.chernClasses E).c 1 * (D.chernClasses E).c 3
        - 4 * (D.chernClasses E).c 4) := rfl

/-- The second Todd component produced from the tangent Chern classes. -/
theorem toNumericalVariety_toddComp_two (D : NumericalData X n A N) :
    D.toNumericalVariety.toddComp 2 = algebraMap ℚ A (1 / 12) *
      (D.tangentChernClasses.c 1 ^ 2 + D.tangentChernClasses.c 2) := rfl

/-- The third Todd component produced from the tangent Chern classes. -/
theorem toNumericalVariety_toddComp_three (D : NumericalData X n A N) :
    D.toNumericalVariety.toddComp 3 = algebraMap ℚ A (1 / 24) *
      (D.tangentChernClasses.c 1 * D.tangentChernClasses.c 2) := rfl

/-- The fourth Todd component produced from the tangent Chern classes. -/
theorem toNumericalVariety_toddComp_four (D : NumericalData X n A N) :
    D.toNumericalVariety.toddComp 4 = algebraMap ℚ A (1 / 720) *
      (-D.tangentChernClasses.c 1 ^ 4
        + 4 * D.tangentChernClasses.c 1 ^ 2 * D.tangentChernClasses.c 2
        + 3 * D.tangentChernClasses.c 2 ^ 2
        + D.tangentChernClasses.c 1 * D.tangentChernClasses.c 3
        - D.tangentChernClasses.c 4) := rfl

@[simp] theorem toNumericalVariety_chi (D : NumericalData X n A N) :
    D.toNumericalVariety.chi = D.chi := rfl

/-- The numerical class of a coherent sheaf. -/
noncomputable abbrev classOf (D : NumericalData X n A N) (F : Coh X.toScheme) : N :=
  D.classOfHom (K₀Ab.of F)

@[simp]
theorem classOf_apply (D : NumericalData X n A N) (F : Coh X.toScheme) :
    D.classOf F = D.classOfHom (K₀Ab.of F) := rfl

theorem classOfHom_of_iso (D : NumericalData X n A N) {F G : Coh X.toScheme} (e : F ≅ G) :
    D.classOfHom (K₀Ab.of F) = D.classOfHom (K₀Ab.of G) := by
  rw [K₀Ab.of_iso e]

theorem classOfHom_of_shortExact (D : NumericalData X n A N)
    (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact) :
    D.classOfHom (K₀Ab.of S.X₂) =
      D.classOfHom (K₀Ab.of S.X₁) + D.classOfHom (K₀Ab.of S.X₃) := by
  rw [K₀Ab.of_shortExact S hS, map_add]

/-! ### The two formal laws, now theorems

`classOf_iso` and `classOf_shortExact` were fields. They are `K₀Ab.of_iso` and
`K₀Ab.of_shortExact` composed with `classOfHom`, so they are proved here and the
names and argument shapes are unchanged. -/

theorem classOf_iso (D : NumericalData X n A N) {F G : Coh X.toScheme} (e : F ≅ G) :
    D.classOf F = D.classOf G := by
  rw [classOf, classOf, K₀Ab.of_iso e]

theorem classOf_shortExact (D : NumericalData X n A N)
    (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact) :
    D.classOf S.X₂ = D.classOf S.X₁ + D.classOf S.X₃ := by
  rw [classOf, classOf, classOf, K₀Ab.of_shortExact S hS, map_add]

/-- The numerical Chern character of a coherent sheaf is computed from its geometric Chern
classes. -/
theorem chernCharacter_classOf (D : NumericalData X n A N) (F : Coh X.toScheme) (i : ℕ) :
    D.toNumericalVariety.chComp (D.classOf F) i =
      ChernClassData.chernCharacterComponent (D.coherentChernClasses F) i := by
  rw [toNumericalVariety_chComp, D.coherentChernClasses_classOf]

/-- Numerical and geometric Euler characteristics agree on coherent sheaves. -/
theorem chi_classOf (D : NumericalData X n A N) (F : Coh X.toScheme) :
    D.toNumericalVariety.chi (D.classOf F) = D.coherentEulerCharacteristic F :=
  D.coherentEulerCharacteristic_classOf F

/-- Geometric Chern-character components are invariant under isomorphism of coherent sheaves. -/
theorem coherentChernCharacter_iso (D : NumericalData X n A N) {F G : Coh X.toScheme}
    (e : F ≅ G) (i : ℕ) :
    ChernClassData.chernCharacterComponent (D.coherentChernClasses F) i =
      ChernClassData.chernCharacterComponent (D.coherentChernClasses G) i := by
  rw [← D.coherentChernClasses_classOf, ← D.coherentChernClasses_classOf,
    D.classOfHom_of_iso e]

/-- Geometric Chern-character components are additive in short exact sequences. This is the
characteristic-class form of descent through the numerical Grothendieck group. -/
theorem coherentChernCharacter_shortExact (D : NumericalData X n A N)
    (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact) (i : ℕ) :
    ChernClassData.chernCharacterComponent (D.coherentChernClasses S.X₂) i =
      ChernClassData.chernCharacterComponent (D.coherentChernClasses S.X₁) i +
        ChernClassData.chernCharacterComponent (D.coherentChernClasses S.X₃) i := by
  rw [← D.coherentChernClasses_classOf, ← D.coherentChernClasses_classOf,
    ← D.coherentChernClasses_classOf, D.classOfHom_of_shortExact S hS, D.chernCharacter_add]

/-- Geometric Euler characteristic is invariant under isomorphism of coherent sheaves. -/
theorem coherentEulerCharacteristic_iso (D : NumericalData X n A N) {F G : Coh X.toScheme}
    (e : F ≅ G) : D.coherentEulerCharacteristic F = D.coherentEulerCharacteristic G := by
  exact D.finiteCohomology.eulerCharacteristic_iso e

/-- Geometric Euler characteristic is additive in short exact sequences. -/
theorem coherentEulerCharacteristic_shortExact (D : NumericalData X n A N)
    (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact) :
    D.coherentEulerCharacteristic S.X₂ =
      D.coherentEulerCharacteristic S.X₁ + D.coherentEulerCharacteristic S.X₃ := by
  change D.finiteCohomology.eulerCharacteristic S.X₂ =
    D.finiteCohomology.eulerCharacteristic S.X₁ +
      D.finiteCohomology.eulerCharacteristic S.X₃
  rw [← D.coherentEulerCharacteristic_classOf, ← D.coherentEulerCharacteristic_classOf,
    ← D.coherentEulerCharacteristic_classOf, D.classOfHom_of_shortExact S hS, map_add]

end NumericalData

end Variety

end AlgebraicGeometry
