/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Order.Bayer

/-!
# The abstract cofiltration property

Definition 3.22 of arXiv:2607.28411v1 is geometric only in the names of its
objects.  Its categorical content is a chosen object `G₀`, a finite sequence
of morphisms ending at zero, prescribed shifted finite sums as the first cone
fibres, and a final cone fibre lying below a chosen t-structure bound.

`CofiltrationProperty` records exactly that content over an arbitrary
pretriangulated category.  The inputs are deliberately ordered as in the
paper: the initial object, then the family of model objects, their shifts, and
finally the integer bound.  The multiplicities and the cofiltration itself
remain existential.  In a geometric instantiation these become

* `G₀ = f_* O_X`,
* `L i` the invertible sheaves `Lᵢ`, and
* `t` the standard t-structure on `Dᵇ(Y)`.

This module does not construct any of those geometric data and makes no claim
about Propositions 3.24, 3.26, or 3.27, whose pullback, tensor-product, scheme,
and moduli hypotheses lie outside this abstract categorical API.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The finite cone-by-cone data underlying the cofiltration property.

`G 0` is the initial object.  Each `s i : G i ⟶ G (i+1)` has prescribed
shifted finite-biproduct fibre, and the final map lands in a zero object. -/
structure CofiltrationData (G₀ : C) {m : ℕ} (L : Fin m → C)
    (l : Fin m → ℤ) where
  /-- The successive objects, including the terminal zero object. -/
  G : Fin (m + 2) → C
  /-- Identification of the first object with the object being cofiltered. -/
  initialIso : G 0 ≅ G₀
  /-- A triangle presenting each cofiltration arrow and its cone. -/
  triangle : Fin (m + 1) → Triangle C
  /-- Each presenting triangle is distinguished. -/
  triangle_distinguished : ∀ i, triangle i ∈ distTriang C
  /-- The first vertex of each triangle is the corresponding cofiltration
  object. -/
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ G i.castSucc)
  /-- The second vertex is the following cofiltration object. -/
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ G i.succ)
  /-- Positive multiplicity of each prescribed fibre. -/
  multiplicity : Fin m → ℕ
  /-- The source definition requires every multiplicity to be positive. -/
  multiplicity_pos : ∀ i, 0 < multiplicity i
  /-- The first `m` shifted cone fibres have the prescribed finite-biproduct
  form `Lᵢ^{⊕aᵢ}[lᵢ]`. -/
  fibreIso : ∀ i : Fin m,
    (triangle i.castSucc).obj₃⟦(-1 : ℤ)⟧ ≅
      (⨁ fun _ : Fin (multiplicity i) ↦ L i)⟦l i⟧
  /-- The last object is zero. -/
  terminalIsZero : IsZero (G ⟨m + 1, by lia⟩)

/-- The final shifted cone fibre of a cofiltration. -/
abbrev CofiltrationData.remainder {G₀ : C} {m : ℕ} {L : Fin m → C}
    {l : Fin m → ℤ} (F : CofiltrationData G₀ L l) : C :=
  (F.triangle (Fin.last m)).obj₃⟦(-1 : ℤ)⟧

/-- Abstract cofiltration property with the source paper's quantifier order:
for fixed `G₀`, model objects `L`, shifts `l`, and bound `N`, there exists a
finite cofiltration with positive multiplicities whose final shifted cone
fibre lies in `t.le (-N)`. -/
def CofiltrationProperty (t : TStructure C) (G₀ : C) {m : ℕ}
    (L : Fin m → C) (l : Fin m → ℤ) (N : ℤ) : Prop :=
  ∃ F : CofiltrationData G₀ L l, t.le (-N) F.remainder

/-- The `N = infinity` clause of Definition 3.22: the last cone itself is
zero.  This is kept separate from the integer-bounded property because the
source treats infinity as an additional case, not as an integer. -/
def CofiltrationPropertyInfinity (G₀ : C) {m : ℕ}
    (L : Fin m → C) (l : Fin m → ℤ) : Prop :=
  ∃ F : CofiltrationData G₀ L l, IsZero (F.triangle (Fin.last m)).obj₃

/-- An infinite-bound cofiltration yields the integer-bounded property for
every t-structure and every bound. -/
theorem CofiltrationPropertyInfinity.toCofiltrationProperty
    {G₀ : C} {m : ℕ} {L : Fin m → C} {l : Fin m → ℤ}
    (h : CofiltrationPropertyInfinity G₀ L l) (t : TStructure C) (N : ℤ) :
    CofiltrationProperty t G₀ L l N := by
  obtain ⟨F, hF⟩ := h
  have hRemainder : IsZero F.remainder := (shiftFunctor C (-1 : ℤ)).map_isZero hF
  letI : t.IsLE F.remainder (-N) := t.isLE_of_isZero hRemainder (-N)
  exact ⟨F, t.le_of_isLE F.remainder (-N)⟩

end CategoryTheory.Triangulated
