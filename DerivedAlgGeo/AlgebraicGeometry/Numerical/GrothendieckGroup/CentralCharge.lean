/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.CentralCharge
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.IntegralBridge

/-!
# `Z(β,ω)` as a function of a numerical class

Route (A) states the central charge on a lattice vector. This file composes it
with the Mukai vector, so it becomes a function of a **numerical class**:

```
N --mukaiVectorHom--> MukaiLattice Λ --extendMap--> ℝ × W × ℝ --expCharge--> ℂ
```

Every link exists already: `mukaiVectorHom` is the additive Mukai vector,
`extendMap` places the integral lattice in the real extension, and `expCharge`
is `Z(β,ω)`. What the composition buys is that route (A)'s conclusions become
statements about classes rather than about a quadratic space:

* `numericalCharge_add` — the charge is additive in the class, by composition.
* `mukaiForm_neg_of_numericalCharge_eq_zero` — **the support property in
  numerical terms**: a class killed by the charge has negative Mukai square.
* `numericalCharge_ne_zero_of_nonneg` — a class of nonnegative Mukai square is
  never killed.
* `mem_wall_iff_numericalCharge_eq_zero` — a wall is a vanishing charge, for the
  class of an object rather than for a raw lattice vector.

## What is still not here

The Mukai vector of an **object** of `Dᵇ(Coh X)`, and any stability condition.
`N` is the numerical Grothendieck group and the class map into it is geometry
that lives elsewhere; nothing below constructs a slicing, a heart, or a
Harder–Narasimhan filtration.

The compatibility `hf` — that the embedding of `Λ` in its real span carries the
integral form to the real one — is a hypothesis, as it is throughout the lane;
for `Λ = NS(X)` it says the intersection form is the restriction of its own real
extension.
-/

open QuadraticMap

namespace AlgebraicGeometry.Numerical

namespace K3

universe u v w w'

variable {A : Type u} {N : Type v} {Λ : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [AddCommGroup Λ]
variable {V : NumericalVarietyData 2 A N}

namespace AdditiveMukaiData

variable {W : Type w'} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable (D : AdditiveMukaiData V Λ) (bR : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : Λ →ₗ[ℤ] W) (β ω : W)

/-- **`Z(β,ω)` on a numerical class**: the charge of the real Mukai vector. -/
noncomputable def numericalCharge (E : N) : ℂ :=
  Mukai.expCharge bR β ω (Mukai.extendMap f (D.mukaiVectorHom E))

variable {D bR f β ω}

theorem numericalCharge_apply (E : N) :
    D.numericalCharge bR f β ω E
      = Mukai.expCharge bR β ω (Mukai.extendMap f (D.mukaiVectorHom E)) := rfl

/-- The charge is **additive in the class** — every link of the composition is. -/
theorem numericalCharge_add (E F : N) :
    D.numericalCharge bR f β ω (E + F)
      = D.numericalCharge bR f β ω E + D.numericalCharge bR f β ω F := by
  simp only [numericalCharge, Mukai.expCharge, map_add, Mukai.extendMap_add]
  exact PeriodDomain.centralCharge_add _ _ _ _

variable (D bR f β ω)

/-- **The charge as a bundled hom**, `N →+ ℂ`.

`numericalCharge` was proved additive and then left unbundled, which is what kept
the numerical lane from ever meeting the stability-function side: every charge
there is an `AddMonoidHom`, and an equation is not one.  With this the chain from
a numerical class to `ℂ` is a composition of homs and nothing along it re-proves
additivity. -/
noncomputable def numericalChargeHom : N →+ ℂ :=
  AddMonoidHom.mk' (D.numericalCharge bR f β ω) (fun E F ↦ numericalCharge_add E F)

@[simp]
theorem numericalChargeHom_apply (E : N) :
    D.numericalChargeHom bR f β ω E = D.numericalCharge bR f β ω E := rfl

/-- The charge **kills the zero class** — free once it is a hom, and absent
before. -/
@[simp]
theorem numericalCharge_zero : D.numericalCharge bR f β ω 0 = 0 :=
  (D.numericalChargeHom bR f β ω).map_zero

variable {D bR f β ω}

/-- The real square of a class is half its Mukai square. -/
theorem realForm_extendMap_mukaiVector
    (hf : ∀ x y : Λ, bR (f x) (f y) = ((D.b x) y : ℝ)) (E : N) :
    Mukai.realForm bR (Mukai.extendMap f (D.mukaiVectorHom E)) = (D.mukaiForm E E : ℝ) / 2 := by
  rw [Mukai.realForm_apply, Mukai.realPairing_extendMap D.b bR f hf, D.mukaiForm_apply]
  rfl

/-- **The support property, in numerical terms.** A class killed by the charge
has negative Mukai square — the statement `neg_of_mem_orthogonal` becomes once it
is read through the Mukai vector. -/
theorem mukaiForm_neg_of_numericalCharge_eq_zero [FiniteDimensional ℝ W]
    (hsig : PeriodDomain.HasSignatureTwo (Mukai.realForm bR))
    (hb : ∀ x y : W, bR x y = bR y x) (hω : 0 < bR ω ω)
    (hf : ∀ x y : Λ, bR (f x) (f y) = ((D.b x) y : ℝ)) {E : N}
    (hE : D.numericalCharge bR f β ω E = 0)
    (hne : Mukai.extendMap f (D.mukaiVectorHom E) ≠ 0) :
    D.mukaiForm E E < 0 := by
  have h := Mukai.neg_of_expCharge_eq_zero bR β ω hsig hb hω hE hne
  rw [realForm_extendMap_mukaiVector hf E] at h
  have : ((D.mukaiForm E E : ℤ) : ℝ) < 0 := by linarith
  exact_mod_cast this

/-- **A class of nonnegative Mukai square is never killed** — there are no walls
in the positive cone, said of classes. -/
theorem numericalCharge_ne_zero_of_nonneg [FiniteDimensional ℝ W]
    (hsig : PeriodDomain.HasSignatureTwo (Mukai.realForm bR))
    (hb : ∀ x y : W, bR x y = bR y x) (hω : 0 < bR ω ω)
    (hf : ∀ x y : Λ, bR (f x) (f y) = ((D.b x) y : ℝ)) {E : N}
    (hsq : 0 ≤ D.mukaiForm E E)
    (hne : Mukai.extendMap f (D.mukaiVectorHom E) ≠ 0) :
    D.numericalCharge bR f β ω E ≠ 0 := by
  refine Mukai.expCharge_ne_zero_of_nonneg bR β ω hsig hb hω ?_ hne
  rw [realForm_extendMap_mukaiVector hf E]
  have : (0 : ℝ) ≤ ((D.mukaiForm E E : ℤ) : ℝ) := by exact_mod_cast hsq
  linarith

/-- **A wall is a vanishing charge**, for the class of an object. -/
theorem mem_wall_iff_numericalCharge_eq_zero (hb : ∀ x y : W, bR x y = bR y x)
    (hω : 0 < bR ω ω) (E : N) :
    PeriodDomain.pairSpan (Mukai.expRe bR β ω) (Mukai.expIm bR β ω) ∈
        PeriodDomain.wall (Mukai.realForm bR) (Mukai.extendMap f (D.mukaiVectorHom E)) ↔
      D.numericalCharge bR f β ω E = 0 :=
  Mukai.mem_wall_iff_expCharge_eq_zero bR β ω hb hω

end AdditiveMukaiData

end K3

end AlgebraicGeometry.Numerical
