/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Realization
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# Transferring Euler-form preservation across a realization

`Realization.PreservesEuler` is the hypothesis that a map of numerical
Grothendieck groups preserves `χ`.  This file reduces it to two inputs on the
categorical side, so that it stops being an opaque assumption about `N`.

## Why it does not follow from adjunction

The classical argument preserves `χ` from **full faithfulness**, not
adjunction: `χ(E,F) = Σᵢ (-1)ⁱ dim Hom(E, F[i])`, and a fully faithful functor
commuting with the shift matches the summands one by one.  Adjunction alone
gives `Hom(ΦE, ΦF) ≅ Hom(E, ΦᴿΦF)`, which is `Hom(E,F)` only once `ΦᴿΦ ≅ 𝟭` —
that is, only once `Φ` is fully faithful.  Serre duality is *not* needed for
this step; once full faithfulness is known the summands already match.

Full faithfulness alone is also not quite enough, and the missing word is
`k`-linear.  The summands are equal as `k`-dimensions, so the functor must
induce `k`-linear isomorphisms on `Hom`; an additive fully faithful functor
need not.  The hypothesis the construction below would discharge is therefore
a fully faithful `k`-linear shift-compatible functor, together with the
Hom-finiteness and boundedness that make the sum finite.

Neither hypothesis reaches `chi₂` on its own, and the reason is structural.
`NumericalVarietyData.chi₂` is `∫ ch(E)ᵛ · ch(F) · td(X)`: a formula in Chern
characters, with no `Hom` anywhere in it.  `EulerPairing`'s own docstring is
explicit that `chi₂ E F = Σᵢ (-1)ⁱ dim Extⁱ(E,F)` is **the bilinear
Hirzebruch--Riemann--Roch**, that there is no `Ext` at this layer to state it
against, and that discharging it is Layer B's job.  So a categorical
hypothesis can only reach `chi₂` through an HRR comparison, and that
comparison has to be supplied.

This file supplies it as `IsRiemannRoch` and does the bookkeeping.

## The reduction

`preservesEuler_of_descends` takes

* `hΦ : E.Preserves E' Φ` — what full faithfulness gives for the generic
  categorical Euler forms;
* `hRR`, `hRR'` — bilinear HRR for the two realizations;
* `hsurj` — surjectivity of the source realization, which is what lets a
  statement about classes of complexes become a statement about all of `N`;
* `hd` — the descent square from the generic `K₀.Realization` root;

and concludes `PreservesEuler φ`, hence (via
`pairing_mukaiVector_eq_on_realized`) that a kernel functor leaves the Mukai
pairing unchanged on realized classes.  Against `IntegralMukaiData` that is an
equality of pairings and not an isometry of lattices; against
`AdditiveMukaiData` the same conclusion is an isometry of the Mukai forms on
`N` and `N'` (`Realization.isometryOfPreservesEuler`), and still not a map of
Mukai extensions.  See `Realization`'s docstring for why the distinctions
matter here.

## What this file does not assert

* **A `K₀.EulerForm` can be constructed** — `ofLinear`, from
  `Triangulated/GrothendieckGroup/EulerForm.lean`'s `chiK₀`. What that costs is
  `HomFiniteBounded`: finite-dimensionality of every `Hom(X, Y⟦i⟧)` and finite
  support in `i`.  So the obligation is *moved*, from "produce a biadditive
  pairing" to "produce Hom-finiteness", not eliminated.  A caller with an
  abstract `𝒯` and no `k` still supplies the additive form directly.
* **`K₀.EulerForm.Preserves` is proved** for a fully faithful `k`-linear
  shift-compatible functor between Hom-finite categories, against forms built by
  `ofLinear` (`K₀.EulerForm.ofLinear_preserves`). It stays a hypothesis for
  *supplied* forms, where there is no `Hom` for the argument to run on.
* `IsRiemannRoch` is bilinear HRR, assumed.  No variety is shown to satisfy
  it, and `NumericalVarietyData.hirzebruch_riemannRoch` — the one-variable
  statement — is itself an axiom of the Layer A interface.
-/

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃ x₁ x₂ y₁ y₂

namespace AlgebraicGeometry.Numerical

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open NumericalRingData NumericalRingDualData NumericalVarietyData

section Transfer

variable {n : ℕ} {𝒳 : Type u₁} {𝒴 : Type u₂}
  {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ m : ℤ, (shiftFunctor 𝒳 m).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ m : ℤ, (shiftFunctor 𝒴 m).Additive] [Pretriangulated 𝒴]
  [CommRing A] [Algebra ℚ A] [AddCommGroup N]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N']
  {V : NumericalVarietyData n A N} {V' : NumericalVarietyData n A' N'}

/-- **Bilinear Hirzebruch--Riemann--Roch for a realization**: the categorical
Euler form computes the numerical one on realized classes.

This is the comparison the whole reduction turns on, and it is assumed.  The
one-variable statement `NumericalVarietyData.hirzebruch_riemannRoch` is already an
axiom of the Layer A interface; this is its bilinear companion. -/
def IsRiemannRoch (V : NumericalVarietyData n A N) (R : K₀.Realization 𝒳 N)
    (E : K₀.EulerForm 𝒳) : Prop :=
  ∀ x y : K₀ 𝒳, ((E x y : ℤ) : ℚ) = V.chi₂ (R x) (R y)

/-- **Euler preservation transfers across a realization.**

Given bilinear HRR on both sides, a functor preserving the categorical Euler
form, and a descent, the descended map preserves the numerical Euler form.
Surjectivity of the source realization is what turns a statement about classes
of complexes into one about all of `N`. -/
theorem preservesEuler_of_descends {Φ : 𝒳 ⥤ 𝒴} [Φ.CommShift ℤ]
    [Φ.IsTriangulated] {R : K₀.Realization 𝒳 N}
    {R' : K₀.Realization 𝒴 N'} {E : K₀.EulerForm 𝒳}
    {E' : K₀.EulerForm 𝒴} {φ : N →+ N'}
    (hsurj : Function.Surjective R)
    (hRR : IsRiemannRoch V R E) (hRR' : IsRiemannRoch V' R' E')
    (hΦ : E.Preserves E' Φ) (hd : R.Descends R' Φ φ) :
    PreservesEuler V V' φ := by
  intro F G
  obtain ⟨x, rfl⟩ := hsurj F
  obtain ⟨y, rfl⟩ := hsurj G
  rw [← hd x, ← hd y, ← hRR', hΦ, hRR]

end Transfer

section KernelFunctor

open K3 CategoryTheory.Triangulated.FourierMukai

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒲 : Type u₃}
  {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  {Λ : Type w₁} {Λ' : Type w₂}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒲]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ m : ℤ, (shiftFunctor 𝒳 m).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ m : ℤ, (shiftFunctor 𝒴 m).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ m : ℤ, (shiftFunctor 𝒲 m).Additive] [Pretriangulated 𝒲]
  [CommRing A] [Algebra ℚ A] [AddCommGroup N]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N']
  [AddCommGroup Λ] [AddCommGroup Λ']
  {V : NumericalVarietyData 2 A N} {V' : NumericalVarietyData 2 A' N'}

/-- **A kernel functor preserving the categorical Euler form leaves the Mukai
pairing unchanged on realized classes.**

An equality of pairings, stated against `IntegralMukaiData`, where there is no
bilinear form for it to be an isometry of. This is
`pairing_mukaiVector_eq_on_realized` with its `PreservesEuler` hypothesis
discharged from categorical input; with `AdditiveMukaiData` the same
`PreservesEuler` output feeds `isometryOfPreservesEuler`, and no map of Mukai
*extensions* is built there either.

Three obligations remain, and all three are named rather than hidden:
constructing the categorical Euler form from `Hom`, proving a fully faithful
`k`-linear functor preserves it, and bilinear HRR. -/
theorem pairing_mukaiVector_eq_on_realized_of_categorical
    (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated]
    (R : K₀.Realization 𝒳 N) (R' : K₀.Realization 𝒴 N')
    (E : K₀.EulerForm 𝒳) (E' : K₀.EulerForm 𝒴)
    (φ : N →+ N') (hsurj : Function.Surjective R)
    (hRR : IsRiemannRoch V R E) (hRR' : IsRiemannRoch V' R' E')
    (hΦ : E.Preserves E' (C.transform K))
    (hd : R.Descends R' (C.transform K) φ)
    (D : IntegralMukaiData V Λ) (D' : IntegralMukaiData V' Λ')
    (hHRR : V.SatisfiesHRR) (hHRR' : V'.SatisfiesHRR)
    (hK3 : IsK3 V) (hK3' : IsK3 V')
    (x y : K₀ 𝒳) :
    Mukai.pairing D'.b (D'.mukaiVector (R' (C.transformK₀ K x)))
        (D'.mukaiVector (R' (C.transformK₀ K y)))
      = Mukai.pairing D.b (D.mukaiVector (R x))
        (D.mukaiVector (R y)) :=
  pairing_mukaiVector_eq_on_realized C K R R' φ hd D D' hHRR hHRR' hK3 hK3'
    (preservesEuler_of_descends hsurj hRR hRR' hΦ hd) x y

end KernelFunctor

end AlgebraicGeometry.Numerical
