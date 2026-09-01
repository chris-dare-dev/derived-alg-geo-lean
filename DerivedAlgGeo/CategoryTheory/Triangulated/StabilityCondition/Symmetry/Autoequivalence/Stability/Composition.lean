/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport

/-!
# Composing two transports

`actStabAut` transports a stability condition along one autoequivalence. This
file proves that doing it twice is the same as doing it once along the
composite — the associativity clause of a group action, without asserting that
there is a group.

Two halves, and only one of them has content:

* the **slicing** half is definitional. `Slicing.mapEquiv` reindexes by
  `Φ.inverse`, and `(Φ.trans Ψ).inverse` is `Ψ.inverse ⋙ Φ.inverse` on the
  nose, so `mapEquiv_trans` is `Slicing.ext` applied to `rfl`;
* the **charge** half is where the composite lattice map appears. If `Φ`
  carries `lam₁` and `Ψ` carries `lam₂`, then `Φ.trans Ψ` carries
  `lam₁.comp lam₂` — note the order: `hlam` is stated for the *quasi-inverse*,
  and inverses reverse, so `lam₁` is applied last.

## `Equivalence.trans` and instance search

`(Φ.trans Ψ).functor` is *reducibly* `Φ.functor ⋙ Ψ.functor`, but instance
search does not unfold `Equivalence.trans` to find it, so
`(Φ.trans Ψ).functor.Additive` fails to synthesize. The six `inferInstanceAs`
instances below supply what search cannot reach. They are stated once here and
are what let `mapEquiv (Φ.trans Ψ)` be written at all.

## What this file does not assert

* **No new group and no new `MulAction`.** This is one equation between two
  transports, stated for a bare `lam : Λ →+ Λ`. The bundled version already
  exists: `GroupAction.AutPairQuot v` (`Stability/ClassMap.lean`) is a group
  with a `MulAction` on `WithClassMap C v`, whose `act_mul` is this equation
  for pairs whose `lam` is invertible. This file is the strictly more general
  unbundled statement — a non-invertible `lam` still transports — and the
  kernel-tracking consumer (`KernelAutoequivalence.actStab_trans`) needs it in
  this form.
* Nothing about the *composite* of two stability conditions, which is not a
  thing; only about applying two transports in sequence.
* No claim that `lam₁.comp lam₂` is the unique lattice map compatible with
  `Φ.trans Ψ`; uniqueness would need `v` surjective.
-/

universe u u'

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

variable {C : Type u} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section TransInstances

variable (Φ Ψ : C ≌ C)
  [Φ.functor.Additive] [Φ.inverse.Additive]
  [Ψ.functor.Additive] [Ψ.inverse.Additive]
  [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Ψ.functor.CommShift ℤ] [Ψ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated]
  [Ψ.functor.IsTriangulated] [Ψ.inverse.IsTriangulated]

instance transFunctorAdditive : (Φ.trans Ψ).functor.Additive :=
  inferInstanceAs (Φ.functor ⋙ Ψ.functor).Additive

instance transInverseAdditive : (Φ.trans Ψ).inverse.Additive :=
  inferInstanceAs (Ψ.inverse ⋙ Φ.inverse).Additive

instance transFunctorCommShift : (Φ.trans Ψ).functor.CommShift ℤ :=
  inferInstanceAs ((Φ.functor ⋙ Ψ.functor).CommShift ℤ)

instance transInverseCommShift : (Φ.trans Ψ).inverse.CommShift ℤ :=
  inferInstanceAs ((Ψ.inverse ⋙ Φ.inverse).CommShift ℤ)

instance transFunctorIsTriangulated : (Φ.trans Ψ).functor.IsTriangulated :=
  inferInstanceAs (Φ.functor ⋙ Ψ.functor).IsTriangulated

instance transInverseIsTriangulated : (Φ.trans Ψ).inverse.IsTriangulated :=
  inferInstanceAs (Ψ.inverse ⋙ Φ.inverse).IsTriangulated

/-- **Reindexing twice is reindexing along the composite.**

Definitional: `mapEquiv` reindexes by `Φ.inverse`, and `(Φ.trans Ψ).inverse` is
`Ψ.inverse ⋙ Φ.inverse` on the nose. The bundled counterpart is
`TriEquiv.act_comp` (`Slicing/Quotient.lean`) — the same `Slicing.ext`-on-`rfl`
argument for a `TriEquiv` instead of a bare `Equivalence`.

Pin note: "on the nose" is Mathlib's literal `inverse := f.inverse ⋙ e.inverse`
in the definition of `Equivalence.trans`. If a Mathlib bump redefines
`Equivalence.trans`, this `rfl` — and `KernelAutoequivalence.actStab_trans`
behind it — is the first thing to break. Re-check here if the pin moves. -/
theorem Slicing.mapEquiv_trans (s : Slicing C) :
    (s.mapEquiv Φ).mapEquiv Ψ = s.mapEquiv (Φ.trans Ψ) := by
  ext φ X
  rfl

end TransInstances

section Charge

variable [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
variable (Φ Ψ : C ≌ C)
  [Φ.functor.Additive] [Φ.inverse.Additive]
  [Ψ.functor.Additive] [Ψ.inverse.Additive]
  [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Ψ.functor.CommShift ℤ] [Ψ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated]
  [Ψ.functor.IsTriangulated] [Ψ.inverse.IsTriangulated]

omit [IsTriangulated C] [Φ.functor.Additive] [Ψ.functor.Additive]
  [Φ.functor.CommShift ℤ] [Ψ.functor.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Ψ.functor.IsTriangulated] in
/-- The composite carries the composite lattice map.

The order is the one the quasi-inverse forces: `(Φ.trans Ψ).inverse` is
`Ψ.inverse ⋙ Φ.inverse`, so `lam₂` acts first and `lam₁` last. -/
theorem hlam_trans {lam₁ lam₂ : Λ →+ Λ}
    (h₁ : ∀ x : K₀ C, v (K₀.map Φ.inverse x) = lam₁ (v x))
    (h₂ : ∀ x : K₀ C, v (K₀.map Ψ.inverse x) = lam₂ (v x)) (x : K₀ C) :
    v (K₀.map (Φ.trans Ψ).inverse x) = (lam₁.comp lam₂) (v x) := by
  have hcomp : K₀.map (Φ.trans Ψ).inverse
      = (K₀.map Φ.inverse).comp (K₀.map Ψ.inverse) :=
    K₀.map_comp Ψ.inverse Φ.inverse
  rw [hcomp]
  simpa [h₂ x] using h₁ (K₀.map Ψ.inverse x)

/-- **Transporting twice is transporting once along the composite.**

The associativity clause of an action, stated as a single equation. The
lattice map of the composite is `lam₁.comp lam₂`, supplied by `hlam_trans`, so
no new hypothesis enters. -/
theorem actStabAut_trans {lam₁ lam₂ : Λ →+ Λ}
    (h₁ : ∀ x : K₀ C, v (K₀.map Φ.inverse x) = lam₁ (v x))
    (h₂ : ∀ x : K₀ C, v (K₀.map Ψ.inverse x) = lam₂ (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    actStabAut Ψ v lam₂ h₂ (actStabAut Φ v lam₁ h₁ σ)
      = actStabAut (Φ.trans Ψ) v (lam₁.comp lam₂) (hlam_trans v Φ Ψ h₁ h₂) σ := by
  refine StabilityCondition.WithClassMap.ext ?_ rfl
  exact Slicing.mapEquiv_trans Φ Ψ σ.slicing

end Charge

end

end CategoryTheory.Triangulated
