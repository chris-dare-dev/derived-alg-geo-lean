/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Duality.Serre.Cohomology

/-!
# Serre duality in its bilinear form

`Serre/Cohomology.lean` supplies duality **into the dualizing object**:
`H^i(X,F)ᵛ ≃ Ext^(n-i)(F, ω_X)`.  That is the form its consumers need, and it is the form
`Data.duality` states.

Several statements want the **bilinear** form instead,

`Ext^i(E,F)ᵛ ≃ Ext^(n-i)(F, E ⊗ ω_X)`,

which specialises at `E = 𝒪` to the above and at `E = F` on a surface with trivial canonical
bundle to `Ext²(E,E) ≃ Hom(E,E)ᵛ`.  That last is what Bridgeland's Lemma 5.1 runs on.  This file
supplies it, in the same idiom, and proves the consequences.

## Supplied, and why

`BilinearData` is **data, not a theorem**, exactly as `DerivedStatement` and `Data` are, and for
the same upstream reason recorded there: the pinned Mathlib has derived categories and `Ext` but
no derived global-sections functor into `D(k)`, no coherent `RHom`, and no Grothendieck-duality
theorem.  `Duality.Serre.DerivedStatement` is this repository's idiom for "supplied, not proved"
— `Surface/K3.lean` and `Surface/Spherical.lean` both name it that way — and this structure joins
it rather than pretending to more.

**It is not an inhabitant of anything and does not claim to be.**  What it buys is that the
bilinear form is stated once, in one place, with its consequences proved from it, instead of being
re-supplied ad hoc by each consumer that needs `Ext²(E,E) ≃ Hom(E,E)ᵛ`.

## What the consequences sharpen

`surface_selfEuler_eq` computes, on a surface with trivial canonical bundle,

```
χ(E,E) = 2·hom(E,E) − ext¹(E,E)
```

and `surface_selfEuler_le` drops the middle term to give `χ(E,E) ≤ 2·hom(E,E)`.

That isolates the remaining input for Lemma 5.1 (`χ(E,E) ≤ 2`, hence `v(E)² ≥ −2`) to a single
fact: **`hom(E,E) = 1` for a stable sheaf.**  Simplicity is still not in this repository, and
neither is the bilinear Riemann–Roch that would connect this categorical Euler characteristic to
`NumericalVarietyData.chi₂`.  Both gaps are real and neither is closed here; see
`ag-lean-handoff/lemma-5-1/SCOPE.md`.
-/

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.Duality.Serre

open AlgebraicGeometry

variable {k : Type u} [Field k]
variable {X : SmoothProperVariety k} {n : ℕ}

noncomputable section

/-- The `Ext` groups below are Mathlib's `Abelian.Ext`, which needs `HasExt`.

`Serre/Cohomology.lean` declares the same instance, but as a `local instance`, so it does not
cross the import boundary into this file. Without it the elaborator does not report a missing
instance: it tries to synthesize `HasSmallLocalizedHom` for the quasi-isomorphism localization
from scratch and exhausts the `synthInstance` budget, and the timeout surfaces as an ordinary
"failed to synthesize" on `extComparison`. `references/instance-transparency.md` names that
failure mode; raising `synthInstance.maxHeartbeats` treats the symptom.

`HasExt.standard` is the sanctioned route, and it is the one the sibling file takes. -/
local instance : HasExt.{u + 1} (Coh X.toVariety.toScheme) :=
  HasExt.standard _

/-- **Bilinear coherent Serre duality**, as supplied realization data.

The fields mirror `Serre.Data`: a base-field-linear realization of the `Ext` groups, its
comparison with Mathlib's actual `Abelian.Ext`, finiteness, the canonical twist `E ⊗ ω_X`, and
the duality isomorphism itself. -/
structure BilinearData (K : X.CanonicalSheafData n) where
  /-- A base-field-linear realization of `Ext^j(E,F)`. -/
  extSpace : Coh X.toVariety.toScheme → Coh X.toVariety.toScheme → ℕ → ModuleCat.{u + 1} k
  /-- Forgetting scalars recovers Mathlib's actual Ext group. -/
  extComparison : ∀ (E F : Coh X.toVariety.toScheme) (j : ℕ),
    (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).obj (extSpace E F j) ≅
      AddCommGrpCat.of (Abelian.Ext.{u + 1} E F j)
  /-- The Ext spaces are finite-dimensional. -/
  extFinite : ∀ (E F : Coh X.toVariety.toScheme) (j : ℕ),
    Module.Finite k (extSpace E F j)
  /-- The canonical twist `E ⊗ ω_X`, carried explicitly because the present sheaf API does not
  construct internal tensor with the dualizing sheaf. -/
  canonicalTwist : Coh X.toVariety.toScheme → Coh X.toVariety.toScheme
  /-- **Perfect bilinear Serre duality** in every degree in the geometric range. -/
  duality : ∀ (E F : Coh X.toVariety.toScheme) (i : ℕ), i ≤ n →
    Module.Dual k (extSpace E F i) ≃ₗ[k] extSpace F (canonicalTwist E) (n - i)

namespace BilinearData

variable {K : X.CanonicalSheafData n} (S : BilinearData K)

/-- Perfection gives equality of complementary Ext dimensions. -/
theorem finrank_eq (E F : Coh X.toVariety.toScheme) (i : ℕ) (hi : i ≤ n) :
    Module.finrank k (S.extSpace E F i) =
      Module.finrank k (S.extSpace F (S.canonicalTwist E) (n - i)) := by
  letI := S.extFinite E F i
  letI := S.extFinite F (S.canonicalTwist E) (n - i)
  rw [← (S.duality E F i hi).finrank_eq, Subspace.dual_finrank_eq]

/-- **A trivial canonical bundle**, recorded as the twist acting trivially on the realized `Ext`
spaces.  On a K3 the canonical bundle is `𝒪_X`, so this is the case the surface results below are
about.  It is stated on the realization rather than on the sheaf because the twist itself is
carried as a function, not constructed. -/
structure TrivialCanonical where
  /-- Twisting by the canonical bundle does not change the realized `Ext` spaces. -/
  twistIso : ∀ (E F : Coh X.toVariety.toScheme) (j : ℕ),
    S.extSpace F (S.canonicalTwist E) j ≃ₗ[k] S.extSpace F E j

variable {S}

/-- With trivial canonical bundle, duality is symmetric in the two arguments. -/
theorem finrank_eq_of_trivialCanonical (T : S.TrivialCanonical)
    (E F : Coh X.toVariety.toScheme) (i : ℕ) (hi : i ≤ n) :
    Module.finrank k (S.extSpace E F i) =
      Module.finrank k (S.extSpace F E (n - i)) := by
  letI := S.extFinite F (S.canonicalTwist E) (n - i)
  letI := S.extFinite F E (n - i)
  rw [S.finrank_eq E F i hi, (T.twistIso E F (n - i)).finrank_eq]

/-- **`Ext^n(E,E)` and `Hom(E,E)` have the same dimension** when the canonical bundle is trivial.
This is the case Bridgeland's Lemma 5.1 uses, at `n = 2`. -/
theorem finrank_top_eq_finrank_hom (T : S.TrivialCanonical)
    (E : Coh X.toVariety.toScheme) :
    Module.finrank k (S.extSpace E E n) = Module.finrank k (S.extSpace E E 0) := by
  have h := finrank_eq_of_trivialCanonical T E E 0 (Nat.zero_le n)
  simpa using h.symm

variable (S)

/-- The categorical Euler characteristic of a pair, from the realized `Ext` dimensions. -/
def eulerChar (E F : Coh X.toVariety.toScheme) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1) ^ i * (Module.finrank k (S.extSpace E F i) : ℤ)

variable {S}

/-- **On a surface with trivial canonical bundle, `χ(E,E) = 2·hom(E,E) − ext¹(E,E)`.**

The two ends of the sum are equal by `finrank_top_eq_finrank_hom`, which is where duality
enters. -/
theorem surface_selfEuler_eq (hn : n = 2) (T : S.TrivialCanonical)
    (E : Coh X.toVariety.toScheme) :
    S.eulerChar E E =
      2 * (Module.finrank k (S.extSpace E E 0) : ℤ) -
        (Module.finrank k (S.extSpace E E 1) : ℤ) := by
  have htop := finrank_top_eq_finrank_hom T E
  subst hn
  simp only [eulerChar, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [htop]
  ring

/-- **`χ(E,E) ≤ 2·hom(E,E)`** on such a surface, by dropping `ext¹ ≥ 0`.

This is the shape Bridgeland's Lemma 5.1 needs.  What remains is `hom(E,E) = 1` for a stable
sheaf — simplicity — which is not in this repository, and the bilinear Riemann–Roch that would
identify this `eulerChar` with `NumericalVarietyData.chi₂`, which is supplied rather than proved
in `EulerTransfer.lean`. -/
theorem surface_selfEuler_le (hn : n = 2) (T : S.TrivialCanonical)
    (E : Coh X.toVariety.toScheme) :
    S.eulerChar E E ≤ 2 * (Module.finrank k (S.extSpace E E 0) : ℤ) := by
  rw [surface_selfEuler_eq hn T E]
  have : (0 : ℤ) ≤ (Module.finrank k (S.extSpace E E 1) : ℤ) := Int.natCast_nonneg _
  linarith

end BilinearData

end

end AlgebraicGeometry.Duality.Serre
