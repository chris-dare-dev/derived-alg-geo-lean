/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Coefficients

/-!
# Hilbert purity of a coherent sheaf

A coherent sheaf is *pure* for a polarization when every nonzero subsheaf has positive Hilbert
multiplicity. The condition mentions the multiplicity and nothing else: no order on Hilbert
polynomials, no slope, and no semistability notion.

## Why it has its own file

Purity has two consumers that do not depend on one another, which is what earns it an owner
rather than a block inside either. `Gieseker/Basic.lean` carries it as a conjunct of Gieseker
semistability — without it the reduced Hilbert function's junk value at multiplicity zero would
satisfy the Gieseker order vacuously. `Slope/HarderNarasimhan/` needs it for a different reason
and never mentions the Gieseker order: purity is exactly the condition under which the maximal
destabilizing subobject has finite slope rather than `⊤`, which is what makes the
Harder–Narasimhan recursion descend on multiplicity.

Before MO1.08 (#1319) it was declared in `Gieseker/Basic.lean`, so the μ-slope theory reached it
only by importing the Gieseker order it does not use. That import was the whole of the μ-lane's
dependence on Gieseker stability, and removing it is what makes `Slope/` a sibling of `Gieseker/`
rather than a child.

## What is not claimed

The geometric characterisation of purity — no associated point of support dimension below
`P.dim` — is **not** proved here and is not equivalent to this definition at this pin, because no
dimension-of-support theory exists. This is purity in the Hilbert-multiplicity sense, and
`Gieseker/Basic.lean`'s docstring says the same about the classical definition it is a conjunct
of.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable (P : PolarizedVarietyData k X)

/-- **Hilbert purity.** Every nonzero subsheaf has positive multiplicity, that is, full
`P.dim`-dimensional support in the Hilbert sense.

This is a definition, not a supplied `…Data` field. The geometric characterisation — no subsheaf
whose support has dimension below `P.dim` — is not proved here, because no dimension-of-support
theory exists at this pin. -/
def IsPure (F : Coh X) : Prop :=
  ¬IsZero F ∧ ∀ (G : Coh X) (i : G ⟶ F), Mono i → ¬IsZero G → 0 < P.multiplicity G

variable {P}

/-- A pure sheaf has positive multiplicity, by testing purity against its own identity. -/
theorem IsPure.multiplicity_pos {F : Coh X} (h : P.IsPure F) : 0 < P.multiplicity F :=
  h.2 F (𝟙 F) inferInstance h.1

theorem IsPure.not_isZero {F : Coh X} (h : P.IsPure F) : ¬IsZero F := h.1

/-- Purity is invariant under isomorphism. -/
theorem IsPure.of_iso {F G : Coh X} (h : P.IsPure F) (e : F ≅ G) : P.IsPure G := by
  refine ⟨fun hG ↦ h.1 (hG.of_iso e), fun H i hi hH ↦ ?_⟩
  haveI := hi
  exact h.2 H (i ≫ e.inv) (mono_comp i e.inv) hH

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
