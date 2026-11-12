/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.FiberwiseSupport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.Ordinary
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.FieldExtension

/-!
# Stability over a field and the good-moduli input chain

Definition 8.17 of arXiv:2607.28411v1 and the implication chain of its Theorem
8.23. `StabilityOverFieldConditions` specializes the canonical
`OrdinaryDeformationInputConditions` root to the actual semistable classes of
the fiber slicings. Its four conditions are uniform quotient support,
openness, relative HN structures after the specified Dedekind base changes,
and boundedness.

## Main definitions

* `StabilityOverFieldConditions` — Definition 8.17, as a specialization of the
  canonical deformation-input root.
* `SemistableOverFieldConditions` — the same root with semistable openness and
  boundedness probes, as in Lemma 8.22.
* `BoundedMassPhaseOfMassHomBound`, `OpennessOfBoundedMassPhase`,
  `DedekindHNOfBoundedMassPhase`, `BoundednessOfBoundedMassPhase` — the
  external implications the paper takes from HLR and BLMNPS, as propositions.
* `StableOfSemistableOverField` — Lemma 8.22 as an implication.
* `ProperGoodModuliOfOverField` — BLMNPS Theorem 21.24 in characteristic zero,
  as an implication to a caller-supplied good-moduli proposition.

## Main results

* `semistableOverFieldConditions_of_massHom` — the mass--Hom estimate and the
  external implications give the semistable conditions.
* `stabilityOverFieldConditions_of_massHom` — Theorem 8.23 up to
  Definition 8.17.
* `properGoodModuli_of_massHom` — the characteristic-zero good-moduli
  conclusion of Theorem 8.23.

## Implementation notes

The external results are named proposition types. The assembly theorems
consume them as hypotheses; no structure carries a good-moduli conclusion, and
this file does not construct a moduli space.

## References

* arXiv:2607.28411v1, Definition 8.17, Lemma 8.22 and Theorem 8.23.
* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in
  families*, arXiv:1902.08184, Theorems 5.7, 18.7 and 21.24.

## Tags

stability condition, family, good moduli space, mass--Hom bound
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Moduli
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.StabilityCondition.WithClassMap
open CategoryTheory.Triangulated.WeakStabilityCondition.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

noncomputable section

universe u

variable {I JOpen D M V : Type*} {C : I → Type u}
  [∀ i : I, Category (C i)] [∀ i : I, Preadditive (C i)]
  [∀ i : I, HasZeroObject (C i)] [∀ i : I, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i : I, Pretriangulated (C i)]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {v : ∀ i, K₀ (C i) →+ V}

/-- The four clauses of Definition 8.17 as a specialization of the
canonical deformation-input root.  The support locus is definitionally the
set of classes of actual nonzero semistable objects in each fiber.  The
zero-charge subspace and its containment proof stay explicit, as required by
the repository's quotient-support interface. -/
abbrev StabilityOverFieldConditions
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (V₀ : Submodule ℝ V)
    (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (openLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (boundedness : BoundednessProblem M) : Prop :=
  OrdinaryDeformationInputConditions openLoci dedekind V₀ Zlin hV₀
    (ordinaryFiberSemistableClasses σ) boundedness

/-- The `(ii')`/`(iv')` semistable variant used in Lemma 8.22.  It is the
same canonical four-condition interface; only the caller's openness and
boundedness probes now describe semistable objects. -/
abbrev SemistableOverFieldConditions
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (V₀ : Submodule ℝ V)
    (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (semistableLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (semistableBoundedness : BoundednessProblem M) : Prop :=
  StabilityOverFieldConditions σ V₀ Zlin hV₀ semistableLoci dedekind
    semistableBoundedness

/-- HLR Theorem 2.35, implication `(1) → (2)`, in the exact direction used
in Theorem 8.23. -/
def BoundedMassPhaseOfMassHomBound {J : Type*}
    (dimension : J → ℕ) (mass : J → ℝ)
    (boundedMassAndPhase : Prop) : Prop :=
  UniformMassHomBound dimension mass → boundedMassAndPhase

/-- HLR Proposition 2.38 as used to obtain semistable openness from the
bounded-mass-and-phase condition. -/
def OpennessOfBoundedMassPhase
    (boundedMassAndPhase : Prop)
    (semistableLoci : JOpen → OpenLocusProbe) : Prop :=
  boundedMassAndPhase → UniversalOpenness semistableLoci

/-- BLMNPS Theorems 18.7 and 5.7, together with HLR Proposition 2.38, in the
direction used to construct relative HN structures. -/
def DedekindHNOfBoundedMassPhase
    (boundedMassAndPhase : Prop) (dedekind : DedekindHNProblem D) : Prop :=
  boundedMassAndPhase → IntegratesAfterDedekindBaseChange dedekind

/-- The boundedness implication extracted from the proof of HLR Proposition
2.41, producing the semistable form of clause `(iv')`. -/
def BoundednessOfBoundedMassPhase
    (boundedMassAndPhase : Prop)
    (semistableBoundedness : BoundednessProblem M) : Prop :=
  boundedMassAndPhase → UniversalBoundedness semistableBoundedness

/-- Lemma 8.22, kept as an explicit implication from its semistable
hypotheses to Definition 8.17. -/
def StableOfSemistableOverField
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    (V₀ : Submodule ℝ V)
    {Zlin : V →ₗ[ℝ] ℂ}
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (semistableLoci : JOpen → OpenLocusProbe)
    (stableLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (semistableBoundedness stableBoundedness : BoundednessProblem M) : Prop :=
  SemistableOverFieldConditions σ V₀ Zlin hV₀ semistableLoci dedekind
      semistableBoundedness →
    StabilityOverFieldConditions σ V₀ Zlin hV₀ stableLoci dedekind
      stableBoundedness

/-- BLMNPS Theorem 21.24 in the characteristic-zero direction used in
Theorem 8.23.  `ProperGoodModuli` is a caller-supplied proposition because the
repository does not yet define good moduli spaces. -/
def ProperGoodModuliOfOverField
    (k : Type*) [Field k]
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    (V₀ : Submodule ℝ V)
    {Zlin : V →ₗ[ℝ] ℂ}
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (stableLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (stableBoundedness : BoundednessProblem M)
    (ProperGoodModuli : Prop) : Prop :=
  CharZero k →
    StabilityOverFieldConditions σ V₀ Zlin hV₀ stableLoci dedekind
        stableBoundedness → ProperGoodModuli

/-- Assemble the semistable four-condition input of Lemma 8.22 from the
mass--Hom estimate and the named HLR/BLMNPS implications. -/
theorem semistableOverFieldConditions_of_massHom
    {J : Type*} {dimension : J → ℕ} {mass : J → ℝ}
    {boundedMassAndPhase : Prop}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    {semistableLoci : JOpen → OpenLocusProbe}
    {dedekind : DedekindHNProblem D}
    {semistableBoundedness : BoundednessProblem M}
    (hSupport : HasUniformQuadraticSupportPropertyModulo
      V₀ Zlin hV₀ (ordinaryFiberSemistableClasses σ))
    (hMassHom : UniformMassHomBound dimension mass)
    (hMassPhase : BoundedMassPhaseOfMassHomBound dimension mass boundedMassAndPhase)
    (hOpen : OpennessOfBoundedMassPhase boundedMassAndPhase semistableLoci)
    (hHN : DedekindHNOfBoundedMassPhase boundedMassAndPhase dedekind)
    (hBounded : BoundednessOfBoundedMassPhase boundedMassAndPhase semistableBoundedness) :
    SemistableOverFieldConditions σ V₀ Zlin hV₀ semistableLoci dedekind
      semistableBoundedness := by
  have hbounded : boundedMassAndPhase := hMassPhase hMassHom
  exact ⟨hOpen hbounded, hHN hbounded, hSupport, hBounded hbounded⟩

/-- Theorem 8.23 up to Definition 8.17: the mass--Hom estimate feeds the
named HLR/BLMNPS chain, and Lemma 8.22 upgrades the semistable clauses. -/
theorem stabilityOverFieldConditions_of_massHom
    {J : Type*} {dimension : J → ℕ} {mass : J → ℝ}
    {boundedMassAndPhase : Prop}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    {semistableLoci stableLoci : JOpen → OpenLocusProbe}
    {dedekind : DedekindHNProblem D}
    {semistableBoundedness stableBoundedness : BoundednessProblem M}
    (hSupport : HasUniformQuadraticSupportPropertyModulo
      V₀ Zlin hV₀ (ordinaryFiberSemistableClasses σ))
    (hMassHom : UniformMassHomBound dimension mass)
    (hMassPhase : BoundedMassPhaseOfMassHomBound dimension mass boundedMassAndPhase)
    (hOpen : OpennessOfBoundedMassPhase boundedMassAndPhase semistableLoci)
    (hHN : DedekindHNOfBoundedMassPhase boundedMassAndPhase dedekind)
    (hBounded : BoundednessOfBoundedMassPhase boundedMassAndPhase semistableBoundedness)
    (hStable : StableOfSemistableOverField (σ := σ) V₀ hV₀
      semistableLoci stableLoci dedekind
      semistableBoundedness stableBoundedness) :
    StabilityOverFieldConditions σ V₀ Zlin hV₀ stableLoci dedekind
      stableBoundedness :=
  hStable (semistableOverFieldConditions_of_massHom
    (C := C) (v := v) hSupport hMassHom hMassPhase hOpen hHN hBounded)

/-- The final characteristic-zero good-moduli conclusion of Theorem
8.23, conditional on the named BLMNPS Theorem 21.24 implication.  The field
and its characteristic-zero instance remain explicit. -/
theorem properGoodModuli_of_massHom
    (k : Type*) [Field k] [CharZero k]
    {J : Type*} {dimension : J → ℕ} {mass : J → ℝ}
    {boundedMassAndPhase ProperGoodModuli : Prop}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    {semistableLoci stableLoci : JOpen → OpenLocusProbe}
    {dedekind : DedekindHNProblem D}
    {semistableBoundedness stableBoundedness : BoundednessProblem M}
    (hSupport : HasUniformQuadraticSupportPropertyModulo
      V₀ Zlin hV₀ (ordinaryFiberSemistableClasses σ))
    (hMassHom : UniformMassHomBound dimension mass)
    (hMassPhase : BoundedMassPhaseOfMassHomBound dimension mass boundedMassAndPhase)
    (hOpen : OpennessOfBoundedMassPhase boundedMassAndPhase semistableLoci)
    (hHN : DedekindHNOfBoundedMassPhase boundedMassAndPhase dedekind)
    (hBounded : BoundednessOfBoundedMassPhase boundedMassAndPhase semistableBoundedness)
    (hStable : StableOfSemistableOverField (σ := σ) V₀ hV₀
      semistableLoci stableLoci dedekind
      semistableBoundedness stableBoundedness)
    (hGoodModuli : ProperGoodModuliOfOverField (C := C) (v := v) (σ := σ) (Zlin := Zlin) k
      V₀ hV₀ stableLoci dedekind stableBoundedness ProperGoodModuli) :
    ProperGoodModuli :=
  hGoodModuli inferInstance (stabilityOverFieldConditions_of_massHom
    (C := C) (v := v) hSupport hMassHom hMassPhase hOpen hHN hBounded hStable)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
