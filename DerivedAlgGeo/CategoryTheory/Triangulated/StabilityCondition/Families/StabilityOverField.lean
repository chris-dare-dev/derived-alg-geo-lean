/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.FiberwiseSupport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.Ordinary
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.FieldExtension

/-!
# Stability over a field and the good-moduli input chain

This file records Definition 8.17 and the implication chain used in Theorem
8.23 of arXiv:2607.28411v1.  `Definition817Conditions` specializes the
existing canonical `OrdinaryDeformationInputConditions` root to the actual
semistable classes of the fiber slicings.  Its four conditions are uniform
quotient support, openness, relative HN structures after the specified
Dedekind base changes, and boundedness.

The external HLR and BLMNPS results used by the paper are named proposition
types.  Assembly theorems consume them as hypotheses; no structure carries a
good-moduli conclusion, and this file does not manufacture a moduli space.
The semistable variant used by Lemma 8.22 is a second abbreviation of the same
root with semistable probes substituted for stable probes.
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

/-- The four clauses of PF4 Definition 8.17 as a specialization of the
canonical deformation-input root.  The support locus is definitionally the
set of classes of actual nonzero semistable objects in each fiber.  The
zero-charge subspace and its containment proof stay explicit, as required by
the repository's quotient-support interface. -/
abbrev Definition817Conditions
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (V₀ : Submodule ℝ V)
    (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (openLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (boundedness : BoundednessProblem M) : Prop :=
  OrdinaryDeformationInputConditions openLoci dedekind V₀ Zlin hV₀
    (ordinaryFiberSemistableClasses σ) boundedness

/-- The `(ii')`/`(iv')` semistable variant used in PF4 Lemma 8.22.  It is the
same canonical four-condition interface; only the caller's openness and
boundedness probes now describe semistable objects. -/
abbrev Lemma822SemistableConditions
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (V₀ : Submodule ℝ V)
    (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (semistableLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (semistableBoundedness : BoundednessProblem M) : Prop :=
  Definition817Conditions σ V₀ Zlin hV₀ semistableLoci dedekind
    semistableBoundedness

/-- HLR Theorem 2.35, implication `(1) → (2)`, in the exact direction used
in PF4 Theorem 8.23. -/
def HLRTheorem235OneToTwo {J : Type*}
    (dimension : J → ℕ) (mass : J → ℝ)
    (boundedMassAndPhase : Prop) : Prop :=
  UniformMassHomBound dimension mass → boundedMassAndPhase

/-- HLR Proposition 2.38 as used to obtain semistable openness from the
bounded-mass-and-phase condition. -/
def HLRProposition238
    (boundedMassAndPhase : Prop)
    (semistableLoci : JOpen → OpenLocusProbe) : Prop :=
  boundedMassAndPhase → UniversalOpenness semistableLoci

/-- BLMNPS Theorems 18.7 and 5.7, together with HLR Proposition 2.38, in the
direction used to construct relative HN structures. -/
def BLMNPSTheorems187And57
    (boundedMassAndPhase : Prop) (dedekind : DedekindHNProblem D) : Prop :=
  boundedMassAndPhase → IntegratesAfterDedekindBaseChange dedekind

/-- The boundedness implication extracted from the proof of HLR Proposition
2.41, producing the semistable form of clause `(iv')`. -/
def HLRProposition241
    (boundedMassAndPhase : Prop)
    (semistableBoundedness : BoundednessProblem M) : Prop :=
  boundedMassAndPhase → UniversalBoundedness semistableBoundedness

/-- PF4 Lemma 8.22, kept as an explicit implication from its semistable
hypotheses to Definition 8.17. -/
def PF4Lemma822
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    (V₀ : Submodule ℝ V)
    {Zlin : V →ₗ[ℝ] ℂ}
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (semistableLoci : JOpen → OpenLocusProbe)
    (stableLoci : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (semistableBoundedness stableBoundedness : BoundednessProblem M) : Prop :=
  Lemma822SemistableConditions σ V₀ Zlin hV₀ semistableLoci dedekind
      semistableBoundedness →
    Definition817Conditions σ V₀ Zlin hV₀ stableLoci dedekind
      stableBoundedness

/-- BLMNPS Theorem 21.24 in the characteristic-zero direction used in PF4
Theorem 8.23.  `ProperGoodModuli` is a caller-supplied proposition because the
repository does not yet define good moduli spaces. -/
def BLMNPSTheorem2124
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
    Definition817Conditions σ V₀ Zlin hV₀ stableLoci dedekind
        stableBoundedness → ProperGoodModuli

/-- Assemble the semistable four-condition input of PF4 Lemma 8.22 from the
mass--Hom estimate and the named HLR/BLMNPS implications. -/
theorem lemma822SemistableConditions_of_massHom
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
    (h84 : UniformMassHomBound dimension mass)
    (h235 : HLRTheorem235OneToTwo dimension mass boundedMassAndPhase)
    (h238 : HLRProposition238 boundedMassAndPhase semistableLoci)
    (hHN : BLMNPSTheorems187And57 boundedMassAndPhase dedekind)
    (h241 : HLRProposition241 boundedMassAndPhase semistableBoundedness) :
    Lemma822SemistableConditions σ V₀ Zlin hV₀ semistableLoci dedekind
      semistableBoundedness := by
  have hbounded : boundedMassAndPhase := h235 h84
  exact ⟨h238 hbounded, hHN hbounded, hSupport, h241 hbounded⟩

/-- PF4 Theorem 8.23 up to Definition 8.17: the mass--Hom estimate feeds the
named HLR/BLMNPS chain, and PF4 Lemma 8.22 upgrades the semistable clauses. -/
theorem theorem823_definition817
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
    (h84 : UniformMassHomBound dimension mass)
    (h235 : HLRTheorem235OneToTwo dimension mass boundedMassAndPhase)
    (h238 : HLRProposition238 boundedMassAndPhase semistableLoci)
    (hHN : BLMNPSTheorems187And57 boundedMassAndPhase dedekind)
    (h241 : HLRProposition241 boundedMassAndPhase semistableBoundedness)
    (h822 : PF4Lemma822 (σ := σ) V₀ hV₀
      semistableLoci stableLoci dedekind
      semistableBoundedness stableBoundedness) :
    Definition817Conditions σ V₀ Zlin hV₀ stableLoci dedekind
      stableBoundedness :=
  h822 (lemma822SemistableConditions_of_massHom
    (C := C) (v := v) hSupport h84 h235 h238 hHN h241)

/-- The final characteristic-zero good-moduli conclusion of PF4 Theorem
8.23, conditional on the named BLMNPS Theorem 21.24 implication.  The field
and its characteristic-zero instance remain explicit. -/
theorem theorem823_properGoodModuli
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
    (h84 : UniformMassHomBound dimension mass)
    (h235 : HLRTheorem235OneToTwo dimension mass boundedMassAndPhase)
    (h238 : HLRProposition238 boundedMassAndPhase semistableLoci)
    (hHN : BLMNPSTheorems187And57 boundedMassAndPhase dedekind)
    (h241 : HLRProposition241 boundedMassAndPhase semistableBoundedness)
    (h822 : PF4Lemma822 (σ := σ) V₀ hV₀
      semistableLoci stableLoci dedekind
      semistableBoundedness stableBoundedness)
    (h2124 : BLMNPSTheorem2124 (C := C) (v := v) (σ := σ) (Zlin := Zlin) k
      V₀ hV₀ stableLoci dedekind stableBoundedness ProperGoodModuli) :
    ProperGoodModuli :=
  h2124 inferInstance (theorem823_definition817
    (C := C) (v := v) hSupport h84 h235 h238 hHN h241 h822)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
