/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.IntersectionTheory.Surface.Number

/-!
# The Hilbert function of a coherent sheaf against a polarization

For a coherent sheaf `F` on a variety `X` over a field `k` and a line-bundle class `L`, the
Hilbert function is `n ↦ χ(F ⊗ L^n)`. This file names it, proves it invariant under
isomorphism and additive on short exact sequences, factors it through the Grothendieck group
as `hilbertHom : K₀Ab (Coh X) →+ (ℤ → ℤ)`, and records that Snapper's theorem bounds its
finite-difference degree by the supplied dimension.

Both the numerical content and the supplied-input carrier already exist under other names:
`Snapper.oneVariableEulerFunction` is the function, and
`IntersectionTheory.Number.TwistContext` is the carrier of Snapper's inputs. This file is
the geometric packaging and the additivity that nobody had stated. It creates no new carrier.

## What is supplied, and why

`PolarizedVarietyData k X` is the `…Data` idiom for genuinely external input. Its five fields
are a line-bundle class `L`, finite coherent cohomology `D`, a linear connecting system `C`,
a natural number `dim`, and, for every coherent sheaf, a `TwistContext`. Every
supplied-not-proved field reachable from it is listed here:

* `L : Pic X` is **not** asserted to be ample. Ampleness does not exist at this pin;
  `git grep -in 'ample'` finds only numerical-example docstrings. Nothing below uses it,
  and the objects that would (positivity of the leading coefficient, hyperplane sections)
  belong to later issues in this lane.
* `D : FiniteCohomology k X` supplies coherent cohomology as finite-dimensional `k`-modules
  with a vanishing bound, the two inputs that make `χ` a finite sum.
* `C : D.LinearConnectingSystem` chooses, for every short exact sequence of coherent
  sheaves, `k`-linear connecting maps compatible with the `Ext` connecting maps. Euler
  additivity is proved from it; it is the temporary input that a Grothendieck-group
  factorization needs.
* `twists F : TwistContext D F dim` bundles, for every finite family of Picard classes,
  the coherence of every integer twist (`CoherentTwistFamily`), the hyperplane-section
  induction that the classical proof of Snapper's theorem uses (`GeometricInduction`), and a
  Picard-level Euler function `eulerPic` together with its identification `realization`
  with the geometric one. Coherence of a twist by an invertible sheaf and the geometric
  induction are both open at this pin; `dim` is the number of cuts after which the induction
  terminates, and is not derived from `X`.

Compare `RiemannRoch.ReconstructionSystem`, which also quantifies a `TwistContext` over
every coherent sheaf but additionally demands a `PairingContext`, a graded ring, a rank, and
takes additivity of `eulerPic` as a *field*. None of that is needed here, and additivity of
the Hilbert function is a theorem below rather than an assumption.

## Why the definition goes through `oneVariableEulerFunction`

`hilbertFunction` is defined as `Snapper.oneVariableEulerFunction` on the rank-one twist
family, and `hilbertFunction_eq_eulerPic` identifies it with `eulerPic (L ^ n)` as a lemma.
Defining it through `eulerPic` directly would be shorter but would leave additivity
unprovable: `TwistContext` carries no additivity of `eulerPic`, which is precisely the field
`ReconstructionSystem` adds. Through `eulerFunction` the additivity is a genuine theorem,
from `Coh.shortExact_map_ι`, `Modules.shortExact_map_tensorLeft_of_invertible` and
`eulerCharacteristic_additive_modules`, and both descriptions are then available.

## Placement

`AlgebraicGeometry/Stability/` is stability *of sheaves*: slope, Gieseker, and their
Harder–Narasimhan theory on `Coh X`. It is distinct from `AlgebraicGeometry/StabilityCondition/`,
which belongs to the derived-category families lane, and it imports nothing from the
abstract stability-condition tree.

Not here: coefficient extraction (multiplicity and degree), any semistability notion,
Harder–Narasimhan filtrations, and any construction of `GeometricInduction` from ampleness.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.IntersectionTheory.Snapper
open AlgebraicGeometry.IntersectionTheory.Number
open NumericalPolynomial

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **A polarized variety, as supplied data.** A line-bundle class, finite coherent
cohomology with linear connecting maps, a dimension, and Snapper's inputs for every coherent
sheaf. See the module docstring for what each field supplies and why none is proved here;
in particular `L` is not asserted to be ample. -/
structure PolarizedVarietyData (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsVariety k X] where
  /-- The polarizing line-bundle class. Not asserted to be ample. -/
  L : Pic X
  /-- Finite coherent cohomology: finite-dimensional `Hⁱ` with a vanishing bound. -/
  D : FiniteCohomology k X
  /-- Linear connecting maps for every short exact sequence of coherent sheaves. -/
  C : D.LinearConnectingSystem
  /-- The number of hyperplane cuts after which the geometric induction terminates. -/
  dim : ℕ
  /-- Snapper's supplied inputs for every coherent sheaf: coherence of every twist, the
  geometric induction, and the Picard-level Euler function with its realization. -/
  twists : ∀ F : Coh X, TwistContext D F dim

namespace PolarizedVarietyData

variable (P : PolarizedVarietyData k X)

/-- The rank-one coherent twist family `n ↦ F ⊗ L^n`, projected from `twists`. -/
noncomputable abbrev twistFamily (F : Coh X) :
    CoherentTwistFamily F (fun _ : Fin 1 ↦ P.L) :=
  (P.twists F).twistFamily 1 (fun _ ↦ P.L)

/-- **The Hilbert function** `n ↦ χ(F ⊗ L^n)`, as Snapper's one-variable Euler function of
the rank-one twist family. -/
noncomputable def hilbertFunction (F : Coh X) : ℤ → ℤ :=
  oneVariableEulerFunction P.D P.L (P.twistFamily F)

theorem hilbertFunction_apply (F : Coh X) (n : ℤ) :
    P.hilbertFunction F n =
      P.D.eulerCharacteristic ((P.twistFamily F).obj (oneVariablePoint n)) := rfl

/-- The rank-one Picard monomial is the Picard power. -/
theorem picardMonomial_fin_one (L : Pic X) (n : ℤ) :
    picardMonomial (fun _ : Fin 1 ↦ L) (oneVariablePoint n) = picardPower L n := by
  rw [picardMonomial, Fin.prod_univ_one]
  rfl

/-- **The Hilbert function is the Picard-level Euler function at `L ^ n`.** This is the
identification `TwistContext.realization` provides; it is a lemma, not the definition, for
the reason given in the module docstring. -/
theorem hilbertFunction_eq_eulerPic (F : Coh X) (n : ℤ) :
    P.hilbertFunction F n = (P.twists F).eulerPic (picardPower P.L n) := by
  rw [← picardMonomial_fin_one,
    (P.twists F).realization 1 (fun _ ↦ P.L) (oneVariablePoint n)]
  rfl

/-- The Hilbert function is invariant under isomorphism of coherent sheaves. -/
theorem hilbertFunction_eq_of_iso {F G : Coh X} (e : F ≅ G) :
    P.hilbertFunction F = P.hilbertFunction G := by
  funext n
  exact congrFun
    (eulerFunction_eq_of_coherentSheafIso P.D e (P.twistFamily F) (P.twistFamily G))
    (oneVariablePoint n)

/-- At rank one the simultaneous twist is a single tensor product by the integer power. -/
theorem twistModules_fin_one (L : Pic X) (n : ℤ) (M : X.Modules) :
    twistModules (fun _ : Fin 1 ↦ L) (oneVariablePoint n) M =
      tensorObj (linePower L n) M := by
  unfold twistModules
  rw [Finset.univ_unique, Finset.toList_singleton]
  rfl

/-- Coherence of `F ⊗ L^n`, read off the supplied twist family. -/
theorem isCoherent_tensor_linePower (F : Coh X) (n : ℤ) :
    Scheme.Modules.IsCoherent X (tensorObj (linePower P.L n) F.obj) := by
  rw [← twistModules_fin_one P.L n F.obj]
  exact (P.twistFamily F).coherent (oneVariablePoint n)

/-- The Hilbert function evaluated at `n` is the Euler characteristic of the single tensor
product `F ⊗ L^n`, as a coherent sheaf. -/
theorem hilbertFunction_eq_eulerCharacteristic_tensor (F : Coh X) (n : ℤ) :
    P.hilbertFunction F n =
      P.D.eulerCharacteristic
        ⟨tensorObj (linePower P.L n) F.obj, P.isCoherent_tensor_linePower F n⟩ := by
  rw [P.hilbertFunction_apply]
  exact P.D.eulerCharacteristic_iso
    (ObjectProperty.isoMk (Scheme.coherent X) (eqToIso (twistModules_fin_one P.L n F.obj)))

/-- **Additivity of the Hilbert function**, as a theorem. The short exact sequence is pushed
to module sheaves by `Coh.shortExact_map_ι`, tensored by the invertible sheaf `L^n` with
`Modules.shortExact_map_tensorLeft_of_invertible`, and returned to coherent sheaves by
`eulerCharacteristic_additive_modules` with connecting maps from `C`. -/
theorem hilbertFunction_additive (S : ShortComplex (Coh X)) (hS : S.ShortExact) (n : ℤ) :
    P.hilbertFunction S.X₂ n = P.hilbertFunction S.X₁ n + P.hilbertFunction S.X₃ n := by
  have hS' : ((S.map (Coh.ι X)).map (tensorLeftFunctor (linePower P.L n))).ShortExact :=
    shortExact_map_tensorLeft_of_invertible (linePower P.L n) _ (Coh.shortExact_map_ι X hS)
  have hadd := P.D.eulerCharacteristic_additive_modules hS'
    (P.isCoherent_tensor_linePower S.X₁ n) (P.isCoherent_tensor_linePower S.X₂ n)
    (P.isCoherent_tensor_linePower S.X₃ n)
    (P.C _ (FiniteCohomology.coherentShortComplex_shortExact hS'
      (P.isCoherent_tensor_linePower S.X₁ n) (P.isCoherent_tensor_linePower S.X₂ n)
      (P.isCoherent_tensor_linePower S.X₃ n)))
  rw [P.hilbertFunction_eq_eulerCharacteristic_tensor S.X₁ n,
    P.hilbertFunction_eq_eulerCharacteristic_tensor S.X₂ n,
    P.hilbertFunction_eq_eulerCharacteristic_tensor S.X₃ n]
  exact hadd

/-- **The Hilbert function as a homomorphism `K₀(Coh X) → (ℤ → ℤ)`**, by the universal
property of the Grothendieck group, exactly as `FiniteCohomology.grothendieckEulerHom`
factors `χ`. -/
noncomputable def hilbertHom : K₀Ab (Coh X) →+ (ℤ → ℤ) :=
  K₀Ab.liftOf P.hilbertFunction
    (fun S hS ↦ funext fun n ↦ P.hilbertFunction_additive S hS n)

@[simp]
theorem hilbertHom_of (F : Coh X) : P.hilbertHom (K₀Ab.of F) = P.hilbertFunction F :=
  K₀Ab.liftOf_of _ _ F

/-- **Snapper's bound**: the Hilbert function has finite-difference degree at most `dim`,
from the supplied geometric induction. -/
theorem hilbertFunction_degreeLE (F : Coh X) :
    DegreeLE P.dim (oneVariable (P.hilbertFunction F)) := by
  rw [hilbertFunction, oneVariable_eulerFunction]
  exact snapper P.D P.C (P.twistFamily F) P.dim
    ((P.twists F).geometricInduction 1 (fun _ ↦ P.L))

/-- The ordinary form of Snapper's bound: the `(dim + 1)`st forward difference of the
Hilbert function vanishes. -/
theorem fwdDiff_hilbertFunction (F : Coh X) :
    (fwdDiff (1 : ℤ))^[P.dim + 1] (P.hilbertFunction F) = 0 :=
  oneVariable_fwdDiff_euler_vanishes P.D P.C P.L (P.twistFamily F) P.dim
    ((P.twists F).geometricInduction 1 (fun _ ↦ P.L))

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
