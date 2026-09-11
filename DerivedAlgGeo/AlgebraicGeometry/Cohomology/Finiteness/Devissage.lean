/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.LinearConnecting
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Boundedness
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Dévissage: finite-dimensional cohomology from a class of generators

The descending induction behind Serre's finiteness theorem, stated once for any variety and any
supply of generators.

## The argument

Suppose every coherent `F` sits in a short exact sequence `0 → K → G → F → 0` of coherent sheaves
whose middle term has finite-dimensional cohomology in every degree. Above the cohomological
bound of a finite affine cover every group vanishes (`coherent_H_subsingleton_of_cohomologicalBound`),
which starts a descending induction on the degree; at each step the exact, `k`-linear
`Hⁱ(G) → Hⁱ(F) → Hⁱ⁺¹(K)` (`linearCoherentH_exact₃`) has finite-dimensional outer terms -- the
left by hypothesis, the right by the inductive hypothesis applied to `K` -- so its middle term is
finite-dimensional (`Function.Exact.module_finite_of_finite`).

The linearity of the connecting map is what makes this work over the base field; see
`LinearConnecting.lean` for why an additive exact sequence would not suffice.

## The generators are a hypothesis here

On projective space the generators are the twisted structure sheaves, supplied by Serre's theorem
in the form `∐ O(-N) ↠ F` (`ProjectiveSpectrum/Modules/TwistInverse.lean`); `Projective.lean`
instantiates this file there. Nothing about them enters the induction beyond the finiteness of
their cohomology, which is why the induction is stated abstractly.

`module_finite_linearCoherentH_coproduct` supplies the one bookkeeping fact the instantiation
needs: cohomology of a finite coproduct of sheaves with finite-dimensional cohomology is
finite-dimensional, because `linearCoherentH` is additive and so carries finite coproducts to
finite products of vector spaces.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

omit [IsVariety k X] in
/-- **Cohomology of a finite coproduct of coherent sheaves with finite-dimensional cohomology is
finite-dimensional.** `linearCoherentH` is additive, so it preserves finite coproducts, and a
finite coproduct in `ModuleCat k` is a finite product of vector spaces.

Additivity of `linearCoherentH` needs no variety hypothesis, so `IsVariety` is omitted rather
than carried: `runLinter`'s `unusedArguments` rejects a section instance a declaration does not
use. -/
theorem module_finite_linearCoherentH_coproduct [IsLocallyNoetherian X] {J : Type u} [Finite J]
    (G : J → Coh X) (i : ℕ) (hG : ∀ j, Module.Finite k ((linearCoherentH k X i).obj (G j))) :
    Module.Finite k ((linearCoherentH k X i).obj (∐ G)) := by
  classical
  haveI := Fintype.ofFinite J
  haveI : ∀ j, Module.Finite k ((linearCoherentH k X i).obj (G j)) := hG
  let e₁ : (linearCoherentH k X i).obj (∐ G) ≅ ∐ fun j => (linearCoherentH k X i).obj (G j) :=
    PreservesCoproduct.iso (linearCoherentH k X i) G
  haveI : HasBiproductsOfShape J (ModuleCat.{u + 1} k) :=
    hasBiproductsOfShape_finite (ModuleCat.{u + 1} k)
  let e₂ : (∐ fun j => (linearCoherentH k X i).obj (G j)) ≅
      ⨁ fun j => (linearCoherentH k X i).obj (G j) :=
    (biproduct.isoCoproduct _).symm
  let e₃ : (⨁ fun j => (linearCoherentH k X i).obj (G j)) ≅
      ∏ᶜ fun j => (linearCoherentH k X i).obj (G j) :=
    biproduct.isoProduct _
  let e₄ : (∏ᶜ fun j => (linearCoherentH k X i).obj (G j)) ≅
      ModuleCat.of k (∀ j, (linearCoherentH k X i).obj (G j)) :=
    ModuleCat.piIsoPi.{u, u, u + 1} _
  exact Module.Finite.equiv (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).toLinearEquiv.symm

/-- **Dévissage.** If every coherent sheaf on `X` is the quotient of a coherent sheaf with
finite-dimensional cohomology in every degree, by a coherent kernel, then every coherent sheaf
has finite-dimensional cohomology in every degree.

Descending induction on the degree, from the vanishing bound of a finite affine cover, along the
linear exact sequence `Hⁱ(G) → Hⁱ(F) → Hⁱ⁺¹(K)`. -/
theorem module_finite_linearCoherentH_of_devissage [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hgen : ∀ F : Coh X, ∃ (S : ShortComplex (Coh X)) (_ : S.ShortExact) (_ : S.X₃ ≅ F),
      ∀ i, Module.Finite k ((linearCoherentH k X i).obj S.X₂))
    (i : ℕ) (F : Coh X) : Module.Finite k ((linearCoherentH k X i).obj F) := by
  suffices h : ∀ (m i : ℕ), cohomologicalBound X + 1 ≤ i + m →
      ∀ F : Coh X, Module.Finite k ((linearCoherentH k X i).obj F) from
    h (cohomologicalBound X + 1) i (by omega) F
  intro m
  induction m with
  | zero =>
    intro i hi F
    haveI : Subsingleton ((linearCoherentH k X i).obj F) :=
      coherent_H_subsingleton_of_cohomologicalBound F i (by omega)
    exact Module.Finite.of_finite
  | succ m ih =>
    intro i hi F
    obtain ⟨S, hS, e, hG⟩ := hgen F
    haveI : Module.Finite k ((linearCoherentH k X i).obj S.X₂) := hG i
    haveI : Module.Finite k ((linearCoherentH k X (i + 1)).obj S.X₁) :=
      ih (i + 1) (by omega) S.X₁
    haveI : Module.Finite k ((linearCoherentH k X i).obj S.X₃) :=
      (linearCoherentH_exact₃ S hS i).module_finite_of_finite
    exact Module.Finite.equiv ((linearCoherentH k X i).mapIso e).toLinearEquiv

end AlgebraicGeometry.Cohomology
