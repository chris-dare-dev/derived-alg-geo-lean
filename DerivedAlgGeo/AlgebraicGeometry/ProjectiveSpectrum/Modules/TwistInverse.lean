/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistComparison
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.GlobalGeneration
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible

/-!
# `O(-N)` is the tensor inverse of `O(N)`, and Serre's surjection `⊕ O(-N) ↠ F`

The `L = O(N)` case of `#806`, and with it the literal deliverable of `#586`.

## The inverse is four isomorphisms

`twistingSheafTensorAddIso` gives `O(N) ⊗ O(-N) ≅ O(N + -N)`; the index is `0`; `O(0)` is the
associated sheaf of `𝒜` over itself (`twistingSheafZeroIso`); and that is the unit
(`associatedSheafSelfIso`). `twistingSheafTensorNegIso` is the composite. As `#806` records, this
composite did not typecheck before `#821` put both factors in one graded setting; it does now, and
nothing about it is specific to the sign of `N`.

## Untwisting an arbitrary `F`

`tensorTwistNegIso : (F ⊗ O(N)) ⊗ O(-N) ≅ F` is the associator, the inverse above under `F ⊗ -`,
and the right unitor. `F` is **arbitrary** -- `TensorTwist.lean`'s warning about `F(d)(e) ≅ F(d+e)`
concerned an associator that then carried invertibility hypotheses; `tensorAssocIso` no longer
does, so the only invertible factors needed are the two twists, and they are invertible.

## From `free I ↠ F(N)` to `⊕ O(-N) ↠ F`

`exists_epi_free_tensorTwist` produces `p : free I ↠ F ⊗ O(N)`. Tensoring by `O(-N)` on the left
keeps it an epimorphism (`epi_tensorHom_id_of_invertible`), the symmetry and `tensorTwistNegIso`
carry the target to `F`, and `tensorLeftFreeIso` identifies the source with `∐ O(-N)`. That is
Hartshorne II.5.17 in the form `#586` states: every coherent `F` on `Proj 𝒜` is a quotient of a
finite direct sum of copies of one `O(-N)`.

## What is not here

The general `IsInvertible L → ∃ L', L ⊗ L' ≅ unit` and the hom-equivalence
`Hom(L ⊗ M, N) ≅ Hom(M, L' ⊗ N)` with identified composites, which `#806` also asks for. The
first needs the per-chart trivializations glued; the second needs the associator natural in all
three arguments. Neither is needed for the surjection, and `#806` stays open for them.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

section Inverse

variable {I : Type u} (g : I → 𝒜 1) (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)

/-- **`O(N) ⊗ O(-N) ≅ O`.** The tensor inverse of the twisting sheaf, for degree-one generated
`𝒜`: the twist-addition isomorphism at `N + -N = 0`, then the identification of `O(0)` with the
unit. -/
def twistingSheafTensorNegIso (N : ℤ) :
    Scheme.Modules.tensorObj (twistingSheaf 𝒜 N) (twistingSheaf 𝒜 (-N)) ≅
      SheafOfModules.unit (Proj 𝒜).ringCatSheaf :=
  twistingSheafTensorAddIso 𝒜 g N (-N) hg ≪≫
    eqToIso (congrArg (twistingSheaf 𝒜) (add_neg_cancel N)) ≪≫
    twistingSheafZeroIso 𝒜 ≪≫ associatedSheafSelfIso 𝒜

/-- **Untwisting: `(F ⊗ O(N)) ⊗ O(-N) ≅ F`**, for an arbitrary module sheaf `F`.

The associator, the inverse of `O(N)` under `F ⊗ -`, and the right unitor. This is the
isomorphism `GlobalGeneration.lean` records as the gap between `free I ↠ F(N)` and
`⊕ O(-N) ↠ F`. -/
def tensorTwistNegIso (F : (Proj 𝒜).Modules) (N : ℤ) :
    Scheme.Modules.tensorObj (Scheme.Modules.tensorObj F (twistingSheaf 𝒜 N))
      (twistingSheaf 𝒜 (-N)) ≅ F :=
  Scheme.Modules.tensorAssocIso F (twistingSheaf 𝒜 N) (twistingSheaf 𝒜 (-N)) ≪≫
    Scheme.Modules.tensorObjIso (Iso.refl F) (twistingSheafTensorNegIso 𝒜 g hg N) ≪≫
    Scheme.Modules.tensorUnitRightIso F

end Inverse

/-- **Serre's theorem: a coherent sheaf on `Proj 𝒜` is a quotient of a finite direct sum of
copies of `O(-N)`**, for `𝒜` generated over `𝒜 0` by finitely many degree-one elements.

Hartshorne II.5.17 / EGA II 2.7.9 in the form `#586` states. The surjection is
`exists_epi_free_tensorTwist`'s `free I ↠ F ⊗ O(N)` tensored by `O(-N)`, untwisted by
`tensorTwistNegIso`, and read on `∐ O(-N)` through `tensorLeftFreeIso`. No global-generation or
resolution hypothesis, and no instance supplies the surjection. The exponent can be pushed above
any `N₀`; the dévissage on `Pⁿ` takes `N ≥ 1` so that `H⁰(O(-N)) = 0`. -/
theorem exists_epi_coproduct_twistingSheaf_ge (F : (Proj 𝒜).Modules)
    (hF : Scheme.Modules.IsCoherent (Proj 𝒜) F)
    {ι : Type u} [Finite ι] {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤) (N₀ : ℕ) :
    ∃ (N : ℕ) (_ : N₀ ≤ N) (I : Type u) (_ : Finite I)
      (q : ∐ (fun _ : I => twistingSheaf 𝒜 (-(N : ℤ))) ⟶ F), Epi q := by
  obtain ⟨N, hN₀, I, hI, p, hp⟩ := exists_epi_free_tensorTwist_ge 𝒜 F hF hg hcov N₀
  have hcov' : Algebra.adjoin (𝒜 0)
      (Set.range fun j => ((fun i => (⟨g i, hg i⟩ : 𝒜 1)) j : A)) = ⊤ := hcov
  haveI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from twistingSheaf 𝒜 (-(N : ℤ))) :=
    twistingSheaf_isInvertible 𝒜 (fun i => (⟨g i, hg i⟩ : 𝒜 1)) (-(N : ℤ)) hcov'
  haveI hp' : Epi (show (show (Proj 𝒜).Modules from SheafOfModules.free.{u} I) ⟶
      Scheme.Modules.tensorObj F (twistingSheaf 𝒜 (N : ℤ)) from p) := hp
  refine ⟨N, hN₀, I, hI,
    (Scheme.Modules.tensorLeftFreeIso (twistingSheaf 𝒜 (-(N : ℤ))) I).inv ≫
      Scheme.Modules.tensorHom (𝟙 (twistingSheaf 𝒜 (-(N : ℤ)))) p ≫
      (Scheme.Modules.tensorCommIso _ _).hom ≫
      (tensorTwistNegIso 𝒜 (fun i => (⟨g i, hg i⟩ : 𝒜 1)) hcov' F (N : ℤ)).hom, ?_⟩
  haveI := Scheme.Modules.epi_tensorHom_id_of_invertible (twistingSheaf 𝒜 (-(N : ℤ))) p
  infer_instance

/-- **Serre's theorem in the `∐ O(-N) ↠ F` form**, with the exponent unconstrained. -/
theorem exists_epi_coproduct_twistingSheaf (F : (Proj 𝒜).Modules)
    (hF : Scheme.Modules.IsCoherent (Proj 𝒜) F)
    {ι : Type u} [Finite ι] {g : ι → A} (hg : ∀ i, g i ∈ 𝒜 1)
    (hcov : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤) :
    ∃ (N : ℕ) (I : Type u) (_ : Finite I)
      (q : ∐ (fun _ : I => twistingSheaf 𝒜 (-(N : ℤ))) ⟶ F), Epi q := by
  obtain ⟨N, -, I, hI, q, hq⟩ := exists_epi_coproduct_twistingSheaf_ge 𝒜 F hF hg hcov 0
  exact ⟨N, I, hI, q, hq⟩

end AlgebraicGeometry.Proj
