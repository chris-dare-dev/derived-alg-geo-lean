/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistComparison
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.GlobalGeneration
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle

/-!
# `O(-N)` is the tensor inverse of `O(N)`, and Serre's surjection `⊕ O(-N) ↠ F`

The twisting sheaf `O(-N)` is a tensor inverse of `O(N)` when degree-one elements generate `A` over
`𝒜 0`. With it, the global-generation form `free I ↠ F(N)` of Serre's theorem untwists to a
surjection `⊕ O(-N) ↠ F` onto an arbitrary coherent `F`.

## Main definitions

* `AlgebraicGeometry.Proj.twistingSheafTensorNegIso`: `O(N) ⊗ O(-N) ≅ O`.
* `AlgebraicGeometry.Proj.twistingSheafLineBundleData`: `O(N)` with `O(-N)` as a chosen tensor
  inverse.
* `AlgebraicGeometry.Proj.twistingSheafHomTopEquiv`: `Hom(O(N), F) ≃ Γ(O(-N) ⊗ F)`.
* `AlgebraicGeometry.Proj.tensorTwistNegIso`: untwisting, `(F ⊗ O(N)) ⊗ O(-N) ≅ F`, for an
  arbitrary module sheaf `F`.

## Main results

* `AlgebraicGeometry.Proj.exists_epi_coproduct_twistingSheaf_ge`: Serre's theorem, a coherent sheaf
  on `Proj 𝒜` is a quotient of a finite direct sum of copies of `O(-N)`, with `N` above any
  prescribed bound.
* `AlgebraicGeometry.Proj.exists_epi_coproduct_twistingSheaf`: the same with the exponent
  unconstrained.

## Implementation notes

### The inverse is four isomorphisms

`twistingSheafTensorAddIso` gives `O(N) ⊗ O(-N) ≅ O(N + -N)`; the index is `0`; `O(0)` is the
associated sheaf of `𝒜` over itself (`twistingSheafZeroIso`); and that is the unit
(`associatedSheafSelfIso`). `twistingSheafTensorNegIso` is the composite. It typechecks because
both factors live in one graded setting, and nothing about it is specific to the sign of `N`.

### Untwisting an arbitrary `F`

`tensorTwistNegIso : (F ⊗ O(N)) ⊗ O(-N) ≅ F` is the associator, the inverse above under `F ⊗ -`,
and the right unitor. `F` is **arbitrary**: `tensorAssocIso` carries no invertibility hypotheses,
so the only invertible factors needed are the two twists, and they are invertible.

### From `free I ↠ F(N)` to `⊕ O(-N) ↠ F`

`exists_epi_free_tensorTwist` produces `p : free I ↠ F ⊗ O(N)`. Tensoring by `O(-N)` on the left
keeps it an epimorphism (`epi_tensorHom_id_of_invertible`), the symmetry and `tensorTwistNegIso`
carry the target to `F`, and `tensorLeftFreeIso` identifies the source with `∐ O(-N)`. That is
Hartshorne II.5.17 in its coproduct form: every coherent `F` on `Proj 𝒜` is a quotient of a
finite direct sum of copies of one `O(-N)`.
Its specialization to projective space and lift to a coherent short exact sequence is
`exists_shortExact_coproduct_twist` in `Cohomology/Finiteness/Projective.lean`.

### What is not here

The general `IsInvertible L → ∃ L', L ⊗ L' ≅ unit`, which needs the per-chart trivializations
glued. For an explicit `LineBundleData`, the hom-equivalence `Hom(L ⊗ M, N) ≃ Hom(M, L⁻¹ ⊗ N)` is
`LineBundleData.tensorLeftHomEquiv`, from associator naturality in the monoidal structure. Its
scalar-linear refinement is downstream at `LineBundleData.tensorLeftHomLinearEquiv`.

## References

Hartshorne, *Algebraic Geometry*, II.5.17; EGA II 2.7.9.

## Tags

Serre's theorem, projective spectrum, twisting sheaf, invertible sheaf, coherent sheaf
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

/-- The twisting sheaf with its opposite twist as a chosen tensor inverse. -/
def twistingSheafLineBundleData (N : ℤ) :
    Scheme.Modules.LineBundleData (Proj 𝒜) where
  line := twistingSheaf 𝒜 N
  inverse := twistingSheaf 𝒜 (-N)
  lineIsInvertible := twistingSheaf_isInvertible 𝒜 g N hg
  inverseIsInvertible := twistingSheaf_isInvertible 𝒜 g (-N) hg
  tensorInverseIso := twistingSheafTensorNegIso 𝒜 g hg N

/-- The projective twisting-sheaf specialization of the line-bundle Hom/sections comparison:
`Hom(O(N), F) ≃ Γ(O(-N) ⊗ F)`.

This file records the categorical equivalence at the neutral line-bundle layer. The generic
scalar-linear refinement is `LineBundleData.lineHomTopLinearEquivOver`, and the projective
Hom-finiteness reduction using it lives in `Cohomology.Finiteness.Hom`. -/
def twistingSheafHomTopEquiv (N : ℤ) (F : (Proj 𝒜).Modules) :
    (twistingSheaf 𝒜 N ⟶ F) ≃
      Γ(Scheme.Modules.tensorObj (twistingSheaf 𝒜 (-N)) F, ⊤) :=
  (twistingSheafLineBundleData 𝒜 g hg N).lineHomTopEquiv F

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

Hartshorne II.5.17 / EGA II 2.7.9 in its coproduct form. The surjection is
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
