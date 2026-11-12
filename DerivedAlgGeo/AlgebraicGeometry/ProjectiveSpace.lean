/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Grading
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.MapPullback
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistComparison
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Projective space over a base scheme

For a type `n` of homogeneous coordinates and a scheme `S`, projective space over `S` is the base
change of the universal projective space (Stacks 01NF):

    ℙ(n; S) := S ×_ℤ Proj ℤ[n].

This follows Mathlib's `AffineSpace n S := S ×_ℤ Spec ℤ[n]`, notation `𝔸(n; S)`. Since `n` indexes
homogeneous coordinates, `ℙ(n; S)` is `ℙ^{|n| - 1}_S`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace n S`, with its structure morphism to `S` as a
  `CanonicallyOver` instance and `ProjectiveSpace.toProj` to the universal model.
* `ProjectiveSpace.map`: functoriality in `S`.
* `ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`, from `Proj.isPullback_map_baseChange`.
* `ProjectiveSpace.twistingSheaf n S d`, the pullback of `𝒪(d)` from `Proj ℤ[n]`.
* `ProjectiveSpace.twistingSheafSpecIso`: under `SpecIso`, `𝒪(d)` on `ℙ(n; Spec R)` is `𝒪(d)` on
  `Proj R[n]`.

## Main results

* `ProjectiveSpace.isProper`: `ℙ(n; S) → S` is proper for finite `n`.
* `ProjectiveSpace.isPullback_map`: `ℙ(n; S') = S' ×_S ℙ(n; S)`.
* `ProjectiveSpace.SpecIso_hom_comp_projectiveSpaceToSpec`: over a field, `SpecIso` identifies
  `ℙ(n; Spec k)` with the field-level `projectiveSpace` and its structure morphism, so there is one
  projective space.
* `ProjectiveSpace.isInvertible_twistingSheaf`: `𝒪(d)` is invertible.
* `ProjectiveSpace.twistingSheafTensorIso`: `𝒪(d) ⊗ 𝒪(e) ≅ 𝒪(d + e)` once pullback along `toProj`
  is strong monoidal.

## Notation

* `ℙ(n; S)`, scoped in `AlgebraicGeometry`, for `ProjectiveSpace n S`.

## Implementation notes

`ℤ[n]` is `MvPolynomial n (ULift ℤ)`, Mathlib's universe device in `AffineSpace`, and its standard
grading `MvPolynomial.gradedAlgebra` is a local instance, as in `Variety/Projective.lean`.
`SpecIso` composes the base-change square of `Proj ℤ[n]` along `Spec R → Spec ℤ` with `Proj` of
the graded ring isomorphism `R ⊗[ℤ] ℤ[n] ≅ R[n]`. `twistingSheafSpecIso` is the comparison `θ` of
`Proj.mapPullbackTwistingSheafIso` for the composite `ℤ[n] → R[n]`, an isomorphism because `ℤ[n]`
is generated in degree one.

## References

* [Stacks, Section 27.13 (Tag 01ND)](https://stacks.math.columbia.edu/tag/01ND), Definition
  27.13.2 (Tag 01NF).
* [Stacks, Lemma 27.11.6 (Tag 01N2)](https://stacks.math.columbia.edu/tag/01N2).
* [Stacks, Lemma 27.11.1 (Tag 01MY)](https://stacks.math.columbia.edu/tag/01MY).

## Tags

projective space, base change, Proj, twisting sheaf, proper morphism
-/

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective space over `S` with homogeneous coordinates indexed by `n` (Stacks 01NF): the base
change `S ×_ℤ Proj ℤ[n]` of the universal projective space. -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ))))

namespace ProjectiveSpace

/-- `ℙ(n; S)` is projective space over `S` with homogeneous coordinates indexed by `n`. -/
scoped[AlgebraicGeometry] notation "ℙ(" n "; " S ")" => ProjectiveSpace n S

variable (n : Type u) (S : Scheme.{u})

/-- The structure morphism `ℙ(n; S) ⟶ S`. -/
@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from `ℙ(n; S)` to the universal projective space `Proj ℤ[n]`. -/
def toProj : ℙ(n; S) ⟶ Proj (homogeneousSubmodule n (ULift.{u} ℤ)) :=
  pullback.snd _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- For finitely many homogeneous coordinates, `ℙ(n; S)` is proper over `S`: it is a base change
of `Proj ℤ[n] → Spec ℤ`, which is `Proj.toSpecZero` for a polynomial ring of finite type over its
degree-zero part. Finiteness is load-bearing: in infinitely many variables `Proj ℤ[n]` is not of
finite type over `ℤ`. -/
instance isProper [Finite n] : IsProper (ℙ(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ <| by
  have : IsIso (CommRingCat.ofHom (homogeneousZeroRingEquiv n (ULift.{u} ℤ)).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (homogeneousZeroRingEquiv n _).bijective
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Proj.toSpecZero (homogeneousSubmodule n (ULift.{u} ℤ)) ≫
    Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv n (ULift.{u} ℤ)).toRingHom))]
  infer_instance

section functorial

variable {n}

variable (n) in
/-- `ℙ(n; S)` is functorial in `S`. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ ℙ(n; T) ↘ T = ℙ(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma map_toProj {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ toProj n T = toProj n S :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- **Base change of projective space**: `ℙ(n; S) = S ×_T ℙ(n; T)` over `S`. -/
lemma isPullback_map {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (map n f) (ℙ(n; S) ↘ S) (ℙ(n; T) ↘ T) f := by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from]
  convert! (IsPullback.of_hasPullback _ _).flip
  rw [← toProj, ← toProj, map_toProj]

end functorial

section SpecIso

variable (R : Type u) [CommRing R] [Algebra (ULift.{u} ℤ) R]

/-- `R ⊗[ℤ] ℤ[n] ≅ R[n]` respects the standard gradings. -/
private def tensorGradedHom :
    (fun i ↦ (homogeneousSubmodule n (ULift.{u} ℤ) i).baseChange R) →+*ᵍ
      homogeneousSubmodule n R where
  toRingHom := (algebraTensorAlgEquiv (σ := n) (ULift.{u} ℤ) R).toRingHom
  map_mem {i x} hx := by
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      simp only [TensorProduct.mk_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toRingEquiv, algebraTensorAlgEquiv_tmul, one_smul]
      exact ((mem_homogeneousSubmodule _ _).1 hp).map _
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      change algebraTensorAlgEquiv (σ := n) (ULift.{u} ℤ) R (r • y) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r hy

private lemma tensorGradedHom_bijective : Function.Bijective (tensorGradedHom n R) :=
  (algebraTensorAlgEquiv (σ := n) (ULift.{u} ℤ) R).bijective

end SpecIso

set_option backward.isDefEq.respectTransparency false in
/-- The base-change square of `Proj ℤ[n]` along `Spec R → Spec ℤ`, with the terminal scheme in
the corner. -/
private lemma isPullback_tensor (R : CommRingCat.{u}) [Algebra (ULift.{u} ℤ) R] :
    IsPullback
      (Proj.toSpecZero (fun i ↦ (homogeneousSubmodule n (ULift.{u} ℤ) i).baseChange R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R ((homogeneousSubmodule n (ULift.{u} ℤ) 0).baseChange R))))
      (Proj.map (GradedRingHom.includeRight R _)
        (GradedRingHom.irrelevant_baseChange_le_map R _))
      (terminal.from (Spec R))
      (terminal.from (Proj (homogeneousSubmodule n (ULift.{u} ℤ)))) :=
  (Proj.isPullback_map_baseChange R (homogeneousSubmodule n (ULift.{u} ℤ))).flip.of_iso
    (Iso.refl _) (Iso.refl (Spec R)) (Iso.refl _)
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp]; exact Category.comp_id _)
    (Category.comp_id _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- `ℙ(n; Spec R) ≅ Proj (R ⊗[ℤ] ℤ[n])`, the cone point comparison of `isPullback_tensor`. -/
private def tensorIso (R : CommRingCat.{u}) [Algebra (ULift.{u} ℤ) R] :
    ℙ(n; Spec R) ≅ Proj (fun i ↦ (homogeneousSubmodule n (ULift.{u} ℤ) i).baseChange R) :=
  (isPullback_tensor n R).isoPullback.symm

private lemma tensorIso_hom_toSpecZero (R : CommRingCat.{u}) [Algebra (ULift.{u} ℤ) R] :
    (tensorIso n R).hom ≫
      Proj.toSpecZero (fun i ↦ (homogeneousSubmodule n (ULift.{u} ℤ) i).baseChange R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R ((homogeneousSubmodule n (ULift.{u} ℤ) 0).baseChange R))) =
      ℙ(n; Spec R) ↘ Spec R :=
  (isPullback_tensor n R).isoPullback_inv_fst

/-- **`ℙ(n; Spec R) ≅ Proj R[n]`**, by base change of `Proj` (Stacks 01N2) and
`R ⊗[ℤ] ℤ[n] ≅ R[n]`. A construction, not a supplied equivalence. -/
def SpecIso (R : CommRingCat.{u}) : ℙ(n; Spec R) ≅ Proj (homogeneousSubmodule n R) :=
  letI := ULift.algebra' ℤ R
  haveI := Proj.isIso_map_of_bijective (tensorGradedHom n R)
    (GradedRingHom.irrelevant_le_map_of_bijective _ (tensorGradedHom_bijective n R))
    (tensorGradedHom_bijective n R)
  tensorIso n R ≪≫ (asIso (Proj.map (tensorGradedHom n R)
    (GradedRingHom.irrelevant_le_map_of_bijective _ (tensorGradedHom_bijective n R)))).symm

/-- `SpecIso` lies over `Spec R`, where `Proj R[n]` maps to `Spec R` through the identification
of `R` with the degree-zero part. -/
@[reassoc]
lemma SpecIso_hom_toSpecZero (R : CommRingCat.{u}) :
    (SpecIso n R).hom ≫ Proj.toSpecZero (homogeneousSubmodule n R) ≫
      Spec.map (CommRingCat.ofHom (homogeneousZeroRingEquiv n R).toRingHom) =
      ℙ(n; Spec R) ↘ Spec R := by
  let _ : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  have h₀ : CommRingCat.ofHom (homogeneousZeroRingEquiv n R).toRingHom =
      CommRingCat.ofHom (algebraMap R ((homogeneousSubmodule n (ULift.{u} ℤ) 0).baseChange R)) ≫
        CommRingCat.ofHom (tensorGradedHom n R).gradedZeroRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change C r = algebraTensorAlgEquiv (σ := n) (ULift.{u} ℤ) R (r ⊗ₜ 1)
    rw [algebraTensorAlgEquiv_tmul, map_one, smul_eq_C_mul, mul_one]
  rw [h₀, Spec.map_comp]
  simp only [SpecIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← Proj.map_toSpecZero_assoc (tensorGradedHom n R)
    (GradedRingHom.irrelevant_le_map_of_bijective _ (tensorGradedHom_bijective n R)),
    IsIso.inv_hom_id_assoc]
  exact tensorIso_hom_toSpecZero n R

/-- **Agreement with the field-level model.** Over a field, `SpecIso` identifies `ℙ(n; Spec k)`
with `projectiveSpace n k` over `Spec k`, so the field-level `Proj` model the Čech lane computes
with is reached from `ℙ(n; S)` by a proved comparison. -/
theorem SpecIso_hom_comp_projectiveSpaceToSpec (k : Type u) [Field k] :
    (SpecIso n (CommRingCat.of k)).hom ≫ projectiveSpaceToSpec n k =
      ℙ(n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k) :=
  SpecIso_hom_toSpecZero n (CommRingCat.of k)

section TwistingSheaf

/-- The variables, as elements of degree one. -/
private def variable' (R : Type u) [CommRing R] (i : n) : homogeneousSubmodule n R 1 :=
  ⟨X i, isHomogeneous_X R i⟩

/-- The twisting sheaf `𝒪(d)` on `ℙ(n; S)`: the pullback of `𝒪(d)` on `Proj ℤ[n]`, with the
convention `A(d)ₘ = A_{m + d}`. -/
def twistingSheaf (d : ℤ) : ℙ(n; S).Modules :=
  (Scheme.Modules.pullback (toProj n S)).obj
    (Proj.twistingSheaf (homogeneousSubmodule n (ULift.{u} ℤ)) d)

/-- `𝒪(d)` is invertible: it is the pullback of the invertible `𝒪(d)` on `Proj ℤ[n]`, which the
variables trivialize chart by chart. -/
instance isInvertible_twistingSheaf (d : ℤ) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules ℙ(n; S).ringCatSheaf from twistingSheaf n S d) :=
  haveI := Proj.twistingSheaf_isInvertible _ (variable' n (ULift.{u} ℤ)) d
    (polynomialVariable_adjoin_eq_top n (ULift.{u} ℤ))
  Scheme.Modules.isInvertible_pullback _ _

/-- **`𝒪(d) ⊗ 𝒪(e) ≅ 𝒪(d + e)`** on `ℙ(n; S)`: the pullback of
`Proj.twistingSheafTensorAddIso`, through the tensor comparison of a strong monoidal pullback. -/
def twistingSheafTensorIso [(Scheme.Modules.pullback (toProj n S)).Monoidal] (d e : ℤ) :
    Scheme.Modules.tensorObj (twistingSheaf n S d) (twistingSheaf n S e) ≅
      twistingSheaf n S (d + e) :=
  Scheme.Modules.pullbackTensorIso (toProj n S) _ _ ≪≫
    (Scheme.Modules.pullback (toProj n S)).mapIso
      (Proj.twistingSheafTensorAddIso _ (variable' n (ULift.{u} ℤ)) d e
        (polynomialVariable_adjoin_eq_top n (ULift.{u} ℤ)))

/-- `SpecIso` followed by the map to the universal model is `Proj` of `ℤ[n] → R ⊗ ℤ[n] → R[n]`. -/
private lemma SpecIso_inv_toProj (R : CommRingCat.{u}) :
    letI := ULift.algebra' ℤ R
    (SpecIso n R).inv ≫ toProj n (Spec R) =
      Proj.map ((tensorGradedHom n R).comp (GradedRingHom.includeRight R _))
        (HomogeneousIdeal.irrelevant_le_map_comp
          (GradedRingHom.irrelevant_baseChange_le_map R _)
          (GradedRingHom.irrelevant_le_map_of_bijective _ (tensorGradedHom_bijective n R))) := by
  let _ : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  rw [Proj.map_comp (GradedRingHom.includeRight R _) (tensorGradedHom n R)
    (GradedRingHom.irrelevant_baseChange_le_map R _)
    (GradedRingHom.irrelevant_le_map_of_bijective _ (tensorGradedHom_bijective n R))]
  simp only [SpecIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc]
  congr 1
  exact (isPullback_tensor n R).isoPullback_hom_snd

/-- **`𝒪(d)` on `ℙ(n; Spec R)` is `𝒪(d)` on `Proj R[n]`** under `SpecIso`: the comparison `θ` of
`Proj.mapPullbackTwistingSheafIso` for `ℤ[n] → R[n]`, which is an isomorphism because `ℤ[n]` is
generated by its variables in degree one. -/
def twistingSheafSpecIso (R : CommRingCat.{u}) (d : ℤ) :
    (Scheme.Modules.pullback (SpecIso n R).inv).obj (twistingSheaf n (Spec R) d) ≅
      Proj.twistingSheaf (homogeneousSubmodule n R) d :=
  letI := ULift.algebra' ℤ R
  (Scheme.Modules.pullbackComp (SpecIso n R).inv (toProj n (Spec R))).app _ ≪≫
    (Scheme.Modules.pullbackCongr (SpecIso_inv_toProj n R)).app _ ≪≫
      Proj.mapPullbackTwistingSheafIso _ _ (variable' n (ULift.{u} ℤ))
        (polynomialVariable_adjoin_eq_top n (ULift.{u} ℤ)) d

end TwistingSheaf

end ProjectiveSpace

end AlgebraicGeometry
