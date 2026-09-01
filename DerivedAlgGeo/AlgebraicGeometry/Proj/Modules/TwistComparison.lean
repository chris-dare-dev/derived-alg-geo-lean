/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistMultiplication
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TensorTwist
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistAdd
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CoversTop

/-!
# The comparison `F ⊗ O(d) ≅ F(d)`, and what follows from it

`#584`'s remaining structural piece. `TwistMultiplication.lean` built the map
`M̃ ⊗ A(d)~ ⟶ M(d)~` and showed what it looks like on a degree-one chart; this file shows the map
is inverted by sheafification, and reads off the two deliverables that were waiting on it —
`F(d)(e) ≅ F(d + e)` and preservation of coherence.

## The route, and why it is not `Divisors/AssociatedSheaf/Construction.lean`'s

That file proves the corresponding Cartier statement by exhibiting a generator of the tensor on a
chart and finishing by 2-out-of-3. **The generator route is unavailable here**: it works because
*both* Cartier factors are invertible, so the unit generates the tensor. Only `O(d)` is invertible
here and `F` is arbitrary.

What replaces it is stronger and shorter. Over an open inside a degree-one chart the twisted
multiplication is not merely a local weak equivalence — it is already **bijective on sections**,
because `A(d)` is there the structure sheaf and the map is the scalar action. So the local input to
`Presheaf.W_of_coversTop` is an isomorphism of presheaves, and no local injectivity or surjectivity
has to be proved by hand at all.

Concretely `twistMultiplicationHom_app_eq` factors the map on sections as

    M̃(U) ⊗ A(d)~(U) --(1 ⊗ ψ)--> M̃(U) ⊗ 𝒪(U) --rid--> M̃(U) --φ⁻¹--> M(d)~(U)

with `ψ` and `φ` the two chart trivializations. The content of that factorization is one identity,
`chartModuleTwistSectionEquiv_sectionTwistMul`, and it is four lines on top of
`intShiftZeroModuleLinearEquiv_twistMul`: both trivializations are multiplication by the same
scalar, so what is left is associativity of that action.

## Deliverables

* `tensorTwistIso` — the comparison, and `associatedTensorTwistIso` in `tensorTwist` spelling
  (2a);
* `tensorTwistAddIso` / `associatedTensorTwistAddIso` — `F(d)(e) ≅ F(d + e)` (2b). With the
  comparison this is `sheafTwistAddIso` and needs no associator; `TensorTwist.lean` records why
  the monoidal structure cannot deliver it directly;
* `tensorObj_twistingSheaf_isCoherent` / `tensorTwist_isCoherent` — coherence preservation (3),
  through the graded side, where `intShiftModuleOverSelfIso` trivializes the twist on a chart.
  It is not visible through the tensor, which is why it waited on the comparison.

## Scope

`F` is an **associated sheaf**. That is the honest statement: identifying an arbitrary coherent
sheaf on `Proj` with an associated one is Serre's theorem, which is downstream —
`TwistInvertible.lean` records the same boundary, and it is why `O(d)` was proved invertible
rather than the tensor avoided.

## Two things the section level needs that the fibre level did not

`sectionLinearEquivOfMemIff` is the section-level counterpart of
`DegreeZeroLocalization.linearEquivOfMemIff`: `intShift 𝓜 0` and `𝓜` have the same members, so the
underlying element never moves and only the local-fraction certificate is rebuilt. Both chart
trivializations land at the `(0)`-twist rather than at the module, so this is what closes the gap;
`Finiteness.lean` needs the same step at the sheaf level and gets it from
`associatedIsoOfPiecewiseIff`.

The monoidal structure is `TwistMultiplication.lean`'s local instance, re-enabled here with
`attribute [local instance]` rather than redeclared — a second instance over the same spelling is
the mistake `references/instance-transparency.md` names.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace MonoidalCategory

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

section General

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- Sections of `M̃` depend only on the membership predicates of the graded pieces. -/
noncomputable def sectionLinearEquivOfMemIff {σN : Type u} [SetLike σN M]
    [AddSubgroupClass σN M] (𝓝 : ℕ → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) (U : Opens X) :
    (associatedSheafInType 𝒜 𝓜).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 𝓝).1.obj (op U) where
  toFun s := ⟨fun x => DegreeZeroLocalization.linearEquivOfMemIff 𝓝 hmem (s.1 x), by
    intro x
    obtain ⟨V, hxV, j, e, r, u, hu, h⟩ := s.2 x
    refine ⟨V, hxV, j, e, ⟨(r : M), (hmem e (r : M)).mp r.2⟩, u, hu, fun y => ?_⟩
    have hy := h y
    change s.1 (j y) = _ at hy
    show DegreeZeroLocalization.linearEquivOfMemIff 𝓝 hmem (s.1 (j y)) = _
    rw [hy]
    apply DegreeZeroLocalization.ext
    rfl⟩
  invFun s := ⟨fun x => (DegreeZeroLocalization.linearEquivOfMemIff 𝓝 hmem).symm (s.1 x), by
    intro x
    obtain ⟨V, hxV, j, e, r, u, hu, h⟩ := s.2 x
    refine ⟨V, hxV, j, e, ⟨(r : M), (hmem e (r : M)).mpr r.2⟩, u, hu, fun y => ?_⟩
    have hy := h y
    change s.1 (j y) = _ at hy
    show (DegreeZeroLocalization.linearEquivOfMemIff 𝓝 hmem).symm (s.1 (j y)) = _
    rw [hy]
    apply DegreeZeroLocalization.ext
    rfl⟩
  left_inv s := by
    apply section_ext
    funext x
    rfl
  right_inv s := by
    apply section_ext
    funext x
    rfl
  map_add' s t := by
    apply section_ext
    funext x
    rfl
  map_smul' r s := by
    apply section_ext
    funext x
    rfl

/-- At the zero twist the twisted multiplication is the scalar action. -/
theorem twistMul_zero_eq_smul (S : Submonoid A)
    (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 0) S) (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    DegreeZeroLocalization.linearEquivOfMemIff 𝓜 (mem_intShift_zero_iff 𝓜)
        (twistMul 𝒜 𝓜 S 0 w z) =
      (DegreeZeroLocalization.selfLinearEquiv 𝒜 S).symm
        (DegreeZeroLocalization.linearEquivOfMemIff 𝒜 (mem_intShift_zero_iff 𝒜) w) • z := by
  apply DegreeZeroLocalization.ext
  show (w : LocalizedModule S A) • (z : LocalizedModule S M) =
    algebraMap (HomogeneousLocalization 𝒜 S) (Localization S)
      ((DegreeZeroLocalization.selfLinearEquiv 𝒜 S).symm
        (DegreeZeroLocalization.linearEquivOfMemIff 𝒜 (mem_intShift_zero_iff 𝒜) w)) •
      (z : LocalizedModule S M)
  congr 1
  rw [HomogeneousLocalization.algebraMap_apply,
    ← DegreeZeroLocalization.coe_selfLinearEquiv 𝒜 S
      ((DegreeZeroLocalization.selfLinearEquiv 𝒜 S).symm
        (DegreeZeroLocalization.linearEquivOfMemIff 𝒜 (mem_intShift_zero_iff 𝒜) w)),
    LinearEquiv.apply_symm_apply]
  rfl

/-- Over a degree-one chart, `A(d)` is the structure sheaf, on sections. -/
noncomputable def chartRingTwistSectionEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      𝒪.1.obj (op U) :=
  intShiftSectionLinearEquivOn 𝒜 hf d hU ≪≫ₗ
    sectionLinearEquivOfMemIff 𝒜 (intShift 𝒜 0) 𝒜 (mem_intShift_zero_iff 𝒜) U ≪≫ₗ
    selfSectionLinearEquiv 𝒜 (op U)

/-- Over a degree-one chart, `M(d)` is `M̃`, on sections. -/
noncomputable def chartModuleTwistSectionEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 𝓜).1.obj (op U) :=
  intShiftModuleSectionLinearEquivOn 𝒜 𝓜 hf d hU ≪≫ₗ
    sectionLinearEquivOfMemIff 𝒜 (intShift 𝓜 0) 𝓜 (mem_intShift_zero_iff 𝓜) U

/-- **Over a degree-one chart the twisted multiplication is the scalar action**, conjugated by
the two chart trivializations. -/
theorem chartModuleTwistSectionEquiv_sectionTwistMul {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    chartModuleTwistSectionEquiv 𝒜 𝓜 hf d hU (sectionTwistMul 𝒜 𝓜 d s t) =
      chartRingTwistSectionEquiv 𝒜 hf d hU t • s := by
  apply section_ext
  funext x
  show DegreeZeroLocalization.linearEquivOfMemIff 𝓜 (mem_intShift_zero_iff 𝓜)
      (DegreeZeroLocalization.intShiftZeroModuleLinearEquiv 𝒜 𝓜 hf d (hU x.2)
        (twistMul 𝒜 𝓜 _ d (t.1 x) (s.1 x))) = _
  rw [intShiftZeroModuleLinearEquiv_twistMul, twistMul_zero_eq_smul]
  rfl

attribute [local instance] monoidalCategoryAssociatedPresheaf

/-- Over a degree-one chart, the tensor of sections is the twisted sections. -/
noncomputable def chartTensorEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    TensorProduct (𝒪.1.obj (op U))
        ((associatedSheafInType 𝒜 𝓜).1.obj (op U))
        ((associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) :=
  TensorProduct.congr (LinearEquiv.refl _ _) (chartRingTwistSectionEquiv 𝒜 hf d hU) ≪≫ₗ
    TensorProduct.rid _ _ ≪≫ₗ (chartModuleTwistSectionEquiv 𝒜 𝓜 hf d hU).symm

theorem twistMultiplicationHom_app_eq {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (twistMultiplicationHom 𝒜 𝓜 d).app (op U) =
      (chartTensorEquiv 𝒜 𝓜 hf d hU).toModuleIso.hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  show sectionTwistMul 𝒜 𝓜 d m n =
    (chartModuleTwistSectionEquiv 𝒜 𝓜 hf d hU).symm
      (chartRingTwistSectionEquiv 𝒜 hf d hU n • m)
  rw [LinearEquiv.eq_symm_apply]
  exact chartModuleTwistSectionEquiv_sectionTwistMul 𝒜 𝓜 hf d hU m n

/-- Over a degree-one chart the twisted multiplication is already an isomorphism on sections. -/
theorem isIso_twistMultiplicationHom_app {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    IsIso ((twistMultiplicationHom 𝒜 𝓜 d).app (op U)) := by
  rw [twistMultiplicationHom_app_eq 𝒜 𝓜 hf d hU]
  infer_instance

theorem isIso_toPresheaf_map_twistMultiplicationHom_app {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    IsIso (((PresheafOfModules.toPresheaf _).map (twistMultiplicationHom 𝒜 𝓜 d)).app (op U)) := by
  haveI hiso := isIso_twistMultiplicationHom_app 𝒜 𝓜 hf d hU
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (ConcreteCategory.isIso_iff_bijective
    ((twistMultiplicationHom 𝒜 𝓜 d).app (op U))).mp hiso

/-- **The twisted multiplication is a local weak equivalence** as soon as degree-one elements
generate `A` over `𝒜 0`. -/
theorem twistMultiplicationHom_mem_W {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜)).W
      ((PresheafOfModules.toPresheaf _).map (twistMultiplicationHom 𝒜 𝓜 d)) := by
  refine Presheaf.W_of_coversTop _
    (fun i : I => (standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)
    (degreeOneCharts_coversTop 𝒜 g hg) (fun i => ?_)
  haveI : ∀ W, IsIso ((Functor.whiskerLeft
      (Over.forget ((standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)).op
      ((PresheafOfModules.toPresheaf _).map (twistMultiplicationHom 𝒜 𝓜 d))).app W) :=
    fun W => isIso_toPresheaf_map_twistMultiplicationHom_app 𝒜 𝓜 (g i).2 d
      ((leOfHom W.unop.hom).trans (standardAway_degreeOne_opensRange_le 𝒜 (g i)))
  haveI : IsIso (Functor.whiskerLeft
      (Over.forget ((standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)).op
      ((PresheafOfModules.toPresheaf _).map (twistMultiplicationHom 𝒜 𝓜 d))) :=
    NatIso.isIso_of_isIso_app _
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

theorem isIso_sheafification_map_twistMultiplicationHom {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    IsIso ((PresheafOfModules.sheafification
        (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).map
      (twistMultiplicationHom 𝒜 𝓜 d)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj))
    ((Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜)).W.inverseImage
      (PresheafOfModules.toPresheaf (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj))
  exact twistMultiplicationHom_mem_W 𝒜 𝓜 g d hg

/-- **The comparison `M̃ ⊗ O(d) ≅ M(d)~`.** -/
noncomputable def tensorTwistIso {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    AlgebraicGeometry.Scheme.Modules.tensorObj (associatedSheaf 𝒜 𝓜) (twistingSheaf 𝒜 d) ≅
      sheafTwist 𝒜 𝓜 d :=
  (@asIso _ _ _ _
      ((PresheafOfModules.sheafification
        (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).map (twistMultiplicationHom 𝒜 𝓜 d))
      (isIso_sheafification_map_twistMultiplicationHom 𝒜 𝓜 g d hg)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).counit).app (sheafTwist 𝒜 𝓜 d)

/-- **`F(d)(e) ≅ F(d + e)`** for `F` an associated sheaf, deliverable 2b of `#584`. -/
noncomputable def tensorTwistAddIso {I : Type u} (g : I → 𝒜 1) (d e : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorObj (associatedSheaf 𝒜 𝓜)
          (twistingSheaf 𝒜 d))
        (twistingSheaf 𝒜 e) ≅
      AlgebraicGeometry.Scheme.Modules.tensorObj (associatedSheaf 𝒜 𝓜)
        (twistingSheaf 𝒜 (d + e)) :=
  AlgebraicGeometry.Scheme.Modules.tensorObjIso
      (tensorTwistIso 𝒜 𝓜 g d hg) (Iso.refl _) ≪≫
    tensorTwistIso 𝒜 (intShift 𝓜 d) g e hg ≪≫
    sheafTwistAddIso 𝒜 𝓜 d e ≪≫
    (tensorTwistIso 𝒜 𝓜 g (d + e) hg).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **An integer twist of a coherent associated sheaf is coherent.** -/
theorem intShiftModule_isCoherent {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)
    (hM : AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝓜)) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 (intShift 𝓜 d)) := by
  apply SheafOfModules.IsFinitePresentation.of_coversTop
    (associatedSheaf 𝒜 (intShift 𝓜 d))
    (fun i => (standardAway 𝒜 (degreeOneStandardChart 𝒜 (g i))).opensRange)
    (degreeOneCharts_coversTop 𝒜 g hg)
  intro i
  exact SheafOfModules.IsFinitePresentation.of_iso.{u}
    (intShiftModuleOverSelfIso 𝒜 𝓜 (g i).2 d
      (standardAway_degreeOne_opensRange_le 𝒜 (g i))).symm
    (SheafOfModules.IsFinitePresentation.over hM _)

/-- **The twist of a coherent associated sheaf is coherent**, deliverable 3 of `#584`. -/
theorem tensorObj_twistingSheaf_isCoherent {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)
    (hM : AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝓜)) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent (AlgebraicGeometry.Proj 𝒜)
      (AlgebraicGeometry.Scheme.Modules.tensorObj (associatedSheaf 𝒜 𝓜)
        (twistingSheaf 𝒜 d)) :=
  SheafOfModules.IsFinitePresentation.of_iso.{u}
    (tensorTwistIso 𝒜 𝓜 g d hg).symm (intShiftModule_isCoherent 𝒜 𝓜 g d hg hM)

/-! ## The `tensorTwist` spelling

The same three results in the names `#584` uses. `tensorTwist F d` is by definition
`tensorObj F (twistingSheaf 𝒜 d)`, so each is its counterpart above under a different name and in
the same graded setting — they are kept only because `#584`'s deliverables are stated in the
`tensorTwist` spelling.

Both spellings live in the general graded setting. `Modules/Tensor/Basic.lean`'s machinery needs a
locally free rank-one factor, which `TwistInvertible.lean` supplies for `O(d)`; it does not need
`A` to be an algebra over a base ring, and nothing in the twist API uses such a structure. -/

/-- **`F ⊗ O(d) ≅ F(d)` for `F = M̃`**, deliverable 2a of `#584`. -/
noncomputable def associatedTensorTwistIso {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    tensorTwist 𝒜 (associatedSheaf 𝒜 𝓜) d ≅ sheafTwist 𝒜 𝓜 d :=
  tensorTwistIso 𝒜 𝓜 g d hg

/-- **`F(d)(e) ≅ F(d + e)` for `F = M̃`**, deliverable 2b of `#584`. -/
noncomputable def associatedTensorTwistAddIso {I : Type u} (g : I → 𝒜 1) (d e : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    tensorTwist 𝒜 (tensorTwist 𝒜 (associatedSheaf 𝒜 𝓜) d) e ≅
      tensorTwist 𝒜 (associatedSheaf 𝒜 𝓜) (d + e) :=
  tensorTwistAddIso 𝒜 𝓜 g d e hg

/-- **The twist preserves coherence**, deliverable 3 of `#584`. -/
theorem tensorTwist_isCoherent {I : Type u} (g : I → 𝒜 1) (d : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)
    (hM : AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝓜)) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent (AlgebraicGeometry.Proj 𝒜)
      (tensorTwist 𝒜 (associatedSheaf 𝒜 𝓜) d) :=
  tensorObj_twistingSheaf_isCoherent 𝒜 𝓜 g d hg hM

/-- **`O(d) ⊗ O(e) ≅ O(d + e)`, on the tensor side.**

`twistingSheafAddIso` is the graded-shift form, `sheafTwist 𝒜 (intShift 𝒜 d) e ≅ O(d + e)`. This is
the same statement written through `tensorObj`, which is the form `#806` needs in order to hand
`O(-N)` to `IsInvertible` as a tensor inverse of `O(N)`.

It is four lines because the graded ring as a module over itself is the unit: recognise each
`O(·)` as `(Ã)(·)` with `associatedSelfTensorTwistIso`, apply the comparison at `𝓜 = 𝒜`, and
recognise the result back.

Both factors are `O(·)` rather than an arbitrary `F`, so this does not contradict what
`TensorTwist.lean` records about `F(d)(e) ≅ F(d + e)`: there the obstruction is a non-invertible
outer factor, and here there is none. -/
noncomputable def twistingSheafTensorAddIso {I : Type u} (g : I → 𝒜 1) (d e : ℤ)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤) :
    AlgebraicGeometry.Scheme.Modules.tensorObj (twistingSheaf 𝒜 d) (twistingSheaf 𝒜 e) ≅
      twistingSheaf 𝒜 (d + e) :=
  AlgebraicGeometry.Scheme.Modules.tensorObjIso
      (associatedSelfTensorTwistIso 𝒜 d).symm (Iso.refl _) ≪≫
    tensorTwistAddIso 𝒜 𝒜 g d e hg ≪≫ associatedSelfTensorTwistIso 𝒜 (d + e)

end General

end AlgebraicGeometry.Proj
