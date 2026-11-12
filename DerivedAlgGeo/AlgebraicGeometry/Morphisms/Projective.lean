/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.RelativelyAmple
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.FracSection
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.StructureModule
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistChart
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInvertible

/-!
# H-projective and locally projective morphisms

A morphism `f : X ⟶ S` is H-projective (Stacks 01W8) when it factors as a closed immersion into
projective space `ℙ(n; S)` over `S`, for a finite type `n` of homogeneous coordinates, followed by
the structure morphism. It is locally projective (Stacks 01WB) when it is H-projective over the
members of an open cover of `S`.

## Main definitions

* `AlgebraicGeometry.IsHProjective f`: `f` is H-projective.
* `AlgebraicGeometry.IsLocallyProjective f`: `f` is locally H-projective on the base.

## Main results

* `AlgebraicGeometry.IsHProjective.isProper`, `AlgebraicGeometry.IsLocallyProjective.isProper`:
  H-projective and locally projective morphisms are proper (Stacks 01W9, 01WC).
* `AlgebraicGeometry.IsHProjective.isStableUnderBaseChange`,
  `AlgebraicGeometry.IsLocallyProjective.isStableUnderBaseChange`: both notions are stable under
  base change (Stacks 01WF, 02V6).
* `AlgebraicGeometry.IsHProjective.isLocallyProjective`: H-projective morphisms are locally
  projective.
* `AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_twistingSheaf_one`: `𝒪(1)` on `ℙ(n; S)` is
  relatively ample over `S`, and so is its restriction along any closed immersion
  (`AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_pullback_twistingSheaf_one`).
* `AlgebraicGeometry.Variety.isProjective_iff_isHProjective`: over a field, `Variety.IsProjective`
  is H-projectivity of the structure morphism, so there is one notion.
* `AlgebraicGeometry.Proj.nonvanishingLocus_sectionOfMem_one`: on `Proj 𝒜` generated in degree
  one, a degree-one `f`, as a section `f / 1` of `𝒪(1)`, vanishes nowhere exactly on `D₊(f)`.

## Notation

`X` and `𝒪` are local notation for `ProjectiveSpectrum.top 𝒜` and its structure sheaf in the
section on `Proj`.

## Implementation notes

`IsHProjective` is a proposition in Mathlib's morphism-property style. It quantifies the embedding
existentially and carries no presentation data, as `Variety.IsProjective` separates itself from
`ProjectivePresentation`. Stacks' projective morphisms (closed subschemes of `P(E)`) are a
different notion and are not defined here.

`𝒪(1)` on `ℙ(n; S)` is the pullback of `𝒪(1)` on `Proj ℤ[n]`. Over an affine `V ⊆ S` the pulled-back
variables `X_i` are sections whose non-vanishing loci are the affine `V ×_ℤ D₊(X_i)`, by `0H78` and
the computation `X_{X_i} = D₊(X_i)` on `Proj`.

## References

* [Stacks, Section 29.43 (Tag 01W7)](https://stacks.math.columbia.edu/tag/01W7).
* [Stacks, Lemma 27.13.4 (Tag 01NH)](https://stacks.math.columbia.edu/tag/01NH).

## Tags

projective morphism, H-projective, locally projective, proper morphism, twisting sheaf
-/

universe u

open CategoryTheory Limits

/-! ## The twisting sheaf on `Proj` -/

namespace AlgebraicGeometry.Proj

open Opposite TopologicalSpace GradedModule

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- Dividing by a degree-one element `g`, at a point of `D₊(g)`: the fiber of `A(1)~` there is
free of rank one over the homogeneous localization. -/
private noncomputable def twistOneFiberEquiv {g : A} (hg : g ∈ 𝒜 1) {x : ProjectiveSpectrum 𝒜}
    (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 g) :
    Fiber 𝒜 (intShift 𝒜 ((1 : ℕ) : ℤ)) x ≃ₗ[
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
  (intShiftFiberLinearEquivOfMem 𝒜 hg _ hx).trans
    ((DegreeZeroLocalization.linearEquivOfMemIff (𝒜 := 𝒜) (𝓜 := intShift 𝒜 0) 𝒜
      (mem_intShift_zero_iff 𝒜)).trans (selfFiberLinearEquiv 𝒜 x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem twistOneFiberEquiv_sectionOfMem {g : A} (hg : g ∈ 𝒜 1) (U : Opens X) (x : U)
    (hx : x.1 ∈ ProjectiveSpectrum.basicOpen 𝒜 g) :
    twistOneFiberEquiv 𝒜 hg hx ((sectionOfMem 𝒜 𝒜 U 1 hg).1 x) = 1 := by
  rw [sectionOfMem_apply]
  simp only [twistOneFiberEquiv, LinearEquiv.trans_apply, intShiftFiberLinearEquivOfMem,
    DegreeZeroLocalization.intShiftZeroLinearEquiv_apply_mk,
    DegreeZeroLocalization.linearEquivOfMemIff_mk, selfFiberLinearEquiv_apply_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- The coefficient of a section of `A(1)~` against `g / 1`, over an open inside `D₊(g)`. -/
private noncomputable def twistOneCoeff {g : A} (hg : g ∈ 𝒜 1) {V : Opens X}
    (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒜 g)
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 ((1 : ℕ) : ℤ))).1.obj (op V)) : 𝒪.1.obj (op V) :=
  selfSectionToStructure 𝒜 (sectionAddEquivOfMemIff 𝒜 (intShift 𝒜 0) 𝒜
    (mem_intShift_zero_iff 𝒜) V (intShiftSectionToZeroOn 𝒜 hg _ hV t))

/-- **`g / 1` freely generates `𝒪(1)` over every open inside `D₊(g)`**, for `g` of degree one. -/
theorem isLocalBasis_sectionOfMem_one {g : A} (hg : g ∈ 𝒜 1) {W : (Proj 𝒜).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    Scheme.Modules.IsLocalBasis (twistingSheaf 𝒜 1) W (sectionOfMem 𝒜 𝒜 W 1 hg) := by
  intro V hVW
  have hV : V ≤ ProjectiveSpectrum.basicOpen 𝒜 g := hVW.trans hW
  have hres : (twistingSheaf 𝒜 1).presheaf.map (homOfLE hVW).op
      (sectionOfMem 𝒜 𝒜 W 1 hg) = sectionOfMem 𝒜 𝒜 V 1 hg :=
    res_sectionOfMem 𝒜 𝒜 hVW 1 hg
  rw [hres]
  have key : ∀ (a : Γ(Proj 𝒜, V)) (x : V),
      twistOneFiberEquiv 𝒜 hg (hV x.2)
        ((show (associatedSheafInType 𝒜 (intShift 𝒜 ((1 : ℕ) : ℤ))).1.obj (op V) from
          a • (show Γ(twistingSheaf 𝒜 1, V) from sectionOfMem 𝒜 𝒜 V 1 hg)).1 x) =
        (show 𝒪.1.obj (op V) from a).1 x := by
    intro a x
    change twistOneFiberEquiv 𝒜 hg (hV x.2)
      ((show 𝒪.1.obj (op V) from a).1 x • (sectionOfMem 𝒜 𝒜 V 1 hg).1 x) = _
    rw [LinearEquiv.map_smul]
    exact (congrArg _ (twistOneFiberEquiv_sectionOfMem 𝒜 hg V x (hV x.2))).trans (mul_one _)
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun t => ⟨twistOneCoeff 𝒜 hg hV t, ?_⟩⟩
  · have ha' : a • (show Γ(twistingSheaf 𝒜 1, V) from sectionOfMem 𝒜 𝒜 V 1 hg) = 0 :=
      ha
    apply Subtype.ext
    funext x
    rw [← key a x, ha']
    exact map_zero _
  · change (show Γ(Proj 𝒜, V) from twistOneCoeff 𝒜 hg hV t) •
      (show Γ(twistingSheaf 𝒜 1, V) from sectionOfMem 𝒜 𝒜 V 1 hg) = t
    apply section_ext
    funext x
    apply (twistOneFiberEquiv 𝒜 hg (hV x.2)).injective
    exact (key (twistOneCoeff 𝒜 hg hV t) x).trans rfl

/-- The fraction `a / b` is a unit at a point of `D₊(b)` exactly when the point lies in
`D₊(a)`. -/
theorem isUnit_frac_iff {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 b) :
    IsUnit (frac 𝒜 ha hb hx) ↔ x ∈ ProjectiveSpectrum.basicOpen 𝒜 a := by
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, frac, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff
      (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) x.asHomogeneousIdeal.toIdeal]
  rfl

/-- A function on `Proj` is invertible at a point exactly when its value in the homogeneous
localization there is. -/
theorem isUnit_germ_iff {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) {x : Proj 𝒜} (hx : x ∈ U) :
    IsUnit ((Proj 𝒜).presheaf.germ U x hx s) ↔
      IsUnit ((show 𝒪.1.obj (op U) from s).1 ⟨x, hx⟩) := by
  rw [← stalkIso'_germ 𝒜 U x hx s]
  exact (isUnit_map_iff (stalkIso' 𝒜 x) _).symm

/-- **The basic open of the function `a / b`** on an open inside `D₊(b)` is its meet with
`D₊(a)`. -/
theorem basicOpen_fracSection {a b : A} {k : ℕ} (ha : a ∈ 𝒜 k) (hb : b ∈ 𝒜 k)
    {U : (Proj 𝒜).Opens} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 b) :
    (Proj 𝒜).basicOpen (show Γ(Proj 𝒜, U) from fracSection 𝒜 ha hb hU) =
      U ⊓ ProjectiveSpectrum.basicOpen 𝒜 a := by
  refine le_antisymm (fun x hx => ?_) (fun x ⟨hxU, hxa⟩ => ?_)
  · obtain ⟨hxU, hunit⟩ := (Scheme.mem_basicOpen'' (Proj 𝒜) _ x).1 hx
    exact ⟨hxU, (isUnit_frac_iff 𝒜 ha hb (hU hxU)).1 ((isUnit_germ_iff 𝒜 _ hxU).1 hunit)⟩
  · exact (Scheme.mem_basicOpen'' (Proj 𝒜) _ x).2
      ⟨hxU, (isUnit_germ_iff 𝒜 _ hxU).2 ((isUnit_frac_iff 𝒜 ha hb (hU hxU)).2 hxa)⟩

/-- On an open inside `D₊(g)`, for `f` and `g` of degree one, the section `f / 1` of `𝒪(1)` is
nonvanishing exactly on `D₊(f)`. -/
theorem nonvanishingLocus_sectionOfMem_one_of_le
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from twistingSheaf 𝒜 1)]
    {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) {W : (Proj 𝒜).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1)
        (sectionOfMem 𝒜 𝒜 W 1 hf) = W ⊓ ProjectiveSpectrum.basicOpen 𝒜 f := by
  have h1 : Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1)
      ((show Γ(Proj 𝒜, W) from fracSection 𝒜 hf hg hW) •
        (show Γ(twistingSheaf 𝒜 1, W) from sectionOfMem 𝒜 𝒜 W 1 hg)) =
      Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1)
        (sectionOfMem 𝒜 𝒜 W 1 hf) :=
    congrArg _ (fracSection_smul_sectionOfMem 𝒜 hf hg hW)
  rw [← h1, Scheme.Modules.nonvanishingLocus_smul]
  rw [(isLocalBasis_sectionOfMem_one 𝒜 hg hW).nonvanishingLocus_eq, basicOpen_fracSection]
  exact inf_of_le_left inf_le_left

/-- **The non-vanishing locus of `f / 1` on an open `U`**: for `f` of degree one in a graded ring
generated in degree one, the section `f / 1` of `𝒪(1)` over `U` vanishes nowhere exactly on
`U ⊓ D₊(f)`. -/
theorem nonvanishingLocus_sectionOfMem_one_inf {I : Type*} (g : I → 𝒜 1)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from twistingSheaf 𝒜 1)]
    (U : (Proj 𝒜).Opens) {f : A} (hf : f ∈ 𝒜 1) :
    Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1) (sectionOfMem 𝒜 𝒜 U 1 hf) =
      U ⊓ ProjectiveSpectrum.basicOpen 𝒜 f := by
  have hloc : ∀ i, Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1)
        (sectionOfMem 𝒜 𝒜 U 1 hf) ⊓ (U ⊓ ProjectiveSpectrum.basicOpen 𝒜 (g i : A)) =
      U ⊓ ProjectiveSpectrum.basicOpen 𝒜 (g i : A) ⊓ ProjectiveSpectrum.basicOpen 𝒜 f := by
    intro i
    have hres : (twistingSheaf 𝒜 1).presheaf.map
        (homOfLE (inf_le_left : U ⊓ ProjectiveSpectrum.basicOpen 𝒜 (g i : A) ≤ U)).op
        (sectionOfMem 𝒜 𝒜 U 1 hf) =
          sectionOfMem 𝒜 𝒜 (U ⊓ ProjectiveSpectrum.basicOpen 𝒜 (g i : A)) 1 hf :=
      res_sectionOfMem 𝒜 𝒜 inf_le_left 1 hf
    exact (Scheme.Modules.nonvanishingLocus_res inf_le_left _).symm.trans
      ((congrArg _ hres).trans (nonvanishingLocus_sectionOfMem_one_of_le 𝒜 hf (g i).2 inf_le_right))
  have hcov : ∀ x : Proj 𝒜, ∃ i, x ∈ ProjectiveSpectrum.basicOpen 𝒜 (g i : A) := by
    intro x
    have hx : x ∈ ⨆ i, Proj.basicOpen 𝒜 (g i : A) := by
      rw [Proj.iSup_basicOpen_eq_top' 𝒜 (fun j => (g j : A)) (fun j => ⟨1, (g j).2⟩) hg]
      trivial
    exact Opens.mem_iSup.1 hx
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨i, hi⟩ := hcov x
    have hxU := Scheme.Modules.nonvanishingLocus_le _ hx
    exact ⟨hxU, ((hloc i).le ⟨hx, hxU, hi⟩).2⟩
  · obtain ⟨i, hi⟩ := hcov x
    exact ((hloc i).ge ⟨⟨hx.1, hi⟩, hx.2⟩).1

/-- **The non-vanishing locus of the global section `f / 1` of `𝒪(1)` is `D₊(f)`**, for `f` of
degree one in a graded ring generated in degree one. -/
theorem nonvanishingLocus_sectionOfMem_one {I : Type*} (g : I → 𝒜 1)
    (hg : Algebra.adjoin (𝒜 0) (Set.range fun j => (g j : A)) = ⊤)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from twistingSheaf 𝒜 1)]
    {f : A} (hf : f ∈ 𝒜 1) :
    Scheme.Modules.nonvanishingLocus (twistingSheaf 𝒜 1) (sectionOfMem 𝒜 𝒜 ⊤ 1 hf) =
      ProjectiveSpectrum.basicOpen 𝒜 f :=
  (nonvanishingLocus_sectionOfMem_one_inf 𝒜 g hg ⊤ hf).trans (top_inf_eq _)

/- Usage check: the invertibility instance is the one `twistingSheaf_isInvertible` provides. -/

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry

/-- **H-projective morphism** (Stacks 01W8): `f` factors as a closed immersion into `ℙ(n; S)`,
for a finite type `n` of homogeneous coordinates, followed by the structure morphism. -/
@[mk_iff]
class IsHProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  exists_closedImmersion : ∃ (n : Type u) (_ : Finite n) (i : X ⟶ ℙ(n; S)),
    IsClosedImmersion i ∧ i ≫ ℙ(n; S) ↘ S = f

/-- **Locally projective morphism** (Stacks 01W8, 01WB): `f` is H-projective over every member of
an open cover of the base. -/
@[mk_iff]
class IsLocallyProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  exists_cover : ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ i, IsHProjective (f ∣_ (𝒰.f i).opensRange)

namespace IsHProjective

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **An H-projective morphism is proper** (Stacks 01W9, 01NH): a closed immersion followed by the
proper `ℙ(n; S) ⟶ S`. -/
instance (priority := 900) isProper [IsHProjective f] : IsProper f := by
  obtain ⟨n, hn, i, hi, rfl⟩ := IsHProjective.exists_closedImmersion (f := f)
  infer_instance

/-- **H-projectivity is stable under base change** (Stacks 01WF): `ℙ(n; S')` is the base change of
`ℙ(n; S)`, and closed immersions are stable under base change. -/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsHProjective where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    obtain ⟨n, hn, i, hi, hig⟩ := hg.exists_closedImmersion
    let t := ProjectiveSpace.isPullback_map (n := n) f
    let j : Y' ⟶ ℙ(n; X) := t.lift (f' ≫ i) g' (by rw [Category.assoc, hig, sq.w])
    have hj : IsPullback f' j i (ProjectiveSpace.map n f) :=
      .of_bot (by rwa [t.lift_snd, hig]) (t.lift_fst _ _ _).symm t
    exact ⟨n, hn, j, MorphismProperty.of_isPullback hj hi, t.lift_snd _ _ _⟩

/-- H-projectivity restricts to every open of the base. -/
instance morphismRestrict [IsHProjective f] (U : S.Opens) : IsHProjective (f ∣_ U) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹_›

/-- **H-projective morphisms are locally projective.** -/
instance (priority := 900) isLocallyProjective [IsHProjective f] : IsLocallyProjective f :=
  ⟨S.affineCover, fun _ ↦ inferInstance⟩

end IsHProjective

/-- **A locally projective morphism is proper** (Stacks 01WC): properness is local on the base. -/
instance (priority := 900) IsLocallyProjective.isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyProjective f] : IsProper f := by
  obtain ⟨𝒰, h⟩ := IsLocallyProjective.exists_cover (f := f)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top _ 𝒰.iSup_opensRange fun i ↦ inferInstance

/-- Restricting a pullback square over an open of the base gives a pullback square. -/
private lemma isPullback_morphismRestrict_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (W : S.Opens) :
    ∃ h : (g' ⁻¹ᵁ f ⁻¹ᵁ W).toScheme ⟶ (g ⁻¹ᵁ W).toScheme,
      IsPullback h (g' ∣_ f ⁻¹ᵁ W) (g ∣_ W) (f ∣_ W) := by
  have A := isPullback_morphismRestrict g' (f ⁻¹ᵁ W)
  have C := isPullback_morphismRestrict f W
  have D := isPullback_morphismRestrict g W
  have outer := A.flip.paste_horiz sq
  refine ⟨D.flip.lift ((g' ⁻¹ᵁ f ⁻¹ᵁ W).ι ≫ f') (g' ∣_ f ⁻¹ᵁ W ≫ f ∣_ W) ?_, ?_⟩
  · rw [Category.assoc, sq.w, ← Category.assoc, ← A.w, Category.assoc, Category.assoc, C.w]
  · refine .of_right ?_ (D.flip.lift_snd _ _ _) D.flip
    rw [D.flip.lift_fst, C.w]
    exact outer

/-- **Local projectivity is stable under base change** (Stacks 02V6): the base change of `f` over
`f'⁻¹ W` is a base change of `f` over `W`. -/
instance IsLocallyProjective.isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsLocallyProjective where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    obtain ⟨𝒰, h⟩ := hg.exists_cover
    refine ⟨⟨X.openCoverOfIsOpenCover (fun i ↦ f ⁻¹ᵁ (𝒰.f i).opensRange) ?_, fun i ↦ ?_⟩⟩
    · change ⨆ i, f ⁻¹ᵁ (𝒰.f i).opensRange = ⊤
      rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange, Scheme.Hom.preimage_top]
    · dsimp only [Scheme.openCoverOfIsOpenCover]
      rw [Scheme.Opens.opensRange_ι]
      have := 𝒰.map_prop i
      obtain ⟨k, hk⟩ := isPullback_morphismRestrict_of_isPullback sq (𝒰.f i).opensRange
      exact MorphismProperty.of_isPullback hk (h i)

/-! ## Projective varieties -/

/-- **Projective varieties are H-projective over the base field**: a projective presentation is a
closed immersion into `ℙ(ι; Spec k)` through `ProjectiveSpace.SpecIso`, and conversely. -/
theorem Variety.isProjective_iff_isHProjective {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] :
    Variety.IsProjective k X ↔ IsHProjective (X ↘ Spec (CommRingCat.of k)) := by
  constructor
  · rintro ⟨⟨P⟩⟩
    refine ⟨P.index, P.finiteIndex,
      P.embedding ≫ (ProjectiveSpace.SpecIso P.index (CommRingCat.of k)).inv, inferInstance, ?_⟩
    rw [Category.assoc, ← ProjectiveSpace.SpecIso_hom_comp_projectiveSpaceToSpec,
      Iso.inv_hom_id_assoc, P.overBase]
  · rintro ⟨n, hn, i, hi, h⟩
    exact .ofPresentation
      { index := n
        finiteIndex := hn
        embedding := i ≫ (ProjectiveSpace.SpecIso n (CommRingCat.of k)).hom
        overBase := by
          rw [Category.assoc, ProjectiveSpace.SpecIso_hom_comp_projectiveSpaceToSpec, h] }

/-! ## Relative ampleness of `𝒪(1)` -/

section TwistingSheaf

open MvPolynomial Opposite TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- Over an affine open of the base and an affine open of the universal model, `ℙ(n; S)` is
affine. -/
lemma isAffineOpen_preimage_inf_preimage {V : S.Opens} (hV : IsAffineOpen V)
    {D : (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).Opens} (hD : IsAffineOpen D) :
    IsAffineOpen ((ℙ(n; S) ↘ S) ⁻¹ᵁ V ⊓ toProj n S ⁻¹ᵁ D) := by
  have : IsAffine V := hV
  have : IsAffine D := hD
  let m : pullback (V.ι ≫ terminal.from S) (D.ι ≫ terminal.from _) ⟶ ℙ(n; S) :=
    pullback.map (V.ι ≫ terminal.from S) (D.ι ≫ terminal.from _) (terminal.from S)
      (terminal.from _) V.ι D.ι (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion m := inferInstanceAs (IsOpenImmersion (pullback.map
    (V.ι ≫ terminal.from S) (D.ι ≫ terminal.from _) (terminal.from S) (terminal.from _) V.ι D.ι
    (𝟙 _) (by simp) (by simp)))
  have hm : (ℙ(n; S) ↘ S) ⁻¹ᵁ V ⊓ toProj n S ⁻¹ᵁ D = m.opensRange := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_map]
    simp [toProj]
    rfl
  rw [hm]
  exact isAffineOpen_opensRange m

open Scheme.Modules in
/-- **`𝒪(1)` is relatively ample** over the base: over an affine `V ⊆ S`, the pulled-back
variables `X_i` are sections of `𝒪(1)` whose non-vanishing loci `V ×_ℤ D₊(X_i)` are affine and
cover. -/
theorem isRelativelyAmple_twistingSheaf_one [Finite n] :
    IsRelativelyAmple (ℙ(n; S) ↘ S) (twistingSheaf n S 1) := by
  let 𝒜 := homogeneousSubmodule n (ULift.{u} ℤ)
  have : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj 𝒜).ringCatSheaf from Proj.twistingSheaf 𝒜 1) :=
    Proj.twistingSheaf_isInvertible _ (fun i ↦ ⟨X i, isHomogeneous_X _ i⟩) 1
      (polynomialVariable_adjoin_eq_top n _)
  refine isRelativelyAmple_iff_isAmpleOn.2 ⟨inferInstance, fun V hV ↦ ?_⟩
  refine IsAmpleOn.of_sections ((ℙ(n; S) ↘ S).isCompact_preimage hV.isCompact) fun x hx ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, toProj n S x ∈ ProjectiveSpectrum.basicOpen 𝒜 (X i) := by
    have := Proj.iSup_basicOpen_eq_top' 𝒜 (fun i ↦ (X i : MvPolynomial n (ULift.{u} ℤ)))
      (fun i ↦ ⟨1, isHomogeneous_X _ i⟩) (polynomialVariable_adjoin_eq_top n _)
    exact Opens.mem_iSup.1 (this ▸ Opens.mem_top (toProj n S x) :)
  let s : Γ(twistingSheaf n S 1, ⊤) := pullbackSection (toProj n S) (Proj.twistingSheaf 𝒜 1)
    (Proj.sectionOfMem 𝒜 𝒜 ⊤ 1 (isHomogeneous_X (ULift.{u} ℤ) i))
  let σ := (twistingSheaf n S 1).presheaf.map (homOfLE (le_top : (ℙ(n; S) ↘ S) ⁻¹ᵁ V ≤ ⊤)).op s
  have hσ : nonvanishingLocus _ σ =
      toProj n S ⁻¹ᵁ ProjectiveSpectrum.basicOpen 𝒜 (X i) ⊓ (ℙ(n; S) ↘ S) ⁻¹ᵁ V := by
    rw [nonvanishingLocus_res]
    erw [nonvanishingLocus_pullbackSection]
    exact congrArg (fun W ↦ toProj n S ⁻¹ᵁ W ⊓ _)
      (Proj.nonvanishingLocus_sectionOfMem_one 𝒜 (fun i ↦ ⟨X i, isHomogeneous_X _ i⟩)
        (polynomialVariable_adjoin_eq_top n _) (isHomogeneous_X (ULift.{u} ℤ) i))
  refine ⟨σ, ?_, ?_⟩
  · rw [hσ]
    exact ⟨hi, hx⟩
  · rw [hσ, inf_comm]
    exact isAffineOpen_preimage_inf_preimage n S hV
      (Proj.isAffineOpen_basicOpen 𝒜 (X i) (isHomogeneous_X (ULift.{u} ℤ) i) one_pos)


/-- **The restriction of `𝒪(1)` along a closed immersion into `ℙ(n; S)` is relatively ample.** In
particular every H-projective morphism carries a relatively ample sheaf, the pullback of `𝒪(1)`
along any of its embeddings. -/
theorem isRelativelyAmple_pullback_twistingSheaf_one [Finite n] {X : Scheme.{u}}
    {f : X ⟶ S} (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) :
    IsRelativelyAmple f ((Scheme.Modules.pullback i).obj (twistingSheaf n S 1)) :=
  hi ▸ (isRelativelyAmple_twistingSheaf_one n S).of_isClosedImmersion i

end ProjectiveSpace

end TwistingSheaf

end AlgebraicGeometry
