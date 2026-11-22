/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Descent.Locality
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Descent.Fpqc
import DerivedAlgGeo.RingTheory.Finiteness.Descent

/-!
# Finite presentation descends along fpqc coverings

A quasi-coherent module sheaf is of finite presentation when its pullbacks along an fpqc
covering are (Stacks 05B0). So finite presentation is a local property of the quasi-coherent
pseudofunctor `Scheme.qcohPseudofunctor` for the fpqc topology, and finitely presented
quasi-coherent module sheaves form an fpqc substack.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.finitePresentationProperty`: finite presentation, as a
  property of objects of `qcohPseudofunctor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_pullback_Spec_map`: the affine case,
  along a faithfully flat ring map.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_cover`: Stacks 05B0.
* `AlgebraicGeometry.Scheme.Modules.finitePresentationProperty` is local for
  `Scheme.fpqcTopology`, and its full sub-pseudofunctor is an fpqc stack.

## Implementation notes

On `Spec A` a quasi-coherent `F` is `M̃` with `M = Γ(F)`, and its pullback along
`Spec B ⟶ Spec A` is `(B ⊗_A M)~` (`pullbackSpecMapTildeIso`). Over any ring, `N~` is finitely
presented exactly when `N` is (`isFinitePresentation_tilde_iff`), so the affine case is Stacks
03C4 (2), `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`.

For a cover of `Spec A`, `QuasiCompactCover.exists_hom` refines it by finitely many flat maps
`Spec Bⱼ ⟶ Spec A`, each factoring through a member. Their coproduct is affine and maps flatly
and surjectively to `Spec A`, so it is `Spec B` with `A ⟶ B` faithfully flat; the pullback of `F`
to it is finitely presented on each `Spec Bⱼ`, hence everywhere. A general base reduces to an
affine one along its affine open cover, as finite presentation is Zariski-local.

## References

* [Stacks, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU): substacks cut out by local
  properties.

## Tags

finite presentation, quasi-coherent sheaf, fpqc, faithfully flat, descent, stack
-/

open CategoryTheory CategoryTheory.Limits Bicategory
open scoped TensorProduct

universe v u

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite presentation of a pullback along a composite is that of the iterated pullback. -/
private theorem isFinitePresentation_pullback_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (F : Z.Modules) :
    SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (f ≫ g)).obj F) ↔
      SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback f).obj ((pullback g).obj F)) :=
  ⟨fun h ↦ SheafOfModules.IsFinitePresentation.of_iso.{u} ((pullbackComp f g).app F).symm h,
    fun h ↦ SheafOfModules.IsFinitePresentation.of_iso.{u} ((pullbackComp f g).app F) h⟩

/-- Finite presentation is Zariski-local: it holds when it holds for the pullbacks along the
members of an open cover. -/
private theorem isFinitePresentation_of_openCover {X : Scheme.{u}} (𝒲 : X.OpenCover)
    (F : X.Modules)
    (h : ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (𝒲.f i)).obj F)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  have := 𝒲.map_prop
  exact SheafOfModules.IsFinitePresentation.of_coversTop F (fun i ↦ (𝒲.f i).opensRange)
    (TopCat.Opens.grothendieckTopology_coversTop _ (OpenCover.iSup_opensRange 𝒲)) fun i ↦
      ((𝒲.f i).isFinitePresentation_over_iff_restrict F).mpr
        (SheafOfModules.IsFinitePresentation.of_iso.{u}
          ((restrictFunctorIsoPullback (𝒲.f i)).app F).symm (h i))

/-- **The affine case of Stacks 05B0.** Let `φ : A ⟶ B` be faithfully flat. A quasi-coherent
module sheaf on `Spec A` whose pullback to `Spec B` is of finite presentation is of finite
presentation.

Faithful flatness cannot be dropped: for `ℤ ⟶ ℚ` and `F = (ℚ/ℤ)~`, the pullback is `0`, and
`ℚ/ℤ` is not finitely generated. -/
theorem isFinitePresentation_of_pullback_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) (F : (Spec A).Modules) [F.IsQuasicoherent]
    (hF : SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (Spec.map φ)).obj F)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  haveI : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent F
  let M := moduleSpecΓFunctor.obj F
  let eF := asIso F.fromTildeΓ
  letI : Algebra A B := φ.hom.toAlgebra
  haveI : Module.FaithfullyFlat A B := hφ
  have h₁ : SheafOfModules.IsFinitePresentation.{u, u, u}
      ((tilde.functor B).obj ((ModuleCat.extendScalars φ.hom).obj M)) :=
    SheafOfModules.IsFinitePresentation.of_iso.{u}
      ((pullback (Spec.map φ)).mapIso eF.symm ≪≫ (pullbackSpecMapTildeIso φ).app M) hF
  haveI : Module.FinitePresentation B (B ⊗[A] M) :=
    (isFinitePresentation_tilde_iff ((ModuleCat.extendScalars φ.hom).obj M)).mp h₁
  haveI : Module.FinitePresentation A M :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B
  exact SheafOfModules.IsFinitePresentation.of_iso.{u} eF (isFinitePresentation_tilde M)

set_option maxHeartbeats 400000 in
/-- Stacks 05B0 over an affine base. The coproduct of a finite affine refinement maps flatly
and surjectively onto `Spec A`; whnf of that coproduct as a `Spec` needs the extra heartbeats. -/
private theorem isFinitePresentation_of_cover_Spec {A : CommRingCat.{u}}
    (𝒰 : (Spec A).Cover.{u} Scheme.fpqcPrecoverage) (F : (Spec A).Modules)
    (hFq : F.IsQuasicoherent)
    (hF : ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (𝒰.f i)).obj F)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  have : MorphismProperty.RespectsLeft @Flat @IsOpenImmersion :=
    ⟨fun i hi f hf ↦ by
      have : IsOpenImmersion i := hi
      have : Flat f := hf
      exact (inferInstance : Flat (i ≫ f))⟩
  let 𝒰₀ : (Spec A).Cover.{u} (Scheme.propQCPrecoverage @Flat) := 𝒰
  have : QuasiCompactCover 𝒰₀.forgetQc.toPreZeroHypercover :=
    Scheme.instQuasiCompactCoverForgetQc (P := @Flat) 𝒰₀
  obtain ⟨𝒱, r, hfin, -⟩ := QuasiCompactCover.exists_hom 𝒰₀.forgetQc
  have := hfin
  have : ∀ j, Flat (𝒱.f j) := 𝒱.map_prop
  let Y : 𝒱.I₀ → Scheme.{u} := fun j ↦ Spec (𝒱.X j)
  let p : (∐ Y) ⟶ Spec A := Sigma.desc 𝒱.f
  have : Flat p := inferInstance
  have : Surjective p := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := 𝒱.covers x
    exact ⟨Sigma.ι Y (𝒱.idx x) y, by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      exact hy⟩⟩
  have : IsAffine (∐ Y) := inferInstance
  have hp : SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback p).obj F) := by
    refine isFinitePresentation_of_openCover (sigmaOpenCover Y) _ fun (j : 𝒱.I₀) ↦ ?_
    have hj : r.h₀ j ≫ 𝒰.f (r.s₀ j) = (sigmaOpenCover Y).f j ≫ p :=
      (r.w₀ j).trans (Sigma.ι_comp_desc 𝒱.f j).symm
    have h := (isFinitePresentation_pullback_comp_iff (r.h₀ j) (𝒰.f (r.s₀ j)) F).mpr
      (isFinitePresentation_pullback _ _ (hF _))
    rw [hj] at h
    exact (isFinitePresentation_pullback_comp_iff _ _ F).mp h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((∐ Y).isoSpec.inv ≫ p)
  have hφff : φ.hom.FaithfullyFlat := by
    refine (flat_and_surjective_SpecMap_iff φ).mp ⟨?_, ?_⟩ <;> rw [hφ] <;> infer_instance
  refine @isFinitePresentation_of_pullback_Spec_map _ _ φ hφff F hFq ?_
  rw [hφ]
  exact (isFinitePresentation_pullback_comp_iff _ _ F).mpr (isFinitePresentation_pullback _ _ hp)

/-- **Finite presentation descends along fpqc coverings** (Stacks 05B0). A quasi-coherent module
sheaf is of finite presentation when its pullbacks along the members of an fpqc covering are.

Quasi-compactness of the covering cannot be dropped: the flat, jointly surjective family of all
`Spec ℤ_(p)` and `Spec ℚ` over `Spec ℤ` and `F = (⊕_p ℤ/p)~` have pullbacks `(ℤ/p)~` or `0`,
all finitely presented, while `⊕_p ℤ/p` is not finitely generated. No finite subfamily covers the
closed points. -/
@[stacks 05B0]
theorem isFinitePresentation_of_cover {X : Scheme.{u}}
    (𝒰 : X.Cover.{v} Scheme.fpqcPrecoverage) (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ i, SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (𝒰.f i)).obj F)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  -- Every fpqc cover has a subcover indexed in universe `u`.
  let 𝒰₀ : X.Cover.{v} (Scheme.propQCPrecoverage @Flat) := 𝒰
  have : Precoverage.Small.{u} (Scheme.propQCPrecoverage @Flat) :=
    Scheme.instSmallPropQCPrecoverage (P := @Flat)
  let 𝒰' : X.Cover.{u} Scheme.fpqcPrecoverage := 𝒰₀.restrictIndexOfSmall.{u}
  have hF' (i : 𝒰'.I₀) :
      SheafOfModules.IsFinitePresentation.{u, u, u} ((pullback (𝒰'.f i)).obj F) := hF _
  refine isFinitePresentation_of_openCover X.affineCover F fun j ↦ ?_
  refine isFinitePresentation_of_cover_Spec (𝒰'.pullback₁ (X.affineCover.f j)) _
    (isQuasicoherent_pullback (X.affineCover.f j) F inferInstance) fun i ↦ ?_
  refine (isFinitePresentation_pullback_comp_iff _ _ F).mp ?_
  have h := (isFinitePresentation_pullback_comp_iff
    (Limits.pullback.snd (X.affineCover.f j) (𝒰'.f i)) (𝒰'.f i) F).mpr
      (isFinitePresentation_pullback _ _ (hF' i))
  rw [← Limits.pullback.condition] at h
  exact h

/-- Finite presentation, as a property of objects of the quasi-coherent pseudofunctor
`qcohPseudofunctor`. -/
def finitePresentationProperty : qcohPseudofunctor.{u}.ObjectProperty where
  prop _ := fun M ↦ SheafOfModules.IsFinitePresentation.{u, u, u} M.obj

instance : finitePresentationProperty.{u}.IsClosedUnderMapObj where
  map_obj {_ _} M hM f := isFinitePresentation_pullback f.as.unop M.obj hM

instance : finitePresentationProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X :=
    { of_iso e h := SheafOfModules.IsFinitePresentation.of_iso.{u}
        ((SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).ι.mapIso e) h }

/-- Finite presentation is local for the fpqc topology: a covering sieve contains an fpqc
covering family, and `isFinitePresentation_of_cover` applies to it. -/
instance : finitePresentationProperty.{u}.IsLocal Scheme.fpqcTopology where
  of_sieve {S} M R hR h := by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
    obtain ⟨T, hT, hle⟩ := hR
    rw [Precoverage.mem_iff_exists_zeroHypercover] at hT
    obtain ⟨𝒰, rfl⟩ := hT
    haveI : M.obj.IsQuasicoherent := M.property
    exact isFinitePresentation_of_cover (𝒰 : S.Cover fpqcPrecoverage) M.obj fun i ↦
      h (𝒰.f i) (hle _ _ (Presieve.ofArrows.mk i))

/-- Finitely presented quasi-coherent module sheaves form an fpqc stack: the substack of
`qcohPseudofunctor` cut out by the local property `finitePresentationProperty`. -/
instance : finitePresentationProperty.{u}.fullsubcategory.IsStack Scheme.fpqcTopology :=
  Pseudofunctor.ObjectProperty.isStack_fullsubcategory _

end AlgebraicGeometry.Scheme.Modules
