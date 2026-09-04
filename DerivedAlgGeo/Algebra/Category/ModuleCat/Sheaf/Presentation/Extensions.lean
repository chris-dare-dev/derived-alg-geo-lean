/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Finite
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Locality
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Exactness
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Data.Finite.Sum

/-!
# Extensions of finitely presented module sheaves

Finite presentation of sheaves of modules is closed under extensions. The proof is local on
the site. On a finite cover, generators of the quotient are lifted simultaneously; after a
second finite refinement, the resulting correction relations are lifted as well. A finite
horseshoe presentation then presents the middle term.

This avoids affine cohomology entirely, so the theorem needs no noetherian hypothesis.

## Main results

* `SheafOfModules.IsFinitePresentation.middle_of_shortExact`;
* `SheafOfModules.isFinitePresentation_isClosedUnderExtensions`.
-/

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite ZeroObject

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

noncomputable local instance : Abelian (Sheaf J AddCommGrpCat.{u}) :=
  CategoryTheory.sheafIsAbelian

noncomputable local instance : NonPreadditiveAbelian (Sheaf J AddCommGrpCat.{u}) :=
  CategoryTheory.Abelian.nonPreadditiveAbelian

noncomputable def simultaneousImageCover {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections) (X : C) : J.Cover X := by
  letI := Fintype.ofFinite I
  let f' := (toSheaf R).map f
  haveI : Presheaf.IsLocallySurjective J f'.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) f').mpr (by infer_instance)
  exact Finset.univ.inf fun i ↦
    ⟨Presheaf.imageSieve f'.hom ((s i).1 (.op X)), Presheaf.imageSieve_mem J f'.hom _⟩

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma simultaneousImageCover_mem {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections) (X : C) (a : (simultaneousImageCover f s X).Arrow)
    (i : I) : Presheaf.imageSieve ((toSheaf R).map f).hom ((s i).1 (.op X)) a.f := by
  classical
  letI := Fintype.ofFinite I
  let T : I → J.Cover X := fun i ↦
    ⟨Presheaf.imageSieve ((toSheaf R).map f).hom ((s i).1 (.op X)), by
      let f' := (toSheaf R).map f
      haveI : Presheaf.IsLocallySurjective J f'.hom :=
        (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) f').mpr (by infer_instance)
      exact Presheaf.imageSieve_mem J f'.hom _⟩
  have hle : Finset.univ.inf T ≤ T i := Finset.inf_le (Finset.mem_univ i)
  exact hle a.f (by simpa [simultaneousImageCover, T] using a.hf)

noncomputable def simultaneousImageCoverObjects {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections) : (Σ X, (simultaneousImageCover f s X).Arrow) → C :=
  fun a ↦ a.2.Y

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma simultaneousImageCoverObjects_coversTop {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections) :
    J.CoversTop (simultaneousImageCoverObjects f s) := by
  intro X
  refine J.superset_covering ?_ (simultaneousImageCover f s X).condition
  intro Y a ha
  apply (Sieve.mem_ofObjects_iff ..).mpr
  exact ⟨⟨X, ⟨Y, a, ha⟩⟩, ⟨𝟙 Y⟩⟩

noncomputable def sectionOfInitial {D : Type u} [Category.{u} D]
    {S : Dᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} S)
    (X : Dᵒᵖ) (hX : IsInitial X) (x : M.obj X) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun Y ↦ M.map (hX.to Y) x)
    (fun {Y Z} f ↦ by
      rw [← M.map_comp_apply]
      exact M.congr_map_apply (hX.hom_ext _ _) x)

@[simp]
lemma sectionOfInitial_eval {D : Type u} [Category.{u} D]
    {S : Dᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} S)
    (X : Dᵒᵖ) (hX : IsInitial X) (x : M.obj X) :
    (sectionOfInitial M X hX x).1 X = x := by
  change M.map (hX.to X) x = x
  rw [hX.hom_ext (hX.to X) (𝟙 X)]
  simp

noncomputable def overSection (M : SheafOfModules.{u} R) {X : C}
    (x : (M.over X).val.obj (.op (Over.mk (𝟙 X)))) :
    (M.over X).sections :=
  sectionOfInitial (M.over X).val (.op (Over.mk (𝟙 X)))
    (Limits.initialOpOfTerminal Over.mkIdTerminal) x

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[simp]
lemma overSection_eval_mkId (M : SheafOfModules.{u} R) {X : C}
    (x : (M.over X).val.obj (.op (Over.mk (𝟙 X)))) :
    (overSection M x).1 (.op (Over.mk (𝟙 X))) = x := by
  apply sectionOfInitial_eval

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma overSection_ext (M : SheafOfModules.{u} R) {X : C}
    (s t : (M.over X).sections)
    (h : s.1 (.op (Over.mk (𝟙 X))) = t.1 (.op (Over.mk (𝟙 X)))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro Y
  rw [← PresheafOfModules.sections_property s
    (Over.mkIdTerminal.from Y.unop).op]
  rw [← PresheafOfModules.sections_property t
    (Over.mkIdTerminal.from Y.unop).op]
  exact congr_arg _ h

noncomputable def overUnitIso [HasBinaryProducts C] (U : C) :
    unit (R.over U) ≅ (overFunctor R U).obj (unit R) :=
  Iso.refl _

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[simp]
lemma unitToPushforwardObjUnit_over [HasBinaryProducts C] (U : C) :
    unitToPushforwardObjUnit (𝟙 (R.over U)) = (overUnitIso U).hom := by
  ext X
  rfl

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 1600000 in
lemma freeHomEquiv_mapFree_over [HasBinaryProducts C]
    {N : SheafOfModules.{u} R} {I : Type u}
    (p : free (R := R) I ⟶ N) (i : I) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)] :
    (N.over U).freeHomEquiv
        ((mapFreeIso (overFunctor R U) I (overUnitIso U)).hom ≫
          (overFunctor R U).map p) i =
      pushforwardSections (𝟙 (R.over U)) (N.freeHomEquiv p i) := by
  haveI : (overFunctor R U).IsLeftAdjoint := by
    change (pushforward.{u} (𝟙 (R.over U))).IsLeftAdjoint
    infer_instance
  apply (N.over U).unitHomEquiv.symm.injective
  rw [unitHomEquiv_symm_freeHomEquiv_apply]
  have hp₀ :
      pushforwardSections (𝟙 (R.over U))
          ((N.unitHomEquiv) (ιFree i ≫ p)) =
        (N.over U).unitHomEquiv
          (unitToPushforwardObjUnit (𝟙 (R.over U)) ≫
            (overFunctor R U).map (ιFree i ≫ p)) :=
    pushforwardSections_unitHomEquiv (𝟙 (R.over U)) (ιFree i ≫ p)
  have hp := congrArg (N.over U).unitHomEquiv.symm hp₀
  simp only [Equiv.symm_apply_apply] at hp
  symm
  calc
    (N.over U).unitHomEquiv.symm
        (pushforwardSections (𝟙 (R.over U)) (N.freeHomEquiv p i)) =
        unitToPushforwardObjUnit (𝟙 (R.over U)) ≫
          (overFunctor R U).map (ιFree i ≫ p) := hp
    _ = ιFree i ≫ (mapFreeIso (overFunctor R U) I (overUnitIso U)).hom ≫
        (overFunctor R U).map p := by
      rw [ιFree_mapFreeIso_hom_assoc]
      rw [← Functor.map_comp]
      simp [unitToPushforwardObjUnit_over, overUnitIso]

noncomputable def localLift {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections)
    (a : Σ X, (simultaneousImageCover f s X).Arrow) :
    free (R := R.over a.2.Y) I ⟶ M.over a.2.Y :=
  (M.over a.2.Y).freeHomEquiv.symm fun i ↦
    overSection M <| show M.val.obj (.op a.2.Y) from
      Presheaf.localPreimage ((toSheaf R).map f).hom
        ((s i).1 (.op a.1)) a.2.f
        (simultaneousImageCover_mem f s a.1 a.2 i)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 3200000 in
lemma localLift_comp {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] {I : Type u} [Finite I]
    (s : I → N.sections)
    (a : Σ X, (simultaneousImageCover f s X).Arrow)
    [HasBinaryProducts C]
    [HasSheafify (J.over a.2.Y) AddCommGrpCat.{u}]
    [(J.over a.2.Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R a.2.Y)] :
    localLift f s a ≫ (overFunctor R a.2.Y).map f =
      (mapFreeIso (overFunctor R a.2.Y) I (overUnitIso a.2.Y)).hom ≫
        (overFunctor R a.2.Y).map (N.freeHomEquiv.symm s) := by
  haveI : (overFunctor R a.2.Y).IsLeftAdjoint := by
    change (pushforward.{u} (𝟙 (R.over a.2.Y))).IsLeftAdjoint
    infer_instance
  apply (N.over a.2.Y).freeHomEquiv.injective
  funext i
  change sectionsMap ((overFunctor R a.2.Y).map f)
      ((M.over a.2.Y).freeHomEquiv (localLift f s a) i) = _
  have hmap :
      (N.over a.2.Y).freeHomEquiv
          ((mapFreeIso (overFunctor R a.2.Y) I (overUnitIso a.2.Y)).hom ≫
            (overFunctor R a.2.Y).map (N.freeHomEquiv.symm s)) i =
        pushforwardSections (𝟙 (R.over a.2.Y)) (s i) := by
    simpa using freeHomEquiv_mapFree_over
      (N.freeHomEquiv.symm s) i a.2.Y
  calc
    sectionsMap ((overFunctor R a.2.Y).map f)
        ((M.over a.2.Y).freeHomEquiv (localLift f s a) i) =
        pushforwardSections (𝟙 (R.over a.2.Y)) (s i) := by
      apply overSection_ext N
      let x : M.val.obj (.op a.2.Y) :=
        Presheaf.localPreimage ((toSheaf R).map f).hom
          ((s i).1 (.op a.1)) a.2.f
          (simultaneousImageCover_mem f s a.1 a.2 i)
      have hfree :
          (M.over a.2.Y).freeHomEquiv (localLift f s a) i =
            overSection M x := by
        simp [localLift, x]
      change ((overFunctor R a.2.Y).map f).val.app
          (.op (Over.mk (𝟙 a.2.Y)))
          (((M.over a.2.Y).freeHomEquiv (localLift f s a) i).1
            (.op (Over.mk (𝟙 a.2.Y)))) =
        (pushforwardSections (𝟙 (R.over a.2.Y)) (s i)).1
          (.op (Over.mk (𝟙 a.2.Y)))
      rw [hfree, overSection_eval_mkId]
      change ((toSheaf R).map f).hom.app (.op a.2.Y) x =
        (s i).1 (.op a.2.Y)
      dsimp only [x]
      rw [Presheaf.app_localPreimage]
      exact PresheafOfModules.sections_property (s i) a.2.f.op
    _ = _ := hmap.symm

noncomputable abbrev Presentation.mapOver [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : M.Presentation) (U : C)
    [(J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)] :
    (M.over U).Presentation :=
  P.map (overFunctor R U) (overUnitIso U)

instance Presentation.mapOver_isFinite [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite] (U : C)
    [(J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)] :
    (P.mapOver U).IsFinite := by
  dsimp only [Presentation.mapOver]
  exact Presentation.isFinite_map (S := R.over U) P
    (overFunctor R U) (overUnitIso U)

namespace Presentation

variable (S : ShortComplex (SheafOfModules.{u} R))
  (hS : S.ShortExact) (P₁ : S.X₁.Presentation) (P₃ : S.X₃.Presentation)

noncomputable local instance : NonPreadditiveAbelian (SheafOfModules.{u} R) :=
  CategoryTheory.Abelian.nonPreadditiveAbelian

noncomputable abbrev relationMap {M : SheafOfModules.{u} R} (P : M.Presentation) :
    free (R := R) P.relations.I ⟶ free (R := R) P.generators.I :=
  P.relations.π ≫ kernel.ι P.generators.π

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[simp]
lemma relationMap_presentationOfIsCokernelFree {ι σ : Type u}
    {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    relationMap (presentationOfIsCokernelFree f g H H') = f := by
  change (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv.symm
      ((kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv
        (kernel.lift (generatorsOfIsCokernelFree f g H H').π f
          (by simpa only [generatorsOfIsCokernelFree_π] using H))) ≫
      kernel.ι (generatorsOfIsCokernelFree f g H H').π = f
  rw [Equiv.symm_apply_apply, kernel.lift_ι]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 800000 in
lemma relationMap_mapOver [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : M.Presentation) (U : C)
    [(J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)] :
    relationMap (P.mapOver U) =
      (mapFreeIso (overFunctor R U) P.relations.I (overUnitIso U)).hom ≫
        (overFunctor R U).map (relationMap P) ≫
        (mapFreeIso (overFunctor R U) P.generators.I (overUnitIso U)).inv := by
  change relationMap (P.map (overFunctor R U) (overUnitIso U)) = _
  dsimp only [Presentation.map]
  rw [relationMap_presentationOfIsCokernelFree]
  dsimp only [Presentation.mapRelations, relationMap, GeneratingSections.π]
  simp only [Functor.map_comp, Category.assoc]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[reassoc (attr := simp)]
lemma freeMap_inl_freeSumIso_inv (I K : Type u) :
    freeMap (R := R) (Sum.inl : I → I ⊕ K) ≫ (freeSumIso (R := R) I K).inv =
      coprod.inl := by
  rw [← inl_freeSumIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[reassoc (attr := simp)]
lemma freeMap_inr_freeSumIso_inv (I K : Type u) :
    freeMap (R := R) (Sum.inr : K → I ⊕ K) ≫ (freeSumIso (R := R) I K).inv =
      coprod.inr := by
  rw [← inr_freeSumIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def correction
    (h : free P₃.generators.I ⟶ S.X₂)
    (hh : h ≫ S.g = P₃.generators.π) :
    free P₃.relations.I ⟶ S.X₁ := by
  letI := hS.mono_f
  exact hS.exact.lift (relationMap P₃ ≫ h) (by simp [hh, relationMap])

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
@[reassoc]
lemma correction_comp
    (h : free P₃.generators.I ⟶ S.X₂)
    (hh : h ≫ S.g = P₃.generators.π) :
    correction S hS P₃ h hh ≫ S.f = relationMap P₃ ≫ h := by
  letI := hS.mono_f
  dsimp only [correction]
  exact hS.exact.lift_f (relationMap P₃ ≫ h) (by simp [hh, relationMap])

noncomputable def extensionGeneratorsMap
    (h : free P₃.generators.I ⟶ S.X₂) :
    free (P₁.generators.I ⊕ P₃.generators.I) ⟶ S.X₂ :=
  (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
    coprod.desc (P₁.generators.π ≫ S.f) h

variable (h : free P₃.generators.I ⟶ S.X₂)
  (hh : h ≫ S.g = P₃.generators.π)
  (k : free P₃.relations.I ⟶ free P₁.generators.I)
  (hk : k ≫ P₁.generators.π = correction S hS P₃ h hh)

noncomputable def extensionRelationLeft :
    free P₁.relations.I ⟶ kernel (extensionGeneratorsMap S P₁ P₃ h) :=
  kernel.lift _
    (relationMap P₁ ≫ coprod.inl ≫
      (freeSumIso (R := R) P₁.generators.I P₃.generators.I).hom)
    (by
      simp only [extensionGeneratorsMap, relationMap, Category.assoc]
      rw [Iso.hom_inv_id_assoc]
      simp only [coprod.inl_desc]
      simp)

noncomputable def extensionRelationRight :
    free P₃.relations.I ⟶ kernel (extensionGeneratorsMap S P₁ P₃ h) :=
  kernel.lift _
    ((-k) ≫ coprod.inl ≫
        (freeSumIso (R := R) P₁.generators.I P₃.generators.I).hom +
      relationMap P₃ ≫ coprod.inr ≫
        (freeSumIso (R := R) P₁.generators.I P₃.generators.I).hom)
    (by
      have hc : correction S hS P₃ h hh ≫ S.f =
          relationMap P₃ ≫ h := by
        exact correction_comp S hS P₃ h hh
      simp only [extensionGeneratorsMap, Preadditive.add_comp, Category.assoc,
        Iso.hom_inv_id_assoc]
      simp only [coprod.inl_desc, coprod.inr_desc]
      rw [Preadditive.neg_comp, reassoc_of% hk]
      rw [hc]
      simp)

noncomputable def extensionRelationsMap :
    free (P₁.relations.I ⊕ P₃.relations.I) ⟶
      kernel (extensionGeneratorsMap S P₁ P₃ h) :=
  (freeSumIso (R := R) P₁.relations.I P₃.relations.I).inv ≫
    coprod.desc
      (extensionRelationLeft S P₁ P₃ h)
      (extensionRelationRight S hS P₁ P₃ h hh k hk)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
include hS hh in
lemma epi_extensionGeneratorsMap :
    Epi (extensionGeneratorsMap S P₁ P₃ h) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z z hz
  have hfz : S.f ≫ z = 0 := by
    apply (cancel_epi P₁.generators.π).1
    simpa [extensionGeneratorsMap, coprod.inl_desc] using
      freeMap (R := R) (Sum.inl : P₁.generators.I →
        P₁.generators.I ⊕ P₃.generators.I) ≫= hz
  letI := hS.epi_g
  let z' := hS.exact.desc z hfz
  have hgz : S.g ≫ z' = z := by
    dsimp only [z']
    exact hS.exact.g_desc z hfz
  have hhz : h ≫ z = 0 := by
    simpa [extensionGeneratorsMap, coprod.inr_desc] using
      freeMap (R := R) (Sum.inr : P₃.generators.I →
        P₁.generators.I ⊕ P₃.generators.I) ≫= hz
  have hz' : z' = 0 := by
    apply (cancel_epi P₃.generators.π).1
    calc
      P₃.generators.π ≫ z' = h ≫ S.g ≫ z' := by
        simpa only [Category.assoc] using hh.symm =≫ z'
      _ = h ≫ z := h ≫= hgz
      _ = 0 := hhz
  calc
    z = S.g ≫ z' := hgz.symm
    _ = 0 := by rw [hz', comp_zero]

noncomputable def extensionKernelToRightRelations :
    kernel (extensionGeneratorsMap S P₁ P₃ h) ⟶ kernel P₃.generators.π :=
  kernel.lift _
    (kernel.ι (extensionGeneratorsMap S P₁ P₃ h) ≫
      (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
      coprod.desc 0 (𝟙 _))
    (by
      have eqp :
          (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
              coprod.desc 0 (𝟙 _) ≫ P₃.generators.π =
            extensionGeneratorsMap S P₁ P₃ h ≫ S.g := by
        rw [← hh]
        simp [extensionGeneratorsMap, S.zero]
      simpa only [Category.assoc] using
        (kernel.ι (extensionGeneratorsMap S P₁ P₃ h) ≫= eqp).trans (by simp))

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma extensionRelationRight_comp_kernelToRightRelations :
    extensionRelationRight S hS P₁ P₃ h hh k hk ≫
      extensionKernelToRightRelations S P₁ P₃ h hh = P₃.relations.π := by
  apply (cancel_mono (kernel.ι P₃.generators.π)).1
  simp only [extensionRelationRight, extensionKernelToRightRelations,
    kernel.lift_ι, kernel.lift_ι_assoc, Category.assoc,
    Preadditive.add_comp, Iso.hom_inv_id_assoc]
  rw [coprod.inl_desc, coprod.inr_desc]
  simp

noncomputable def extensionLeftRelationsToKernel :
    kernel P₁.generators.π ⟶ kernel (extensionGeneratorsMap S P₁ P₃ h) :=
  kernel.lift _
    (kernel.ι P₁.generators.π ≫ coprod.inl ≫
      (freeSumIso (R := R) P₁.generators.I P₃.generators.I).hom)
    (by
      simp only [extensionGeneratorsMap, Category.assoc, Iso.hom_inv_id_assoc]
      rw [coprod.inl_desc]
      simp)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma extensionLeftRelationsToKernel_comp_kernelToRightRelations :
    extensionLeftRelationsToKernel S P₁ P₃ h ≫
      extensionKernelToRightRelations S P₁ P₃ h hh = 0 := by
  apply (cancel_mono (kernel.ι P₃.generators.π)).1
  simp only [extensionLeftRelationsToKernel, extensionKernelToRightRelations,
    Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, Iso.hom_inv_id_assoc]
  rw [coprod.inl_desc]
  simp

noncomputable def extensionKernelOfRightRelationsToLeftRelations :
    kernel (extensionKernelToRightRelations S P₁ P₃ h hh) ⟶
      kernel P₁.generators.π :=
  kernel.lift _
    (kernel.ι (extensionKernelToRightRelations S P₁ P₃ h hh) ≫
      kernel.ι (extensionGeneratorsMap S P₁ P₃ h) ≫
      (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
      coprod.desc (𝟙 _) 0)
    (by
      let q := extensionGeneratorsMap S P₁ P₃ h
      let s := extensionKernelToRightRelations S P₁ P₃ h hh
      let p₁ : free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I ⟶
          free (R := R) P₁.generators.I :=
        coprod.desc (𝟙 _) 0
      let p₃ : free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I ⟶
          free (R := R) P₃.generators.I :=
        coprod.desc 0 (𝟙 _)
      have hdesc :
          coprod.desc (P₁.generators.π ≫ S.f) h =
            p₁ ≫ P₁.generators.π ≫ S.f + p₃ ≫ h := by
        apply coprod.hom_ext
        · simp only [p₁, p₃, coprod.inl_desc,
            coprod.inl_desc_assoc,
            Preadditive.comp_add, Category.id_comp, zero_comp, add_zero]
        · simp only [p₁, p₃, coprod.inr_desc,
            coprod.inr_desc_assoc,
            Preadditive.comp_add, Category.id_comp, zero_comp, zero_add]
      have hs :
          s ≫ kernel.ι P₃.generators.π =
            kernel.ι q ≫
              (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫ p₃ := by
        simp [s, q, p₃, extensionKernelToRightRelations]
      have hr :
          kernel.ι s ≫ kernel.ι q ≫
              (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫ p₃ = 0 := by
        simpa only [Category.assoc, hs, zero_comp] using
          kernel.condition s =≫ kernel.ι P₃.generators.π
      have hq :
          kernel.ι s ≫ kernel.ι q ≫
              (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
              coprod.desc (P₁.generators.π ≫ S.f) h = 0 := by
        simp [q, extensionGeneratorsMap, comp_zero]
      have hl :
          kernel.ι s ≫ kernel.ι q ≫
              (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
              p₁ ≫ P₁.generators.π ≫ S.f = 0 := by
        have hright :
            kernel.ι s ≫ kernel.ι q ≫
                (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
                p₃ ≫ h = 0 := by
          simpa only [Category.assoc, zero_comp] using hr =≫ h
        have hsum :
            kernel.ι s ≫ kernel.ι q ≫
                  (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
                  p₁ ≫ P₁.generators.π ≫ S.f +
              kernel.ι s ≫ kernel.ι q ≫
                  (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
                  p₃ ≫ h = 0 := by
          rw [← Preadditive.comp_add, ← Preadditive.comp_add]
          simpa only [Category.assoc, hdesc, Preadditive.comp_add] using hq
        simpa only [hright, add_zero] using hsum
      letI := hS.mono_f
      apply (cancel_mono S.f).1
      simpa [p₁, Category.assoc] using hl)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 800000 in
lemma extensionKernelOfRightRelationsToLeftRelations_comp :
    extensionKernelOfRightRelationsToLeftRelations S hS P₁ P₃ h hh ≫
      extensionLeftRelationsToKernel S P₁ P₃ h =
        kernel.ι (extensionKernelToRightRelations S P₁ P₃ h hh) := by
  let q := extensionGeneratorsMap S P₁ P₃ h
  let s := extensionKernelToRightRelations S P₁ P₃ h hh
  let p₁ : free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I ⟶
      free (R := R) P₁.generators.I :=
    coprod.desc (𝟙 _) 0
  let p₃ : free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I ⟶
      free (R := R) P₃.generators.I :=
    coprod.desc 0 (𝟙 _)
  have hs :
      s ≫ kernel.ι P₃.generators.π =
        kernel.ι q ≫
          (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫ p₃ := by
    simp [s, q, p₃, extensionKernelToRightRelations]
  have hr :
      kernel.ι s ≫ kernel.ι q ≫
          (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫ p₃ = 0 := by
    simpa only [Category.assoc, hs, zero_comp] using
      kernel.condition s =≫ kernel.ι P₃.generators.π
  have htotal :
      p₁ ≫ coprod.inl + p₃ ≫ coprod.inr =
        𝟙 (free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I) := by
    apply coprod.hom_ext
    · simp only [p₁, p₃, Preadditive.comp_add, ← Category.assoc,
        coprod.inl_desc, Category.id_comp, Category.comp_id, zero_comp, add_zero]
    · simp only [p₁, p₃, Preadditive.comp_add, ← Category.assoc,
        coprod.inr_desc, Category.id_comp, Category.comp_id, zero_comp, zero_add]
  have ha :
      kernel.ι s ≫ kernel.ι q ≫
          (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv =
        kernel.ι s ≫ kernel.ι q ≫
          (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
          p₁ ≫ coprod.inl := by
    conv_lhs => rw [← Category.comp_id
      (kernel.ι s ≫ kernel.ι q ≫
        (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv)]
    rw [← htotal, Preadditive.comp_add]
    simp only [Category.assoc]
    have hrr :
        kernel.ι s ≫ kernel.ι q ≫
            (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv ≫
            p₃ ≫
              (coprod.inr : free (R := R) P₃.generators.I ⟶
                free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I) = 0 := by
      simpa only [Category.assoc, zero_comp] using hr =≫
        (coprod.inr : free (R := R) P₃.generators.I ⟶
          free (R := R) P₁.generators.I ⨿ free (R := R) P₃.generators.I)
    rw [hrr, add_zero]
  apply (cancel_mono (kernel.ι q)).1
  apply (cancel_mono
    (freeSumIso (R := R) P₁.generators.I P₃.generators.I).inv).1
  simpa [s, q, p₁, extensionKernelOfRightRelationsToLeftRelations,
    extensionLeftRelationsToKernel] using ha.symm

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma extensionRelationLeft_eq :
    extensionRelationLeft S P₁ P₃ h =
      P₁.relations.π ≫ extensionLeftRelationsToKernel S P₁ P₃ h := by
  apply (cancel_mono (kernel.ι (extensionGeneratorsMap S P₁ P₃ h))).1
  simp [extensionRelationLeft, extensionLeftRelationsToKernel, relationMap]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
include hS hh in
lemma epi_extensionKernelToRightRelations
    (k : free P₃.relations.I ⟶ free P₁.generators.I)
    (hk : k ≫ P₁.generators.π = correction S hS P₃ h hh) :
    Epi (extensionKernelToRightRelations S P₁ P₃ h hh) :=
  epi_of_epi_fac
    (extensionRelationRight_comp_kernelToRightRelations S hS P₁ P₃ h hh k hk)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
include hS hh hk in
set_option maxHeartbeats 800000 in
lemma epi_extensionRelationsMap :
    Epi (extensionRelationsMap S hS P₁ P₃ h hh k hk) := by
  let q := extensionGeneratorsMap S P₁ P₃ h
  let s := extensionKernelToRightRelations S P₁ P₃ h hh
  let l := extensionLeftRelationsToKernel S P₁ P₃ h
  haveI : Epi s := epi_extensionKernelToRightRelations S hS P₁ P₃ h hh k hk
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z z hz
  have hleft : extensionRelationLeft S P₁ P₃ h ≫ z = 0 := by
    simpa [extensionRelationsMap, coprod.inl_desc] using
      freeMap (R := R) (Sum.inl : P₁.relations.I →
        P₁.relations.I ⊕ P₃.relations.I) ≫= hz
  have hright :
      extensionRelationRight S hS P₁ P₃ h hh k hk ≫ z = 0 := by
    simpa [extensionRelationsMap, coprod.inr_desc] using
      freeMap (R := R) (Sum.inr : P₃.relations.I →
        P₁.relations.I ⊕ P₃.relations.I) ≫= hz
  have hlz : l ≫ z = 0 := by
    apply (cancel_epi P₁.relations.π).1
    calc
      P₁.relations.π ≫ l ≫ z =
          extensionRelationLeft S P₁ P₃ h ≫ z := by
        simpa only [l, Category.assoc] using
          (extensionRelationLeft_eq S P₁ P₃ h).symm =≫ z
      _ = 0 := hleft
  have hkz : kernel.ι s ≫ z = 0 := by
    simpa only [s, l, Category.assoc,
      comp_zero,
      ← extensionKernelOfRightRelationsToLeftRelations_comp S hS P₁ P₃ h hh] using
        extensionKernelOfRightRelationsToLeftRelations S hS P₁ P₃ h hh ≫= hlz
  let z' := Abelian.epiDesc s z hkz
  have hsz' : s ≫ z' = z := by
    simp [z']
  have hz' : z' = 0 := by
    apply (cancel_epi P₃.relations.π).1
    calc
      P₃.relations.π ≫ z' =
          extensionRelationRight S hS P₁ P₃ h hh k hk ≫ s ≫ z' := by
        simpa only [s, Category.assoc] using
          (extensionRelationRight_comp_kernelToRightRelations
            S hS P₁ P₃ h hh k hk).symm =≫ z'
      _ = extensionRelationRight S hS P₁ P₃ h hh k hk ≫ z := by
        exact extensionRelationRight S hS P₁ P₃ h hh k hk ≫= hsz'
      _ = 0 := hright
  calc
    z = s ≫ z' := hsz'.symm
    _ = 0 := by simpa only [comp_zero] using s ≫= hz'

noncomputable def extension : S.X₂.Presentation := by
  let q := extensionGeneratorsMap S P₁ P₃ h
  let r := extensionRelationsMap S hS P₁ P₃ h hh k hk
  letI : Epi q := epi_extensionGeneratorsMap S hS P₁ P₃ h hh
  letI : Epi r := epi_extensionRelationsMap S hS P₁ P₃ h hh k hk
  refine presentationOfIsCokernelFree
    (r ≫ kernel.ι q) q (by simp) ?_
  exact isCokernelEpiComp
    (c := CokernelCofork.ofπ q (kernel.condition q))
    (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) r rfl

noncomputable instance extension_isFinite [P₁.IsFinite] [P₃.IsFinite] :
    (extension (hS := hS) S P₁ P₃ h hh k hk).IsFinite where
  isFiniteType_generators := by
    refine ⟨?_⟩
    change Finite (P₁.generators.I ⊕ P₃.generators.I)
    infer_instance
  isFiniteType_relations := by
    refine ⟨?_⟩
    change Finite (P₁.relations.I ⊕ P₃.relations.I)
    infer_instance

end Presentation

instance overFunctor_preservesZeroMorphisms (U : C) :
    (overFunctor R U).PreservesZeroMorphisms where

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
lemma ShortExact.map_over [HasBinaryProducts C]
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (S.map (overFunctor R U)).ShortExact := by
  haveI : (overFunctor R U).IsRightAdjoint := by
    change (pushforward.{u} (𝟙 (R.over U))).IsRightAdjoint
    infer_instance
  haveI : (overFunctor R U).IsLeftAdjoint := by
    change (pushforward.{u} (𝟙 (R.over U))).IsLeftAdjoint
    infer_instance
  exact hS.map_of_exact (overFunctor R U)

namespace Presentation

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 1600000 in
lemma correction_mapOver [HasBinaryProducts C]
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (P₃ : S.X₃.Presentation)
    (h : free P₃.generators.I ⟶ S.X₂)
    (hh : h ≫ S.g = P₃.generators.π) (U : C)
    [(J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)]
    (hhU :
      ((mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)).hom ≫
          (overFunctor R U).map h) ≫
        (S.map (overFunctor R U)).g = (P₃.mapOver U).generators.π) :
    (mapFreeIso (overFunctor R U) P₃.relations.I (overUnitIso U)).hom ≫
        (overFunctor R U).map (correction S hS P₃ h hh) =
      correction (S.map (overFunctor R U)) (ShortExact.map_over hS U) (P₃.mapOver U)
        ((mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)).hom ≫
          (overFunctor R U).map h) hhU := by
  haveI : Mono (S.map (overFunctor R U)).f :=
    (ShortExact.map_over hS U).mono_f
  apply (cancel_mono (S.map (overFunctor R U)).f).1
  have hleft :
      ((mapFreeIso (overFunctor R U) P₃.relations.I (overUnitIso U)).hom ≫
            (overFunctor R U).map (correction S hS P₃ h hh)) ≫
          (S.map (overFunctor R U)).f =
        relationMap (P₃.mapOver U) ≫
          ((mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)).hom ≫
            (overFunctor R U).map h) := by
    rw [ShortComplex.map_f]
    rw [Category.assoc]
    change (mapFreeIso (overFunctor R U) P₃.relations.I (overUnitIso U)).hom ≫
        ((overFunctor R U).map (correction S hS P₃ h hh) ≫
          (overFunctor R U).map S.f) = _
    rw [← Functor.map_comp, correction_comp S hS P₃ h hh]
    rw [relationMap_mapOver]
    let e := mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)
    let a := (mapFreeIso (overFunctor R U) P₃.relations.I (overUnitIso U)).hom ≫
      (overFunctor R U).map (relationMap P₃)
    change a ≫ (overFunctor R U).map h =
      (a ≫ e.inv) ≫ e.hom ≫ (overFunctor R U).map h
    simp [Category.assoc]
  exact hleft.trans <| (correction_comp (S.map (overFunctor R U))
    (ShortExact.map_over hS U) (P₃.mapOver U) _ hhU).symm

end Presentation

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 1600000 in
lemma mapOver_lift_comp [HasBinaryProducts C]
    {S : ShortComplex (SheafOfModules.{u} R)}
    (P₃ : S.X₃.Presentation)
    (h : free P₃.generators.I ⟶ S.X₂)
    (hh : h ≫ S.g = P₃.generators.π) (U : C)
    [(J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R U)] :
    ((mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)).hom ≫
        (overFunctor R U).map h) ≫ (S.map (overFunctor R U)).g =
      (P₃.mapOver U).generators.π := by
  rw [Category.assoc]
  change (mapFreeIso (overFunctor R U) P₃.generators.I (overUnitIso U)).hom ≫
    ((overFunctor R U).map h ≫ (overFunctor R U).map S.g) = _
  rw [← Functor.map_comp, hh]
  exact (Presentation.map_π_eq P₃ (overFunctor R U) (overUnitIso U)).symm

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 1600000 in
lemma localLift_comp_mapOver [HasBinaryProducts C]
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Epi f]
    (P : N.Presentation) [P.IsFinite]
    (a : Σ X, (simultaneousImageCover f P.generators.s X).Arrow)
    [(J.over a.2.Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over a.2.Y) AddCommGrpCat.{u}]
    [(J.over a.2.Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R a.2.Y)] :
    localLift f P.generators.s a ≫ (overFunctor R a.2.Y).map f =
      (P.mapOver a.2.Y).generators.π :=
  (localLift_comp f P.generators.s a).trans <|
    (Presentation.map_π_eq P (overFunctor R a.2.Y) (overUnitIso a.2.Y)).symm

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 1600000 in
lemma localLift_mapOver_generators_comp [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : M.Presentation)
    {I : Type u} [Finite I] (s : I → M.sections)
    (a : Σ X, (simultaneousImageCover P.generators.π s X).Arrow)
    [(J.over a.2.Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasSheafify (J.over a.2.Y) AddCommGrpCat.{u}]
    [(J.over a.2.Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfSize.{u, u} (overFunctor R a.2.Y)] :
    (localLift P.generators.π s a ≫
        (mapFreeIso (overFunctor R a.2.Y) P.generators.I
          (overUnitIso a.2.Y)).inv) ≫
      (P.mapOver a.2.Y).generators.π =
        (mapFreeIso (overFunctor R a.2.Y) I (overUnitIso a.2.Y)).hom ≫
          (overFunctor R a.2.Y).map (M.freeHomEquiv.symm s) := by
  have h₁ :
      (localLift P.generators.π s a ≫
          (mapFreeIso (overFunctor R a.2.Y) P.generators.I
            (overUnitIso a.2.Y)).inv) ≫
        (P.mapOver a.2.Y).generators.π =
      localLift P.generators.π s a ≫
        (overFunctor R a.2.Y).map P.generators.π := by
    change (localLift P.generators.π s a ≫
        (mapFreeIso (overFunctor R a.2.Y) P.generators.I
          (overUnitIso a.2.Y)).inv) ≫
      (P.map (overFunctor R a.2.Y) (overUnitIso a.2.Y)).generators.π = _
    rw [Presentation.map_π_eq]
    simp
  exact h₁.trans (localLift_comp P.generators.π s a)

section Extensions

variable [HasBinaryProducts C] [HasPullbacks C]
  [hasSheafComposeOver : ∀ X,
    (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOver : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hasWeakSheafifyOver : ∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOver : ∀ X,
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hasSheafComposeOverOver : ∀ X Y, ((J.over X).over Y).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOverOver : ∀ X Y,
    HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [hasWeakSheafifyOverOver : ∀ X Y,
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOverOver : ∀ X Y,
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance (X : C) : HasBinaryProducts (Over X) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  hasSheafComposeOverOver in
set_option maxHeartbeats 3200000 in
/-- After the quotient generators have been lifted, one further finite cover lifts the
correction relations and produces a finite presentation of the middle term. -/
theorem IsFinitePresentation.middle_of_presentations_of_generatorLift
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (P₁ : S.X₁.Presentation) (P₃ : S.X₃.Presentation)
    (hP₁ : P₁.IsFinite) (hP₃ : P₃.IsFinite)
    (h : free (R := R) P₃.generators.I ⟶ S.X₂)
    (hh : h ≫ S.g = P₃.generators.π) : IsFinitePresentation S.X₂ := by
  letI := hP₁
  letI := hP₃
  let c : free (R := R) P₃.relations.I ⟶ S.X₁ :=
    Presentation.correction S hS P₃ h hh
  apply IsFinitePresentation.of_coversTop S.X₂
    (simultaneousImageCoverObjects P₁.generators.π (S.X₁.freeHomEquiv c))
    (simultaneousImageCoverObjects_coversTop P₁.generators.π
      (S.X₁.freeHomEquiv c))
  intro b
  haveI : PreservesColimitsOfSize.{u, u} (overFunctor R b.2.Y) := by
    change PreservesColimitsOfSize.{u, u} (pushforward.{u} (𝟙 (R.over b.2.Y)))
    exact preservesColimitsOfSize_shrink.{u, u, u, u} _
  let Sᵥ := S.map (overFunctor R b.2.Y)
  let hSᵥ := ShortExact.map_over hS b.2.Y
  let P₁ᵥ := P₁.mapOver b.2.Y
  let P₃ᵥ := P₃.mapOver b.2.Y
  let hᵥ : free (R := R.over b.2.Y) P₃.generators.I ⟶ Sᵥ.X₂ :=
    (mapFreeIso (overFunctor R b.2.Y) P₃.generators.I (overUnitIso b.2.Y)).hom ≫
      (overFunctor R b.2.Y).map h
  have hhᵥ : hᵥ ≫ Sᵥ.g = P₃ᵥ.generators.π := by
    exact mapOver_lift_comp P₃ h hh b.2.Y
  let k : free (R := R.over b.2.Y) P₃.relations.I ⟶
      free (R := R.over b.2.Y) P₁.generators.I :=
    localLift P₁.generators.π (S.X₁.freeHomEquiv c) b ≫
      (mapFreeIso (overFunctor R b.2.Y) P₁.generators.I (overUnitIso b.2.Y)).inv
  have hk : k ≫ P₁ᵥ.generators.π =
      Presentation.correction Sᵥ hSᵥ P₃ᵥ hᵥ hhᵥ := by
    have hk₀ := localLift_mapOver_generators_comp P₁ (S.X₁.freeHomEquiv c) b
    have hk₁ : k ≫ P₁ᵥ.generators.π =
        (mapFreeIso (overFunctor R b.2.Y) P₃.relations.I
            (overUnitIso b.2.Y)).hom ≫ (overFunctor R b.2.Y).map c := by
      simpa only [k, P₁ᵥ, Equiv.symm_apply_apply] using hk₀
    exact hk₁.trans <|
      Presentation.correction_mapOver hS P₃ h hh b.2.Y hhᵥ
  change IsFinitePresentation Sᵥ.X₂
  let P := Presentation.extension Sᵥ hSᵥ P₁ᵥ P₃ᵥ hᵥ hhᵥ k hk
  letI : P.IsFinite := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_⟩
      change Finite (P₁.generators.I ⊕ P₃.generators.I)
      infer_instance
    · refine ⟨?_⟩
      change Finite (P₁.relations.I ⊕ P₃.relations.I)
      infer_instance
  exact IsFinitePresentation.of_presentation P

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
set_option maxHeartbeats 3200000 in
/-- The middle term of a short exact sequence has finite presentation when both endpoints
have finite global presentations. -/
theorem IsFinitePresentation.middle_of_presentations
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (P₁ : S.X₁.Presentation) (P₃ : S.X₃.Presentation)
    (hP₁ : P₁.IsFinite) (hP₃ : P₃.IsFinite) : IsFinitePresentation S.X₂ := by
  letI := hP₁
  letI := hP₃
  letI : Epi S.g := hS.epi_g
  apply IsFinitePresentation.of_coversTop S.X₂
    (simultaneousImageCoverObjects S.g P₃.generators.s)
    (simultaneousImageCoverObjects_coversTop S.g P₃.generators.s)
  intro a
  haveI : PreservesColimitsOfSize.{u, u} (overFunctor R a.2.Y) := by
    change PreservesColimitsOfSize.{u, u} (pushforward.{u} (𝟙 (R.over a.2.Y)))
    exact preservesColimitsOfSize_shrink.{u, u, u, u} _
  let Sᵤ := S.map (overFunctor R a.2.Y)
  let hSᵤ := ShortExact.map_over hS a.2.Y
  let P₁ᵤ := P₁.mapOver a.2.Y
  let P₃ᵤ := P₃.mapOver a.2.Y
  let h : free (R := R.over a.2.Y) P₃.generators.I ⟶ Sᵤ.X₂ :=
    localLift S.g P₃.generators.s a
  have hh : h ≫ Sᵤ.g = P₃ᵤ.generators.π := by
    exact localLift_comp_mapOver S.g P₃ a
  exact IsFinitePresentation.middle_of_presentations_of_generatorLift
    hSᵤ P₁ᵤ P₃ᵤ
      (Presentation.mapOver_isFinite P₁ a.2.Y)
      (Presentation.mapOver_isFinite P₃ a.2.Y) h hh

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  hasSheafComposeOver in
set_option maxHeartbeats 9600000 in
/-- Finite presentation of sheaves of modules is closed under extensions. -/
theorem IsFinitePresentation.middle_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (h₁ : IsFinitePresentation S.X₁) (h₃ : IsFinitePresentation S.X₃) :
    IsFinitePresentation S.X₂ := by
  obtain ⟨q₃, hq₃⟩ := h₃.exists_quasicoherentData
  letI (i : q₃.I) : (q₃.presentation i).IsFinite :=
    hq₃.isFinite_presentation i
  apply IsFinitePresentation.of_coversTop S.X₂ q₃.X q₃.coversTop
  intro i
  let Sᵢ := S.map (overFunctor R (q₃.X i))
  let hSᵢ := ShortExact.map_over hS (q₃.X i)
  have h₁ᵢ : IsFinitePresentation Sᵢ.X₁ := h₁.over (q₃.X i)
  obtain ⟨q₁, hq₁⟩ := h₁ᵢ.exists_quasicoherentData
  letI (j : q₁.I) : (q₁.presentation j).IsFinite :=
    hq₁.isFinite_presentation j
  apply IsFinitePresentation.of_coversTop Sᵢ.X₂ q₁.X q₁.coversTop
  intro j
  haveI : PreservesColimitsOfSize.{u, u}
      (overFunctor (R.over (q₃.X i)) (q₁.X j)) := by
    change PreservesColimitsOfSize.{u, u}
      (pushforward.{u} (𝟙 ((R.over (q₃.X i)).over (q₁.X j))))
    exact preservesColimitsOfSize_shrink.{u, u, u, u} _
  let Sᵢⱼ := Sᵢ.map (overFunctor (R.over (q₃.X i)) (q₁.X j))
  let hSᵢⱼ := ShortExact.map_over hSᵢ (q₁.X j)
  let P₃ := (q₃.presentation i).mapOver (q₁.X j)
  exact IsFinitePresentation.middle_of_presentations hSᵢⱼ
    (q₁.presentation j) P₃ (hq₁.isFinite_presentation j)
      (Presentation.mapOver_isFinite (q₃.presentation i) (q₁.X j))

noncomputable instance isFinitePresentation_isClosedUnderExtensions :
    (isFinitePresentation R).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    IsFinitePresentation.middle_of_shortExact hS h₁ h₃

end Extensions

end SheafOfModules
