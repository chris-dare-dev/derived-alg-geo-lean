/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Picard
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CoversTop
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Invertible
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Tensor
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Tensor descent for scheme module sheaves

This file compares restriction with module sheafification, proves closure of invertible scheme
module sheaves under the sheafified tensor product, and constructs the resulting associator.

The intrinsic rank-one property and arbitrary-site tensor descent are imported from
`Algebra.Category.ModuleCat.Sheaf`; the stronger stalkwise tensor result is imported from
`Topology.Sheaves.ModuleTensor`. This module begins only when the scheme-indexed module category
and its topological site enter the signatures.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

local instance : MonoidalCategory
    (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance : SymmetricCategory
    (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private abbrev associatedSheaf' (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

private abbrev overPresheafFunctor (X : Scheme.{u}) (U : X.Opens) :=
  PresheafOfModules.pushforward
    (𝟙 (X.ringCatSheaf.over U).obj)

/-- Restriction of an associated module sheaf is the associated sheaf of the restriction. -/
noncomputable def overSheafificationComparison
    (P : X.PresheafOfModules) (U : X.Opens) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj
        ((overPresheafFunctor X U).obj P) ⟶
      ((associatedSheaf' X).obj P).over U :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).map
      ((overPresheafFunctor X U).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P)) ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
        (((associatedSheaf' X).obj P).over U)

private lemma overSheafificationUnit_mem_W
    (P : X.PresheafOfModules) (U : X.Opens) :
    (_root_.Opens.grothendieckTopology X).over U |>.W
      ((PresheafOfModules.toPresheaf _).map
        ((overPresheafFunctor X U).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P))) := by
  let K := _root_.Opens.grothendieckTopology X
  let F := overPresheafFunctor X U
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  let g := F.map η
  have hη : K.W ((PresheafOfModules.toPresheaf _).map η) := by
    dsimp only [η]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact K.W_toSheafify P.presheaf
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map η) := hη.isLocallyInjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map η) := hη.isLocallySurjective
  haveI hi : Presheaf.IsLocallyInjective (K.over U)
      ((PresheafOfModules.toPresheaf _).map g) := by
    change Presheaf.IsLocallyInjective (K.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf _).map η))
    exact Presheaf.isLocallyInjective_whisker (K.over U) K
      (Over.forget U) _
  haveI hs : Presheaf.IsLocallySurjective (K.over U)
      ((PresheafOfModules.toPresheaf _).map g) := by
    change Presheaf.IsLocallySurjective (K.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf _).map η))
    exact Presheaf.isLocallySurjective_whisker (K.over U) K
      (Over.forget U) _
  exact (K.over U).W_of_isLocallyBijective _

private lemma isIso_overSheafificationUnit_map
    (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).map
        ((overPresheafFunctor X U).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P))) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj))
    (((_root_.Opens.grothendieckTopology X).over U).W.inverseImage
      (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj))
  exact overSheafificationUnit_mem_W P U

lemma isIso_overSheafificationComparison
    (P : X.PresheafOfModules) (U : X.Opens) :
    IsIso (overSheafificationComparison P U) := by
  haveI : IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit := by
    infer_instance
  dsimp only [overSheafificationComparison]
  apply IsIso.comp_isIso'
  · exact isIso_overSheafificationUnit_map P U
  · exact NatIso.isIso_app_of_isIso _ _

set_option maxHeartbeats 800000 in
private noncomputable def tensorPresheaf'
    (X : Scheme.{u}) (P Q : X.PresheafOfModules) : X.PresheafOfModules := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact P ⊗ Q

set_option maxHeartbeats 800000 in
/-- Restriction of the objectwise tensor presheaf is the tensor of the restrictions. -/
noncomputable def overTensorPresheafIso
    (P Q : X.PresheafOfModules) (U : X.Opens) :
    letI : MonoidalCategory
        (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
      PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
    (overPresheafFunctor X U).obj (tensorPresheaf' X P Q) ≅
      (overPresheafFunctor X U).obj P ⊗ (overPresheafFunctor X U).obj Q := by
  exact Iso.refl _

/-- The tensor product is trivial on an open where both factors are trivial. -/
noncomputable def tensorOverIsoOfTrivializations
    (L M : X.Modules) (U : X.Opens)
    (eL : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ L.over U)
    (eM : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    (tensorObj L M).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let eLP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eL
  let eMP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eM
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overTensorPresheafIso
      ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj M) U) ≪≫
    aU.mapIso (MonoidalCategory.tensorIso eLP.symm eMP.symm) ≪≫
    aU.mapIso (λ_ _) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit).app
        (SheafOfModules.unit (X.ringCatSheaf.over U))

set_option maxHeartbeats 1600000 in
/-- **Tensoring with a sheaf that is trivial on `U` does nothing to the restriction to `U`.**

The one-sided companion of `tensorOverIsoOfTrivializations`, which needs *both*
factors trivial and lands on the unit. Here only the right factor is trivialized
and the left one is arbitrary, so the right unitor replaces the left one and the
result is `L.over U` rather than the unit.

This is the shape a twist consumes: `F(n) = F ⊗ O(n)` restricted to a chart where
`O(n)` is trivial is just `F` restricted to that chart, with `F` arbitrary. -/
noncomputable def tensorOverIsoOfTrivializationRight
    (L M : X.Modules) (U : X.Opens)
    (eM : SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) :
    (tensorObj L M).over U ≅ L.over U := by
  letI : MonoidalCategory
      (_root_.PresheafOfModules.{u} (X.ringCatSheaf.over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let eMP := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso eM
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) U
  let cL := overSheafificationComparison ((toPresheafOfModules X).obj L) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overTensorPresheafIso
      ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj M) U) ≪≫
    aU.mapIso (MonoidalCategory.tensorIso (Iso.refl _) eMP.symm) ≪≫
    aU.mapIso (ρ_ _) ≪≫
    (@asIso _ _ _ _ cL (isIso_overSheafificationComparison _ _)) ≪≫
    (SheafOfModules.overFunctor _ _).mapIso
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app L)

set_option maxHeartbeats 1600000 in
/-- The sheafified tensor product of invertible sheaves is invertible. -/
lemma isInvertible_tensorObj (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from tensorObj L M) := by
  obtain ⟨qL, hqL, hrankL⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from L)
  obtain ⟨qM, hqM, hrankM⟩ :=
    SheafOfModules.IsInvertible.exists_rankOneData
      (M := show SheafOfModules X.ringCatSheaf from M)
  letI : qL.IsLocallyFreeData := hqL
  letI : qM.IsLocallyFreeData := hqM
  let Y : qL.I × qM.I → X.Opens := fun k : qL.I × qM.I =>
    qL.X k.1 ⊓ qM.X k.2
  have hYL : ⨆ i, qL.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (X : Type u) qL.X).mp qL.coversTop
  have hYM : ⨆ i, qM.X i = ⊤ :=
    (_root_.Opens.coversTop_iff (X : Type u) qM.X).mp qM.coversTop
  have hY : (_root_.Opens.grothendieckTopology X).CoversTop Y := by
    rw [_root_.Opens.coversTop_iff]
    change ⨆ k : qL.I × qM.I, qL.X k.1 ⊓ qM.X k.2 = ⊤
    rw [← iSup_inf_iSup, hYL, hYM, inf_top_eq]
  apply SheafOfModules.IsInvertible.of_trivializations Y hY
  intro k
  exact (tensorOverIsoOfTrivializations L M (Y k)
    (qL.rankOneTrivializationOver hrankL k.1
      (homOfLE inf_le_left))
    (qM.rankOneTrivializationOver hrankM k.2
      (homOfLE inf_le_right))).symm

attribute [instance] isInvertible_tensorObj

/-- **Sheafification inverts `M ◁ toSheafify` for an arbitrary `M`.**

The general form of `SheafOfModules.isIso_sheafification_map_whiskerLeft_unit_of_rankOneData`,
with the rank-one hypothesis on the whiskering factor gone. It is available here and not over a
general site because the proof is stalkwise; see
`PresheafOfModules.W_whiskerLeft_of_isIso_stalk`. -/
lemma isIso_sheafification_map_whiskerLeft_unit (M P : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (M ◁ (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    ((_root_.Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
  apply PresheafOfModules.W_whiskerLeft_of_isIso_stalk (R := X.presheaf)
  intro x
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf

/-- Comparison from tensoring before sheafification to tensoring with the associated sheaf. -/
noncomputable def tensorSheafificationComparisonLeft
    (L : X.Modules) (P : X.PresheafOfModules) :
    (associatedSheaf' X).obj ((toPresheafOfModules X).obj L ⊗ P) ⟶
      tensorObj L ((associatedSheaf' X).obj P) :=
  (associatedSheaf' X).map
    ((toPresheafOfModules X).obj L ◁
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)

/-- Right-handed comparison from tensoring before sheafification. -/
noncomputable def tensorSheafificationComparisonRight
    (P : X.PresheafOfModules) (L : X.Modules) :
    (associatedSheaf' X).obj (P ⊗ (toPresheafOfModules X).obj L) ⟶
      tensorObj ((associatedSheaf' X).obj P) L :=
  (associatedSheaf' X).map
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ▷
        (toPresheafOfModules X).obj L)

/-- The left comparison is an isomorphism for **arbitrary** `L`.

The invertibility hypothesis this carried until #833 was an artifact of proving local
injectivity and local surjectivity separately: the injective half then needed `L` locally
trivial. Going through stalks avoids the split — see
`isIso_sheafification_map_whiskerLeft_unit`. -/
lemma isIso_tensorSheafificationComparisonLeft (L : X.Modules) (P : X.PresheafOfModules) :
    IsIso (tensorSheafificationComparisonLeft L P) :=
  isIso_sheafification_map_whiskerLeft_unit ((toPresheafOfModules X).obj L) P

set_option backward.isDefEq.respectTransparency false in
/-- The right comparison is an isomorphism for arbitrary `L`.

The left comparison is already invertible without a finiteness or flatness hypothesis. Symmetry of
the objectwise tensor conjugates the right comparison to that left comparison, so the same result
holds on the other side. This removes the last rank-one restriction from associativity of the
sheafified tensor product. -/
lemma isIso_tensorSheafificationComparisonRight (P : X.PresheafOfModules) (L : X.Modules) :
    IsIso (tensorSheafificationComparisonRight P L) := by
  let a := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let U := (toPresheafOfModules X).obj L
  let V := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
    SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  have hNat := BraidedCategory.braiding_naturality_right U eta
  have h : eta ▷ U =
      (β_ P U).hom ≫ (U ◁ eta) ≫ (β_ U V).hom := by
    symm
    dsimp only [V]
    calc
      (β_ P U).hom ≫ (U ◁ eta) ≫ (β_ U V).hom =
          (β_ P U).hom ≫
            (β_ U ((𝟭 X.PresheafOfModules).obj P)).hom ≫ (eta ▷ U) := by
              rw [hNat]
      _ = eta ▷ U := by
        change (β_ P U).hom ≫ (β_ U P).hom ≫ (eta ▷ U) = eta ▷ U
        simp
  haveI hMiddle : IsIso (a.map (U ◁ eta)) := by
    change IsIso (tensorSheafificationComparisonLeft L P)
    exact isIso_tensorSheafificationComparisonLeft L P
  change IsIso (a.map (eta ▷ U))
  rw [h, Functor.map_comp, Functor.map_comp]
  infer_instance

attribute [instance] isIso_tensorSheafificationComparisonLeft
  isIso_tensorSheafificationComparisonRight

/-- Associativity of the sheafified tensor product for arbitrary module sheaves. -/
noncomputable def tensorAssocIso (L M N : X.Modules) :
    tensorObj (tensorObj L M) N ≅ tensorObj L (tensorObj M N) := by
  let cR := tensorSheafificationComparisonRight
    ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M) N
  let cL := tensorSheafificationComparisonLeft L
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)
  exact (@asIso _ _ _ _ cR
      (isIso_tensorSheafificationComparisonRight _ _)).symm ≪≫
    tensorTripleAssocIso L M N ≪≫
    @asIso _ _ _ _ cL (isIso_tensorSheafificationComparisonLeft _ _)

end


end AlgebraicGeometry.Scheme.Modules
