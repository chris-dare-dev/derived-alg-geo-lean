/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Invertible sheaves of modules on a ringed site

This file defines an invertible sheaf of modules intrinsically as a sheaf that is locally free
of rank one. The definition and its local trivializations use only a sheaf of rings on an
arbitrary Grothendieck site; scheme Picard groups and tensor products are downstream consumers.

## Main declarations

* `SheafOfModules.LocalGeneratorsData.IsRankOne`: every local basis is a singleton;
* `SheafOfModules.IsInvertible`: local freeness of rank one;
* `SheafOfModules.LocalGeneratorsData.rankOneTrivialization`: the resulting local
  identification with the unit sheaf;
* `SheafOfModules.IsInvertible.of_trivializations`: reconstruction from a covering family of
  local trivializations.
-/

open CategoryTheory Limits

namespace SheafOfModules

universe u v u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable section

/-- A free sheaf on one generator is the unit sheaf. -/
noncomputable def freePUnitIsoUnit : free (R := R) PUnit ≅ unit R := by
  let e : free (R := R) PUnit ⟶ unit R :=
    (freeHomEquiv (unit R)).symm
      (fun _ => (unit R).unitHomEquiv (𝟙 (unit R)))
  have h : ιFree (R := R) PUnit.unit ≫ e = 𝟙 (unit R) := by
    rw [← unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [e, Equiv.apply_symm_apply]
    exact (unit R).unitHomEquiv.symm_apply_apply _
  exact
    { hom := e
      inv := ιFree PUnit.unit
      hom_inv_id := by
        apply (freeHomEquiv (free (R := R) PUnit)).injective
        funext i
        cases i
        apply (free (R := R) PUnit).unitHomEquiv.symm.injective
        rw [unitHomEquiv_symm_freeHomEquiv_apply,
          unitHomEquiv_symm_freeHomEquiv_apply]
        have hh := reassoc_of% h
        exact hh (ιFree (R := R) PUnit.unit)
      inv_hom_id := h }

section RankOne

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- Local generator data has rank one when every local basis index is a singleton. -/
def IsRankOne {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) : Prop :=
  ∀ i, Nonempty (q.generators i).I ∧ Subsingleton (q.generators i).I

/-- Transport local generator data across an isomorphism. -/
noncomputable def ofIso {M N : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (e : M ≅ N) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (GeneratingSections.equivOfIso
    ((overFunctor R (q.X i)).mapIso e)) (q.generators i)

instance {M N : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] (e : M ≅ N) : (q.ofIso e).IsLocallyFreeData where
  isIso i := by
    change q.I at i
    change IsIso ((q.generators i).ofEpi
      ((overFunctor R (q.X i)).mapIso e).hom).π
    rw [GeneratingSections.ofEpi_π]
    haveI : IsIso (q.generators i).π :=
      LocalGeneratorsData.IsLocallyFreeData.isIso i
    haveI : IsIso (((overFunctor R (q.X i)).mapIso e).hom) := by
      infer_instance
    exact IsIso.comp_isIso'
      (LocalGeneratorsData.IsLocallyFreeData.isIso i) inferInstance

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transporting local generator data along an isomorphism preserves the rank-one condition. -/
lemma isRankOne_ofIso {M N : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (e : M ≅ N) (h : q.IsRankOne) :
    (q.ofIso e).IsRankOne := by
  intro i
  simpa [ofIso, GeneratingSections.equivOfIso] using h i

end LocalGeneratorsData

/-- An invertible sheaf is locally free of rank one. -/
class IsInvertible (M : SheafOfModules.{u} R) : Prop where
  exists_rankOneData : ∃ q : LocalGeneratorsData.{u₁} M,
    q.IsLocallyFreeData ∧ q.IsRankOne

instance (priority := 90) (M : SheafOfModules.{u} R) [h : M.IsInvertible] :
    M.IsLocallyFree where
  exists_isLocallyFreeData :=
    ⟨h.exists_rankOneData.choose, h.exists_rankOneData.choose_spec.1⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Invertibility is invariant under isomorphism of module sheaves. -/
lemma IsInvertible.ofIso {M N : SheafOfModules.{u} R} [M.IsInvertible]
    (e : M ≅ N) : N.IsInvertible := by
  obtain ⟨q, hq, hrank⟩ := IsInvertible.exists_rankOneData (M := M)
  letI : q.IsLocallyFreeData := hq
  exact ⟨q.ofIso e, inferInstance, q.isRankOne_ofIso e hrank⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An invertible sheaf is finitely presented: its rank-one local bases give presentations
with one generator and no relations. -/
theorem IsInvertible.isFinitePresentation {M : SheafOfModules.{u} R} [M.IsInvertible]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq, hrank⟩ := IsInvertible.exists_rankOneData (M := M)
  letI : q.IsLocallyFreeData := hq
  refine ⟨q.quasiCoherentData, ?_⟩
  constructor
  intro i
  constructor
  · constructor
    change Finite (q.generators i).I
    letI : Nonempty (q.generators i).I := (hrank i).1
    letI : Subsingleton (q.generators i).I := (hrank i).2
    exact Finite.of_injective (fun _ => PUnit.unit)
      (fun _ _ _ => Subsingleton.elim _ _)
  · constructor
    dsimp [LocalGeneratorsData.quasiCoherentData]
    infer_instance

variable [HasSheafify J AddCommGrpCat.{u}] [HasBinaryProducts C]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]

instance : (free (R := R) PUnit).IsInvertible where
  exists_rankOneData := by
    let q := (free.generatingSections (R := R) PUnit).localGeneratorsData
    refine ⟨q, inferInstance, ?_⟩
    intro i
    change Nonempty PUnit ∧ Subsingleton PUnit
    exact ⟨inferInstance, inferInstance⟩

instance : (unit R).IsInvertible :=
  IsInvertible.ofIso freePUnitIsoUnit

end RankOne

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocalGeneratorsData

/-- The local trivialization determined by rank-one locally free generator data. -/
noncomputable def rankOneTrivialization {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (i : q.I) : unit (R.over (q.X i)) ≅ M.over (q.X i) := by
  letI : Nonempty (q.generators i).I := (hq i).1
  letI : Subsingleton (q.generators i).I := (hq i).2
  let i₀ : (q.generators i).I := Classical.choice (hq i).1
  letI : Unique (q.generators i).I := uniqueOfSubsingleton i₀
  let e := (q.generators i).π
  exact (freePUnitIsoUnit (R := R.over (q.X i))).symm ≪≫
    (freeFunctor (R := R.over (q.X i))).mapIso
      (Equiv.ofUnique PUnit (q.generators i).I).toIso ≪≫
    @asIso _ _ _ _ e (LocalGeneratorsData.IsLocallyFreeData.isIso i)

/-- Restrict a rank-one trivialization from a cover member to an object over it. -/
noncomputable def rankOneTrivializationOver {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (i : q.I) {Y : C} (f : Y ⟶ q.X i) :
    unit (R.over Y) ≅ M.over Y :=
  (overMapUnitIso f).symm ≪≫
    (overMap R f).mapIso (q.rankOneTrivialization hq i) ≪≫
    (overFunctorMap R f).app M

end LocalGeneratorsData

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A sheaf locally isomorphic to the structure sheaf on a covering family is invertible. -/
lemma IsInvertible.of_trivializations {M : SheafOfModules.{u} R}
    {I : Type u₁} (Y : I → C) (hY : J.CoversTop Y)
    (e : ∀ i, unit (R.over (Y i)) ≅ M.over (Y i)) : M.IsInvertible := by
  let q : M.LocalGeneratorsData :=
    { I := I
      X := Y
      coversTop := hY
      generators i :=
        { I := PUnit
          s := (M.over (Y i)).freeHomEquiv
            ((freePUnitIsoUnit (R := R.over (Y i))) ≪≫ e i).hom
          epi := by
            rw [Equiv.symm_apply_apply]
            infer_instance } }
  have hfree : q.IsLocallyFreeData := by
    constructor
    intro i
    change IsIso ((M.over (Y i)).freeHomEquiv.symm
      ((M.over (Y i)).freeHomEquiv
        ((freePUnitIsoUnit (R := R.over (Y i))) ≪≫ e i).hom))
    rw [Equiv.symm_apply_apply]
    infer_instance
  have hrank : q.IsRankOne := by
    intro i
    exact ⟨inferInstance, inferInstance⟩
  exact ⟨q, hfree, hrank⟩

end

end SheafOfModules
