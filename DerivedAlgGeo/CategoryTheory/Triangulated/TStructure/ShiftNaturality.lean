/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Shift
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Naturality of truncation--shift comparisons

The objectwise truncation--shift isomorphisms from `TStructure.Shift` assemble
into natural isomorphisms. The signs in their compatibility with the
truncation unit and counit cancel by centrality of scalar multiplication.
-/

universe v u

namespace CategoryTheory.Triangulated.TStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : CategoryTheory.Triangulated.TStructure C) (a n : ℤ)

/-- The `truncLT` shift comparison is natural in the object. -/
noncomputable def truncLTShiftNatIso :
    t.truncLT (a + n) ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙ t.truncLT a :=
  NatIso.ofComponents (fun X => truncLTShiftIso t a n X) (fun {X Y} f => by
    simp only [Functor.comp_map]
    have hLE : t.IsLE (((t.truncLT (a + n)).obj X)⟦n⟧) (a - 1) :=
      t.isLE_shift _ (a + n - 1) n (a - 1) (by lia)
    letI : t.IsLE ((t.truncLT (a + n) ⋙ shiftFunctor C n).obj X)
        (a - 1) := by simpa using hLE
    apply t.to_truncLT_obj_ext (n := a)
    change (((shiftFunctor C n).map ((t.truncLT (a + n)).map f) ≫
      (truncLTShiftIso t a n Y).hom) ≫
        (t.truncLTι a).app (Y⟦n⟧)) = _
    rw [Category.assoc] at ⊢
    rw [truncLTShiftIso_hom_comp_truncLTι]
    erw [Category.assoc]
    erw [(t.truncLTι a).naturality ((shiftFunctor C n).map f)]
    simp only [Functor.id_map]
    calc
      (shiftFunctor C n).map ((t.truncLT (a + n)).map f) ≫
          (n.negOnePow • (shiftFunctor C n).map
            ((t.truncLTι (a + n)).app Y)) =
          n.negOnePow • ((shiftFunctor C n).map
            ((t.truncLT (a + n)).map f) ≫
              (shiftFunctor C n).map ((t.truncLTι (a + n)).app Y)) := by
            rw [Linear.comp_units_smul]
      _ = n.negOnePow • (shiftFunctor C n).map
          (((t.truncLT (a + n)).map f) ≫
            (t.truncLTι (a + n)).app Y) := by rw [Functor.map_comp]
      _ = n.negOnePow • (shiftFunctor C n).map
          ((t.truncLTι (a + n)).app X ≫ f) := by
            exact congrArg
              (fun k => n.negOnePow • (shiftFunctor C n).map k)
              ((t.truncLTι (a + n)).naturality f)
      _ = n.negOnePow •
          ((shiftFunctor C n).map ((t.truncLTι (a + n)).app X) ≫
            (shiftFunctor C n).map f) := by rw [Functor.map_comp]
      _ = (n.negOnePow •
          (shiftFunctor C n).map ((t.truncLTι (a + n)).app X)) ≫
            (shiftFunctor C n).map f := by rw [Linear.units_smul_comp]
      _ = ((truncLTShiftIso t a n X).hom ≫
          (t.truncLTι a).app (X⟦n⟧)) ≫
            (shiftFunctor C n).map f := by
              exact congrArg (fun k => k ≫ (shiftFunctor C n).map f)
                (truncLTShiftIso_hom_comp_truncLTι t a n X).symm
      _ = (truncLTShiftIso t a n X).hom ≫
          (t.truncLTι a).app (X⟦n⟧) ≫
            (shiftFunctor C n).map f := Category.assoc ..)

/-- The `truncGE` shift comparison is natural in the object. -/
noncomputable def truncGEShiftNatIso :
    t.truncGE (a + n) ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙ t.truncGE a :=
  NatIso.ofComponents (fun X => truncGEShiftIso t a n X) (fun {X Y} f => by
    simp only [Functor.comp_map]
    have hinv : (shiftFunctor C n ⋙ t.truncGE a).map f ≫
        (truncGEShiftIso t a n Y).inv =
        (truncGEShiftIso t a n X).inv ≫
          (t.truncGE (a + n) ⋙ shiftFunctor C n).map f := by
      letI : t.IsGE (((t.truncGE (a + n)).obj Y)⟦n⟧) a :=
        t.isGE_shift _ (a + n) n a (by lia)
      apply t.from_truncGE_obj_ext (n := a)
      change (t.truncGEπ a).app (X⟦n⟧) ≫
        ((t.truncGE a).map ((shiftFunctor C n).map f) ≫ _) = _
      rw [← Category.assoc]
      rw [← (t.truncGEπ a).naturality ((shiftFunctor C n).map f)]
      simp only [Functor.id_obj, Functor.id_map]
      let common := n.negOnePow • (shiftFunctor C n).map
        ((t.truncGEπ (a + n)).app X ≫ (t.truncGE (a + n)).map f)
      have hleft : (((shiftFunctor C n).map f ≫
          (t.truncGEπ a).app (Y⟦n⟧)) ≫
            (truncGEShiftIso t a n Y).inv) = common := by
        erw [Category.assoc]
        exact ((congrArg (fun k => (shiftFunctor C n).map f ≫ k)
          (truncGEπ_comp_truncGEShiftIso_inv t a n Y)).trans <| by
        calc
          (shiftFunctor C n).map f ≫ (n.negOnePow •
              (shiftFunctor C n).map ((t.truncGEπ (a + n)).app Y)) =
              n.negOnePow • ((shiftFunctor C n).map f ≫
                (shiftFunctor C n).map ((t.truncGEπ (a + n)).app Y)) :=
                Linear.comp_units_smul _ _ _
          _ = n.negOnePow • (shiftFunctor C n).map
              (f ≫ (t.truncGEπ (a + n)).app Y) := by rw [Functor.map_comp]
          _ = common := by
            dsimp [common]
            exact congrArg
              (fun k => n.negOnePow • (shiftFunctor C n).map k)
              ((t.truncGEπ (a + n)).naturality f))
      have hright : (t.truncGEπ a).app (X⟦n⟧) ≫
          ((truncGEShiftIso t a n X).inv ≫
            (shiftFunctor C n).map ((t.truncGE (a + n)).map f)) = common := by
        rw [← Category.assoc]
        rw [truncGEπ_comp_truncGEShiftIso_inv]
        exact (Linear.units_smul_comp _ _ _).trans (by
          dsimp [common]
          rw [← Functor.map_comp])
      exact hleft.trans hright.symm
    have hfinal : (truncGEShiftIso t a n X).inv ≫
        (shiftFunctor C n).map ((t.truncGE (a + n)).map f) ≫
          (truncGEShiftIso t a n Y).hom =
        (t.truncGE a).map ((shiftFunctor C n).map f) := by
      rw [← Category.assoc]
      exact (congrArg (fun k => k ≫ (truncGEShiftIso t a n Y).hom)
        hinv.symm).trans ((Iso.comp_inv_eq
          (truncGEShiftIso t a n Y)).mp rfl).symm
    exact (Iso.inv_comp_eq (truncGEShiftIso t a n X)).mp hfinal)

/-- The `truncLE` shift comparison, obtained from `truncLTShiftNatIso` by the
canonical identification `truncLE a ≅ truncLT (a + 1)`. -/
noncomputable def truncLEShiftNatIso :
    t.truncLE (a + n) ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙ t.truncLE a :=
  Functor.isoWhiskerRight
      (t.truncLEIsoTruncLT (a + n) ((a + 1) + n) (by lia))
      (shiftFunctor C n) ≪≫
    truncLTShiftNatIso t (a + 1) n ≪≫
    Functor.isoWhiskerLeft (shiftFunctor C n)
      (t.truncLEIsoTruncLT a (a + 1) rfl).symm

/-- Pure truncation commutes naturally with the shift. -/
noncomputable def truncGELEShiftNatIso :
    t.truncGELE (a + n) (a + n) ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙ t.truncGELE a a :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (t.truncLE (a + n))
      (truncGEShiftNatIso t a n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (truncLEShiftNatIso t a n) (t.truncGE a) ≪≫
    Functor.associator _ _ _

end CategoryTheory.Triangulated.TStructure
