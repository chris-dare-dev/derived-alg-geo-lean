/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Preadditive.CompactObject
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Compact objects in a triangulated category

Compact objects form a thick triangulated subcategory.  The extension step is
the five lemma applied to the compactness comparison maps and the long exact
Hom sequence of a distinguished triangle.  Closure under retracts is proved by
observing that the comparison map for a retract is itself a retract in the
arrow category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite
open scoped ZeroObject

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace AddCommGrpCat

/-- Exact coproducts in additive commutative groups may be indexed in the
universe immediately below the carrier universe. -/
instance hasCoproductsSucc :
    HasCoproducts.{u} AddCommGrpCat.{u + 1} :=
  hasCoproducts_shrink.{u, u + 1}

instance ab4OfSizeSucc : AB4OfSize.{u} AddCommGrpCat.{u + 1} :=
  AB4OfSize_shrink.{u, u + 1} _

end AddCommGrpCat

namespace ShortComplex

variable {J : Type*} [Category J]

private lemma exact_of_eval (S : ShortComplex (J ⥤ AddCommGrpCat))
    (hS : ∀ j : J,
      (S.map ((evaluation J AddCommGrpCat).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  ext j x
  dsimp
  have hx : S.g.app j ((kernel.ι S.g).app j x) = 0 := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (kernel.condition S.g) j) x
    change S.g.app j ((kernel.ι S.g).app j x) = 0 at h
    exact h
  obtain ⟨y, hy⟩ :=
    ((S.map ((evaluation J AddCommGrpCat).obj j)).ab_exact_iff.mp (hS j)) _ hx
  rw [← hy]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cokernel.condition S.f) j) y
  change (cokernel.π S.f).app j (S.f.app j y) = 0 at h
  exact h

end ShortComplex

namespace IsCompactObject

variable {K : C} (hK : IsCompactObject.{w} K)
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

include hK

/-- A shift of a compact object is compact in the same indexing universe. -/
theorem shift (n : ℤ) : IsCompactObject.{w} (K⟦n⟧) := by
  let adj : shiftFunctor C n ⊣ shiftFunctor C (-n) :=
    (shiftEquiv C n).toAdjunction
  have hpres : (shiftFunctor C (-n)).PreservesSmallCoproducts.{w} :=
    fun _ => inferInstance
  exact adj.isCompactObject_leftAdjoint_obj hpres hK

end IsCompactObject

private instance : (preadditiveYoneda (C := C)).flip.Additive where
  map_add {X Y} f g := by
    ext X x
    change (f + g).unop ≫ x = f.unop ≫ x + g.unop ≫ x
    rw [unop_add, Preadditive.add_comp]

private def homDiagram {ι : Type w} (D : Discrete ι ⥤ C) :
    Cᵒᵖ ⥤ Discrete ι ⥤ AddCommGrpCat.{v} :=
  preadditiveYoneda.flip ⋙
    (Functor.whiskeringLeft (Discrete ι) C AddCommGrpCat).obj D

private instance {ι : Type w} (D : Discrete ι ⥤ C) :
    (homDiagram D).Additive := by
  dsimp [homDiagram]
  infer_instance

omit [Preadditive C] in
private lemma colimitPost_naturality {ι : Type w}
    (D : Discrete ι ⥤ C) {F G : C ⥤ AddCommGrpCat.{v}} (α : F ⟶ G)
    [HasColimit D] [HasColimit (D ⋙ F)] [HasColimit (D ⋙ G)] :
    colimit.post D F ≫ α.app (colimit D) =
      colimMap (Functor.whiskerLeft D α) ≫ colimit.post D G := by
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
  exact α.naturality _

private lemma colimit_preadditiveYoneda_exact {ι : Type w}
    (D : Discrete ι ⥤ C)
    [HasColimitsOfShape (Discrete ι) AddCommGrpCat.{v}]
    [HasExactColimitsOfShape (Discrete ι) AddCommGrpCat.{v}]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (((shortComplexOfDistTriangle T hT).op.map (homDiagram D)).map
      (colim : (Discrete ι ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})).Exact := by
  let S := (shortComplexOfDistTriangle T hT).op.map (homDiagram D)
  have hS : S.Exact := by
    apply ShortComplex.exact_of_eval
    intro j
    change
      (((shortComplexOfDistTriangle T hT).op.map
        (preadditiveYoneda.obj (D.obj j))).Exact)
    exact preadditiveYoneda_map_distinguished T hT (D.obj j)
  exact hS.map
    (colim : (Discrete ι ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v})

namespace IsCompactObject

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} AddCommGrpCat.{v}]
  [AB4OfSize.{w} AddCommGrpCat.{v}]

set_option maxHeartbeats 800000 in
/-- In a distinguished triangle, the middle object is compact when the two
outer objects are compact. -/
theorem extension (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactObject.{w} T.obj₁) (h₃ : IsCompactObject.{w} T.obj₃) :
    IsCompactObject.{w} T.obj₂ := by
  intro ι
  refine ⟨fun {D} => ?_⟩
  apply PreservesColimit.mk'
  intro hD
  letI := hD
  let H := homDiagram D
  let R := (((shortComplexOfDistTriangle T.rotate
    (rot_of_distTriang T hT)).op.map H).map
      (colim : (Discrete ι ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}))
  let M := (((shortComplexOfDistTriangle T hT).op.map H).map
    (colim : (Discrete ι ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}))
  let L := (((shortComplexOfDistTriangle T.invRotate
    (inv_rot_of_distTriang T hT)).op.map H).map
      (colim : (Discrete ι ⥤ AddCommGrpCat.{v}) ⥤ AddCommGrpCat.{v}))
  let R' := (shortComplexOfDistTriangle T.rotate
    (rot_of_distTriang T hT)).op.map (preadditiveYoneda.obj (colimit D))
  let M' := (shortComplexOfDistTriangle T hT).op.map
    (preadditiveYoneda.obj (colimit D))
  let L' := (shortComplexOfDistTriangle T.invRotate
    (inv_rot_of_distTriang T hT)).op.map
      (preadditiveYoneda.obj (colimit D))
  let f₁ := colimMap (H.map T.mor₃.op)
  let f₂ := colimMap (H.map T.mor₂.op)
  let f₃ := colimMap (H.map T.mor₁.op)
  let f₄ := colimMap (H.map T.invRotate.mor₁.op)
  let g₁ := (preadditiveYoneda.flip.map T.mor₃.op).app (colimit D)
  let g₂ := (preadditiveYoneda.flip.map T.mor₂.op).app (colimit D)
  let g₃ := (preadditiveYoneda.flip.map T.mor₁.op).app (colimit D)
  let g₄ := (preadditiveYoneda.flip.map T.invRotate.mor₁.op).app (colimit D)
  let i₁ := colimit.post D
    (preadditiveYoneda.flip.obj (op (T.obj₁⟦(1 : ℤ)⟧)))
  let i₂ := colimit.post D
    (preadditiveYoneda.flip.obj (op T.obj₃))
  let i₃ := colimit.post D
    (preadditiveYoneda.flip.obj (op T.obj₂))
  let i₄ := colimit.post D
    (preadditiveYoneda.flip.obj (op T.obj₁))
  let i₅ := colimit.post D
    (preadditiveYoneda.flip.obj (op (T.obj₃⟦-1⟧)))
  have hR : R.Exact :=
    colimit_preadditiveYoneda_exact D T.rotate (rot_of_distTriang T hT)
  have hM : M.Exact := colimit_preadditiveYoneda_exact D T hT
  have hL : L.Exact :=
    colimit_preadditiveYoneda_exact D T.invRotate (inv_rot_of_distTriang T hT)
  have hR' : R'.Exact :=
    preadditiveYoneda_map_distinguished T.rotate (rot_of_distTriang T hT) (colimit D)
  have hM' : M'.Exact :=
    preadditiveYoneda_map_distinguished T hT (colimit D)
  have hL' : L'.Exact :=
    preadditiveYoneda_map_distinguished T.invRotate
      (inv_rot_of_distTriang T hT) (colimit D)
  have hf₁ : Function.Exact f₁.hom f₂.hom := by
    change Function.Exact R.f.hom R.g.hom
    exact R.ab_exact_iff_function_exact.mp hR
  have hf₂ : Function.Exact f₂.hom f₃.hom := by
    change Function.Exact M.f.hom M.g.hom
    exact M.ab_exact_iff_function_exact.mp hM
  have hf₃ : Function.Exact f₃.hom f₄.hom := by
    change Function.Exact L.f.hom L.g.hom
    exact L.ab_exact_iff_function_exact.mp hL
  have hg₁ : Function.Exact g₁.hom g₂.hom := by
    change Function.Exact R'.f.hom R'.g.hom
    exact R'.ab_exact_iff_function_exact.mp hR'
  have hg₂ : Function.Exact g₂.hom g₃.hom := by
    change Function.Exact M'.f.hom M'.g.hom
    exact M'.ab_exact_iff_function_exact.mp hM'
  have hg₃ : Function.Exact g₃.hom g₄.hom := by
    change Function.Exact L'.f.hom L'.g.hom
    exact L'.ab_exact_iff_function_exact.mp hL'
  have hc₁ : i₁ ≫ g₁ = f₁ ≫ i₂ := by
    convert colimitPost_naturality D
      (preadditiveYoneda.flip.map T.mor₃.op) using 1 ; rfl
  have hc₂ : i₂ ≫ g₂ = f₂ ≫ i₃ := by
    convert colimitPost_naturality D
      (preadditiveYoneda.flip.map T.mor₂.op) using 1 ; rfl
  have hc₃ : i₃ ≫ g₃ = f₃ ≫ i₄ := by
    convert colimitPost_naturality D
      (preadditiveYoneda.flip.map T.mor₁.op) using 1 ; rfl
  have hc₄ : i₄ ≫ g₄ = f₄ ≫ i₅ := by
    convert colimitPost_naturality D
      (preadditiveYoneda.flip.map T.invRotate.mor₁.op) using 1 <;> rfl
  have hA₁ : IsCompactObject.{w} T.rotate.obj₃ := by
    change IsCompactObject.{w} (T.obj₁⟦(1 : ℤ)⟧)
    exact h₁.shift 1
  have hA₅ : IsCompactObject.{w} T.invRotate.obj₁ := by
    change IsCompactObject.{w} (T.obj₃⟦-1⟧)
    exact h₃.shift (-1)
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveYoneda.flip.obj (op (T.obj₁⟦(1 : ℤ)⟧))) := by
    change PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op (T.obj₁⟦(1 : ℤ)⟧)))
    exact hA₁ ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveYoneda.flip.obj (op T.obj₃)) := by
    change PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op T.obj₃))
    exact h₃ ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveYoneda.flip.obj (op T.obj₁)) := by
    change PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op T.obj₁))
    exact h₁ ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveYoneda.flip.obj (op (T.obj₃⟦-1⟧))) := by
    change PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op (T.obj₃⟦-1⟧)))
    exact hA₅ ι
  have hi₁ : Function.Bijective i₁ := ConcreteCategory.bijective_of_isIso i₁
  have hi₂ : Function.Bijective i₂ := ConcreteCategory.bijective_of_isIso i₂
  have hi₄ : Function.Bijective i₄ := ConcreteCategory.bijective_of_isIso i₄
  have hi₅ : Function.Bijective i₅ := ConcreteCategory.bijective_of_isIso i₅
  have hi₃ : Function.Bijective i₃ :=
    AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      f₁.hom f₂.hom f₃.hom f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom
      i₁.hom i₂.hom i₃.hom i₄.hom i₅.hom
      (by exact congrArg ConcreteCategory.hom hc₁)
      (by exact congrArg ConcreteCategory.hom hc₂)
      (by exact congrArg ConcreteCategory.hom hc₃)
      (by exact congrArg ConcreteCategory.hom hc₄)
      hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
      hi₁.surjective hi₂ hi₄ hi₅.injective
  letI : IsIso i₃ := (ConcreteCategory.isIso_iff_bijective i₃).2 hi₃
  haveI : IsIso (colimit.post D
      (preadditiveCoyoneda.obj (op T.obj₂))) := by
    change IsIso i₃
    infer_instance
  exact preservesColimit_of_isIso_post
    (preadditiveCoyoneda.obj (op T.obj₂)) D

end IsCompactObject

namespace IsCompactObject

variable [HasZeroObject C]
  [HasCoproducts.{w} AddCommGrpCat.{v}]

/-- A zero object is compact. -/
theorem zero : IsCompactObject.{w} (0 : C) := by
  intro ι
  refine ⟨fun {D} => ?_⟩
  apply PreservesColimit.mk'
  intro hD
  letI := hD
  let F := preadditiveCoyoneda.obj (op (0 : C))
  have hF : IsZero F := by
    apply Functor.isZero
    intro X
    rw [IsZero.iff_id_eq_zero]
    ext f
    change f = 0
    exact (isZero_zero C).eq_of_src f 0
  have hDF : IsZero (D ⋙ F) :=
    Functor.isZero _ (fun j => hF.obj (D.obj j))
  letI : IsIso (colimit.post D F) :=
    IsZero.isIso ((colimit.isColimit (D ⋙ F)).isZero_pt hDF)
      (hF.obj (colimit D)) _
  exact preservesColimit_of_isIso_post F D

omit [HasZeroObject C] in
/-- A retract of a compact object is compact. -/
theorem of_retract_of_size {X Y : C} (r : Retract X Y)
    (hY : IsCompactObject.{w} Y) : IsCompactObject.{w} X := by
  intro ι
  refine ⟨fun {D} => ?_⟩
  apply PreservesColimit.mk'
  intro hD
  letI := hD
  let FX := preadditiveCoyoneda.obj (op X)
  let FY := preadditiveCoyoneda.obj (op Y)
  let rF : Retract FX FY := r.op.map preadditiveCoyoneda
  letI : PreservesColimitsOfShape (Discrete ι) FY := hY ι
  let rA : RetractArrow (colimit.post D FX) (colimit.post D FY) :=
    { i := Arrow.homMk
        (colimMap (Functor.whiskerLeft D rF.i))
        (rF.i.app (colimit D))
        (colimitPost_naturality D rF.i).symm
      r := Arrow.homMk
        (colimMap (Functor.whiskerLeft D rF.r))
        (rF.r.app (colimit D))
        (colimitPost_naturality D rF.r).symm
      retract := by
        apply Arrow.hom_ext
        · change colimMap (Functor.whiskerLeft D rF.i) ≫
            colimMap (Functor.whiskerLeft D rF.r) = 𝟙 _
          apply colimit.hom_ext
          intro j
          rw [Category.comp_id, ι_colimMap_assoc, ι_colimMap]
          rw [← Category.assoc, ← NatTrans.comp_app]
          have hr : Functor.whiskerLeft D rF.i ≫
              Functor.whiskerLeft D rF.r = 𝟙 _ := by
            rw [← Functor.whiskerLeft_comp, rF.retract]
            rfl
          rw [hr]
          simp
        · change rF.i.app (colimit D) ≫ rF.r.app (colimit D) = 𝟙 _
          exact NatTrans.congr_app rF.retract (colimit D) }
  letI : IsIso (colimit.post D FX) :=
    (MorphismProperty.isomorphisms AddCommGrpCat).of_retract rA (by
      change IsIso (colimit.post D FY)
      infer_instance)
  exact preservesColimit_of_isIso_post FX D

end IsCompactObject

namespace ObjectProperty

section Retracts

variable [HasCoproducts.{w} AddCommGrpCat.{v}]

instance compactObjects_isStableUnderRetracts :
    (compactObjects.{w} (C := C)).IsStableUnderRetracts where
  of_retract r hY := IsCompactObject.of_retract_of_size r hY

end Retracts

section Zero

variable [HasZeroObject C] [HasCoproducts.{w} AddCommGrpCat.{v}]

instance compactObjects_containsZero :
    (compactObjects.{w} (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, IsCompactObject.zero⟩

end Zero

section Shift

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

instance compactObjects_isStableUnderShift :
    (compactObjects.{w} (C := C)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun _ hX => IsCompactObject.shift hX n⟩

end Shift

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} AddCommGrpCat.{v}]
  [AB4OfSize.{w} AddCommGrpCat.{v}]

instance compactObjects_isTriangulatedClosed₂ :
    (compactObjects.{w} (C := C)).IsTriangulatedClosed₂ :=
  IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
    IsCompactObject.extension T hT h₁ h₃)

instance compactObjects_isTriangulated :
    (compactObjects.{w} (C := C)).IsTriangulated where
  toContainsZero := inferInstance
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := inferInstance

end Triangulated

end ObjectProperty

end CategoryTheory
