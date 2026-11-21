/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.TotalSite

/-!
# Modules on the total site of a constant simplicial scheme

For a scheme `Y`, let `c(Y)` be the constant simplicial scheme. The projection
`(n, V) ↦ V` from its total site to the opens of `Y` is continuous, so
precomposition gives the "constant system" functor `c^* : Y.Modules ⥤ Modules`.
Its right adjoint `c_*` sends `F` to the equalizer of the two maps
`F_0 ⟶ F_1` given by the coface maps `[0] ⟶ [1]`. This is the module version of
Stacks, Lemma 85.4.2 (Tag 0D70) for the constant augmentation.

## Main definitions

* `AlgebraicGeometry.TotalSite.constPullback Y`: `c^*`.
* `AlgebraicGeometry.TotalSite.constPushforward Y`: `c_*`, an equalizer.
* `AlgebraicGeometry.TotalSite.constAdjunction Y`: `c^* ⊣ c_*`.
* `AlgebraicGeometry.TotalSite.constPullbackRestrictIso Y n`: `g_n⁻¹ ∘ c^* ≅ 𝟭`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits Simplicial

namespace AlgebraicGeometry.TotalSite

variable (Y : Scheme.{u})

/-- The projection `(n, V) ↦ V` from the total site of the constant simplicial
scheme on `Y`. -/
def constProj : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y) ⥤ Y.Opens where
  obj x := x.opens
  map g := homOfLE (Hom.le g)

instance isContinuous_constProj :
    (constProj Y).IsContinuous (topology _) (Opens.grothendieckTopology Y) where
  op_comp_isSheaf_of_types G := by
    rw [← isSheaf_iff_isSheaf_of_type, isSheaf_iff]
    exact fun _ => G.property

/-- The structure sheaf of the total site of `c(Y)` is the pullback of `𝒪_Y`. -/
def constRingHom : ringSheaf ((SimplicialObject.const Scheme.{u}).obj Y) ⟶
    ((constProj Y).sheafPushforwardContinuous RingCat.{u} _ _).obj Y.ringCatSheaf where
  hom :=
    { app _ := 𝟙 _
      naturality _ _ _ := rfl }

/-- The constant system `c^* G` attached to a module `G` on `Y`. -/
noncomputable def constPullback :
    Y.Modules ⥤ Modules ((SimplicialObject.const Scheme.{u}).obj Y) :=
  SheafOfModules.pushforward (constRingHom Y)

variable (n : SimplexCategory)

/-- `constProj` restricted to the level `n` is the identity of `Y.Opens`. -/
def ιCompConstProjIso : 𝟭 Y.Opens ≅ ι ((SimplicialObject.const Scheme.{u}).obj Y) n ⋙ constProj Y :=
  NatIso.ofComponents (fun _ => Iso.refl _)

lemma constPullbackRestrict_ringHom_eq :
    letI : (𝟭 Y.Opens).IsContinuous (Opens.grothendieckTopology
      (((SimplicialObject.const Scheme.{u}).obj Y).obj (op n))) (Opens.grothendieckTopology Y) :=
      Functor.isContinuous_id _
    letI := Functor.isContinuous_comp (ι ((SimplicialObject.const Scheme.{u}).obj Y) n)
      (constProj Y) (Opens.grothendieckTopology (((SimplicialObject.const Scheme.{u}).obj Y).obj
        (op n))) (topology _) (Opens.grothendieckTopology Y)
    (ringSheafRestrict _ n ≫ ((ι _ n).sheafPushforwardContinuous RingCat.{u} _ _).map
        (constRingHom Y)) ≫ (Functor.sheafPushforwardContinuousNatTrans
          (ιCompConstProjIso Y n).hom RingCat.{u} _ _).app Y.ringCatSheaf = 𝟙 Y.ringCatSheaf :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => by
    change 𝟙 _ ≫ Y.ringCatSheaf.obj.map (𝟙 _) = 𝟙 _
    rw [Category.id_comp, CategoryTheory.Functor.map_id]))

/-- The restriction of a constant system to any level is the module it came from. -/
noncomputable def constPullbackRestrictIso :
    constPullback Y ⋙ restrict ((SimplicialObject.const Scheme.{u}).obj Y) n ≅ 𝟭 Y.Modules :=
  letI : (𝟭 Y.Opens).IsContinuous (Opens.grothendieckTopology
    (((SimplicialObject.const Scheme.{u}).obj Y).obj (op n))) (Opens.grothendieckTopology Y) :=
    Functor.isContinuous_id _
  letI := Functor.isContinuous_comp (ι ((SimplicialObject.const Scheme.{u}).obj Y) n)
    (constProj Y) (Opens.grothendieckTopology (((SimplicialObject.const Scheme.{u}).obj Y).obj
      (op n))) (topology _) (Opens.grothendieckTopology Y)
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (ιCompConstProjIso Y n)
      (constPullbackRestrict_ringHom_eq Y n) ≪≫ SheafOfModules.pushforwardId _

variable {Y}

/-- Restriction to the level `n` of a module on the total site of `c(Y)`, as a
module on `Y`. -/
noncomputable def constRestrict (n : SimplexCategory) :
    Modules ((SimplicialObject.const Scheme.{u}).obj Y) ⥤ Y.Modules :=
  restrict ((SimplicialObject.const Scheme.{u}).obj Y) n

variable (Y) in
/-- The coface map `F_0 ⟶ F_1` along `δ i : [0] ⟶ [1]`. -/
noncomputable def coface (i : Fin 2) : constRestrict (Y := Y) ⦋0⦌ ⟶ constRestrict ⦋1⦌ :=
  transition _ (SimplexCategory.δ i) ≫
    Functor.whiskerLeft (constRestrict ⦋1⦌) (Scheme.Modules.pushforwardId Y).hom

lemma coface_app_val_app (i : Fin 2) (F : Modules ((SimplicialObject.const Scheme.{u}).obj Y))
    (U : Y.Opensᵒᵖ) (s : F.val.obj (op (mk ⦋0⦌ U.unop))) :
    ((coface Y i).app F).val.app U s =
      F.val.map (homMk (SimplexCategory.δ i) le_rfl : mk ⦋1⦌ U.unop ⟶ mk ⦋0⦌ U.unop).op s :=
  rfl

/-- The vertex `(m, U) ⟶ (0, U)` over the vertex `0` of `[m]`. -/
def vertexHom (x : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y)) :
    x ⟶ mk ⦋0⦌ x.opens :=
  homMk (SimplexCategory.const ⦋0⦌ x.level 0) le_rfl

section VertexIndependence

variable {F : Modules ((SimplicialObject.const Scheme.{u}).obj Y)} {G : Y.Modules}
  (g₀ : G ⟶ (constRestrict ⦋0⦌).obj F)
  (hg : g₀ ≫ (coface Y 0).app F = g₀ ≫ (coface Y 1).app F)
include hg

lemma map_vertex_eq_of_le {x : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y)}
    {U : Y.Opens} (k k' : x ⟶ mk ⦋0⦌ U)
    (h : (Hom.base k).toOrderHom 0 ≤ (Hom.base k').toOrderHom 0) (s : G.val.obj (op U)) :
    F.val.map k.op (g₀.val.app (op U) s) = F.val.map k'.op (g₀.val.app (op U) s) := by
  have hd : F.val.map (homMk (SimplexCategory.δ 0) le_rfl : mk ⦋1⦌ U ⟶ mk ⦋0⦌ U).op
      (g₀.val.app (op U) s) =
      F.val.map (homMk (SimplexCategory.δ 1) le_rfl : mk ⦋1⦌ U ⟶ mk ⦋0⦌ U).op
        (g₀.val.app (op U) s) :=
    congrArg (fun φ => φ.val.app (op U) s) hg
  let e : ⦋1⦌ ⟶ x.level := SimplexCategory.mkOfLe _ _ h
  let E : x ⟶ mk ⦋1⦌ U := homMk e (Hom.le k)
  have hk : k = E ≫ homMk (SimplexCategory.δ 1) le_rfl :=
    hom_ext (SimplexCategory.Hom.ext_zero_left _ _ rfl)
  have hk' : k' = E ≫ homMk (SimplexCategory.δ 0) le_rfl :=
    hom_ext (SimplexCategory.Hom.ext_zero_left _ _ rfl)
  have h1 := F.val.map_comp_apply
    (homMk (SimplexCategory.δ 1) le_rfl : mk ⦋1⦌ U ⟶ mk ⦋0⦌ U).op E.op (g₀.val.app (op U) s)
  have h0 := F.val.map_comp_apply
    (homMk (SimplexCategory.δ 0) le_rfl : mk ⦋1⦌ U ⟶ mk ⦋0⦌ U).op E.op (g₀.val.app (op U) s)
  have c1 := F.val.congr_map_apply (congrArg Quiver.Hom.op hk) (g₀.val.app (op U) s)
  have c0 := F.val.congr_map_apply (congrArg Quiver.Hom.op hk') (g₀.val.app (op U) s)
  exact c1.trans (h1.trans ((congrArg (F.val.map E.op) hd.symm).trans (h0.symm.trans c0.symm)))

lemma map_vertex_eq {x : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y)}
    {U : Y.Opens} (k k' : x ⟶ mk ⦋0⦌ U) (s : G.val.obj (op U)) :
    F.val.map k.op (g₀.val.app (op U) s) = F.val.map k'.op (g₀.val.app (op U) s) := by
  rcases le_total ((Hom.base k).toOrderHom 0) ((Hom.base k').toOrderHom 0) with h | h
  · exact map_vertex_eq_of_le g₀ hg k k' h s
  · exact (map_vertex_eq_of_le g₀ hg k' k h s).symm

end VertexIndependence

variable (Y) in
/-- `c_*`: the equalizer of the two coface maps `F_0 ⇉ F_1` (Stacks, Lemma 85.4.2,
Tag 0D70, for the constant augmentation). -/
noncomputable def constPushforward :
    Modules ((SimplicialObject.const Scheme.{u}).obj Y) ⥤ Y.Modules where
  obj F := equalizer ((coface Y 0).app F) ((coface Y 1).app F)
  map {F G} φ := equalizer.lift (equalizer.ι _ _ ≫ (constRestrict ⦋0⦌).map φ) (by
    rw [Category.assoc, Category.assoc, (coface Y 0).naturality, (coface Y 1).naturality,
      equalizer.condition_assoc])
  map_id F := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

lemma ringPresheaf_map_vertexHom (x : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y)) :
    (ringPresheaf _).map (vertexHom x).op = 𝟙 _ := by
  change (forget₂ CommRingCat RingCat).map (Y.presheaf.map (𝟙 (op x.opens))) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

section Descend

variable {F : Modules ((SimplicialObject.const Scheme.{u}).obj Y)} {G : Y.Modules}
  (g₀ : G ⟶ (constRestrict ⦋0⦌).obj F)

/-- The section `s|_{(m, U)}` attached to a section `s` of `F_0` over `U`. -/
noncomputable def descendApp (x : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ)
    (s : G.val.obj (op x.unop.opens)) : F.val.obj x :=
  F.val.map (vertexHom x.unop).op (g₀.val.app (op x.unop.opens) s)

lemma descendApp_zero (x : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ) :
    descendApp g₀ x 0 = 0 :=
  (congrArg (fun z => F.val.map (vertexHom x.unop).op z)
    (g₀.val.app (op x.unop.opens)).hom.map_zero).trans
      (F.val.map (vertexHom x.unop).op).hom.map_zero

lemma descendApp_add (x : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ)
    (s s' : G.val.obj (op x.unop.opens)) :
    descendApp g₀ x (s + s') = descendApp g₀ x s + descendApp g₀ x s' :=
  (congrArg (fun z => F.val.map (vertexHom x.unop).op z)
    ((g₀.val.app (op x.unop.opens)).hom.map_add s s')).trans
    ((F.val.map (vertexHom x.unop).op).hom.map_add _ _)

variable (hg : g₀ ≫ (coface Y 0).app F = g₀ ≫ (coface Y 1).app F)
include hg

lemma descendApp_naturality {x y : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ}
    (g : x ⟶ y) (s : G.val.obj (op x.unop.opens)) :
    descendApp g₀ y (G.val.map (homOfLE (Hom.le g.unop)).op s) =
      F.val.map g (descendApp g₀ x s) := by
  have hn := congrArg (fun φ => φ s) (g₀.val.naturality (homOfLE (Hom.le g.unop)).op)
  refine (congrArg (F.val.map (vertexHom y.unop).op) hn).trans ?_
  refine (F.val.map_comp_apply (ιMap ⦋0⦌ (homOfLE (Hom.le g.unop))).op (vertexHom y.unop).op
    (g₀.val.app (op x.unop.opens) s)).symm.trans ?_
  refine (map_vertex_eq g₀ hg (vertexHom y.unop ≫ ιMap ⦋0⦌ (homOfLE (Hom.le g.unop)))
    (g.unop ≫ vertexHom x.unop) s).trans ?_
  exact F.val.map_comp_apply (vertexHom x.unop).op g (g₀.val.app (op x.unop.opens) s)

/-- A map `G ⟶ F_0` equalizing the two cofaces extends uniquely to `c^* G ⟶ F`. -/
noncomputable def descend : (constPullback Y).obj G ⟶ F where
  val := PresheafOfModules.homMk
    { app x := AddCommGrpCat.ofHom
        { toFun := descendApp g₀ x
          map_zero' := descendApp_zero g₀ x
          map_add' := descendApp_add g₀ x }
      naturality _ _ g := AddCommGrpCat.ext fun s => descendApp_naturality g₀ hg g s }
    (fun x r s =>
      (congrArg (fun z => F.val.map (vertexHom x.unop).op z)
        ((g₀.val.app (op x.unop.opens)).hom.map_smul r s)).trans
      ((PresheafOfModules.map_smul F.val _ _ _).trans
        (congrArg (· • F.val.map (vertexHom x.unop).op (g₀.val.app (op x.unop.opens) s))
          (congrArg (fun φ => φ.hom r) (ringPresheaf_map_vertexHom x.unop)))))

end Descend

lemma constPushforward_map_ι {F F' : Modules ((SimplicialObject.const Scheme.{u}).obj Y)}
    (φ : F ⟶ F') :
    (constPushforward Y).map φ ≫ equalizer.ι ((coface Y 0).app F') ((coface Y 1).app F') =
      equalizer.ι ((coface Y 0).app F) ((coface Y 1).app F) ≫ (constRestrict ⦋0⦌).map φ :=
  equalizer.lift_ι _ _

/-- The identification `G ⟶ (c^* G)_0`; on sections it is the identity. -/
noncomputable def constUnit (G : Y.Modules) :
    G ⟶ (constRestrict ⦋0⦌).obj ((constPullback Y).obj G) where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.id (G.val.obj U))
      naturality _ _ _ := AddCommGrpCat.ext fun s =>
        G.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s }
    (fun _ _ _ => rfl)

lemma constUnit_val_app (G : Y.Modules) (U : Y.Opensᵒᵖ) (s : G.val.obj U) :
    (constUnit G).val.app U s = s := rfl

lemma constUnit_coface (G : Y.Modules) :
    constUnit G ≫ (coface Y 0).app ((constPullback Y).obj G) =
      constUnit G ≫ (coface Y 1).app ((constPullback Y).obj G) :=
  Scheme.Modules.hom_ext _ _ fun _ => AddCommGrpCat.ext fun s =>
    G.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s

lemma constUnit_naturality {G G' : Y.Modules} (ψ : G ⟶ G') :
    ψ ≫ constUnit G' = constUnit G ≫ (constRestrict ⦋0⦌).map ((constPullback Y).map ψ) :=
  Scheme.Modules.hom_ext _ _ fun _ => AddCommGrpCat.ext fun _ => rfl

variable (Y) in
/-- The unit `G ⟶ c_* (c^* G)`. -/
noncomputable def constUnitNatTrans : 𝟭 Y.Modules ⟶ constPullback Y ⋙ constPushforward Y where
  app G := equalizer.lift (constUnit G) (constUnit_coface G)
  naturality {G _} ψ := equalizer.hom_ext <|
    (Category.assoc _ _ _).trans ((congrArg (ψ ≫ ·) (equalizer.lift_ι _ _)).trans
      ((constUnit_naturality ψ).trans
        ((congrArg (· ≫ (constRestrict ⦋0⦌).map ((constPullback Y).map ψ))
          (equalizer.lift_ι (constUnit G) (constUnit_coface G)).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (equalizer.lift (constUnit G) (constUnit_coface G) ≫ ·)
              (constPushforward_map_ι ((constPullback Y).map ψ)).symm).trans
              (Category.assoc _ _ _).symm)))))

lemma constCounit_naturality_apply {F F' : Modules ((SimplicialObject.const Scheme.{u}).obj Y)}
    (φ : F ⟶ F') (x : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ)
    (t : ((constPushforward Y).obj F).val.obj (op x.unop.opens)) :
    descendApp (equalizer.ι ((coface Y 0).app F') ((coface Y 1).app F')) x
        (((constPushforward Y).map φ).val.app (op x.unop.opens) t) =
      φ.val.app x (descendApp (equalizer.ι ((coface Y 0).app F) ((coface Y 1).app F)) x t) := by
  have h := congrArg (fun ψ => ψ.val.app (op x.unop.opens) t) (constPushforward_map_ι φ)
  refine (congrArg (fun z => F'.val.map (vertexHom x.unop).op z) h).trans ?_
  exact (congrArg (fun k => k ((equalizer.ι ((coface Y 0).app F) ((coface Y 1).app F)).val.app
    (op x.unop.opens) t)) (φ.val.naturality (vertexHom x.unop).op)).symm

variable (Y) in
/-- The counit `c^* (c_* F) ⟶ F`. -/
noncomputable def constCounitNatTrans : constPushforward Y ⋙ constPullback Y ⟶ 𝟭 _ where
  app F := descend (equalizer.ι ((coface Y 0).app F) ((coface Y 1).app F))
    (equalizer.condition ((coface Y 0).app F) ((coface Y 1).app F))
  naturality _ _ φ := sheafOfModules_hom_ext fun x t => constCounit_naturality_apply φ x t

lemma constLeftTriangle_apply (G : Y.Modules)
    (x : (TotalSite ((SimplicialObject.const Scheme.{u}).obj Y))ᵒᵖ)
    (s : G.val.obj (op x.unop.opens)) :
    descendApp (equalizer.ι ((coface Y 0).app ((constPullback Y).obj G))
        ((coface Y 1).app ((constPullback Y).obj G))) x
      ((equalizer.lift (constUnit G) (constUnit_coface G)).val.app (op x.unop.opens) s) = s := by
  have h := congrArg (fun ψ => ψ.val.app (op x.unop.opens) s)
    (equalizer.lift_ι (constUnit G) (constUnit_coface G))
  refine (congrArg (fun z => ((constPullback Y).obj G).val.map (vertexHom x.unop).op z) h).trans ?_
  exact (G.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ (𝟙 _))) s).trans
    (presheafOfModules_map_id_apply G.val _ s)

lemma vertexHom_mk_zero (U : Y.Opens) :
    vertexHom (mk ⦋0⦌ U : TotalSite ((SimplicialObject.const Scheme.{u}).obj Y)) = 𝟙 _ :=
  hom_ext (SimplexCategory.Hom.ext_zero_left _ _ rfl)

lemma constRightTriangle (F : Modules ((SimplicialObject.const Scheme.{u}).obj Y)) :
    constUnit ((constPushforward Y).obj F) ≫
        (constRestrict ⦋0⦌).map ((constCounitNatTrans Y).app F) =
      equalizer.ι ((coface Y 0).app F) ((coface Y 1).app F) :=
  Scheme.Modules.hom_ext _ _ fun U => AddCommGrpCat.ext fun _ =>
    (F.val.congr_map_apply (congrArg Quiver.Hom.op (vertexHom_mk_zero U)) _).trans
      (presheafOfModules_map_id_apply F.val _ _)

variable (Y) in
/-- `c^* ⊣ c_*` (Stacks, Lemma 85.4.2, Tag 0D70, for the constant augmentation). -/
noncomputable def constAdjunction : constPullback Y ⊣ constPushforward Y where
  unit := constUnitNatTrans Y
  counit := constCounitNatTrans Y
  left_triangle_components G := sheafOfModules_hom_ext fun x s => constLeftTriangle_apply G x s
  right_triangle_components F := equalizer.hom_ext <|
    (Category.assoc _ _ _).trans ((congrArg (equalizer.lift (constUnit ((constPushforward Y).obj F))
      (constUnit_coface _) ≫ ·) (constPushforward_map_ι ((constCounitNatTrans Y).app F))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (constRestrict ⦋0⦌).map
        ((constCounitNatTrans Y).app F)) (equalizer.lift_ι _ _)).trans
        ((constRightTriangle F).trans (Category.id_comp _).symm))))

end AlgebraicGeometry.TotalSite
