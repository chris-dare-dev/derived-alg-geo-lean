/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.TotalSite

/-!
# The right adjoint of restriction to a level of the total site

For a simplicial scheme `X` and a level `n`, restriction of modules
`TotalSite.restrict X n` (Stacks' `g_n⁻¹`) has a right adjoint `g_{n*}`. On
sections over `(m, W)` it is the product of the sections of `M` over the
opens `X(ψ)⁻¹ W` of `X_n`, one for each `ψ : [m] ⟶ [n]`: the restriction of
the representable presheaf of `(m, W)` to `X_n` is the coproduct of the
representables of those opens.

## Main definitions

* `AlgebraicGeometry.TotalSite.levelPushforward X n`: the functor `g_{n*}`.
* `AlgebraicGeometry.TotalSite.restrictAdjunction X n`: `g_n⁻¹ ⊣ g_{n*}`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.TotalSite

variable {X : SimplicialObject Scheme.{u}} {n : SimplexCategory}

namespace LevelPushforward

/-- The open `X(ψ)⁻¹ U` of `X_n`, for an object `(m, U)` and `ψ : [m] ⟶ [n]`. -/
abbrev opensAt (x : TotalSite X) (ψ : x.level ⟶ n) : (X.obj (op n)).Opens :=
  (Opens.map (X.map ψ.op).base).obj x.opens

lemma opensAt_le {x y : TotalSite X} (g : y ⟶ x) (χ : y.level ⟶ n) :
    opensAt y χ ≤ opensAt x (Hom.base g ≫ χ) := by
  have h : X.map (Hom.base g ≫ χ).op = X.map χ.op ≫ X.map (Hom.base g).op := by simp
  change _ ≤ (Opens.map (X.map (Hom.base g ≫ χ).op).base).obj x.opens
  rw [h]
  exact (Opens.map (X.map χ.op).base).monotone (Hom.le g)

/-- The ring map `𝒪(m, U) ⟶ 𝒪_{X_n}(X(ψ)⁻¹ U)` along which the `ψ`-component of
`g_{n*} M` becomes an `𝒪(m, U)`-module. -/
noncomputable def componentRingHom (x : TotalSite X) (ψ : x.level ⟶ n) :
    (ringPresheaf X).obj (op x) ⟶ (ringPresheaf X).obj (op (mk n (opensAt x ψ))) :=
  (ringPresheaf X).map (homMk ψ le_rfl : mk n (opensAt x ψ) ⟶ x).op

lemma componentRingHom_naturality {x y : TotalSite X} (g : y ⟶ x) (χ : y.level ⟶ n) :
    componentRingHom x (Hom.base g ≫ χ) ≫
        (ringPresheaf X).map (ιMap n (homOfLE (opensAt_le g χ))).op =
      (ringPresheaf X).map g.op ≫ componentRingHom y χ := by
  have h : (ιMap n (homOfLE (opensAt_le g χ)) ≫ homMk (Hom.base g ≫ χ) le_rfl :
      mk n (opensAt y χ) ⟶ x) = homMk χ le_rfl ≫ g := hom_ext (by simp)
  rw [componentRingHom, componentRingHom, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp, h]

/-- `componentRingHom` as a ring homomorphism into the ring of sections of `𝒪_{X_n}`. -/
noncomputable def componentRingHom' (x : TotalSite X) (ψ : x.level ⟶ n) :
    (ringPresheaf X).obj (op x) →+* (X.obj (op n)).ringCatSheaf.obj.obj (op (opensAt x ψ)) :=
  (componentRingHom x ψ).hom

/-- Sections of `M` over `X(ψ)⁻¹ U` and over `X(ψ')⁻¹ U` agree after restriction
when `ψ = ψ'`. -/
lemma map_apply_congr (M : (X.obj (op n)).Modules) {x : TotalSite X}
    (t : ∀ ψ : x.level ⟶ n, M.val.obj (op (opensAt x ψ))) {ψ ψ' : x.level ⟶ n} (h : ψ = ψ')
    {V : (X.obj (op n)).Opens} (a : op (opensAt x ψ) ⟶ op V) (b : op (opensAt x ψ') ⟶ op V) :
    M.val.map a (t ψ) = M.val.map b (t ψ') := by
  subst h
  exact M.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) _

lemma map_le_rfl_apply {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens) (x : M.val.obj (op U)) :
    M.val.map (homOfLE (le_refl U)).op x = x :=
  (M.val.congr_map_apply (Subsingleton.elim _ (𝟙 _)) x).trans
    (presheafOfModules_map_id_apply M.val _ x)

lemma le_opensAt_id (U : (X.obj (op n)).Opens) : U ≤ opensAt (mk n U) (𝟙 n) := by
  change U ≤ (Opens.map (X.map (𝟙 n).op).base).obj U
  rw [show X.map (𝟙 n).op = 𝟙 _ by simp]
  exact le_rfl

lemma componentRingHom_id_comp (U : (X.obj (op n)).Opens) :
    componentRingHom (mk n U) (𝟙 n) ≫ (ringPresheaf X).map (ιMap n (homOfLE (le_opensAt_id U))).op =
      𝟙 _ := by
  rw [componentRingHom, ← CategoryTheory.Functor.map_comp, ← op_comp,
    show (ιMap n (homOfLE (le_opensAt_id U)) ≫ homMk (𝟙 n) le_rfl : mk n U ⟶ mk n U) = 𝟙 _ from
      hom_ext (by simp), op_id, CategoryTheory.Functor.map_id]

variable (M : (X.obj (op n)).Modules)

/-- The underlying abelian presheaf of `g_{n*} M`. -/
noncomputable def presheaf : (TotalSite X)ᵒᵖ ⥤ Ab.{u} where
  obj x := AddCommGrpCat.of (∀ ψ : x.unop.level ⟶ n, M.val.obj (op (opensAt x.unop ψ)))
  map {x y} g := AddCommGrpCat.ofHom
    { toFun := fun t χ => M.val.map (homOfLE (opensAt_le g.unop χ)).op (t (Hom.base g.unop ≫ χ))
      map_zero' := by funext χ; exact map_zero _
      map_add' := fun t t' => by funext χ; exact map_add _ _ _ }
  map_id x := by
    refine AddCommGrpCat.ext fun t => ?_
    funext χ
    exact (map_apply_congr M t (Category.id_comp χ) _ (homOfLE le_rfl).op).trans
      (map_le_rfl_apply M _ _)
  map_comp {x y z} f g := by
    refine AddCommGrpCat.ext fun t => ?_
    funext χ
    exact (M.val.congr_map_apply (Subsingleton.elim _ _) _).trans (M.val.map_comp_apply _ _ _)

lemma presheaf_map_apply {x y : (TotalSite X)ᵒᵖ} (g : x ⟶ y) (t : (presheaf M).obj x)
    (χ : y.unop.level ⟶ n) :
    (presheaf M).map g t χ =
      M.val.map (homOfLE (opensAt_le g.unop χ)).op (t (Hom.base g.unop ≫ χ)) := rfl

/-- The `𝒪(x)`-module structure on the sections of `g_{n*} M` over `x`. -/
noncomputable instance module (x : (TotalSite X)ᵒᵖ) :
    Module ((ringPresheaf X).obj x) ((presheaf M).obj x) :=
  @Pi.module (x.unop.level ⟶ n) (fun ψ => M.val.obj (op (opensAt x.unop ψ)))
    ((ringPresheaf X).obj x) _ _
    (fun ψ => Module.compHom (M.val.obj (op (opensAt x.unop ψ))) (componentRingHom' x.unop ψ))

lemma smul_apply (x : (TotalSite X)ᵒᵖ) (r : (ringPresheaf X).obj x) (t : (presheaf M).obj x)
    (ψ : x.unop.level ⟶ n) :
    (r • t) ψ = componentRingHom' x.unop ψ r • t ψ := rfl

lemma presheaf_map_smul {x y : (TotalSite X)ᵒᵖ} (g : x ⟶ y) (r : (ringPresheaf X).obj x)
    (t : (presheaf M).obj x) :
    (presheaf M).map g (r • t) = (ringPresheaf X).map g r • (presheaf M).map g t := by
  funext χ
  rw [presheaf_map_apply, smul_apply, PresheafOfModules.map_smul, smul_apply, presheaf_map_apply]
  congr 1
  have := congrArg (fun f => f.hom r) (componentRingHom_naturality g.unop χ)
  rw [ringPresheaf_map_ιMap] at this
  exact this

lemma isSheaf_restrict_presheaf (m : SimplexCategory) :
    Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj (op m))) ((ι X m).op ⋙ presheaf M) := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget (Opens.grothendieckTopology _) _
    (CategoryTheory.forget Ab.{u})).2 ?_
  rw [isSheaf_iff_isSheaf_of_type]
  have hQ : ∀ ψ : m ⟶ n, Presieve.IsSheaf (Opens.grothendieckTopology (X.obj (op m)))
      ((Opens.map (X.map ψ.op).base).op ⋙ M.val.presheaf ⋙ CategoryTheory.forget Ab.{u}) :=
    fun ψ => by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact (Presheaf.isSheaf_iff_isSheaf_forget (Opens.grothendieckTopology _) _
        (CategoryTheory.forget Ab.{u})).1 (Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ M.isSheaf)
  have key : ∀ (ψ : m ⟶ n) {V V' : (X.obj (op m)).Opens} (i : V' ⟶ V)
      (t : (((ι X m).op ⋙ presheaf M) ⋙ CategoryTheory.forget Ab.{u}).obj (op V)),
      (((ι X m).op ⋙ presheaf M) ⋙ CategoryTheory.forget Ab.{u}).map i.op t ψ =
        ((Opens.map (X.map ψ.op).base).op ⋙ M.val.presheaf ⋙
          CategoryTheory.forget Ab.{u}).map i.op (t ψ) := fun ψ _ _ i t =>
    map_apply_congr M t (Category.id_comp ψ) _ _
  intro W S hS x hx
  let y : ∀ ψ : m ⟶ n, Presieve.FamilyOfElements
      ((Opens.map (X.map ψ.op).base).op ⋙ M.val.presheaf ⋙ CategoryTheory.forget Ab.{u})
      (S : Presieve W) := fun ψ V f hf => x f hf ψ
  have hy : ∀ ψ, (y ψ).Compatible := fun ψ V₁ V₂ Z g₁ g₂ f₁ f₂ h₁ h₂ eq =>
    (key ψ g₁ (x f₁ h₁)).symm.trans ((congrFun (hx g₁ g₂ h₁ h₂ eq) ψ).trans
      (key ψ g₂ (x f₂ h₂)))
  choose t ht ht' using fun ψ => hQ ψ S hS (y ψ) (hy ψ)
  refine ⟨fun ψ => t ψ, fun V f hf => funext fun ψ => (key ψ f _).trans (ht ψ f hf),
    fun t' h' => funext fun ψ => ht' ψ (t' ψ) fun V f hf => ?_⟩
  exact (key ψ f t').symm.trans (congrFun (h' f hf) ψ)

end LevelPushforward

open LevelPushforward

variable (X n) in
/-- Stacks' `g_{n*}`: the right adjoint of restriction to the level `n`. The
sections over `(m, W)` are `∏_{ψ : [m] ⟶ [n]} M(X(ψ)⁻¹ W)`. -/
noncomputable def levelPushforward : (X.obj (op n)).Modules ⥤ Modules X where
  obj M :=
    letI : ∀ x, Module ((ringSheaf X).obj.obj x) ((presheaf M).obj x) := module M
    { val := PresheafOfModules.ofPresheaf (presheaf M) fun _ _ g r t => presheaf_map_smul M g r t
      isSheaf := (isSheaf_iff _).2 (isSheaf_restrict_presheaf M) }
  map {M N} f :=
    { val := PresheafOfModules.homMk
        { app x := AddCommGrpCat.ofHom
            { toFun := fun t ψ => f.val.app (op (opensAt x.unop ψ)) (t ψ)
              map_zero' := by funext ψ; exact map_zero _
              map_add' := fun t t' => by funext ψ; exact map_add _ _ _ }
          naturality {x y} g := by
            refine AddCommGrpCat.ext fun t => ?_
            funext χ
            exact congrArg (fun h => h (t (Hom.base g.unop ≫ χ)))
              (f.val.naturality (homOfLE (opensAt_le g.unop χ)).op) }
        (fun x r t => funext fun ψ =>
          (f.val.app (op (opensAt x.unop ψ))).hom.map_smul (componentRingHom' x.unop ψ r) (t ψ)) }
  map_id M := rfl
  map_comp f g := rfl

namespace LevelPushforward

/-- The section `ψ ↦ s|_{(n, X(ψ)⁻¹ U)}` of `g_{n*} (g_n⁻¹ F)` attached to a section
`s` of `F` over `(m, U)`. -/
noncomputable def unitApp (F : Modules X) (x : (TotalSite X)ᵒᵖ) (s : F.val.obj x)
    (ψ : x.unop.level ⟶ n) : ((restrict X n).obj F).val.obj (op (opensAt x.unop ψ)) :=
  F.val.map (homMk ψ le_rfl : mk n (opensAt x.unop ψ) ⟶ x.unop).op s

lemma unitApp_naturality (F : Modules X) {x y : (TotalSite X)ᵒᵖ} (g : x ⟶ y) (s : F.val.obj x)
    (χ : y.unop.level ⟶ n) :
    unitApp F y (F.val.map g s) χ =
      ((restrict X n).obj F).val.map (homOfLE (opensAt_le g.unop χ)).op
        (unitApp F x s (Hom.base g.unop ≫ χ)) := by
  have h : (ιMap n (homOfLE (opensAt_le g.unop χ)) ≫ homMk (Hom.base g.unop ≫ χ) le_rfl :
      mk n (opensAt y.unop χ) ⟶ x.unop) = homMk χ le_rfl ≫ g.unop := hom_ext (by simp)
  exact ((F.val.map_comp_apply g
    (homMk χ le_rfl : mk n (opensAt y.unop χ) ⟶ y.unop).op s).symm.trans
    (F.val.congr_map_apply (congrArg Quiver.Hom.op h).symm s)).trans
    (F.val.map_comp_apply (homMk (Hom.base g.unop ≫ χ) le_rfl :
      mk n (opensAt x.unop (Hom.base g.unop ≫ χ)) ⟶ x.unop).op
      (ιMap n (homOfLE (opensAt_le g.unop χ))).op s)

/-- The unit `F ⟶ g_{n*} (g_n⁻¹ F)` on underlying abelian presheaves. -/
noncomputable def unitPresheafHom (F : Modules X) :
    F.val.presheaf ⟶ presheaf ((restrict X n).obj F) where
  app x := AddCommGrpCat.ofHom
    { toFun := unitApp F x
      map_zero' := by funext ψ; exact map_zero _
      map_add' := fun s s' => by funext ψ; exact map_add _ _ _ }
  naturality {x y} g := AddCommGrpCat.ext fun s => funext fun χ => unitApp_naturality F g s χ

variable (X n) in
/-- The unit `F ⟶ g_{n*} (g_n⁻¹ F)`. -/
noncomputable def unit : 𝟭 (Modules X) ⟶ restrict X n ⋙ levelPushforward X n where
  app F :=
    { val := PresheafOfModules.homMk (unitPresheafHom F)
        (fun x r s => funext fun ψ => F.val.map_smul _ r s) }
  naturality {F G} f := by
    ext x s
    funext ψ
    exact (congrArg (fun h => h s) (f.val.naturality (homMk ψ le_rfl).op)).symm

/-- Evaluation at `ψ = 𝟙` of a section of `g_n⁻¹ (g_{n*} M)` over `U`. -/
noncomputable def counitApp (M : (X.obj (op n)).Modules) (U : (X.obj (op n)).Opens)
    (t : ∀ ψ : n ⟶ n, M.val.obj (op (opensAt (mk n U) ψ))) : M.val.obj (op U) :=
  M.val.map (homOfLE (le_opensAt_id U)).op (t (𝟙 n))

/-- The counit `g_n⁻¹ (g_{n*} M) ⟶ M` on underlying abelian presheaves. -/
noncomputable def counitPresheafHom (M : (X.obj (op n)).Modules) :
    ((restrict X n).obj ((levelPushforward X n).obj M)).val.presheaf ⟶ M.val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := fun t => counitApp M U.unop t
      map_zero' := (M.val.map (homOfLE (le_opensAt_id U.unop)).op).hom.map_zero
      map_add' := fun t t' => (M.val.map (homOfLE (le_opensAt_id U.unop)).op).hom.map_add _ _ }
  naturality {U V} i := AddCommGrpCat.ext fun t => by
    change M.val.map (homOfLE (le_opensAt_id V.unop)).op
        (M.val.map (homOfLE (opensAt_le (ιMap n i.unop) (𝟙 n))).op
          (t (Hom.base (ιMap n i.unop) ≫ 𝟙 n))) =
      M.val.map i (M.val.map (homOfLE (le_opensAt_id U.unop)).op (t (𝟙 n)))
    exact ((M.val.map_comp_apply (homOfLE (opensAt_le (ιMap n i.unop) (𝟙 n))).op
      (homOfLE (le_opensAt_id V.unop)).op _).symm.trans
      (map_apply_congr M t (Category.id_comp (𝟙 n)) _ _)).trans
      (M.val.map_comp_apply (homOfLE (le_opensAt_id U.unop)).op i _)

variable (X n) in
/-- The counit `g_n⁻¹ (g_{n*} M) ⟶ M`. -/
noncomputable def counit : levelPushforward X n ⋙ restrict X n ⟶ 𝟭 (X.obj (op n)).Modules where
  app M :=
    { val := PresheafOfModules.homMk (counitPresheafHom M) (fun U r t => by
        change M.val.map (homOfLE (le_opensAt_id U.unop)).op
            (componentRingHom' (mk n U.unop) (𝟙 n) r • t (𝟙 n)) = r • counitApp M U.unop t
        rw [PresheafOfModules.map_smul]
        congr 1
        have := congrArg (fun f => f.hom r) (componentRingHom_id_comp (X := X) U.unop)
        rw [ringPresheaf_map_ιMap] at this
        exact this) }
  naturality {M N} f := by
    ext U t
    exact (congrArg (fun h => h (t (𝟙 n)))
      (f.val.naturality (homOfLE (le_opensAt_id U)).op)).symm

lemma unit_app_val_app (F : Modules X) (x : (TotalSite X)ᵒᵖ) (s : F.val.obj x) :
    ((unit X n).app F).val.app x s = unitApp F x s := rfl

lemma counit_app_app (M : (X.obj (op n)).Modules) (U : (X.obj (op n)).Opens)
    (t : Γ((restrict X n).obj ((levelPushforward X n).obj M), U)) :
    ((counit X n).app M).app U t = counitApp M U t := rfl

lemma counit_app_val_app (M : (X.obj (op n)).Modules) (U : (X.obj (op n)).Opens)
    (t : ((restrict X n).obj ((levelPushforward X n).obj M)).val.obj (op U)) :
    ((counit X n).app M).val.app (op U) t = counitApp M U t := rfl

lemma levelPushforward_map_val_app_apply {M N : (X.obj (op n)).Modules} (f : M ⟶ N)
    (x : (TotalSite X)ᵒᵖ) (t : ((levelPushforward X n).obj M).val.obj x) (ψ : x.unop.level ⟶ n) :
    ((levelPushforward X n).map f).val.app x t ψ = f.val.app (op (opensAt x.unop ψ)) (t ψ) := rfl

lemma levelPushforward_section_ext {M : (X.obj (op n)).Modules} {x : (TotalSite X)ᵒᵖ}
    {t t' : ((levelPushforward X n).obj M).val.obj x}
    (h : ∀ ψ : x.unop.level ⟶ n, (t : ∀ ψ : x.unop.level ⟶ n, M.val.obj (op (opensAt x.unop ψ))) ψ =
      (t' : ∀ ψ : x.unop.level ⟶ n, M.val.obj (op (opensAt x.unop ψ))) ψ) : t = t' :=
  funext h

lemma left_triangle_apply (F : Modules X) (U : (X.obj (op n)).Opens)
    (s : F.val.obj (op (mk n U))) :
    F.val.map (ιMap n (homOfLE (le_opensAt_id U))).op
      (F.val.map (homMk (𝟙 n) le_rfl : mk n (opensAt (mk n U) (𝟙 n)) ⟶ mk n U).op s) = s := by
  have h : (ιMap n (homOfLE (le_opensAt_id U)) ≫ homMk (𝟙 n) le_rfl :
      mk n U ⟶ mk n U) = 𝟙 _ := hom_ext (by simp)
  rw [← F.val.map_comp_apply, ← op_comp, h, op_id]
  exact presheafOfModules_map_id_apply F.val _ s

lemma right_triangle_apply (M : (X.obj (op n)).Modules) (x : (TotalSite X)ᵒᵖ)
    (t : ∀ ψ : x.unop.level ⟶ n, M.val.obj (op (opensAt x.unop ψ))) (ψ : x.unop.level ⟶ n) :
    M.val.map (homOfLE (le_opensAt_id (opensAt x.unop ψ))).op
      (M.val.map (homOfLE (opensAt_le (homMk ψ le_rfl :
        mk n (opensAt x.unop ψ) ⟶ x.unop) (𝟙 n))).op (t (ψ ≫ 𝟙 n))) = t ψ :=
  ((M.val.map_comp_apply (homOfLE (opensAt_le (homMk ψ le_rfl :
      mk n (opensAt x.unop ψ) ⟶ x.unop) (𝟙 n))).op
    (homOfLE (le_opensAt_id (opensAt x.unop ψ))).op (t (ψ ≫ 𝟙 n))).symm.trans
    (map_apply_congr M t (Category.comp_id ψ) _ (𝟙 _))).trans
      (presheafOfModules_map_id_apply M.val _ _)

lemma restrict_map_app {F G : Modules X} (f : F ⟶ G) (U : (X.obj (op n)).Opens)
    (s : Γ((restrict X n).obj F, U)) :
    ((restrict X n).map f).app U s = f.val.app (op (mk n U)) s := rfl

end LevelPushforward

open LevelPushforward in
variable (X n) in
/-- Restriction to the level `n` is left adjoint to `g_{n*}`. -/
noncomputable def restrictAdjunction : restrict X n ⊣ levelPushforward X n where
  unit := unit X n
  counit := counit X n
  left_triangle_components F := by
    refine Scheme.Modules.hom_ext _ _ fun U => AddCommGrpCat.ext fun s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply,
      ConcreteCategory.id_apply, counit_app_app, restrict_map_app]
    change F.val.map (ιMap n (homOfLE (le_opensAt_id U))).op
      (F.val.map (homMk (𝟙 n) le_rfl : mk n (opensAt (mk n U) (𝟙 n)) ⟶ mk n U).op s) = s
    exact left_triangle_apply F U s
  right_triangle_components M := by
    refine sheafOfModules_hom_ext fun x t => ?_
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply]
    refine levelPushforward_section_ext fun ψ => ?_
    rw [levelPushforward_map_val_app_apply]
    change M.val.map (homOfLE (le_opensAt_id (opensAt x.unop ψ))).op
      (M.val.map (homOfLE (opensAt_le (homMk ψ le_rfl :
        mk n (opensAt x.unop ψ) ⟶ x.unop) (𝟙 n))).op (t (ψ ≫ 𝟙 n))) = t ψ
    exact right_triangle_apply M x t ψ

instance (n : SimplexCategory) : (restrict X n).IsLeftAdjoint :=
  (restrictAdjunction X n).isLeftAdjoint

instance (n : SimplexCategory) : (levelPushforward X n).IsRightAdjoint :=
  (restrictAdjunction X n).isRightAdjoint

end AlgebraicGeometry.TotalSite
