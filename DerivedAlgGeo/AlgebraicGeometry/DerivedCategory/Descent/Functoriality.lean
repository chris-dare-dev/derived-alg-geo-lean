/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.LevelPushforward

/-!
# Functoriality of the total site in the simplicial scheme

A morphism `f : X ⟶ Z` of simplicial schemes gives the continuous functor
`(n, V) ↦ (n, f_n⁻¹ V)` from the total site of `Z` to that of `X`, and a map of
structure sheaves. Mathlib's pushforward and pullback of sheaves of modules
along it give `f_total,*` and `f_total^*`.

Restriction to a level commutes with `f_total^*`:
`g_n⁻¹ (f_total^* G) ≅ f_n^* (g_n⁻¹ G)`. Both sides are left adjoints, and
their right adjoints `f_total,* ∘ g_{n*}` and `g_{n*} ∘ f_{n,*}` agree on
sections, because `X(ψ)⁻¹ f_m⁻¹ = f_n⁻¹ Z(ψ)⁻¹` for every `ψ : [m] ⟶ [n]`.

## Main definitions

* `AlgebraicGeometry.TotalSite.comap f`: the functor of sites.
* `AlgebraicGeometry.TotalSite.pushforwardAlong f` and
  `AlgebraicGeometry.TotalSite.pullbackAlong f`, with `pullbackAlongAdjunction f`.
* `AlgebraicGeometry.TotalSite.pullbackAlongRestrictIso f n`:
  `g_n⁻¹ ∘ f_total^* ≅ f_n^* ∘ g_n⁻¹`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.TotalSite

variable {X Z : SimplicialObject Scheme.{u}} (f : X ⟶ Z)

lemma comap_le {x y : TotalSite Z} (g : x ⟶ y) :
    (Opens.map (f.app (op x.level)).base).obj x.opens ≤
      (Opens.map (X.map (Hom.base g).op).base).obj
        ((Opens.map (f.app (op y.level)).base).obj y.opens) := by
  change _ ≤ (Opens.map (X.map (Hom.base g).op ≫ f.app (op y.level)).base).obj y.opens
  rw [f.naturality (Hom.base g).op]
  exact (Opens.map (f.app (op x.level)).base).monotone (Hom.le g)

/-- The functor `(n, V) ↦ (n, f_n⁻¹ V)` of total sites induced by `f : X ⟶ Z`. -/
abbrev comap : TotalSite Z ⥤ TotalSite X where
  obj x := mk x.level ((Opens.map (f.app (op x.level)).base).obj x.opens)
  map g := homMk (Hom.base g) (comap_le f g)
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

@[simp] lemma Hom.base_comap_map {x y : TotalSite Z} (g : x ⟶ y) :
    Hom.base ((comap f).map g) = Hom.base g := rfl

/-- `comap f` restricts on each level to the preimage functor of `f_n`. -/
def ιCompComapIso (n : SimplexCategory) :
    ι Z n ⋙ comap f ≅ Opens.map (f.app (op n)).base ⋙ ι X n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => hom_ext rfl)

instance isContinuous_comap : (comap f).IsContinuous (topology Z) (topology X) where
  op_comp_isSheaf_of_types G := by
    rw [← isSheaf_iff_isSheaf_of_type, isSheaf_iff]
    intro n
    refine (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight
      (NatIso.op (ιCompComapIso f n)).symm G.obj)).2 ?_
    exact Functor.op_comp_isSheaf_of_isSheaf (Opens.map (f.app (op n)).base) _ _ _
      ((isSheaf_iff _).1 G.property n)

lemma comapRingHom_naturality {x y : TotalSite Z} (g : x ⟶ y) :
    (Z.map (Hom.base g).op).appLE y.opens x.opens (Hom.le g) ≫
        (f.app (op x.level)).app x.opens =
      (f.app (op y.level)).app y.opens ≫
        (X.map (Hom.base g).op).appLE ((Opens.map (f.app (op y.level)).base).obj y.opens)
          ((Opens.map (f.app (op x.level)).base).obj x.opens) (comap_le f g) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (f.naturality (Hom.base g).op).symm _ _ _

/-- The map of structure sheaves `𝒪_{Z,total} ⟶ (comap f)_* 𝒪_{X,total}`. -/
def comapRingHom :
    ringSheaf Z ⟶ ((comap f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringSheaf X) where
  hom :=
    { app x := (forget₂ CommRingCat RingCat).map ((f.app (op x.unop.level)).app x.unop.opens)
      naturality {x y} g := by
        exact ((forget₂ CommRingCat RingCat).map_comp _ _).symm.trans
          ((congrArg (forget₂ CommRingCat RingCat).map (comapRingHom_naturality f g.unop)).trans
            ((forget₂ CommRingCat RingCat).map_comp _ _)) }

/-- `f_total,*`: pushforward of modules along a morphism of simplicial schemes. -/
noncomputable def pushforwardAlong : Modules X ⥤ Modules Z :=
  SheafOfModules.pushforward (comapRingHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- `f_total^*`: pullback of modules along a morphism of simplicial schemes. -/
noncomputable def pullbackAlong : Modules Z ⥤ Modules X :=
  SheafOfModules.pullback (comapRingHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- `f_total^* ⊣ f_total,*`. -/
noncomputable def pullbackAlongAdjunction : pullbackAlong f ⊣ pushforwardAlong f :=
  SheafOfModules.pullbackPushforwardAdjunction _

section BaseChange

open LevelPushforward

variable {n : SimplexCategory}

lemma opensAt_comap (x : TotalSite Z) (ψ : x.level ⟶ n) :
    opensAt ((comap f).obj x) ψ = (Opens.map (f.app (op n)).base).obj (opensAt x ψ) := by
  change (Opens.map (X.map ψ.op ≫ f.app (op x.level)).base).obj x.opens =
    (Opens.map (f.app (op n) ≫ Z.map ψ.op).base).obj x.opens
  rw [f.naturality ψ.op]

lemma baseChange_ringHom (x : TotalSite Z) (ψ : x.level ⟶ n) :
    (f.app (op x.level)).app x.opens ≫
        (X.map ψ.op).appLE ((Opens.map (f.app (op x.level)).base).obj x.opens)
          (opensAt ((comap f).obj x) ψ) le_rfl ≫
        (X.obj (op n)).presheaf.map (homOfLE (opensAt_comap f x ψ).ge).op =
      (Z.map ψ.op).appLE x.opens (opensAt x ψ) le_rfl ≫ (f.app (op n)).app (opensAt x ψ) := by
  rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (f.naturality ψ.op) _ _ _

lemma baseChange_ringHom' (x : TotalSite Z) (ψ : x.level ⟶ n) :
    (Z.map ψ.op).appLE x.opens (opensAt x ψ) le_rfl ≫ (f.app (op n)).app (opensAt x ψ) ≫
        (X.obj (op n)).presheaf.map (homOfLE (opensAt_comap f x ψ).le).op =
      (f.app (op x.level)).app x.opens ≫
        (X.map ψ.op).appLE ((Opens.map (f.app (op x.level)).base).obj x.opens)
          (opensAt ((comap f).obj x) ψ) le_rfl := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq (f.naturality ψ.op).symm _ _ _

variable (M : (X.obj (op n)).Modules)

/-- The comparison `f_total,* (g_{n*} M) ⟶ g_{n*} (f_{n,*} M)` on sections. -/
noncomputable def baseChangeHomApp (x : (TotalSite Z)ᵒᵖ)
    (t : ∀ ψ : x.unop.level ⟶ n, M.val.obj (op (opensAt ((comap f).obj x.unop) ψ)))
    (ψ : x.unop.level ⟶ n) :
    M.val.obj (op ((Opens.map (f.app (op n)).base).obj (opensAt x.unop ψ))) :=
  M.val.map (homOfLE (opensAt_comap f x.unop ψ).ge).op (t ψ)

/-- The inverse comparison on sections. -/
noncomputable def baseChangeInvApp (x : (TotalSite Z)ᵒᵖ)
    (t : ∀ ψ : x.unop.level ⟶ n,
      M.val.obj (op ((Opens.map (f.app (op n)).base).obj (opensAt x.unop ψ))))
    (ψ : x.unop.level ⟶ n) :
    M.val.obj (op (opensAt ((comap f).obj x.unop) ψ)) :=
  M.val.map (homOfLE (opensAt_comap f x.unop ψ).le).op (t ψ)

/-- The comparison `f_total,* (g_{n*} M) ⟶ g_{n*} (f_{n,*} M)` on abelian presheaves. -/
noncomputable def baseChangeHomPresheaf :
    ((pushforwardAlong f).obj ((levelPushforward X n).obj M)).val.presheaf ⟶
      ((levelPushforward Z n).obj ((Scheme.Modules.pushforward (f.app (op n))).obj M)).val.presheaf
    where
  app x := AddCommGrpCat.ofHom
    { toFun := baseChangeHomApp f M x
      map_zero' := funext fun _ => map_zero _
      map_add' := fun _ _ => funext fun _ => map_add _ _ _ }
  naturality _ _ _ := AddCommGrpCat.ext fun _ => funext fun _ =>
    schemeModules_map_map_eq M _ _ _ _ _

/-- The inverse comparison on abelian presheaves. -/
noncomputable def baseChangeInvPresheaf :
    ((levelPushforward Z n).obj ((Scheme.Modules.pushforward (f.app (op n))).obj M)).val.presheaf ⟶
      ((pushforwardAlong f).obj ((levelPushforward X n).obj M)).val.presheaf where
  app x := AddCommGrpCat.ofHom
    { toFun := baseChangeInvApp f M x
      map_zero' := funext fun _ => map_zero _
      map_add' := fun _ _ => funext fun _ => map_add _ _ _ }
  naturality _ _ _ := AddCommGrpCat.ext fun _ => funext fun _ =>
    schemeModules_map_map_eq M _ _ _ _ _

/-- The comparison `f_total,* (g_{n*} M) ≅ g_{n*} (f_{n,*} M)`. -/
noncomputable def baseChangeIsoApp :
    (pushforwardAlong f).obj ((levelPushforward X n).obj M) ≅
      (levelPushforward Z n).obj ((Scheme.Modules.pushforward (f.app (op n))).obj M) where
  hom :=
    { val := PresheafOfModules.homMk (baseChangeHomPresheaf f M) (fun x r t => funext fun ψ => by
        refine (PresheafOfModules.map_smul M.val _ _ _).trans ?_
        exact congrArg (· • _) (congrArg (fun φ => φ r) (baseChange_ringHom f x.unop ψ))) }
  inv :=
    { val := PresheafOfModules.homMk (baseChangeInvPresheaf f M) (fun x r t => funext fun ψ => by
        refine (PresheafOfModules.map_smul M.val _ _ _).trans ?_
        exact congrArg (· • _) (congrArg (fun φ => φ r) (baseChange_ringHom' f x.unop ψ))) }
  hom_inv_id := sheafOfModules_hom_ext fun x t => funext fun ψ =>
    schemeModules_map_map_eq_self M _ _ _
  inv_hom_id := sheafOfModules_hom_ext fun x t => funext fun ψ =>
    schemeModules_map_map_eq_self M _ _ _

variable (n) in
/-- Base change for `g_{n*}`: `f_total,* ∘ g_{n*} ≅ g_{n*} ∘ f_{n,*}`. -/
noncomputable def baseChangeIso :
    levelPushforward X n ⋙ pushforwardAlong f ≅
      Scheme.Modules.pushforward (f.app (op n)) ⋙ levelPushforward Z n :=
  NatIso.ofComponents (fun M => baseChangeIsoApp f M) (fun {M N} g =>
    sheafOfModules_hom_ext fun x t => by
      rw [SheafOfModules.comp_val, SheafOfModules.comp_val, PresheafOfModules.comp_app,
        PresheafOfModules.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      refine levelPushforward_section_ext fun ψ => ?_
      exact (congrArg (fun k => k ((t : ∀ ψ : x.unop.level ⟶ n,
        M.val.obj (op (opensAt ((comap f).obj x.unop) ψ))) ψ))
        (g.val.naturality (homOfLE (opensAt_comap f x.unop ψ).ge).op)).symm)

end BaseChange

variable (n : SimplexCategory) in
/-- Restriction to a level commutes with pullback along a morphism of simplicial
schemes: `g_n⁻¹ ∘ f_total^* ≅ f_n^* ∘ g_n⁻¹`. -/
noncomputable def pullbackAlongRestrictIso :
    pullbackAlong f ⋙ restrict X n ≅ restrict Z n ⋙ Scheme.Modules.pullback (f.app (op n)) :=
  Adjunction.leftAdjointUniq ((pullbackAlongAdjunction f).comp (restrictAdjunction X n))
    (((restrictAdjunction Z n).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f.app (op n)))).ofNatIsoRight
        (baseChangeIso f n).symm)

end AlgebraicGeometry.TotalSite
