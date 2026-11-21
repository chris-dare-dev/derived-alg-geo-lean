/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules

/-!
# The total site of a simplicial scheme

For a simplicial scheme `X`, the total site `X_total` of Stacks, Section 85.3,
has as objects the pairs `(n, U)` with `U` an open of `X_n`. A morphism
`(n, U) ⟶ (m, V)` is a map `φ : [m] ⟶ [n]` of `SimplexCategory` with
`U ≤ X(φ)⁻¹ V`. Its coverings are the families `(id, Uᵢ ⟶ U)` coming from a
covering of `U` in a single `X_n` (Stacks, Lemma 85.3.1, Tag 09WC, in the case
of Situation 85.3.3, Tag 09WE, where every `X_n` carries its Zariski site).

The category is Mathlib's Grothendieck construction of `[n] ↦ (Opens X_n)ᵒᵖ`,
taken opposite. The structure sheaf restricts to `𝒪_{X_n}` on each level, and
`TotalSite.Modules X` is Mathlib's category of sheaves of modules over it, so
it is Grothendieck abelian.

## Main definitions

* `AlgebraicGeometry.TotalSite X`: the category underlying `X_total`.
* `AlgebraicGeometry.TotalSite.ι X n`: the inclusion of the opens of `X_n`.
* `AlgebraicGeometry.TotalSite.topology X`: the topology of Tag 09WC.
* `AlgebraicGeometry.TotalSite.ringSheaf X` and `AlgebraicGeometry.TotalSite.Modules X`.
* `AlgebraicGeometry.TotalSite.restrict X n`: Stacks' `g_n⁻¹` on modules.

## Main results

* `AlgebraicGeometry.TotalSite.mem_topology_iff`: a sieve on `(n, U)` covers
  exactly when its trace on the opens of `X_n` covers `U`.
* `AlgebraicGeometry.TotalSite.isSheaf_iff`: a presheaf on `X_total` is a sheaf
  exactly when each of its restrictions to the levels is a sheaf. This is the
  sheaf condition used in Stacks, Lemma 85.3.4 (Tag 09WF); the equivalence with
  systems of sheaves is not formalized here.
* `ι X n` is continuous and cocontinuous (Stacks, Lemma 85.3.5, Tag 09WG).
-/

universe v u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace TotalSite

variable (X : SimplicialObject Scheme.{u})

/-- The functor `[n] ↦ (Opens X_n)ᵒᵖ`. A map `φ : [n] ⟶ [m]` acts by preimage
along `X(φ) : X_m ⟶ X_n`. -/
@[simps]
abbrev opensFunctor : SimplexCategory ⥤ Cat.{u, u} where
  obj n := Cat.of (X.obj (op n)).Opensᵒᵖ
  map φ := (Opens.map (X.map φ.op).base).op.toCatHom
  map_id n := by
    ext1
    refine CategoryTheory.Functor.ext (fun U => by simp) ?_
    intros
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp φ ψ := by
    ext1
    refine CategoryTheory.Functor.ext (fun U => by simp) ?_
    intros
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end TotalSite

/-- The category underlying the total site of a simplicial scheme (Stacks,
Lemma 85.3.1, Tag 09WC): the opposite of the Grothendieck construction of
`[n] ↦ (Opens X_n)ᵒᵖ`. -/
abbrev TotalSite (X : SimplicialObject Scheme.{u}) : Type u :=
  (Grothendieck (TotalSite.opensFunctor X))ᵒᵖ

namespace TotalSite

variable {X : SimplicialObject Scheme.{u}}

/-- The object `(n, U)` of the total site. -/
abbrev mk (n : SimplexCategory) (U : (X.obj (op n)).Opens) : TotalSite X :=
  op ⟨n, op U⟩

/-- The level `n` of an object `(n, U)`. -/
abbrev level (x : TotalSite X) : SimplexCategory :=
  (unop x : Grothendieck (opensFunctor X)).base

/-- The open `U` of an object `(n, U)`. -/
abbrev opens (x : TotalSite X) : (X.obj (op x.level)).Opens :=
  unop (unop x : Grothendieck (opensFunctor X)).fiber

lemma mk_level_opens (x : TotalSite X) : mk x.level x.opens = x := rfl

/-- The underlying map of `SimplexCategory` of a morphism of the total site. -/
def Hom.base {x y : TotalSite X} (f : x ⟶ y) : y.level ⟶ x.level :=
  (Quiver.Hom.unop f : Grothendieck.Hom _ _).base

@[simp] lemma Hom.base_id (x : TotalSite X) : Hom.base (𝟙 x) = 𝟙 _ := rfl

@[simp] lemma Hom.base_comp {x y z : TotalSite X} (f : x ⟶ y) (g : y ⟶ z) :
    Hom.base (f ≫ g) = Hom.base g ≫ Hom.base f := rfl

/-- A morphism of the total site is determined by its map of `SimplexCategory`. -/
lemma hom_ext {x y : TotalSite X} {f g : x ⟶ y} (h : Hom.base f = Hom.base g) : f = g :=
  Quiver.Hom.unop_inj (Grothendieck.ext _ _ h (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

/-- The morphism `(n, U) ⟶ (n, V)` given by an inclusion `U ≤ V` of opens of `X_n`. -/
def ιMap (n : SimplexCategory) {U V : (X.obj (op n)).Opens} (f : U ⟶ V) : mk n U ⟶ mk n V :=
  ((Grothendieck.ι (opensFunctor X) n).map f.op).op

@[simp] lemma Hom.base_ιMap (n : SimplexCategory) {U V : (X.obj (op n)).Opens} (f : U ⟶ V) :
    Hom.base (ιMap n f) = 𝟙 n := rfl

variable (X) in
/-- The inclusion of the opens of `X_n` into the total site. -/
abbrev ι (n : SimplexCategory) : (X.obj (op n)).Opens ⥤ TotalSite X where
  obj U := mk n U
  map f := ιMap n f
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext (by simp)

/-- The morphism `(m, W) ⟶ (n, U)` given by `φ : [n] ⟶ [m]` and `W ≤ X(φ)⁻¹ U`. -/
def homMk {n m : SimplexCategory} (φ : n ⟶ m) {U : (X.obj (op n)).Opens}
    {W : (X.obj (op m)).Opens} (h : W ≤ (Opens.map (X.map φ.op).base).obj U) :
    mk m W ⟶ mk n U :=
  Quiver.Hom.op (show (⟨n, op U⟩ : Grothendieck (opensFunctor X)) ⟶ ⟨m, op W⟩ from
    ⟨φ, (homOfLE h).op⟩)

@[simp] lemma Hom.base_homMk {n m : SimplexCategory} (φ : n ⟶ m) {U : (X.obj (op n)).Opens}
    {W : (X.obj (op m)).Opens} (h : W ≤ (Opens.map (X.map φ.op).base).obj U) :
    Hom.base (homMk φ h) = φ := rfl

/-- The inequality of opens carried by a morphism of the total site. -/
lemma Hom.le {x y : TotalSite X} (f : x ⟶ y) :
    x.opens ≤ (Opens.map (X.map (Hom.base f).op).base).obj y.opens :=
  leOfHom (Quiver.Hom.unop f : Grothendieck.Hom _ _).fiber.unop

section Helpers

/-- Morphisms of sheaves of modules that agree on all sections are equal. -/
lemma sheafOfModules_hom_ext {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} {f g : M ⟶ N}
    (h : ∀ U (x : M.val.obj U), f.val.app U x = g.val.app U x) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.Hom.ext (funext fun U =>
    ModuleCat.hom_ext (LinearMap.ext (h U))))

lemma presheafOfModules_map_id_apply {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) (U : Cᵒᵖ) (x : M.obj U) : M.map (𝟙 U) x = x :=
  congrArg (fun f => f x) (M.presheaf.map_id U)

/-- Two restrictions of a section of a module on a scheme along composable
inclusions with the same endpoints agree. -/
lemma schemeModules_map_map_eq {Y : Scheme.{u}} (M : Y.Modules) {U V V' W : Y.Opensᵒᵖ}
    (a₁ : U ⟶ V) (a₂ : V ⟶ W) (b₁ : U ⟶ V') (b₂ : V' ⟶ W) (s : M.val.obj U) :
    M.val.map a₂ (M.val.map a₁ s) = M.val.map b₂ (M.val.map b₁ s) :=
  (M.val.map_comp_apply a₁ a₂ s).symm.trans ((M.val.congr_map_apply
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s).trans (M.val.map_comp_apply b₁ b₂ s))

lemma schemeModules_map_map_eq_self {Y : Scheme.{u}} (M : Y.Modules) {U V : Y.Opensᵒᵖ}
    (a₁ : U ⟶ V) (a₂ : V ⟶ U) (s : M.val.obj U) :
    M.val.map a₂ (M.val.map a₁ s) = s :=
  (M.val.map_comp_apply a₁ a₂ s).symm.trans ((M.val.congr_map_apply
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s).trans
      (presheafOfModules_map_id_apply M.val _ s))

end Helpers

section Topology

variable (X) in
/-- The coverage of Stacks, Lemma 85.3.1 (Tag 09WC): the covering families of
`(n, U)` are the images of the covering sieves of `U` in `X_n`. -/
def coverage : Coverage (TotalSite X) where
  coverings x := {T | ∃ R : Sieve x.opens, R ∈ Opens.grothendieckTopology _ x.opens ∧
    T = (R : Presieve x.opens).functorPushforward (ι X x.level)}
  pullback := by
    rintro x y f T ⟨R, hR, rfl⟩
    refine ⟨((R.functorPushforward (Opens.map (X.map (Hom.base f).op).base)).pullback
      (homOfLE (Hom.le f)) : Presieve y.opens).functorPushforward (ι X y.level),
      ⟨_, (Opens.grothendieckTopology _).pullback_stable _
        ((coverPreserving_opens_map _).cover_preserve hR), rfl⟩, ?_⟩
    rintro z g ⟨V, k, h, ⟨U', r, l, hr, hl⟩, rfl⟩
    exact ⟨mk x.level U', h ≫ homMk (Hom.base f) (leOfHom l), (ι X x.level).map r,
      ⟨U', r, 𝟙 _, hr, by simp⟩, hom_ext (by simp)⟩

variable (X) in
/-- The topology of the total site (Stacks, Lemma 85.3.1, Tag 09WC). -/
def topology : GrothendieckTopology (TotalSite X) :=
  (coverage X).toGrothendieck

/-- A sieve on `(n, U)` covers exactly when its trace on the opens of `X_n`
covers `U`. -/
theorem mem_topology_iff {x : TotalSite X} (S : Sieve x) :
    S ∈ topology X x ↔
      S.functorPullback (ι X x.level) ∈ Opens.grothendieckTopology _ x.opens := by
  constructor
  · intro hS
    replace hS := Coverage.mem_toGrothendieck.mp hS
    induction hS with
    | of x T hT =>
      obtain ⟨R, hR, rfl⟩ := hT
      refine (Opens.grothendieckTopology _).superset_covering ?_ hR
      intro V g hg
      exact Sieve.le_generate _ _ _ ⟨V, g, 𝟙 _, hg, by simp⟩
    | top x =>
      exact (Opens.grothendieckTopology _).superset_covering (fun _ _ _ => trivial)
        ((Opens.grothendieckTopology _).top_mem _)
    | transitive x R S _ _ ihR ihS =>
      refine (Opens.grothendieckTopology _).transitive ihR _ ?_
      intro V g hg
      rw [← Sieve.functorPullback_pullback]
      exact ihS hg
  · intro hS
    refine Coverage.mem_toGrothendieck_sieves_of_superset _ ?_ ⟨_, hS, rfl⟩
    rintro y f ⟨V, g, h, hg, rfl⟩
    exact S.downward_closed hg h

lemma coverPreserving_ι (n : SimplexCategory) :
    CoverPreserving (Opens.grothendieckTopology (X.obj (op n))) (topology X) (ι X n) where
  cover_preserve {_ _} hS := (mem_topology_iff _).2 <|
    (Opens.grothendieckTopology _).superset_covering (Sieve.le_functorPushforward_pullback _ _) hS

lemma compatiblePreserving_ι (n : SimplexCategory) :
    CompatiblePreserving.{v} (topology X) (ι X n) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  have hb : Hom.base f₂ = Hom.base f₁ := by simpa using (congrArg Hom.base eq).symm
  have h₂ := Hom.le f₂
  rw [hb] at h₂
  let f₃ : W ⟶ (ι X n).obj (Y₁ ⊓ Y₂) := homMk (W := W.opens) (Hom.base f₁) (le_inf (Hom.le f₁) h₂)
  have e₁ : f₁ = f₃ ≫ (ι X n).map (homOfLE inf_le_left) :=
    hom_ext (by simp only [Hom.base_comp, Hom.base_ιMap, Category.id_comp]; rfl)
  have e₂ : f₂ = f₃ ≫ (ι X n).map (homOfLE inf_le_right) :=
    hom_ext (by simp only [Hom.base_comp, Hom.base_ιMap, Category.id_comp]; exact hb)
  have key := hx (homOfLE (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)) (homOfLE (inf_le_right : Y₁ ⊓ Y₂ ≤ Y₂))
    hg₁ hg₂ (Subsingleton.elim _ _)
  dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at key
  rw [e₁, e₂, op_comp, op_comp, ℱ.obj.map_comp, ℱ.obj.map_comp, types_comp_apply,
    types_comp_apply, key]

instance isContinuous_ι (n : SimplexCategory) :
    (ι X n).IsContinuous (Opens.grothendieckTopology (X.obj (op n))) (topology X) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_ι n) (coverPreserving_ι n)

instance isCocontinuous_ι (n : SimplexCategory) :
    (ι X n).IsCocontinuous (Opens.grothendieckTopology (X.obj (op n))) (topology X) where
  cover_lift {_ S} hS := (mem_topology_iff S).1 hS

/-- A presheaf whose restriction to `X_n` is a sheaf for `R` is a sheaf for the
image of `R` in the total site. -/
lemma isSheafFor_functorPushforward {n : SimplexCategory} {U : (X.obj (op n)).Opens}
    (P : (TotalSite X)ᵒᵖ ⥤ Type*) (R : Presieve U)
    (h : Presieve.IsSheafFor ((ι X n).op ⋙ P) R) :
    Presieve.IsSheafFor P (R.functorPushforward (ι X n)) := by
  intro x hx
  let y : Presieve.FamilyOfElements ((ι X n).op ⋙ P) R :=
    fun V g hg => x ((ι X n).map g) ⟨V, g, 𝟙 _, hg, by simp⟩
  have hy : y.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
    exact hx ((ι X n).map g₁) ((ι X n).map g₂) _ _ (hom_ext (by simp))
  obtain ⟨t, ht, ht'⟩ := h y hy
  refine ⟨t, ?_, fun t' h' => ht' t' fun V g hg => h' _ _⟩
  rintro z f ⟨V, g, k, hg, rfl⟩
  have := ht g hg
  dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at this
  rw [op_comp, P.map_comp, types_comp_apply, this]
  simpa using hx k (𝟙 _) _ ⟨V, g, k, hg, rfl⟩ (by simp)

/-- A presheaf on the total site is a sheaf exactly when its restriction to
every level is a sheaf. -/
theorem isSheaf_iff {A : Type*} [Category* A] (P : (TotalSite X)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (topology X) P ↔
      ∀ n, Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj (op n))) ((ι X n).op ⋙ P) := by
  refine ⟨fun h n => Functor.op_comp_isSheaf_of_isSheaf _ _ _ P h, fun h E => ?_⟩
  rw [topology, Presieve.isSheaf_coverage]
  rintro x T ⟨R, hR, rfl⟩
  exact isSheafFor_functorPushforward _ _ (h x.level E R hR)

end Topology

section Ring

/-- `Scheme.Hom.appLE` along equal morphisms of schemes. -/
lemma appLE_eq_of_eq {A B : Scheme.{u}} {f g : A ⟶ B}
    (h : f = g) (U : B.Opens) (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

/-- `Scheme.Hom.appLE` of an identity morphism is a restriction map. -/
lemma id_appLE {A : Scheme.{u}} (U V : A.Opens) (e : V ≤ (𝟙 A : A ⟶ A) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 A) U V e = A.presheaf.map (homOfLE e).op :=
  rfl

variable (X) in
/-- The structure presheaf of rings of the total site, `(n, U) ↦ 𝒪_{X_n}(U)`.
A morphism `(n, U) ⟶ (m, V)` over `φ : [m] ⟶ [n]` acts by
`X(φ)^♯ : 𝒪_{X_m}(V) ⟶ 𝒪_{X_n}(U)`. -/
def ringPresheaf : (TotalSite X)ᵒᵖ ⥤ RingCat.{u} where
  obj x := (forget₂ CommRingCat RingCat).obj Γ(X.obj (op x.unop.level), x.unop.opens)
  map {x y} g := (forget₂ CommRingCat RingCat).map
    ((X.map (Hom.base g.unop).op).appLE x.unop.opens y.unop.opens (Hom.le g.unop))
  map_id x := by
    rw [appLE_eq_of_eq (show X.map (Hom.base (𝟙 x).unop).op = 𝟙 _ by simp),
      id_appLE]
    exact ((X.obj (op x.unop.level)).ringCatSheaf.obj.map_id _)
  map_comp {x y z} f g := by
    rw [← CategoryTheory.Functor.map_comp, Scheme.Hom.appLE_comp_appLE]
    exact congrArg _ (appLE_eq_of_eq (by simp [← CategoryTheory.Functor.map_comp]) _ _ _)

lemma ringPresheaf_map_ιMap (n : SimplexCategory) {U V : (X.obj (op n)).Opens} (i : U ⟶ V) :
    (ringPresheaf X).map (ιMap n i).op =
      (forget₂ CommRingCat RingCat).map ((X.obj (op n)).presheaf.map i.op) := by
  change (forget₂ CommRingCat RingCat).map
    ((X.map (Hom.base (ιMap n i)).op).appLE V U (Hom.le (ιMap n i))) = _
  rw [appLE_eq_of_eq (show X.map (Hom.base (ιMap n i)).op = 𝟙 _ by simp),
    id_appLE]
  rfl

variable (X) in
/-- The restriction of the structure presheaf to the level `n` is `𝒪_{X_n}`. -/
def ringPresheafRestrictIso (n : SimplexCategory) :
    (ι X n).op ⋙ ringPresheaf X ≅ (X.obj (op n)).ringCatSheaf.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun i =>
    (Category.comp_id _).trans ((ringPresheaf_map_ιMap n i.unop).trans (Category.id_comp _).symm))

variable (X) in
/-- The structure sheaf of rings of the total site. -/
def ringSheaf : Sheaf (topology X) RingCat.{u} :=
  ⟨ringPresheaf X, (isSheaf_iff _).2 fun n =>
    (Presheaf.isSheaf_of_iso_iff (ringPresheafRestrictIso X n)).2
      (X.obj (op n)).ringCatSheaf.property⟩

end Ring


section Modules

variable (X) in
/-- Sheaves of modules on the total site of `X`. -/
abbrev Modules : Type (u + 1) :=
  SheafOfModules.{u} (ringSheaf X)

example : IsGrothendieckAbelian.{u} (Modules X) := inferInstance

variable (X) in
/-- The identification of `𝒪_{X_n}` with the restriction of the structure sheaf. -/
def ringSheafRestrict (n : SimplexCategory) :
    (X.obj (op n)).ringCatSheaf ⟶
      ((ι X n).sheafPushforwardContinuous RingCat.{u} _ (topology X)).obj (ringSheaf X) where
  hom := (ringPresheafRestrictIso X n).inv

variable (X) in
/-- Restriction of modules to the level `n`: Stacks' `g_n⁻¹` (Lemma 85.3.5, Tag 09WG). -/
noncomputable def restrict (n : SimplexCategory) : Modules X ⥤ (X.obj (op n)).Modules :=
  SheafOfModules.pushforward (ringSheafRestrict X n)

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to a level has a left adjoint: Mathlib's pullback of sheaves of
modules along `ι X n`. -/
instance (n : SimplexCategory) : (restrict X n).IsRightAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward _).IsRightAdjoint

@[simp] lemma restrict_obj_val_obj (n : SimplexCategory) (F : Modules X)
    (U : ((X.obj (op n)).Opens)ᵒᵖ) :
    ((restrict X n).obj F).val.obj U = (ModuleCat.restrictScalars
      ((ringSheafRestrict X n).hom.app U).hom).obj (F.val.obj (op (mk n (unop U)))) := rfl

@[simp] lemma restrict_map_val_app (n : SimplexCategory) {F G : Modules X} (f : F ⟶ G)
    (U : ((X.obj (op n)).Opens)ᵒᵖ) :
    ((restrict X n).map f).val.app U = (ModuleCat.restrictScalars
      ((ringSheafRestrict X n).hom.app U).hom).map (f.val.app (op (mk n (unop U)))) := rfl

/-- The morphisms `(m, X(φ)⁻¹ U) ⟶ (n, U)` over `φ : [n] ⟶ [m]`, as a natural
transformation of functors on the opens of `X_n`. -/
@[simps]
def cartesianNatTrans {n m : SimplexCategory} (φ : n ⟶ m) :
    Opens.map (X.map φ.op).base ⋙ ι X m ⟶ ι X n where
  app U := homMk φ le_rfl
  naturality _ _ _ := hom_ext (by simp)

lemma transition_ringHom_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    letI := Functor.isContinuous_comp (Opens.map (X.map φ.op).base) (ι X m)
      (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) (topology X)
    ringSheafRestrict X n ≫ (Functor.sheafPushforwardContinuousNatTrans (cartesianNatTrans φ)
        RingCat.{u} _ (topology X)).app (ringSheaf X) =
      (X.map φ.op).toRingCatSheafHom ≫
        ((Opens.map (X.map φ.op).base).sheafPushforwardContinuous RingCat.{u} _ _).map
          (ringSheafRestrict X m) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  change (forget₂ CommRingCat RingCat).map ((X.map φ.op).appLE (unop U)
    ((Opens.map (X.map φ.op).base).obj (unop U)) le_rfl) =
      (forget₂ CommRingCat RingCat).map ((X.map φ.op).app (unop U))
  rw [Scheme.Hom.appLE_eq_app]

variable (X) in
/-- The transition maps `F_n ⟶ X(φ)_* F_m` of a module on the total site, for
`φ : [n] ⟶ [m]`; on sections they are the restriction maps of `F` along the
morphisms `(m, X(φ)⁻¹ U) ⟶ (n, U)`. -/
noncomputable def transition {n m : SimplexCategory} (φ : n ⟶ m) :
    restrict X n ⟶ restrict X m ⋙ Scheme.Modules.pushforward (X.map φ.op) :=
  letI := Functor.isContinuous_comp (Opens.map (X.map φ.op).base) (ι X m)
    (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) (topology X)
  SheafOfModules.pushforwardNatTrans (ringSheafRestrict X n) (cartesianNatTrans φ) ≫
    (SheafOfModules.pushforwardCongr (transition_ringHom_eq φ)).hom ≫
      (SheafOfModules.pushforwardComp _ _).inv

lemma transition_app_val_app {n m : SimplexCategory} (φ : n ⟶ m) (F : Modules X)
    (U : ((X.obj (op n)).Opens)ᵒᵖ) (x) :
    ((transition X φ).app F).val.app U x = F.val.map (homMk φ le_rfl).op x := rfl

variable (X) in
/-- The comparison maps `X(φ)^* F_n ⟶ F_m` of modules on the total site, for
`φ : [n] ⟶ [m]`: on each module, the adjoint of `transition X φ`. -/
noncomputable def transitionPullback {n m : SimplexCategory} (φ : n ⟶ m) :
    restrict X n ⋙ Scheme.Modules.pullback (X.map φ.op) ⟶ restrict X m :=
  Functor.whiskerRight (transition X φ) (Scheme.Modules.pullback (X.map φ.op)) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (restrict X m) (Scheme.Modules.pullbackPushforwardAdjunction _).counit ≫
    (Functor.rightUnitor _).hom

lemma transitionPullback_app {n m : SimplexCategory} (φ : n ⟶ m) (F : Modules X) :
    (transitionPullback X φ).app F =
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ.op)).homEquiv _ _).symm
        ((transition X φ).app F) := by
  simp [transitionPullback, Adjunction.homEquiv_counit]

variable (X) in
/-- Cartesian modules on the total site (Stacks, Definition 85.12.1, Tag 0D7G):
the comparison maps `X(φ)^* F_n ⟶ F_m` are isomorphisms for every `φ`. -/
def IsCartesian : ObjectProperty (Modules X) :=
  fun F => ∀ ⦃n m : SimplexCategory⦄ (φ : n ⟶ m), IsIso ((transitionPullback X φ).app F)

end Modules

end TotalSite

end AlgebraicGeometry
