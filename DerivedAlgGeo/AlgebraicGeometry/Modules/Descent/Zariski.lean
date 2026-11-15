/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.RestrictionComp
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections

/-!
# Sheaves of modules glue along Zariski covers

`X ↦ X.Modules`, with pullback, is a stack for the big Zariski topology
`Scheme.zariskiTopology`: morphisms of module sheaves that agree on overlaps glue uniquely, and
module sheaves on the members of a Zariski cover, with gluing isomorphisms satisfying the
cocycle condition, glue to a module sheaf on the base.

## Main definitions

* `AlgebraicGeometry.Scheme.modulesPseudofunctor`: Mathlib's `Scheme.Modules.pseudofunctor`
  followed by `Adj.forget₁`, the `Cat`-valued pseudofunctor `X ↦ X.Modules`.
* `AlgebraicGeometry.Scheme.ZariskiDescent.glue`: the module sheaf glued from a descent datum
  along a family of open immersions, as the subsheaf of compatible families of
  `∏ᵢ (fᵢ)_* Mᵢ`.
* `AlgebraicGeometry.Scheme.ZariskiDescent.glueIso`: its descent datum is the given one.

## Main results

* `AlgebraicGeometry.Scheme.modulesPseudofunctor_isPrestack`: morphisms glue
  ([Stacks, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)).
* `AlgebraicGeometry.Scheme.modulesPseudofunctor_isStack`: objects glue
  ([Stacks, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL),
  [Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)).

## Implementation notes

### Restriction rather than pullback

The pseudofunctor uses `Modules.pullback`, while sections are computed for restriction along
an open immersion. A descent datum is transported to restrictions by
`restrictFunctorIsoPullback`; its gluing morphism over a test object `q : Y ⟶ S` mapping to
`X i` and `X j` by open immersions is `ZariskiDescent.trans`. The compatibility of the
identification with the compositors (`Modules/Pullback/RestrictionComp.lean`) turns the
cocycle and restriction conditions of the descent datum into the corresponding conditions on
`trans`.

### Overlaps

The overlap of `f i` and `f j` is the open subscheme on `(f i).opensRange ⊓ (f j).opensRange`
of `S`, not the fibre product `X i ×_S X j`; its two open immersions into `X i` and `X j` are
lifts through `f i` and `f j`. Compatibility with the gluing morphisms over these overlaps
implies compatibility over every test object (`ZariskiDescent.comm_of_inter`), since every
test object of a descent datum maps into an overlap.

### Gluing

The glued module is the subsheaf of `∏ᵢ (fᵢ)_* Mᵢ` of families of sections whose components
agree on overlaps under the gluing morphisms: the equalizer of the two maps to
`∏ᵢⱼ (fᵢⱼ)_* (pᵢⱼ)^* Mⱼ`, cut out as a `SheafOfModules.Submodule`. The restriction of this
sheaf to `X k` is compared with `Mₖ` section by section. Mathlib has no extension by zero, so
the comparison is proved bijective on sections directly, using the cocycle condition on
triple overlaps for surjectivity.

### Morphisms

A morphism of descent data is glued on the basis of `S` formed by the images of opens of the
`X i`, with Mathlib's `TopCat.Sheaf.restrictHomEquivHom`.

### Small covers

A Zariski cover may be indexed by a type in any universe, while products in `S.Modules` need
the index in universe `u`. `modulesPseudofunctor_isStack` therefore glues along the subfamily
indexed by the points of `S`, and passes to the whole cover with
`Pseudofunctor.IsStackFor.of_le`.

## References

* [Stacks, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK): Sheaves on Spaces,
  Section 6.33, glueing sheaves; Lemmas 6.33.1 (04TN), 6.33.2 (00AL), 6.33.4 (00AN).

## Tags

module sheaf, Zariski topology, descent, gluing, stack
-/

open CategoryTheory Bicategory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Two successive restrictions of a section are the restriction along the composite. -/
private lemma presheaf_map_map (M : X.Modules) {U V W : X.Opensᵒᵖ} (α : U ⟶ V) (β : V ⟶ W)
    (x : M.presheaf.obj U) :
    M.presheaf.map β (M.presheaf.map α x) = M.presheaf.map (α ≫ β) x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

/-- Restricting along a morphism of opens and back is the identity. -/
@[reassoc]
private lemma presheaf_map_comp_eq_id (M : X.Modules) {U V : X.Opensᵒᵖ} (α : U ⟶ V)
    (β : V ⟶ U) : M.presheaf.map α ≫ M.presheaf.map β = 𝟙 _ := by
  rw [presheaf_map_comp_eq M α β (𝟙 _), CategoryTheory.Functor.map_id]

/-- Restriction along a morphism between equal opens is injective. -/
private lemma presheaf_map_injective_of_eq (M : X.Modules) {U V : X.Opens} (α : op U ⟶ op V)
    (h : U = V) : Function.Injective (M.presheaf.map α) := by
  subst h
  rw [Subsingleton.elim α (𝟙 _), CategoryTheory.Functor.map_id]
  exact fun _ _ h ↦ h

/-- Restrictions along parallel morphisms of opens agree. -/
private lemma presheaf_map_congr (M : X.Modules) {U V : X.Opensᵒᵖ} (α β : U ⟶ V) :
    M.presheaf.map α = M.presheaf.map β :=
  congrArg _ (Subsingleton.elim _ _)

/-- A morphism between restrictions along an open immersion commutes with restriction maps of the
ambient module sheaves. -/
private lemma Hom.app_restrict_naturality {Z : Scheme.{u}} (g : Z ⟶ X) [IsOpenImmersion g]
    {A B : X.Modules} (ψ : A.restrict g ⟶ B.restrict g) {U V : Z.Opens}
    (ρ : op (g ''ᵁ U) ⟶ op (g ''ᵁ V)) :
    A.presheaf.map ρ ≫ ψ.app V = ψ.app U ≫ B.presheaf.map ρ :=
  ψ.mapPresheaf.naturality (homOfLE ((g.image_le_image_iff V U).mp (leOfHom ρ.unop))).op

/-- A morphism between restrictions along an open immersion is linear over the sections of the
ambient scheme. -/
private lemma Hom.app_smul_restrict {Z : Scheme.{u}} (g : Z ⟶ X) [IsOpenImmersion g]
    {A B : X.Modules} (ψ : A.restrict g ⟶ B.restrict g) (U : Z.Opens) (r : Γ(X, g ''ᵁ U))
    (x : Γ(A, g ''ᵁ U)) :
    ψ.app U (r • x) = r • (show Γ(B, g ''ᵁ U) from ψ.app U x) := by
  have h₁ := smul_restrictAppIso_inv_apply g A U r x
  have h₂ := smul_restrictAppIso_inv_apply g B U r (ψ.app U x)
  simp only [restrictAppIso, Iso.refl_inv] at h₁ h₂
  exact (congrArg (ψ.app U) h₁).trans ((Hom.app_smul ψ _ _).trans h₂.symm)

/-- Two sections of a module sheaf agreeing on a covering sieve are equal. -/
private lemma section_eq_of_mem_grothendieckTopology (M : X.Modules) {W : X.Opens}
    (R : Sieve W) (hR : R ∈ Opens.grothendieckTopology X W) {s t : Γ(M, W)}
    (h : ∀ ⦃V : X.Opens⦄ (g : V ⟶ W), R g → M.presheaf.map g.op s = M.presheaf.map g.op t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun p : Σ V : X.Opens, {g : V ⟶ W // R g} ↦ p.1) W (fun p ↦ p.2.1) ?_ s t
    fun p ↦ h _ p.2.2
  intro x hx
  obtain ⟨V, g, hg, hxV⟩ := hR x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, g, hg⟩, hxV⟩

section Product

open Limits

variable {ι : Type u} (P : ι → X.Modules) (W : X.Opens)

/-- Taking sections over an open, as a functor to types. -/
private noncomputable abbrev sectionsFunctor : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op W) ⋙ CategoryTheory.forget AddCommGrpCat

private instance : PreservesLimits (sectionsFunctor W) :=
  have : PreservesLimits ((CategoryTheory.evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W) ⋙
      CategoryTheory.forget AddCommGrpCat) := comp_preservesLimits _ _
  comp_preservesLimits _ _

/-- The sections of a product over an open are the families of sections. -/
private noncomputable def piSectionsEquiv : Γ(∏ᶜ P, W) ≃ ∀ i, Γ(P i, W) :=
  (Types.isLimitEquivSections (isLimitOfPreserves (sectionsFunctor W)
    (limit.isLimit (Discrete.functor P)))).trans
    { toFun s i := s.1 ⟨i⟩
      invFun s := ⟨fun i ↦ s i.as, by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; rfl⟩
      left_inv s := rfl
      right_inv s := rfl }

@[simp]
private lemma piSectionsEquiv_apply (x : Γ(∏ᶜ P, W)) (i : ι) :
    piSectionsEquiv P W x i = (Pi.π P i).app W x := rfl

@[simp]
private lemma pi_π_app_piSectionsEquiv_symm (s : ∀ i, Γ(P i, W)) (i : ι) :
    (Pi.π P i).app W ((piSectionsEquiv P W).symm s) = s i := by
  rw [← piSectionsEquiv_apply, Equiv.apply_symm_apply]

private lemma pi_sections_ext {x y : Γ(∏ᶜ P, W)}
    (h : ∀ i, (Pi.π P i).app W x = (Pi.π P i).app W y) : x = y :=
  (piSectionsEquiv P W).injective (funext h)

end Product

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- `X ↦ X.Modules` with pullback, as a `Cat`-valued pseudofunctor. -/
noncomputable abbrev modulesPseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat :=
  Modules.pseudofunctor.comp Adj.forget₁

open Modules

namespace ZariskiDescent

/-- The compositor of `modulesPseudofunctor`, at a module sheaf, as `pullbackComp'`. -/
lemma mapComp'_hom_app {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hgf : g ≫ f = h) (p : f.op.toLoc ≫ g.op.toLoc = h.op.toLoc) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc h.op.toLoc p).hom.toNatTrans.app M =
      (pullbackComp' g f h hgf).hom.app M := by
  subst hgf
  simp [Pseudofunctor.mapComp', pullbackComp', pullbackCongr]
  rfl

/-- The inverse compositor of `modulesPseudofunctor`, at a module sheaf, as `pullbackComp'`. -/
lemma mapComp'_inv_app {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hgf : g ≫ f = h) (p : f.op.toLoc ≫ g.op.toLoc = h.op.toLoc) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc h.op.toLoc p).inv.toNatTrans.app M =
      (pullbackComp' g f h hgf).inv.app M := by
  subst hgf
  simp [Pseudofunctor.mapComp', pullbackComp', pullbackCongr]
  rfl

/-- `pullHom` for `modulesPseudofunctor`, in terms of `pullbackComp'`. -/
lemma pullHom_eq {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂} (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor) (M₁ := M₁)
      (M₂ := M₂) φ g gf₁ gf₂ h₁ h₂ =
      (pullbackComp' g f₁ gf₁ h₁).hom.app M₁ ≫ (pullback g).map φ ≫
        (pullbackComp' g f₂ gf₂ h₂).inv.app M₂ := by
  subst h₁ h₂
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  exact congrArg₂ (· ≫ ·) (mapComp'_hom_app _ _ _ rfl _ M₁)
    (congrArg₂ (· ≫ ·) rfl (mapComp'_inv_app _ _ _ rfl _ M₂))

/-- The gluing morphisms of the descent datum of a module sheaf, in terms of `pullbackComp'`. -/
lemma toDescentData_obj_hom {ι : Type*} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((modulesPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ =
      (pullbackCompApp f₁ (f i₁) q hf₁ M).inv ≫ (pullbackCompApp f₂ (f i₂) q hf₂ M).hom :=
  congrArg₂ (· ≫ ·) (mapComp'_inv_app f₁ (f i₁) q hf₁ _ M) (mapComp'_hom_app f₂ (f i₂) q hf₂ _ M)

variable {S : Scheme.{u}}

/-- A family of open immersions that is jointly surjective covers `S` by its ranges. -/
lemma iSup_opensRange_eq_top {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    [∀ i, IsOpenImmersion (f i)] (h : ∀ x : S, ∃ i, x ∈ Set.range (f i)) :
    ⨆ i, (f i).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := h x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, by simpa using hi⟩

/-- The lift of the inclusion of an open contained in the range of an open immersion. -/
noncomputable def liftOpens {X : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] {U : S.Opens}
    (h : U ≤ f.opensRange) : (U : Scheme.{u}) ⟶ X :=
  IsOpenImmersion.lift f U.ι (by rw [Opens.range_ι, ← Hom.coe_opensRange]; exact h)

/-- `liftOpens f h` lifts the inclusion of `U` through `f`. -/
@[reassoc (attr := simp)]
lemma liftOpens_fac {X : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] {U : S.Opens}
    (h : U ≤ f.opensRange) : liftOpens f h ≫ f = U.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance {X : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] {U : S.Opens}
    (h : U ≤ f.opensRange) : IsOpenImmersion (liftOpens f h) := by
  have : IsOpenImmersion (liftOpens f h ≫ f) := by rw [liftOpens_fac]; infer_instance
  exact IsOpenImmersion.of_comp _ f

/-- Lifting a smaller open is restricting the lift of a larger one. -/
lemma homOfLE_liftOpens {X : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] {U U' : S.Opens}
    (h : U' ≤ U) (hU : U ≤ f.opensRange) :
    S.homOfLE h ≫ liftOpens f hU = liftOpens f (h.trans hU) := by
  rw [← cancel_mono f]
  simp

section General

variable {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S} [∀ i, IsOpenImmersion (f i)]
  (D : modulesPseudofunctor.DescentData f)

/-- The objects of a descent datum, as module sheaves. -/
abbrev obj (i : ι) : (X i).Modules := D.obj i

section Trans

variable {Y : Scheme.{u}} (q : Y ⟶ S) {i j k : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
  (f₃ : Y ⟶ X k) [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion f₃]
  (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) (hf₃ : f₃ ≫ f k = q)

/-- The gluing morphism of a descent datum over a test object, as a morphism between
pullbacks of module sheaves. -/
noncomputable abbrev homOver :
    (pullback f₁).obj (obj D i) ⟶ (pullback f₂).obj (obj D j) :=
  D.hom q f₁ f₂ hf₁ hf₂

/-- The gluing morphism of a descent datum over a test object mapping to the `X i` by open
immersions, as a morphism between restrictions. -/
noncomputable def trans : (obj D i).restrict f₁ ⟶ (obj D j).restrict f₂ :=
  (restrictFunctorIsoPullback f₁).hom.app (obj D i) ≫ homOver D q f₁ f₂ hf₁ hf₂ ≫
    (restrictFunctorIsoPullback f₂).inv.app (obj D j)

omit [∀ i, IsOpenImmersion (f i)] in
/-- On the diagonal the gluing morphism on restrictions is the identity, by `D.hom_self`. -/
lemma trans_self : trans D q f₁ f₁ hf₁ hf₁ = 𝟙 _ := by
  have : homOver D q f₁ f₁ hf₁ hf₁ = 𝟙 _ := D.hom_self q f₁ hf₁
  simp [trans, this]

omit [∀ i, IsOpenImmersion (f i)] in
/-- The cocycle condition on restrictions, by `D.hom_comp`. -/
@[reassoc]
lemma trans_comp :
    trans D q f₁ f₂ hf₁ hf₂ ≫ trans D q f₂ f₃ hf₂ hf₃ = trans D q f₁ f₃ hf₁ hf₃ := by
  have : homOver D q f₁ f₂ hf₁ hf₂ ≫ homOver D q f₂ f₃ hf₂ hf₃ = homOver D q f₁ f₃ hf₁ hf₃ :=
    D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃
  simp only [trans, Category.assoc, Iso.inv_hom_id_app_assoc, reassoc_of% this]

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] (q' : Y' ⟶ S) (gf₁ : Y' ⟶ X i)
  (gf₂ : Y' ⟶ X j) [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (hq : g ≫ q = q')
  (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)

omit [∀ i, IsOpenImmersion (f i)] [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g]
  [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] in
/-- Restricting the test object along `g` pulls the gluing morphism back along `g`: this is
`D.pullHom_hom`, with `pullHom` computed by `pullHom_eq`. -/
lemma homOver_restrict :
    homOver D q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) =
      (pullbackCompApp g f₁ gf₁ hgf₁ (obj D i)).hom ≫
      (pullback g).map (homOver D q f₁ f₂ hf₁ hf₂) ≫
      (pullbackCompApp g f₂ gf₂ hgf₂ (obj D j)).inv :=
  (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂).symm.trans
    (pullHom_eq (M₁ := obj D i) (M₂ := obj D j) (homOver D q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂)

omit [∀ i, IsOpenImmersion (f i)] in
/-- The gluing morphisms on restrictions are compatible with restricting the test object along an
open immersion. This is where the coherence of restriction with pullback enters. -/
lemma trans_restrict :
    trans D q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) =
      (restrictFunctorComp' g f₁ gf₁ hgf₁).hom.app _ ≫
      (Modules.restrictFunctor g).map (trans D q f₁ f₂ hf₁ hf₂) ≫
      (restrictFunctorComp' g f₂ gf₂ hgf₂).inv.app _ := by
  rw [trans, homOver_restrict D q f₁ f₂ hf₁ hf₂ g q' gf₁ gf₂ hq hgf₁ hgf₂]
  simp only [Category.assoc, pullbackCompApp, Iso.app_hom, Iso.app_inv]
  rw [restrictFunctorIsoPullback_hom_pullbackComp'_hom_assoc,
    pullbackComp'_inv_restrictFunctorIsoPullback_inv, trans]
  simp only [Category.assoc, Functor.map_comp]
  congr 1
  simp only [← Functor.map_comp_assoc]
  rw [← NatIso.naturality_2 (restrictFunctorIsoPullback g)]
  simp only [Category.assoc]

end Trans

variable {D} in
/-- A morphism of descent data, on the module sheaves. -/
abbrev homM {D' : modulesPseudofunctor.DescentData f} (φ : D ⟶ D') (i : ι) :
    obj D i ⟶ obj D' i :=
  φ.hom i

omit [∀ i, IsOpenImmersion (f i)] in
variable {D} in
/-- A morphism of descent data commutes with the gluing morphisms on restrictions. -/
@[reassoc]
lemma Hom.comm_trans {D' : modulesPseudofunctor.DescentData f} (φ : D ⟶ D') {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    (Modules.restrictFunctor f₁).map (homM φ i) ≫ trans D' q f₁ f₂ hf₁ hf₂ =
      trans D q f₁ f₂ hf₁ hf₂ ≫ (Modules.restrictFunctor f₂).map (homM φ j) := by
  have : (pullback f₁).map (homM φ i) ≫ homOver D' q f₁ f₂ hf₁ hf₂ =
      homOver D q f₁ f₂ hf₁ hf₂ ≫ (pullback f₂).map (homM φ j) :=
    φ.comm q f₁ f₂ hf₁ hf₂
  simp only [trans, Category.assoc]
  rw [NatTrans.naturality_assoc, reassoc_of% this]
  simp

variable (f) in
/-- The gluing morphism of the descent datum of a module sheaf `M` on `S` identifies the two
restrictions of `M` to the test object. -/
lemma trans_toDescentData (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion q]
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    trans ((modulesPseudofunctor.toDescentData f).obj M) q f₁ f₂ hf₁ hf₂ =
      (Modules.restrictFunctor f₁).map ((restrictFunctorIsoPullback (f i)).inv.app M) ≫
        (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
        (Modules.restrictFunctor f₂).map ((restrictFunctorIsoPullback (f j)).hom.app M) := by
  have h₁ := pullbackComp'_inv_restrictFunctorIsoPullback_inv f₁ (f i) q hf₁ M
  have h₂ := restrictFunctorIsoPullback_hom_pullbackComp'_hom f₂ (f j) q hf₂ M
  have e : (restrictFunctorIsoPullback f₁).hom.app _ ≫
      (((modulesPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ :
        (pullback f₁).obj ((pullback (f i)).obj M) ⟶ (pullback f₂).obj ((pullback (f j)).obj M)) ≫
      (restrictFunctorIsoPullback f₂).inv.app _ =
    (restrictFunctorIsoPullback f₁).hom.app _ ≫
      ((pullbackCompApp f₁ (f i) q hf₁ M).inv ≫ (pullbackCompApp f₂ (f j) q hf₂ M).hom) ≫
      (restrictFunctorIsoPullback f₂).inv.app _ := by
    rw [toDescentData_obj_hom]
    rfl
  refine e.trans ?_
  simp only [pullbackCompApp, Iso.app_hom, Iso.app_inv]
  rw [show (pullbackComp' f₁ (f i) q hf₁).inv.app M ≫ (pullbackComp' f₂ (f j) q hf₂).hom.app M =
      ((pullbackComp' f₁ (f i) q hf₁).inv.app M ≫ (restrictFunctorIsoPullback q).inv.app M) ≫
      ((restrictFunctorIsoPullback q).hom.app M ≫ (pullbackComp' f₂ (f j) q hf₂).hom.app M) by
      simp, h₁, h₂]
  simp only [Category.assoc]
  rw [← NatIso.naturality_2 (restrictFunctorIsoPullback f₁)
      ((restrictFunctorIsoPullback (f i)).inv.app M),
    ← NatIso.naturality_2 (restrictFunctorIsoPullback f₂)
      ((restrictFunctorIsoPullback (f j)).hom.app M)]
  simp only [Category.assoc]
  rfl

omit [∀ i, IsOpenImmersion (f i)] in
/-- The gluing morphism between pullbacks, recovered from the one between restrictions. -/
lemma homOver_eq_trans {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    homOver D q f₁ f₂ hf₁ hf₂ = (restrictFunctorIsoPullback f₁).inv.app _ ≫
      trans D q f₁ f₂ hf₁ hf₂ ≫ (restrictFunctorIsoPullback f₂).hom.app _ := by
  simp [trans]

variable (f) in
/-- The gluing morphism of the descent datum of a module sheaf, between iterated pullbacks. -/
noncomputable abbrev toDescentDataHom (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    (pullback f₁).obj ((pullback (f i)).obj M) ⟶ (pullback f₂).obj ((pullback (f j)).obj M) :=
  ((modulesPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂

variable (f) in
/-- The gluing morphism of the descent datum of a module sheaf `M` on `S`, through the
identifications of pullbacks with restrictions: it identifies the two restrictions of `M`. -/
lemma toDescentDataHom_eq (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) [IsOpenImmersion q]
    {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    toDescentDataHom f M q f₁ f₂ hf₁ hf₂ =
      (pullback f₁).map ((restrictFunctorIsoPullback (f i)).inv.app M) ≫
        (restrictFunctorIsoPullback f₁).inv.app (M.restrict (f i)) ≫
        (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
        (restrictFunctorIsoPullback f₂).hom.app (M.restrict (f j)) ≫
        (pullback f₂).map ((restrictFunctorIsoPullback (f j)).hom.app M) := by
  refine (toDescentData_obj_hom f M q f₁ f₂ hf₁ hf₂).trans ?_
  simp only [pullbackCompApp, Iso.app_inv, Iso.app_hom]
  rw [show (pullbackComp' f₁ (f i) q hf₁).inv.app M ≫ (pullbackComp' f₂ (f j) q hf₂).hom.app M =
      ((pullbackComp' f₁ (f i) q hf₁).inv.app M ≫ (restrictFunctorIsoPullback q).inv.app M) ≫
      ((restrictFunctorIsoPullback q).hom.app M ≫ (pullbackComp' f₂ (f j) q hf₂).hom.app M) by
      simp, pullbackComp'_inv_restrictFunctorIsoPullback_inv,
    restrictFunctorIsoPullback_hom_pullbackComp'_hom]
  simp only [Category.assoc]
  rfl

variable {D} in
/-- A family of morphisms from the restrictions of a module sheaf to the objects of a descent
datum is compatible with the gluing morphisms over a test object as soon as it is so on
restrictions. -/
lemma descentComm_of_restrict {M : S.Modules} (ε : ∀ i, M.restrict (f i) ⟶ obj D i)
    {Y : Scheme.{u}} (q : Y ⟶ S) [IsOpenImmersion q] {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q)
    (h : (Modules.restrictFunctor f₁).map (ε i) ≫ trans D q f₁ f₂ hf₁ hf₂ =
      (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
        (Modules.restrictFunctor f₂).map (ε j)) :
    (pullback f₁).map ((restrictFunctorIsoPullback (f i)).inv.app M ≫ ε i) ≫
        homOver D q f₁ f₂ hf₁ hf₂ =
      toDescentDataHom f M q f₁ f₂ hf₁ hf₂ ≫
        (pullback f₂).map ((restrictFunctorIsoPullback (f j)).inv.app M ≫ ε j) := by
  rw [homOver_eq_trans, toDescentDataHom_eq, Functor.map_comp_assoc,
    (restrictFunctorIsoPullback f₁).inv.naturality_assoc, reassoc_of% h]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← (restrictFunctorIsoPullback f₂).hom.naturality]

variable {D} in
/-- `descentComm_of_restrict`, for morphisms `e i` equal to the transported `ε i`: the form
required by `Pseudofunctor.DescentData.isoMk`. -/
lemma descentComm_of_restrict_of_eq {M : S.Modules} (ε : ∀ i, M.restrict (f i) ⟶ obj D i)
    (e : ∀ i, ((modulesPseudofunctor.toDescentData f).obj M).obj i ⟶ D.obj i)
    (he : ∀ i, e i = (restrictFunctorIsoPullback (f i)).inv.app M ≫ ε i)
    {Y : Scheme.{u}} (q : Y ⟶ S) [IsOpenImmersion q] {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q)
    (h : (Modules.restrictFunctor f₁).map (ε i) ≫ trans D q f₁ f₂ hf₁ hf₂ =
      (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
        (Modules.restrictFunctor f₂).map (ε j)) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i) ≫ D.hom q f₁ f₂ hf₁ hf₂ =
      ((modulesPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂ ≫
        (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e j) := by
  rw [he, he]
  exact descentComm_of_restrict ε q f₁ f₂ hf₁ hf₂ h

section Sections

variable {Y : Scheme.{u}} (q : Y ⟶ S) {i j k : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) (f₃ : Y ⟶ X k)
  [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion f₃]
  (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) (hf₃ : f₃ ≫ f k = q)

/-- The gluing morphism of a descent datum on sections over an open of the test object. -/
noncomputable def transApp (U : Y.Opens) : Γ(obj D i, f₁ ''ᵁ U) ⟶ Γ(obj D j, f₂ ''ᵁ U) :=
  (trans D q f₁ f₂ hf₁ hf₂).app U

omit [∀ i, IsOpenImmersion (f i)] in
/-- The gluing morphism on sections commutes with restriction of sections. -/
@[reassoc]
lemma transApp_naturality {U V : Y.Opens} (ρ₁ : op (f₁ ''ᵁ U) ⟶ op (f₁ ''ᵁ V))
    (ρ₂ : op (f₂ ''ᵁ U) ⟶ op (f₂ ''ᵁ V)) :
    (obj D i).presheaf.map ρ₁ ≫ transApp D q f₁ f₂ hf₁ hf₂ V =
      transApp D q f₁ f₂ hf₁ hf₂ U ≫ (obj D j).presheaf.map ρ₂ :=
  (trans D q f₁ f₂ hf₁ hf₂).mapPresheaf.naturality
    (homOfLE ((f₁.image_le_image_iff V U).mp (leOfHom ρ₁.unop))).op

omit [∀ i, IsOpenImmersion (f i)] in
/-- The cocycle condition on sections. -/
@[reassoc]
lemma transApp_comp (U : Y.Opens) :
    transApp D q f₁ f₂ hf₁ hf₂ U ≫ transApp D q f₂ f₃ hf₂ hf₃ U =
      transApp D q f₁ f₃ hf₁ hf₃ U := by
  have := congrArg (fun ψ ↦ Modules.Hom.app ψ U) (trans_comp D q f₁ f₂ f₃ hf₁ hf₂ hf₃)
  simp only [Modules.Hom.comp_app] at this
  exact this

omit [∀ i, IsOpenImmersion (f i)] in
/-- On the diagonal the gluing morphism on sections is the identity. -/
lemma transApp_self (U : Y.Opens) : transApp D q f₁ f₁ hf₁ hf₁ U = 𝟙 _ := by
  have := congrArg (fun ψ ↦ Modules.Hom.app ψ U) (trans_self D q f₁ hf₁)
  simp only [Modules.Hom.id_app] at this
  exact this

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] (q' : Y' ⟶ S) (gf₁ : Y' ⟶ X i)
  (gf₂ : Y' ⟶ X j) [IsOpenImmersion gf₁] [IsOpenImmersion gf₂] (hq : g ≫ q = q')
  (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)

omit [∀ i, IsOpenImmersion (f i)] in
/-- The gluing morphism on sections for a smaller test object `Y'`, through the gluing morphism
for `Y` over the image of the open. -/
lemma transApp_restrict (U : Y'.Opens) (ρ₁ : op (gf₁ ''ᵁ U) ⟶ op (f₁ ''ᵁ g ''ᵁ U))
    (ρ₂ : op (f₂ ''ᵁ g ''ᵁ U) ⟶ op (gf₂ ''ᵁ U)) :
    transApp D q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) U =
      (obj D i).presheaf.map ρ₁ ≫ transApp D q f₁ f₂ hf₁ hf₂ (g ''ᵁ U) ≫
        (obj D j).presheaf.map ρ₂ := by
  have := congrArg (fun ψ ↦ Modules.Hom.app ψ U)
    (trans_restrict D q f₁ f₂ hf₁ hf₂ g q' gf₁ gf₂ hq hgf₁ hgf₂)
  simp only [Modules.Hom.comp_app, restrictFunctor_map_app, restrictFunctorComp'_hom_app_app,
    restrictFunctorComp'_inv_app_app] at this
  refine this.trans ?_
  erw [presheaf_map_congr _ ρ₁, presheaf_map_congr _ ρ₂]
  rfl

omit [∀ i, IsOpenImmersion (f i)] in
/-- `transApp_restrict`, solved for the gluing morphism over the image of an open of `Y'`. -/
lemma transApp_image (U : Y'.Opens) (ρ₁ : op (f₁ ''ᵁ g ''ᵁ U) ⟶ op (gf₁ ''ᵁ U))
    (ρ₂ : op (gf₂ ''ᵁ U) ⟶ op (f₂ ''ᵁ g ''ᵁ U)) :
    transApp D q f₁ f₂ hf₁ hf₂ (g ''ᵁ U) = (obj D i).presheaf.map ρ₁ ≫
      transApp D q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) U ≫ (obj D j).presheaf.map ρ₂ := by
  have e₁ : gf₁ ''ᵁ U = f₁ ''ᵁ g ''ᵁ U := by subst hgf₁; simp
  have e₂ : gf₂ ''ᵁ U = f₂ ''ᵁ g ''ᵁ U := by subst hgf₂; simp
  rw [transApp_restrict D q f₁ f₂ hf₁ hf₂ g q' gf₁ gf₂ hq hgf₁ hgf₂ U (eqToHom (congrArg op e₁))
    (eqToHom (congrArg op e₂.symm))]
  simp only [Category.assoc]
  rw [presheaf_map_comp_eq_id_assoc, presheaf_map_comp_eq_id, Category.comp_id]

end Sections

section Prestack

variable (hf : ⨆ i, (f i).opensRange = ⊤)
include hf

/-- Every open of `S` is covered by its intersections with the ranges of the `f i`. -/
lemma le_iSup_image_preimage (W : S.Opens) : W ≤ ⨆ i, f i ''ᵁ f i ⁻¹ᵁ W := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hf.symm ▸ trivial : x ∈ ⨆ i, (f i).opensRange)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, by
    rw [Hom.image_preimage_eq_opensRange_inf]
    exact ⟨hi, hx⟩⟩

/-- Sections of a module sheaf on `S` are determined by their restrictions to the cover. -/
lemma section_ext (N : S.Modules) {W : S.Opens} {s t : Γ(N, W)}
    (h : ∀ i, N.presheaf.map (homOfLE ((f i).image_preimage_le W)).op s =
      N.presheaf.map (homOfLE ((f i).image_preimage_le W)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i ↦ f i ''ᵁ f i ⁻¹ᵁ W) W
    (fun i ↦ homOfLE ((f i).image_preimage_le W)) (le_iSup_image_preimage hf W) s t h

/-- Morphisms of module sheaves on `S` that agree after restriction to every member of the cover
are equal, since sections are determined locally. -/
lemma hom_ext_of_restrict {M N : S.Modules} {ψ₁ ψ₂ : M ⟶ N}
    (h : ∀ i, (Modules.restrictFunctor (f i)).map ψ₁ = (Modules.restrictFunctor (f i)).map ψ₂) :
    ψ₁ = ψ₂ := by
  refine Modules.hom_ext _ _ fun W ↦ ?_
  ext x
  refine section_ext hf N fun i ↦ ?_
  have := congrArg (fun φ ↦ φ.app (f i ⁻¹ᵁ W)) (h i)
  simp only [restrictFunctor_map_app] at this
  rw [homApp_res, homApp_res, this]

/-- The faithful half of the prestack property for a cover by open immersions. -/
lemma faithful_toDescentData : (modulesPseudofunctor.toDescentData f).Faithful where
  map_injective {M N} ψ₁ ψ₂ h := hom_ext_of_restrict hf fun i ↦ by
    have : (pullback (f i)).map ψ₁ = (pullback (f i)).map ψ₂ := congrArg (fun φ ↦ φ.hom i) h
    rw [← NatIso.naturality_2 (restrictFunctorIsoPullback (f i)) ψ₁,
      ← NatIso.naturality_2 (restrictFunctorIsoPullback (f i)) ψ₂, this]

variable {M N : S.Modules}
  (φ : (modulesPseudofunctor.toDescentData f).obj M ⟶
    (modulesPseudofunctor.toDescentData f).obj N)

omit hf in
variable (f) in
/-- The components of a morphism of descent data of module sheaves, between pullbacks. -/
abbrev homP (i : ι) : (pullback (f i)).obj M ⟶ (pullback (f i)).obj N := φ.hom i

omit hf in
variable (f) in
/-- The components of a morphism of descent data of module sheaves, as morphisms between
restrictions. -/
noncomputable def homRestrict (i : ι) : M.restrict (f i) ⟶ N.restrict (f i) :=
  (restrictFunctorIsoPullback (f i)).hom.app M ≫ homP f φ i ≫
    (restrictFunctorIsoPullback (f i)).inv.app N

omit hf in
/-- The components of a morphism of descent data commute with the restriction compositors over a
test object mapping to `X i` and `X j` by open immersions. -/
lemma homRestrict_comm {Y : Scheme.{u}} (q : Y ⟶ S) [IsOpenImmersion q] {i j : ι}
    (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    (hf₁ : f₁ ≫ f i = q) (hf₂ : f₂ ≫ f j = q) :
    (Modules.restrictFunctor f₁).map (homRestrict f φ i) ≫
        (restrictFunctorComp' f₁ (f i) q hf₁).inv.app N ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app N =
      (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
        (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
        (Modules.restrictFunctor f₂).map (homRestrict f φ j) := by
  have h : (Modules.restrictFunctor f₁).map (homP f φ i) ≫
      (Modules.restrictFunctor f₁).map ((restrictFunctorIsoPullback (f i)).inv.app N) ≫
        (restrictFunctorComp' f₁ (f i) q hf₁).inv.app N ≫
          (restrictFunctorComp' f₂ (f j) q hf₂).hom.app N ≫
            (Modules.restrictFunctor f₂).map ((restrictFunctorIsoPullback (f j)).hom.app N) =
      ((Modules.restrictFunctor f₁).map ((restrictFunctorIsoPullback (f i)).inv.app M) ≫
        (restrictFunctorComp' f₁ (f i) q hf₁).inv.app M ≫
          (restrictFunctorComp' f₂ (f j) q hf₂).hom.app M ≫
            (Modules.restrictFunctor f₂).map ((restrictFunctorIsoPullback (f j)).hom.app M)) ≫
      (Modules.restrictFunctor f₂).map (homP f φ j) := by
    have h := Hom.comm_trans φ q f₁ f₂ hf₁ hf₂
    rw [trans_toDescentData, trans_toDescentData] at h
    exact h
  have h' := ((Modules.restrictFunctor f₁).map
    ((restrictFunctorIsoPullback (f i)).hom.app M) ≫= h =≫ (Modules.restrictFunctor f₂).map
      ((restrictFunctorIsoPullback (f j)).inv.app N))
  have e₁ : (Modules.restrictFunctor f₂).map ((restrictFunctorIsoPullback (f j)).hom.app N) ≫
      (Modules.restrictFunctor f₂).map ((restrictFunctorIsoPullback (f j)).inv.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have e₂ : (Modules.restrictFunctor f₁).map ((restrictFunctorIsoPullback (f i)).hom.app M) ≫
      (Modules.restrictFunctor f₁).map ((restrictFunctorIsoPullback (f i)).inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  refine (Eq.trans ?_ h').trans ?_
  · simp only [homRestrict, Functor.map_comp, Category.assoc, e₁]
    erw [Category.comp_id]
  · simp only [homRestrict, Functor.map_comp, Category.assoc, reassoc_of% e₂]

omit hf in
/-- Over an open `W` of `S` inside the ranges of `f i` and `f j`, the components of a morphism of
descent data agree on sections. -/
lemma homRestrict_app_lift {i j : ι} (W : S.Opens) (hi : W ≤ (f i).opensRange)
    (hj : W ≤ (f j).opensRange) (T₀ : W.toScheme.Opens)
    (n : op (f i ''ᵁ liftOpens (f i) hi ''ᵁ T₀) ⟶ op (f j ''ᵁ liftOpens (f j) hj ''ᵁ T₀)) :
    (homRestrict f φ i).app (liftOpens (f i) hi ''ᵁ T₀) ≫ N.presheaf.map n =
      M.presheaf.map n ≫ (homRestrict f φ j).app (liftOpens (f j) hj ''ᵁ T₀) := by
  have E := congrArg (fun ψ ↦ Modules.Hom.app ψ T₀) (homRestrict_comm φ W.ι
    (liftOpens (f i) hi) (liftOpens (f j) hj) (liftOpens_fac _ _) (liftOpens_fac _ _))
  simp only [Modules.Hom.comp_app, restrictFunctor_map_app, restrictFunctorComp'_hom_app_app,
    restrictFunctorComp'_inv_app_app] at E
  erw [presheaf_map_comp_eq N _ _ n, presheaf_map_comp_eq_assoc M _ _ n] at E
  exact E

omit hf in
variable (f) in
/-- The components of a morphism of descent data of module sheaves, on sections over the image
of an open. -/
noncomputable def homSec (i : ι) (T : (X i).Opens) : Γ(M, f i ''ᵁ T) ⟶ Γ(N, f i ''ᵁ T) :=
  (homRestrict f φ i).app T

omit hf in
/-- The components commute with restriction of sections inside one member of the cover. -/
@[reassoc]
lemma homSec_naturality {i : ι} {U V : (X i).Opens} (ρ : op (f i ''ᵁ U) ⟶ op (f i ''ᵁ V)) :
    M.presheaf.map ρ ≫ homSec f φ i V = homSec f φ i U ≫ N.presheaf.map ρ :=
  Hom.app_restrict_naturality (f i) (homRestrict f φ i) ρ

omit hf in
/-- Components over two members of the cover agree on an open contained in both ranges. -/
@[reassoc]
lemma homSec_lift {i j : ι} (W : S.Opens) (hi : W ≤ (f i).opensRange)
    (hj : W ≤ (f j).opensRange) (T₀ : W.toScheme.Opens)
    (n : op (f i ''ᵁ liftOpens (f i) hi ''ᵁ T₀) ⟶ op (f j ''ᵁ liftOpens (f j) hj ''ᵁ T₀)) :
    homSec f φ i (liftOpens (f i) hi ''ᵁ T₀) ≫ N.presheaf.map n =
      M.presheaf.map n ≫ homSec f φ j (liftOpens (f j) hj ''ᵁ T₀) :=
  homRestrict_app_lift φ W hi hj T₀ n

omit hf in
/-- Components over two members of the cover agree along any inclusion of images of opens: the
naturality on the basis of images of opens that lets them glue. -/
lemma homSec_compat {i i' : ι} (T : (X i).Opens) (T' : (X i').Opens)
    (γ : op (f i ''ᵁ T) ⟶ op (f i' ''ᵁ T')) :
    M.presheaf.map γ ≫ homSec f φ i' T' = homSec f φ i T ≫ N.presheaf.map γ := by
  have hW : f i' ''ᵁ T' ≤ f i ''ᵁ T := leOfHom γ.unop
  have hi : f i' ''ᵁ T' ≤ (f i).opensRange := hW.trans ((f i).image_le_opensRange T)
  have hi' : f i' ''ᵁ T' ≤ (f i').opensRange := (f i').image_le_opensRange T'
  have e₁ : f i ''ᵁ liftOpens (f i) hi ''ᵁ ⊤ ≤ f i ''ᵁ T := by
    simp only [← Hom.comp_image, liftOpens_fac, Opens.ι_image_top]; exact hW
  have e₂ : f i' ''ᵁ liftOpens (f i') hi' ''ᵁ ⊤ ≤ f i ''ᵁ liftOpens (f i) hi ''ᵁ ⊤ := by
    simp only [← Hom.comp_image, liftOpens_fac, Opens.ι_image_top]; rfl
  have e₃ : f i' ''ᵁ liftOpens (f i') hi' ''ᵁ ⊤ ≤ f i' ''ᵁ T' := by
    simp only [← Hom.comp_image, liftOpens_fac, Opens.ι_image_top]; rfl
  have e₄ : f i' ''ᵁ T' ≤ f i' ''ᵁ liftOpens (f i') hi' ''ᵁ ⊤ := by
    simp only [← Hom.comp_image, liftOpens_fac, Opens.ι_image_top]; rfl
  rw [presheaf_map_congr N γ ((homOfLE e₁).op ≫ (homOfLE e₂).op ≫ (homOfLE e₄).op),
    Functor.map_comp, Functor.map_comp, ← homSec_naturality_assoc,
    homSec_lift_assoc φ (f i' ''ᵁ T') hi hi' ⊤ (homOfLE e₂).op, ← homSec_naturality]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2

/-- The images of opens of the `X i` form a basis of `S`. -/
lemma isBasis_range_image :
    TopologicalSpace.Opens.IsBasis (Set.range fun p : Σ i, (X i).Opens ↦ f p.1 ''ᵁ p.2) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hf.symm ▸ trivial : x ∈ ⨆ i, (f i).opensRange)
  refine ⟨f i ''ᵁ f i ⁻¹ᵁ U, ⟨⟨i, f i ⁻¹ᵁ U⟩, rfl⟩, ?_, (f i).image_preimage_le U⟩
  rw [Hom.image_preimage_eq_opensRange_inf]
  exact ⟨hi, hx⟩

omit hf in
variable (f) in
/-- The components of a morphism of descent data, on the basis of images of opens. -/
@[simps]
noncomputable def homBasis :
    (inducedFunctor fun p : Σ i, (X i).Opens ↦ f p.1 ''ᵁ p.2).op ⋙ M.presheaf ⟶
      (inducedFunctor fun p : Σ i, (X i).Opens ↦ f p.1 ''ᵁ p.2).op ⋙ N.presheaf where
  app p := homSec f φ p.unop.1 p.unop.2
  naturality _ _ _ := homSec_compat φ _ _ _

variable (f) in
/-- The morphism of underlying presheaves glued from a morphism of descent data. -/
noncomputable def homPresheaf : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ (isBasis_range_image hf)
    (homBasis f φ)

/-- On an image of an open of `X i`, the glued morphism of presheaves is the `i`-th component. -/
lemma homPresheaf_app_image (i : ι) (T : (X i).Opens) :
    (homPresheaf f hf φ).app (op (f i ''ᵁ T)) = homSec f φ i T :=
  TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ (isBasis_range_image hf)
    (homBasis f φ) ⟨i, T⟩

omit hf in
/-- The components are linear over the sections of the structure sheaf of `S`. -/
lemma homSec_smul {i : ι} (T : (X i).Opens) (r : Γ(S, f i ''ᵁ T)) (x : Γ(M, f i ''ᵁ T)) :
    homSec f φ i T (r • x) = r • homSec f φ i T x :=
  Hom.app_smul_restrict (f i) (homRestrict f φ i) T r x

/-- The glued morphism of presheaves is linear; linearity is checked on the cover. -/
lemma homPresheaf_smul (W : S.Opens) (r : Γ(S, W)) (x : Γ(M, W)) :
    (homPresheaf f hf φ).app (op W) (r • x) =
      r • (show Γ(N, W) from (homPresheaf f hf φ).app (op W) x) := by
  refine section_ext hf N fun i ↦ ?_
  have h₁ := NatTrans.naturality_apply (homPresheaf f hf φ)
    (homOfLE ((f i).image_preimage_le W)).op (r • x)
  have h₂ := NatTrans.naturality_apply (homPresheaf f hf φ)
    (homOfLE ((f i).image_preimage_le W)).op x
  rw [homPresheaf_app_image] at h₁ h₂
  rw [Scheme.Modules.map_smul, ← h₁, Scheme.Modules.map_smul, ← h₂, homSec_smul]

variable (f) in
/-- The morphism of module sheaves glued from a morphism of descent data. -/
noncomputable def homOfDescentData : M ⟶ N :=
  ⟨PresheafOfModules.homMk (homPresheaf f hf φ) fun W r x ↦ homPresheaf_smul hf φ W.unop r x⟩

/-- The glued morphism restricts to the components of the morphism of descent data. -/
lemma restrictFunctor_map_homOfDescentData (i : ι) :
    (Modules.restrictFunctor (f i)).map (homOfDescentData f hf φ) = homRestrict f φ i :=
  Modules.hom_ext _ _ fun T ↦ homPresheaf_app_image hf φ i T

/-- The glued morphism induces the given morphism of descent data. -/
lemma toDescentData_map_homOfDescentData :
    (modulesPseudofunctor.toDescentData f).map (homOfDescentData f hf φ) = φ := by
  ext i
  change (pullback (f i)).map (homOfDescentData f hf φ) = homP f φ i
  rw [← NatIso.naturality_1 (restrictFunctorIsoPullback (f i)),
    restrictFunctor_map_homOfDescentData hf φ i, homRestrict]
  simp

/-- The full half of the prestack property for a cover by open immersions: morphisms of descent
data glue to morphisms of module sheaves. -/
lemma full_toDescentData : (modulesPseudofunctor.toDescentData f).Full where
  map_surjective φ := ⟨homOfDescentData f hf φ, toDescentData_map_homOfDescentData hf φ⟩

end Prestack

end General

section Glue

variable {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S} [∀ i, IsOpenImmersion (f i)]
  (D : modulesPseudofunctor.DescentData f)

/-- The overlap of the ranges of `f i` and `f j`. -/
abbrev inter (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)] (i j : ι) : S.Opens :=
  (f i).opensRange ⊓ (f j).opensRange

variable (f) in
/-- The open immersion of the overlap into `X i`. -/
noncomputable abbrev interFst (i j : ι) : (inter f i j : Scheme.{u}) ⟶ X i :=
  liftOpens (f i) inf_le_left

variable (f) in
/-- The open immersion of the overlap into `X j`. -/
noncomputable abbrev interSnd (i j : ι) : (inter f i j : Scheme.{u}) ⟶ X j :=
  liftOpens (f j) inf_le_right

/-- The gluing morphism of a descent datum over the overlap of `f i` and `f j`. -/
noncomputable abbrev transInter (i j : ι) :
    (obj D i).restrict (interFst f i j) ⟶ (obj D j).restrict (interSnd f i j) :=
  trans D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _) (liftOpens_fac _ _)

/-- The product of the pushforwards of the objects of a descent datum. -/
noncomputable abbrev prod : S.Modules :=
  ∏ᶜ fun i ↦ (pushforward (f i)).obj (obj D i)

/-- The pushforward from the overlap of `f i` and `f j` of the restriction of the `j`-th object. -/
noncomputable abbrev target (i j : ι) : S.Modules :=
  (pushforward (inter f i j).ι).obj ((obj D j).restrict (interSnd f i j))

/-- The `i`-th component, transported to the overlap by the gluing morphism. -/
noncomputable def left (i j : ι) : prod D ⟶ target D i j :=
  Limits.Pi.π _ i ≫ (pushforward (f i)).map ((restrictAdjunction (interFst f i j)).unit.app _ ≫
      (pushforward (interFst f i j)).map (transInter D i j)) ≫
    (pushforwardComp (interFst f i j) (f i)).hom.app _ ≫
    (pushforwardCongr (liftOpens_fac _ _)).hom.app _

/-- The `j`-th component, restricted to the overlap. -/
noncomputable def right (i j : ι) : prod D ⟶ target D i j :=
  Limits.Pi.π _ j ≫ (pushforward (f j)).map ((restrictAdjunction (interSnd f i j)).unit.app _) ≫
    (pushforwardComp (interSnd f i j) (f j)).hom.app _ ≫
    (pushforwardCongr (liftOpens_fac _ _)).hom.app _

/-- The compatible families: the sections of the product whose components agree on overlaps
under the gluing morphisms. -/
noncomputable def glueSubmodule : (prod D).Submodule where
  obj W := ⨅ p : ι × ι, LinearMap.ker ((left D p.1 p.2 - right D p.1 p.2).val.app W).hom
  map {W W'} g x hx := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_comap] at hx ⊢
    intro p
    have h := PresheafOfModules.naturality_apply (left D p.1 p.2 - right D p.1 p.2).val g x
    rw [hx p, map_zero] at h
    exact h
  isSheaf W x hx := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro p
    refine section_eq_of_mem_grothendieckTopology (target D p.1 p.2) _ hx fun V g hg ↦ ?_
    have hg' : ((left D p.1 p.2 - right D p.1 p.2).val.app (op V)).hom
        ((prod D).val.map g.op x) = 0 := by
      have h₀ : (show (prod D).val.obj (op V) from (prod D).val.map g.op x) ∈
          ⨅ q : ι × ι, LinearMap.ker ((left D q.1 q.2 - right D q.1 q.2).val.app (op V)).hom := hg
      exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h₀ p)
    have h := PresheafOfModules.naturality_apply (left D p.1 p.2 - right D p.1 p.2).val g.op x
    exact h.symm.trans (hg'.trans (map_zero _).symm)

/-- The module sheaf glued from a descent datum. -/
noncomputable abbrev glue : S.Modules := (glueSubmodule D).toSheafOfModules

/-- The `i`-th component of a section of the product, as a section of the `i`-th object. -/
noncomputable def piπ (i : ι) (W : S.Opens) : Γ(prod D, W) ⟶ Γ(obj D i, f i ⁻¹ᵁ W) :=
  Modules.Hom.app (Limits.Pi.π (fun i ↦ (pushforward (f i)).obj (obj D i)) i) W

/-- The preimage in the overlap of an open of `S`, through the first member. -/
lemma inter_preimage_fst (i j : ι) (W : S.Opens) :
    (inter f i j).ι ⁻¹ᵁ W = interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W := by
  rw [← Hom.comp_preimage, liftOpens_fac]

/-- The preimage in the overlap of an open of `S`, through the second member. -/
lemma inter_preimage_snd (i j : ι) (W : S.Opens) :
    (inter f i j).ι ⁻¹ᵁ W = interSnd f i j ⁻¹ᵁ f j ⁻¹ᵁ W := by
  rw [← Hom.comp_preimage, liftOpens_fac]

/-- On sections, `left` restricts the `i`-th component to the overlap and applies the gluing
morphism. -/
lemma left_app (i j : ι) (W : S.Opens) :
    (left D i j).app W = piπ D i W ≫
      (obj D i).presheaf.map (homOfLE ((interFst f i j).image_preimage_le (f i ⁻¹ᵁ W))).op ≫
      transApp D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
        (liftOpens_fac _ _) (interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W) ≫
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
        (inter_preimage_fst i j W).le)).op := by
  simp only [left, Modules.Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app]
  rfl

/-- On sections, `right` restricts the `j`-th component to the overlap. -/
lemma right_app (i j : ι) (W : S.Opens) :
    (right D i j).app W = piπ D j W ≫
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_preimage_le (f j ⁻¹ᵁ W))).op ≫
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
        (inter_preimage_snd i j W).le)).op := by
  simp only [right, Modules.Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app]
  rfl

/-- A section of the product is compatible when `left` and `right` agree on it for all pairs. -/
lemma mem_glueSubmodule {W : S.Opens} (y : Γ(prod D, W)) :
    (show (prod D).val.obj (op W) from y) ∈ (glueSubmodule D).obj (op W) ↔
      ∀ i j, (left D i j).app W y = (right D i j).app W y := by
  change (show (prod D).val.obj (op W) from y) ∈ ⨅ p : ι × ι,
    LinearMap.ker ((left D p.1 p.2 - right D p.1 p.2).val.app (op W)).hom ↔ _
  rw [Submodule.mem_iInf]
  exact ⟨fun h i j ↦ sub_eq_zero.mp (LinearMap.mem_ker.mp (h (i, j))),
    fun h p ↦ LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h p.1 p.2))⟩

/-- Compatibility of a section of the product, in terms of its components and the gluing
morphisms on sections. -/
lemma mem_glueSubmodule_iff {W : S.Opens} (y : Γ(prod D, W)) :
    (show (prod D).val.obj (op W) from y) ∈ (glueSubmodule D).obj (op W) ↔
      ∀ i j, (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
          (inter_preimage_fst i j W).le)).op
        (transApp D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
          (liftOpens_fac _ _) (interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W)
          ((obj D i).presheaf.map (homOfLE ((interFst f i j).image_preimage_le (f i ⁻¹ᵁ W))).op
            (piπ D i W y))) =
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
          (inter_preimage_snd i j W).le)).op
        ((obj D j).presheaf.map (homOfLE ((interSnd f i j).image_preimage_le (f j ⁻¹ᵁ W))).op
          (piπ D j W y)) := by
  rw [mem_glueSubmodule]
  refine forall₂_congr fun i j ↦ ?_
  rw [left_app, right_app]
  rfl

/-- The comparison of the restriction of the glued module sheaf with the `k`-th object. -/
noncomputable def glueRestrict (k : ι) : (glue D).restrict (f k) ⟶ obj D k :=
  (Modules.restrictFunctor (f k)).map ((glueSubmodule D).ι ≫
    Limits.Pi.π (fun i ↦ (pushforward (f i)).obj (obj D i)) k) ≫
    (restrictAdjunction (f k)).counit.app (obj D k)

/-- On sections, the comparison takes the `k`-th component. -/
lemma glueRestrict_app (k : ι) (T : (X k).Opens) (x : Γ(glue D, f k ''ᵁ T)) :
    (glueRestrict D k).app T x =
      (obj D k).presheaf.map (eqToHom ((f k).preimage_image_eq T).symm).op
        (piπ D k (f k ''ᵁ T) x.1) :=
  rfl

/-- For an open `W` inside the range of `f k`, its overlap with the range of `f j`, seen in
`X j` through the overlap of `f k` and `f j`. -/
lemma interSnd_image_inter_preimage {k j : ι} {W : S.Opens} (hW : W ≤ (f k).opensRange) :
    interSnd f k j ''ᵁ (inter f k j).ι ⁻¹ᵁ W = f j ⁻¹ᵁ W := by
  apply (f j).image_injective
  dsimp only
  simp only [← Hom.comp_image, liftOpens_fac, Hom.image_preimage_eq_opensRange_inf,
    Opens.opensRange_ι]
  change (f k).opensRange ⊓ (f j).opensRange ⊓ W = (f j).opensRange ⊓ W
  rw [inf_comm (f k).opensRange, inf_assoc, inf_eq_right.mpr hW]

/-- The comparison is injective on sections: a compatible family whose `k`-th component vanishes
over a subset of the range of `f k` vanishes, since every other component is obtained from the
`k`-th one by a gluing morphism. -/
lemma glueRestrict_app_injective (k : ι) (T : (X k).Opens) :
    Function.Injective ((glueRestrict D k).app T) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨y, hy⟩ hx
  have hW : f k ''ᵁ T ≤ (f k).opensRange := (f k).image_le_opensRange T
  have hk : piπ D k (f k ''ᵁ T) y = 0 := presheaf_map_injective_of_eq (obj D k)
    (eqToHom ((f k).preimage_image_eq T).symm).op ((f k).preimage_image_eq T)
    ((glueRestrict_app D k T ⟨y, hy⟩).symm.trans (hx.trans (map_zero _).symm))
  have hj : ∀ j, piπ D j (f k ''ᵁ T) y = 0 := fun j ↦ by
    have h := (mem_glueSubmodule_iff D y).mp hy k j
    rw [hk, map_zero, map_zero, map_zero] at h
    rw [← ConcreteCategory.comp_apply, presheaf_map_comp_eq _ _ _ (eqToHom (congrArg op
      (interSnd_image_inter_preimage hW).symm))] at h
    exact presheaf_map_injective_of_eq _ _ (interSnd_image_inter_preimage hW).symm
      (h.symm.trans (map_zero _).symm)
  exact Subtype.ext (pi_sections_ext _ _ fun j ↦ (hj j).trans (map_zero _).symm)

/-- Moving the gluing morphism over an overlap to an open `Y` inside it. -/
@[reassoc]
lemma transApp_inter_eq {a b : ι} {Y : S.Opens} (hYa : Y ≤ (f a).opensRange)
    (hYb : Y ≤ (f b).opensRange) (hab : Y ≤ inter f a b) {Z : (inter f a b).toScheme.Opens}
    {U : Y.toScheme.Opens} (hZ : S.homOfLE hab ''ᵁ U ≤ Z) {A : (X a).Opens} {B : (X b).Opens}
    (hB : B ≤ interSnd f a b ''ᵁ S.homOfLE hab ''ᵁ U)
    (α : op A ⟶ op (interFst f a b ''ᵁ Z)) (β : op (interSnd f a b ''ᵁ Z) ⟶ op B)
    (α' : op A ⟶ op (liftOpens (f a) hYa ''ᵁ U)) (β' : op (liftOpens (f b) hYb ''ᵁ U) ⟶ op B) :
    (obj D a).presheaf.map α ≫ transApp D (inter f a b).ι (interFst f a b) (interSnd f a b)
        (liftOpens_fac _ _) (liftOpens_fac _ _) Z ≫ (obj D b).presheaf.map β =
      (obj D a).presheaf.map α' ≫ transApp D Y.ι (liftOpens (f a) hYa) (liftOpens (f b) hYb)
        (liftOpens_fac _ _) (liftOpens_fac _ _) U ≫ (obj D b).presheaf.map β' := by
  have e₁ : interFst f a b ''ᵁ S.homOfLE hab ''ᵁ U = liftOpens (f a) hYa ''ᵁ U := by
    simp only [← Hom.comp_image, homOfLE_liftOpens]
  have e₂ : interSnd f a b ''ᵁ S.homOfLE hab ''ᵁ U = liftOpens (f b) hYb ''ᵁ U := by
    simp only [← Hom.comp_image, homOfLE_liftOpens]
  rw [presheaf_map_congr _ β ((homOfLE ((interSnd f a b).image_mono hZ)).op ≫
      (homOfLE hB).op), Functor.map_comp,
    ← transApp_naturality_assoc D _ _ _ _ _ (homOfLE ((interFst f a b).image_mono hZ)).op,
    transApp_image D (inter f a b).ι (interFst f a b) (interSnd f a b) (liftOpens_fac _ _)
      (liftOpens_fac _ _) (S.homOfLE hab) Y.ι (liftOpens (f a) hYa) (liftOpens (f b) hYb)
      (S.homOfLE_ι hab) (homOfLE_liftOpens (f a) hab inf_le_left)
      (homOfLE_liftOpens (f b) hab inf_le_right) U (homOfLE e₁.ge).op (homOfLE e₂.le).op]
  simp only [← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc]
  congr 2
  all_goals exact presheaf_map_comp_eq _ _ _ _

/-- Sections over `W` of the `j`-th object obtained from sections of the `k`-th object by the
gluing morphism, for `W` inside the range of `f k`. -/
noncomputable def fromObj (k j : ι) (W : S.Opens) (hW : W ≤ (f k).opensRange) :
    Γ(obj D k, f k ⁻¹ᵁ W) ⟶ Γ(obj D j, f j ⁻¹ᵁ W) :=
  (obj D k).presheaf.map (homOfLE (show interFst f k j ''ᵁ (inter f k j).ι ⁻¹ᵁ W ≤ f k ⁻¹ᵁ W by
      rw [inter_preimage_fst]; exact (interFst f k j).image_preimage_le _)).op ≫
    transApp D (inter f k j).ι (interFst f k j) (interSnd f k j) (liftOpens_fac _ _)
      (liftOpens_fac _ _) ((inter f k j).ι ⁻¹ᵁ W) ≫
    (obj D j).presheaf.map (homOfLE (interSnd_image_inter_preimage hW).ge).op

/-- The family obtained from a section of the `k`-th object by `fromObj` is compatible. This is
the cocycle condition over the triple overlap of `f k`, `f i` and `f j`. -/
lemma fromObj_cocycle (k i j : ι) (W : S.Opens) (hW : W ≤ (f k).opensRange) :
    fromObj D k i W hW ≫ (obj D i).presheaf.map (homOfLE ((interFst f i j).image_preimage_le
        (f i ⁻¹ᵁ W))).op ≫
      transApp D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
        (liftOpens_fac _ _) (interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W) ≫
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
        (inter_preimage_fst i j W).le)).op =
    fromObj D k j W hW ≫ (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_preimage_le
        (f j ⁻¹ᵁ W))).op ≫
      (obj D j).presheaf.map (homOfLE ((interSnd f i j).image_mono
        (inter_preimage_snd i j W).le)).op := by
  have hYk : (f k).opensRange ⊓ (f i).opensRange ⊓ (f j).opensRange ≤ (f k).opensRange :=
    inf_le_left.trans inf_le_left
  have hYi : (f k).opensRange ⊓ (f i).opensRange ⊓ (f j).opensRange ≤ (f i).opensRange :=
    inf_le_left.trans inf_le_right
  have hYj : (f k).opensRange ⊓ (f i).opensRange ⊓ (f j).opensRange ≤ (f j).opensRange :=
    inf_le_right
  have hki := le_inf hYk hYi
  have hij := le_inf hYi hYj
  have hkj := le_inf hYk hYj
  have hWY : inter f i j ⊓ W ≤ ((f k).opensRange ⊓ (f i).opensRange ⊓ (f j).opensRange) ⊓ W :=
    le_inf (le_inf (le_inf (inf_le_right.trans hW) (inf_le_left.trans inf_le_left))
      (inf_le_left.trans inf_le_right)) inf_le_right
  set Y₃ : S.Opens := (f k).opensRange ⊓ (f i).opensRange ⊓ (f j).opensRange with hY₃
  set U₃ := Y₃.ι ⁻¹ᵁ W with hU₃
  have img : ∀ {a : ι} (h : Y₃ ≤ (f a).opensRange), f a ''ᵁ liftOpens (f a) h ''ᵁ U₃ = Y₃ ⊓ W :=
    fun h ↦ by simp only [U₃, ← Hom.comp_image, liftOpens_fac,
      Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι]
  have imgι : ∀ {a b : ι} (h : Y₃ ≤ inter f a b), (inter f a b).ι ''ᵁ S.homOfLE h ''ᵁ U₃ =
      Y₃ ⊓ W := fun h ↦ by
    simp only [U₃, ← Hom.comp_image, homOfLE_ι, Hom.image_preimage_eq_opensRange_inf,
      Opens.opensRange_ι]
  have imgSnd : ∀ {a b : ι} (h : Y₃ ≤ inter f a b),
      f b ''ᵁ interSnd f a b ''ᵁ S.homOfLE h ''ᵁ U₃ = Y₃ ⊓ W := fun h ↦ by
    simp only [U₃, ← Hom.comp_image, liftOpens_fac, Category.assoc, homOfLE_ι,
      Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι]
  have imgInter : ∀ {a b : ι}, (inter f a b).ι ''ᵁ (inter f a b).ι ⁻¹ᵁ W = inter f a b ⊓ W :=
    by simp only [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, implies_true]
  have imgSndInter : ∀ {a b : ι},
      f b ''ᵁ interSnd f a b ''ᵁ (inter f a b).ι ⁻¹ᵁ W = inter f a b ⊓ W := by
    simp only [← Hom.comp_image, liftOpens_fac, Hom.image_preimage_eq_opensRange_inf,
      Opens.opensRange_ι, implies_true]
  have hZki : S.homOfLE hki ''ᵁ U₃ ≤ (inter f k i).ι ⁻¹ᵁ W := by
    rw [← (inter f k i).ι.image_le_image_iff, imgι, imgInter]; exact inf_le_inf_right W hki
  have hZij : S.homOfLE hij ''ᵁ U₃ ≤ interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W := by
    rw [← inter_preimage_fst, ← (inter f i j).ι.image_le_image_iff, imgι, imgInter]
    exact inf_le_inf_right W hij
  have hZkj : S.homOfLE hkj ''ᵁ U₃ ≤ (inter f k j).ι ⁻¹ᵁ W := by
    rw [← (inter f k j).ι.image_le_image_iff, imgι, imgInter]; exact inf_le_inf_right W hkj
  have hBki : liftOpens (f i) hYi ''ᵁ U₃ ≤ interSnd f k i ''ᵁ S.homOfLE hki ''ᵁ U₃ := by
    rw [← (f i).image_le_image_iff, img, imgSnd]
  have hBij : interSnd f i j ''ᵁ (inter f i j).ι ⁻¹ᵁ W ≤
      interSnd f i j ''ᵁ S.homOfLE hij ''ᵁ U₃ := by
    rw [← (f j).image_le_image_iff, imgSnd, imgSndInter]; exact hWY
  have hBkj : interSnd f i j ''ᵁ (inter f i j).ι ⁻¹ᵁ W ≤
      interSnd f k j ''ᵁ S.homOfLE hkj ''ᵁ U₃ := by
    rw [← (f j).image_le_image_iff, imgSnd, imgSndInter]; exact hWY
  have hαk : liftOpens (f k) hYk ''ᵁ U₃ ≤ f k ⁻¹ᵁ W := by
    rw [← (f k).image_le_image_iff, img, Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_inf_right W hYk
  have hβki : liftOpens (f i) hYi ''ᵁ U₃ ≤ interSnd f k i ''ᵁ (inter f k i).ι ⁻¹ᵁ W := by
    rw [← (f i).image_le_image_iff, img, imgSndInter]; exact inf_le_inf_right W hki
  have hαij : interFst f i j ''ᵁ interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ W ≤ liftOpens (f i) hYi ''ᵁ U₃ := by
    rw [← inter_preimage_fst, ← (f i).image_le_image_iff, img]
    simp only [← Hom.comp_image, liftOpens_fac, Hom.image_preimage_eq_opensRange_inf,
      Opens.opensRange_ι]
    exact hWY
  have hβj : interSnd f i j ''ᵁ (inter f i j).ι ⁻¹ᵁ W ≤ liftOpens (f j) hYj ''ᵁ U₃ := by
    rw [← (f j).image_le_image_iff, img, imgSndInter]; exact hWY
  simp only [fromObj, Category.assoc]
  rw [presheaf_map_comp_eq_assoc (obj D i) _ _ ((homOfLE hβki).op ≫ (homOfLE hαij).op),
    Functor.map_comp_assoc,
    transApp_inter_eq_assoc D hYk hYi hki hZki hBki _ _ (homOfLE hαk).op (𝟙 _),
    transApp_inter_eq D hYi hYj hij hZij hBij _ _ (𝟙 _) (homOfLE hβj).op]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [transApp_comp_assoc]
  simp only [← Functor.map_comp]
  rw [transApp_inter_eq D hYk hYj hkj hZkj hBkj _ _ (homOfLE hαk).op (homOfLE hβj).op]

/-- The comparison is surjective on sections: a section of the `k`-th object extends to a
compatible family by `fromObj`. -/
lemma glueRestrict_app_surjective (k : ι) (T : (X k).Opens) :
    Function.Surjective ((glueRestrict D k).app T) := by
  intro t
  have hW : f k ''ᵁ T ≤ (f k).opensRange := (f k).image_le_opensRange T
  set t' : Γ(obj D k, f k ⁻¹ᵁ f k ''ᵁ T) :=
    (obj D k).presheaf.map (eqToHom ((f k).preimage_image_eq T)).op t with ht'
  set y : Γ(prod D, f k ''ᵁ T) := (piSectionsEquiv _ (f k ''ᵁ T)).symm
    fun j ↦ fromObj D k j (f k ''ᵁ T) hW t' with hy
  have hπ (j : ι) : piπ D j (f k ''ᵁ T) y = fromObj D k j (f k ''ᵁ T) hW t' :=
    pi_π_app_piSectionsEquiv_symm _ _ _ j
  have mem : (show (prod D).val.obj (op (f k ''ᵁ T)) from y) ∈
      (glueSubmodule D).obj (op (f k ''ᵁ T)) := by
    rw [mem_glueSubmodule_iff]
    intro i j
    rw [hπ i, hπ j]
    exact congrArg (fun φ ↦ φ t') (fromObj_cocycle D k i j (f k ''ᵁ T) hW)
  refine ⟨⟨y, mem⟩, (glueRestrict_app D k T ⟨y, mem⟩).trans ?_⟩
  change (obj D k).presheaf.map (eqToHom ((f k).preimage_image_eq T).symm).op
    (piπ D k (f k ''ᵁ T) y) = t
  rw [hπ k, fromObj, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, transApp_self,
    ConcreteCategory.id_apply, ht', presheaf_map_map, presheaf_map_map, presheaf_map_map,
    Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

instance (k : ι) : IsIso (glueRestrict D k) :=
  Modules.Hom.isIso_iff_isIso_app.mpr fun T ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨glueRestrict_app_injective D k T, glueRestrict_app_surjective D k T⟩

/-- The comparison of the glued module sheaf with the `k`-th object, on sections. -/
noncomputable def glueRestrictApp (k : ι) (T : (X k).Opens) :
    Γ(glue D, f k ''ᵁ T) ⟶ Γ(obj D k, T) :=
  (glueRestrict D k).app T

/-- A section of the glued module sheaf, as a section of the product. -/
def glueVal {W : S.Opens} (x : Γ(glue D, W)) : Γ(prod D, W) := x.1

/-- A section of the glued module sheaf is a compatible family. -/
lemma glueVal_mem {W : S.Opens} (x : Γ(glue D, W)) :
    (show (prod D).val.obj (op W) from glueVal D x) ∈ (glueSubmodule D).obj (op W) :=
  x.2

/-- On sections, the comparison takes the `k`-th component. -/
lemma glueRestrictApp_apply (k : ι) (T : (X k).Opens) (x : Γ(glue D, f k ''ᵁ T)) :
    glueRestrictApp D k T x = (obj D k).presheaf.map
      (eqToHom ((f k).preimage_image_eq T).symm).op (piπ D k (f k ''ᵁ T) (glueVal D x)) :=
  rfl

/-- Restriction of sections of the glued module sheaf is restriction in the product. -/
lemma glueVal_map {W W' : S.Opens} (g : op W ⟶ op W') (x : Γ(glue D, W)) :
    glueVal D ((glue D).presheaf.map g x) = (prod D).presheaf.map g (glueVal D x) :=
  rfl

omit [∀ i, IsOpenImmersion (f i)] in
/-- The components of a section of the product commute with restriction. -/
lemma piπ_map {W W' : S.Opens} (i : ι) (g : op W ⟶ op W') (y : Γ(prod D, W)) :
    piπ D i W' ((prod D).presheaf.map g y) =
      (obj D i).presheaf.map (homOfLE ((f i).preimage_mono (leOfHom g.unop))).op
        (piπ D i W y) :=
  NatTrans.naturality_apply
    (Limits.Pi.π (fun i ↦ (pushforward (f i)).obj (obj D i)) i).mapPresheaf g y

/-- On sections, the comparisons of the glued module sheaf with the objects of the descent datum
are compatible with its gluing morphisms over the overlaps. -/
lemma glueRestrictApp_comm (i j : ι) (T₀ : (inter f i j).toScheme.Opens)
    (g : op (f i ''ᵁ interFst f i j ''ᵁ T₀) ⟶ op (f j ''ᵁ interSnd f i j ''ᵁ T₀)) :
    glueRestrictApp D i (interFst f i j ''ᵁ T₀) ≫
        transApp D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
          (liftOpens_fac _ _) T₀ =
      (glue D).presheaf.map g ≫ glueRestrictApp D j (interSnd f i j ''ᵁ T₀) := by
  ext x
  change transApp D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
    (liftOpens_fac _ _) T₀ (glueRestrictApp D i (interFst f i j ''ᵁ T₀) x) =
      glueRestrictApp D j (interSnd f i j ''ᵁ T₀) ((glue D).presheaf.map g x)
  rw [glueRestrictApp_apply, glueRestrictApp_apply, glueVal_map, piπ_map]
  have hy := glueVal_mem D x
  set y := glueVal D x
  have hU : interFst f i j ⁻¹ᵁ f i ⁻¹ᵁ f i ''ᵁ interFst f i j ''ᵁ T₀ = T₀ := by simp
  have hW : (inter f i j).ι ⁻¹ᵁ f i ''ᵁ interFst f i j ''ᵁ T₀ = T₀ := by
    rw [inter_preimage_fst, hU]
  have hy' := (mem_glueSubmodule_iff D y).mp hy i j
  have hθ := congrArg (fun φ ↦ φ ((obj D i).presheaf.map
      (homOfLE ((interFst f i j).image_preimage_le
        (f i ⁻¹ᵁ f i ''ᵁ interFst f i j ''ᵁ T₀))).op (piπ D i _ y)))
    (transApp_naturality D (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
      (liftOpens_fac _ _) (homOfLE ((interFst f i j).image_mono hU.ge)).op
      (homOfLE ((interSnd f i j).image_mono hU.ge)).op)
  simp only [ConcreteCategory.comp_apply] at hθ
  have hc : (homOfLE ((interSnd f i j).image_mono hU.ge)).op =
      (homOfLE ((interSnd f i j).image_mono (inter_preimage_fst i j _).le)).op ≫
        (homOfLE ((interSnd f i j).image_mono hW.ge)).op := Subsingleton.elim _ _
  rw [hc, ← presheaf_map_map (obj D j), hy'] at hθ
  simp only [presheaf_map_map] at hθ ⊢
  refine Eq.trans ?_ (hθ.trans ?_) <;> congr 2

/-- A family of morphisms between two descent data along `f` commutes with their gluing
morphisms over every test object as soon as it does over the overlaps: every test object maps
into an overlap, and descent data are compatible with changing the test object. -/
lemma comm_of_inter {D₁ D₂ : modulesPseudofunctor.DescentData f} (e : ∀ i, D₁.obj i ⟶ D₂.obj i)
    (h : ∀ i j, (modulesPseudofunctor.map (interFst f i j).op.toLoc).toFunctor.map (e i) ≫
        D₂.hom (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
          (liftOpens_fac _ _) =
      D₁.hom (inter f i j).ι (interFst f i j) (interSnd f i j) (liftOpens_fac _ _)
          (liftOpens_fac _ _) ≫
        (modulesPseudofunctor.map (interSnd f i j).op.toLoc).toFunctor.map (e j))
    ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map (e i₁) ≫ D₂.hom q f₁ f₂ hf₁ hf₂ =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map (e i₂) := by
  have hrange : Set.range q ⊆ Set.range (inter f i₁ i₂).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hf₁, Hom.comp_apply]; exact ⟨_, rfl⟩
    · rw [← hf₂, Hom.comp_apply]; exact ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g ≫ (inter f i₁ i₂).ι = q :=
    ⟨IsOpenImmersion.lift (inter f i₁ i₂).ι q hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hg₁ : g ≫ interFst f i₁ i₂ = f₁ := by
    rw [← cancel_mono (f i₁), Category.assoc, liftOpens_fac, hg, hf₁]
  have hg₂ : g ≫ interSnd f i₁ i₂ = f₂ := by
    rw [← cancel_mono (f i₂), Category.assoc, liftOpens_fac, hg, hf₂]
  rw [← D₂.pullHom_hom g (inter f i₁ i₂).ι q hg (interFst f i₁ i₂) (interSnd f i₁ i₂)
      (liftOpens_fac _ _) (liftOpens_fac _ _) f₁ f₂ hg₁ hg₂,
    ← D₁.pullHom_hom g (inter f i₁ i₂).ι q hg (interFst f i₁ i₂) (interSnd f i₁ i₂)
      (liftOpens_fac _ _) (liftOpens_fac _ _) f₁ f₂ hg₁ hg₂]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc]
  rw [Pseudofunctor.mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, h,
    Functor.map_comp_assoc, Pseudofunctor.mapComp'_inv_naturality]

/-- The comparisons of the glued module sheaf with the objects of the descent datum commute with
the gluing morphisms over the overlaps. -/
lemma glue_comm_restrict (i j : ι) :
    (Modules.restrictFunctor (interFst f i j)).map (glueRestrict D i) ≫ transInter D i j =
      (restrictFunctorComp' (interFst f i j) (f i) (inter f i j).ι (liftOpens_fac _ _)).inv.app
          (glue D) ≫
        (restrictFunctorComp' (interSnd f i j) (f j) (inter f i j).ι (liftOpens_fac _ _)).hom.app
          (glue D) ≫
        (Modules.restrictFunctor (interSnd f i j)).map (glueRestrict D j) := by
  refine Modules.hom_ext _ _ fun T₀ ↦ ?_
  have e : f j ''ᵁ interSnd f i j ''ᵁ T₀ ≤ f i ''ᵁ interFst f i j ''ᵁ T₀ := by
    simp only [← Hom.comp_image, liftOpens_fac]; rfl
  simp only [Modules.Hom.comp_app, restrictFunctor_map_app, restrictFunctorComp'_hom_app_app,
    restrictFunctorComp'_inv_app_app]
  erw [presheaf_map_comp_eq_assoc (glue D) _ _ (homOfLE e).op]
  exact glueRestrictApp_comm D i j T₀ (homOfLE e).op

variable {D} in
/-- The isomorphisms `f i ^* M ≅ D.obj i` induced by isomorphisms `M|_{X i} ≅ D.obj i`. -/
noncomputable def isoOfRestrictObj {M : S.Modules} (ε : ∀ i, M.restrict (f i) ⟶ obj D i)
    [∀ i, IsIso (ε i)] (i : ι) :
    ((modulesPseudofunctor.toDescentData f).obj M).obj i ≅ D.obj i :=
  (((restrictFunctorIsoPullback (f i)).app M).symm ≪≫ asIso (ε i) :
    (pullback (f i)).obj M ≅ obj D i)

variable {D} in
/-- The forward map of `isoOfRestrictObj`. -/
lemma isoOfRestrictObj_hom {M : S.Modules} (ε : ∀ i, M.restrict (f i) ⟶ obj D i)
    [∀ i, IsIso (ε i)] (i : ι) :
    (isoOfRestrictObj ε i).hom = (restrictFunctorIsoPullback (f i)).inv.app M ≫ ε i :=
  rfl

variable {D} in
/-- A module sheaf on `S` whose restrictions are identified with the objects of a descent datum,
compatibly with its gluing morphisms over the overlaps, has that descent datum. -/
noncomputable def isoOfRestrict {M : S.Modules} (ε : ∀ i, M.restrict (f i) ⟶ obj D i)
    [∀ i, IsIso (ε i)]
    (h : ∀ i j, (Modules.restrictFunctor (interFst f i j)).map (ε i) ≫ transInter D i j =
      (restrictFunctorComp' (interFst f i j) (f i) (inter f i j).ι (liftOpens_fac _ _)).inv.app
          M ≫
        (restrictFunctorComp' (interSnd f i j) (f j) (inter f i j).ι (liftOpens_fac _ _)).hom.app
          M ≫ (Modules.restrictFunctor (interSnd f i j)).map (ε j)) :
    (modulesPseudofunctor.toDescentData f).obj M ≅ D :=
  Pseudofunctor.DescentData.isoMk (isoOfRestrictObj ε)
    (comm_of_inter (D₁ := (modulesPseudofunctor.toDescentData f).obj M) (D₂ := D)
      (fun i ↦ (isoOfRestrictObj ε i).hom)
      fun i j ↦ descentComm_of_restrict_of_eq ε (fun i ↦ (isoOfRestrictObj ε i).hom)
        (isoOfRestrictObj_hom ε) (inter f i j).ι (interFst f i j) (interSnd f i j)
        (liftOpens_fac _ _) (liftOpens_fac _ _) (h i j))

/-- The descent datum of the glued module sheaf is the descent datum it was glued from. -/
noncomputable def glueIso : (modulesPseudofunctor.toDescentData f).obj (glue D) ≅ D :=
  isoOfRestrict (M := glue D) (glueRestrict D) (glue_comm_restrict D)

variable (f) in
/-- Every descent datum along a cover by open immersions indexed in `Type u` is effective: it is
the descent datum of `glue D`. -/
lemma essSurj_toDescentData : (modulesPseudofunctor.toDescentData f).EssSurj :=
  ⟨fun D ↦ ⟨glue D, ⟨glueIso D⟩⟩⟩

variable (f) in
/-- The stack condition for a jointly surjective family of open immersions indexed in `Type u`. -/
lemma isStackFor_ofArrows (hf : ⨆ i, (f i).opensRange = ⊤) :
    modulesPseudofunctor.IsStackFor (Presieve.ofArrows X f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  have := faithful_toDescentData hf
  have := full_toDescentData hf
  have := essSurj_toDescentData f
  exact { }

end Glue

end ZariskiDescent

open ZariskiDescent in
/-- Morphisms of sheaves of modules glue along Zariski covers: `X ↦ X.Modules` is a prestack for
the big Zariski topology ([Stacks, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)). -/
instance modulesPseudofunctor_isPrestack :
    modulesPseudofunctor.{u}.IsPrestack zariskiTopology := by
  refine Pseudofunctor.IsPrestack.of_precoverage (J := zariskiPrecoverage) fun S R hR ↦ ?_
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_precoverage_iff] at hR
  have := hR.2
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
  have hf := iSup_opensRange_eq_top hR.1
  have := faithful_toDescentData hf
  have := full_toDescentData hf
  exact ⟨.ofFullyFaithful _⟩

open ZariskiDescent in
/-- Sheaves of modules glue along Zariski covers: `X ↦ X.Modules` is a stack for the big Zariski
topology ([Stacks, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL),
[Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)). -/
instance modulesPseudofunctor_isStack :
    modulesPseudofunctor.{u}.IsStack zariskiTopology := by
  refine Pseudofunctor.IsStack.of_precoverage (J := zariskiPrecoverage) fun S R hR ↦ ?_
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_precoverage_iff] at hR
  choose idx hidx using hR.1
  have : ∀ x, IsOpenImmersion (f (idx x)) := fun x ↦ hR.2 _
  have hsmall : Presieve.ofArrows _ (fun x ↦ f (idx x)) ∈ zariskiPrecoverage S :=
    (ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ⟨x, hidx x⟩, fun x ↦ hR.2 _⟩
  refine Pseudofunctor.IsStackFor.of_le modulesPseudofunctor (J := zariskiTopology)
    (hR₁ := isStackFor_ofArrows (fun x ↦ f (idx x))
      (iSup_opensRange_eq_top fun x ↦ ⟨x, hidx x⟩))
    (hR₂ := Precoverage.generate_mem_toGrothendieck hsmall) ?_
  rintro _ _ ⟨x⟩
  exact Presieve.ofArrows.mk _

end AlgebraicGeometry.Scheme
