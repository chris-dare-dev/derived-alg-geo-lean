/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Invertible
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Skeletal
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The sheafified tensor product and Picard classes of a scheme

For a scheme, `Scheme.Modules.tensorObj M N` is the associated sheaf of the objectwise tensor
product of the underlying presheaves. The unit, symmetry, and the associator before iterated
sheafification are exported. `Scheme.Modules.PicardClass X` is the set of isomorphism classes of
invertible sheaves, with its distinguished structure-sheaf class. Intrinsic invertibility and
rank-one local trivializations are imported from their arbitrary-site owner.
-/

open CategoryTheory Limits MonoidalCategory BraidedCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

noncomputable section

-- Avoid the reducible-transparency instance diamond between `Scheme.Modules` and its defining
-- `SheafOfModules` category while constructing the sheafified tensor product.
local instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

-- The structure presheaf is commutative, even though `X.Modules` deliberately exposes its
-- `RingCat` forgetful image.
local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private abbrev associatedSheaf (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafification of the objectwise tensor product of two sheaves of modules. -/
noncomputable def tensorObj (M N : X.Modules) : X.Modules :=
  (associatedSheaf X).obj
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)

/-- Tensor two morphisms before sheafification. -/
noncomputable def tensorHom {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  (associatedSheaf X).map
    ((toPresheafOfModules X).map f ⊗ₘ (toPresheafOfModules X).map g)

/-- **Tensoring with a fixed sheaf on the left preserves composition.**

`tensorHom (𝟙 F) −` is functorial. Every layer of `tensorHom` is a functor, so
this is `Functor.map_comp` on top of `tensorHom_comp_tensorHom`; no linearity
is involved anywhere.

That distinction is the point. A scalar cannot be moved across `tensorHom`:
neither `X.Modules` nor `X.PresheafOfModules` carries the monoidal-linear
structure that would need, and supplying it would mean a `Γ`-linear structure on
presheaves, linearity of `toPresheafOfModules` and of `associatedSheaf`, and a
`MonoidalLinear` instance — none of which exist. A *morphism* can be moved
across it, by this lemma. So an argument that would multiply by a section should
compose with multiplication-by-that-section instead.

It has to live here rather than with its consumer: the monoidal structure on
`X.PresheafOfModules` is a `local instance` in this namespace, so
`MonoidalCategoryStruct X.PresheafOfModules` does not synthesize outside it and
the presheaf-level identity below is not even statable elsewhere. -/
@[reassoc]
theorem tensorHom_id_comp (F : X.Modules) {M N P : X.Modules}
    (β : M ⟶ N) (β' : N ⟶ P) :
    tensorHom (𝟙 F) (β ≫ β') = tensorHom (𝟙 F) β ≫ tensorHom (𝟙 F) β' := by
  have h : (toPresheafOfModules X).map (𝟙 F) ⊗ₘ
        (toPresheafOfModules X).map (β ≫ β')
      = ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ (toPresheafOfModules X).map β) ≫
        ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
          (toPresheafOfModules X).map β') := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  unfold tensorHom
  rw [h, CategoryTheory.Functor.map_comp]
  rfl

/-- Sheafification identifies tensoring with the structure sheaf on the left. -/
noncomputable def tensorUnitLeftIso (M : X.Modules) :
    tensorObj (.unit X.ringCatSheaf) M ≅ M :=
  (associatedSheaf X).mapIso (λ_ ((toPresheafOfModules X).obj M)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- Sheafification identifies tensoring with the structure sheaf on the right. -/
noncomputable def tensorUnitRightIso (M : X.Modules) :
    tensorObj M (.unit X.ringCatSheaf) ≅ M :=
  (associatedSheaf X).mapIso (ρ_ ((toPresheafOfModules X).obj M)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- **Conjugating an endomorphism of the unit by the right unitor.**

`M ≅ M ⊗ 𝟙 --(𝟙 ⊗ φ)--> M ⊗ 𝟙 ≅ M`. This is how a map out of the structure sheaf acts on an
arbitrary module sheaf without any linearity of the tensor being available. -/
noncomputable def unitorConj (M : X.Modules)
    (φ : (.unit X.ringCatSheaf : X.Modules) ⟶ .unit X.ringCatSheaf) : M ⟶ M :=
  (tensorUnitRightIso M).inv ≫ tensorHom (𝟙 M) φ ≫ (tensorUnitRightIso M).hom

/-- **The same conjugation, one level down: a morphism of presheaves of modules.**

This is where the computation happens. Mathlib's `PresheafOfModules/Monoidal.lean` gives the
unitors and `⊗ₘ` openwise by `rfl`, reducing to `ModuleCat`'s own monoidal structure, so at this
level `t ↦ t ⊗ₜ 1 ↦ t ⊗ₜ φ(1) ↦ φ(1) • t` is definitional. No such API exists a level up, on the
sheafified tensor — `unitorConj_eq` is what carries the computation across. -/
noncomputable def unitorConjPre (M : X.Modules)
    (φ : (.unit X.ringCatSheaf : X.Modules) ⟶ .unit X.ringCatSheaf) :
    (toPresheafOfModules X).obj M ⟶ (toPresheafOfModules X).obj M :=
  (ρ_ ((toPresheafOfModules X).obj M)).inv ≫
    ((toPresheafOfModules X).map (𝟙 M) ⊗ₘ (toPresheafOfModules X).map φ) ≫
    (ρ_ ((toPresheafOfModules X).obj M)).hom

/-- **The conjugate is the sheaf morphism whose presheaf image is `unitorConjPre`.**

The point of the whole file's approach to this: sheafification is never computed on sections.
`unitorConjPre` is a presheaf endomorphism of `M`'s underlying presheaf; `toPresheafOfModules` is
fully faithful, so it is the image of a unique sheaf endomorphism, and naturality of the
sheafification adjunction's counit collapses `counit.inv ≫ associatedSheaf.map _ ≫ counit.hom` to
exactly that endomorphism.

Two steps are `congrArg`/`exact` rather than `rw`: goals here mention `associatedSheaf`, and are
not type-correct under the `instances` transparency level, which stops `rw` matching patterns that
are syntactically present. -/
theorem unitorConj_eq (M : X.Modules)
    (φ : (.unit X.ringCatSheaf : X.Modules) ⟶ .unit X.ringCatSheaf) :
    unitorConj M φ
      = (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimage
          (unitorConjPre M φ) := by
  have hmap : (toPresheafOfModules X).map
      ((Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimage (unitorConjPre M φ))
      = unitorConjPre M φ :=
    (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).map_preimage _
  have hnat := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).naturality
      ((Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimage (unitorConjPre M φ))
  rw [unitorConj, Iso.inv_comp_eq]
  have hpre : ((toPresheafOfModules X).map (𝟙 M) ⊗ₘ (toPresheafOfModules X).map φ) ≫
        (ρ_ ((toPresheafOfModules X).obj M)).hom
      = (ρ_ ((toPresheafOfModules X).obj M)).hom ≫ unitorConjPre M φ := by
    rw [unitorConjPre, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl
  have hnat' : (associatedSheaf X).map (unitorConjPre M φ) ≫
        ((asIso (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit).app M).hom
      = ((asIso (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit).app M).hom ≫
        (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).preimage
          (unitorConjPre M φ) := by
    rw [← hmap]; exact hnat
  have hAB : (associatedSheaf X).map ((toPresheafOfModules X).map (𝟙 M) ⊗ₘ
          (toPresheafOfModules X).map φ) ≫
        (associatedSheaf X).map (ρ_ ((toPresheafOfModules X).obj M)).hom
      = (associatedSheaf X).map (ρ_ ((toPresheafOfModules X).obj M)).hom ≫
        (associatedSheaf X).map (unitorConjPre M φ) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hpre]
    rfl
  rw [tensorUnitRightIso, tensorHom]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hAB)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hnat'))


/-- **What conjugation does to a section: it multiplies by `φ`'s value on `1`.**

The element-level rule for the sheafified tensor that the twist API needed and did not have.
Before this, no lemma anywhere in the tree said what any of `tensorObj`, `tensorHom` or
`tensorUnitRightIso` does to a section — every consumer used them at the morphism level only.

Given `unitorConj_eq` it is `rfl`: the sheaf morphism *is* `unitorConjPre`, and that computes
openwise by Mathlib's presheaf-monoidal API.

The scalar is ascribed at `Γ(X, U.unop)`. Written bare it elaborates at the unit sheaf's own
section type, where the action on `Γ(M, U)` does not synthesize. -/
theorem unitorConj_app (M : X.Modules)
    (φ : (.unit X.ringCatSheaf : X.Modules) ⟶ .unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ) (t : Γ(M, U.unop)) :
    ((unitorConj M φ).val.app U).hom t
      = (show Γ(X, U.unop) from (φ.val.app U).hom (1 : Γ(X, U.unop))) • t := by
  have hval : (unitorConj M φ).val = unitorConjPre M φ := by
    rw [unitorConj_eq]
    exact (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).map_preimage _
  rw [hval]
  rfl

/-- **A pure tensor of sections, as a section of the sheafified tensor.**

The exportable handle on the sheafified tensor at section level. `tensorObj` is built from
`toPresheafOfModules` and the monoidal structure on `X.PresheafOfModules`, neither of which is
nameable outside this file — the first is used through a `private abbrev`, the second is a
`local instance`. So a consumer cannot write `t ⊗ₜ y` at all, and any section-level statement about
the tensor has to be phrased through a named constructor. This is it.

It is the image of the honest pure tensor under the sheafification adjunction's unit. Sections of a
sheafification are not in general sums of pure tensors, so this is a map *into* the sections, not a
description of them — which is all the twist API needs. -/
noncomputable def tmulSection (M N : X.Modules) (U : X.Opensᵒᵖ)
    (t : Γ(M, U.unop)) (y : Γ(N, U.unop)) : Γ(tensorObj M N, U.unop) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)).app U
      (t ⊗ₜ[Γ(X, U.unop)] y)


/-- **A scalar moves across the pure tensor.**

Tensor bilinearity plus linearity of the unit's component. What makes it usable downstream is the
direction: a scalar sitting outside, where a chart extension leaves it, can be pushed onto the
second factor, where the twist's own section lives. -/
theorem smul_tmulSection (M N : X.Modules) (U : X.Opensᵒᵖ)
    (r : Γ(X, U.unop)) (t : Γ(M, U.unop)) (y : Γ(N, U.unop)) :
    r • tmulSection M N U t y = tmulSection M N U t (r • y) := by
  have h1 : (t ⊗ₜ[Γ(X, U.unop)] (r • y)) = r • (t ⊗ₜ[Γ(X, U.unop)] y) :=
    TensorProduct.tmul_smul _ _ _
  rw [tmulSection, tmulSection]
  set eta := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)).app U with heta
  have hsm : (ModuleCat.Hom.hom eta) (r • (t ⊗ₜ[Γ(X, U.unop)] y))
      = r • (ModuleCat.Hom.hom eta) (t ⊗ₜ[Γ(X, U.unop)] y) := by
    exact (ModuleCat.Hom.hom eta).map_smul r _
  exact (hsm.symm.trans (congrArg _ h1.symm))

/-- **The sheafification unit of a presheaf of modules is locally surjective.**

Its underlying map of abelian presheaves *is* `toSheafify`
(`toPresheaf_map_sheafificationAdjunction_unit_app`, by `rfl`), and that carries Mathlib's
instance. Stated because instance search does not find it on its own: all three of
`HasWeakSheafify`, `HasSheafCompose` and `PreservesSheafification` synthesize here, but the
composite goal does not, and explicit application is what closes it. -/
theorem isLocallySurjective_sheafificationUnit (P : X.PresheafOfModules) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact Presheaf.isLocallySurjective_toSheafify' _ _

/-- **Locally, a section of the sheafified tensor product is a finite sum of pure tensors.**

`tmulSection`'s docstring warns that it is "a map *into* the sections, not a description of them",
and globally that is right: sheafification does not preserve surjectivity of
`M(U) ⊗ N(U) → Γ(M ⊗ N, U)` on the nose. **Locally it does**, and this is that statement — the
missing converse, and the reason it can only live in this file.

Nothing outside can state it. The monoidal structure on `X.PresheafOfModules` is a `local instance`
here and `associatedSheaf` is a `private abbrev`, so a consumer cannot write `t ⊗ₜ y`, cannot name
`M' ⊗ N'`, and therefore cannot say "a section of the sheafification comes from the presheaf
tensor" at all. Anything needing to take a section of `M ⊗ N` apart has to be given this from
inside.

The proof is the three facts that were unavailable to a consumer: the sheafification unit is
locally surjective, so `t` has a preimage `z` in the presheaf tensor near `x`;
`TensorProduct.exists_finset` writes `z` as a finite sum of pure tensors; and the unit's component
is additive, which turns that sum into a sum of `tmulSection`s by definition of `tmulSection`.

The neighbourhood is genuinely needed: `V` is where the preimage exists, and no smaller claim about
`U` itself is available. -/
theorem exists_eq_sum_tmulSection (M N : X.Modules) {U : X.Opens}
    (t : Γ(tensorObj M N, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ s : Finset (Γ(M, V) × Γ(N, V)),
        (tensorObj M N).presheaf.map (homOfLE hV).op t
          = ∑ p ∈ s, tmulSection M N (Opposite.op V) p.1 p.2 := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N))) :=
    isLocallySurjective_sheafificationUnit _
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hls U t x hx
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset z
  refine ⟨V, hV, hxV, s, ?_⟩
  refine (hz.symm : _ = _).trans ?_
  exact map_sum _ _ _

/-- **The `twistBy` shape, applied to a section: it is the pure tensor with `ψ`'s value on `1`.**

`(ρ.inv ≫ tensorHom (𝟙 F) ψ)` is exactly the shape of `Proj.twistBy` and of
`Proj.chartTwistBy`. This says what it does to a section, which nothing in the tree did before.

Proved the same way as `unitorConj_eq`, and sheafification is again never computed on sections.
The counit's inverse *is* the adjunction unit — `hinv`, from the right triangle identity, assembled
mono-free because `Mono` does not synthesize on a `.val`; then naturality of that unit carries a
presheaf-level computation across, and the presheaf-level part (`t ↦ t ⊗ₜ 1 ↦ t ⊗ₜ ψ(1)`) is `rfl`.

Every step is `congrArg`/`exact`: goals here mention `associatedSheaf` and are not type-correct
under the `instances` transparency level, so `rw` will not match patterns that are syntactically
present. The naturality step additionally needs `DFunLike.congr_fun` rather than `congrFun` — the
components are bundled `LinearMap`s, not functions. -/
theorem tensorUnitRight_inv_tensorHom_app (F N : X.Modules)
    (ψ : (.unit X.ringCatSheaf : X.Modules) ⟶ N) (U : X.Opensᵒᵖ) (t : Γ(F, U.unop)) :
    (((tensorUnitRightIso F).inv ≫ tensorHom (𝟙 F) ψ).val.app U).hom t
      = tmulSection F N U t ((ψ.val.app U).hom (1 : Γ(X, U.unop))) := by
  have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).right_triangle_components F
  have hinv : (((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app F).inv).val
      = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((toPresheafOfModules X).obj F) := by
    have h2 : (((asIso (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit).app F).hom).val ≫
        (((asIso (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).counit).app F).inv).val = 𝟙 _ := by
      rw [← SheafOfModules.comp_val, Iso.hom_inv_id]
      rfl
    refine Eq.symm ((Category.comp_id _).symm.trans ?_)
    refine (congrArg (fun z => (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app ((toPresheafOfModules X).obj F) ≫ z) h2.symm).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ _) htri).trans (Category.id_comp _))
  have hnat := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit).naturality
      ((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
        ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ (toPresheafOfModules X).map ψ))
  rw [tensorUnitRightIso, tensorHom, tmulSection]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  have hfuse : ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app F).inv ≫
      (associatedSheaf X).map (ρ_ ((toPresheafOfModules X).obj F)).inv ≫
        (associatedSheaf X).map ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
          (toPresheafOfModules X).map ψ)
      = ((asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app F).inv ≫
        (associatedSheaf X).map ((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
          ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ (toPresheafOfModules X).map ψ)) := by
    rw [CategoryTheory.Functor.map_comp]
    rfl
  refine (congrArg (fun m => (ModuleCat.Hom.hom
    ((m : F ⟶ tensorObj F N).val.app U)) t) hfuse).trans ?_
  have hsplit : (ModuleCat.Hom.hom
        ((((asIso (PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).counit).app F).inv ≫
            (associatedSheaf X).map ((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
              ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
                (toPresheafOfModules X).map ψ))).val.app U)) t
      = (ModuleCat.Hom.hom (((associatedSheaf X).map
            ((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
              ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
                (toPresheafOfModules X).map ψ))).val.app U))
          ((ModuleCat.Hom.hom ((((asIso (PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).counit).app F).inv).val.app U)) t) := rfl
  refine hsplit.trans ?_
  rw [hinv]
  have hn : (ModuleCat.Hom.hom (((associatedSheaf X).map
        ((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
          ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
            (toPresheafOfModules X).map ψ))).val.app U))
      ((ModuleCat.Hom.hom (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app ((toPresheafOfModules X).obj F)).app U)) t)
      = (ModuleCat.Hom.hom (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app ((toPresheafOfModules X).obj F ⊗
            (toPresheafOfModules X).obj N)).app U))
        ((ModuleCat.Hom.hom (((ρ_ ((toPresheafOfModules X).obj F)).inv ≫
          ((toPresheafOfModules X).map (𝟙 F) ⊗ₘ
            (toPresheafOfModules X).map ψ)).app U)) t) := by
    exact (DFunLike.congr_fun (congrArg (fun m => (ModuleCat.Hom.hom (m.app U))) hnat) t).symm
  exact hn.trans rfl

/-- The symmetry of the sheafified tensor product. -/
noncomputable def tensorCommIso (M N : X.Modules) :
    tensorObj M N ≅ tensorObj N M :=
  (associatedSheaf X).mapIso
    (β_ ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N))

/-- Associativity before iterated sheafification. -/
noncomputable def tensorTripleAssocIso (M N P : X.Modules) :
    (associatedSheaf X).obj
        (((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N) ⊗
          (toPresheafOfModules X).obj P) ≅
      (associatedSheaf X).obj
        ((toPresheafOfModules X).obj M ⊗
          ((toPresheafOfModules X).obj N ⊗ (toPresheafOfModules X).obj P)) :=
  (associatedSheaf X).mapIso
    (α_ ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N)
      ((toPresheafOfModules X).obj P))

/-- The object property of being an invertible sheaf. -/
def isInvertible (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun M => SheafOfModules.IsInvertible.{u, u, u}
    (show SheafOfModules X.ringCatSheaf from M)

/-- The category of invertible sheaves on a scheme. -/
abbrev InvertibleSheaf (X : Scheme.{u}) := (isInvertible X).FullSubcategory

/-- Isomorphism classes of invertible sheaves. -/
def PicardClass (X : Scheme.{u}) := Skeleton (InvertibleSheaf X)

namespace PicardClass

/-- The isomorphism class of an invertible sheaf. -/
noncomputable def mk (M : X.Modules)
    [h : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    PicardClass X :=
  ⟦(⟨M, h⟩ : InvertibleSheaf X)⟧

theorem mk_eq_mk_iff (M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N)] :
    mk M = mk N ↔ Nonempty (M ≅ N) := by
  constructor
  · intro h
    exact ⟨(isInvertible X).ι.mapIso (Quotient.eq.mp h).some⟩
  · rintro ⟨e⟩
    exact Quotient.sound ⟨ObjectProperty.isoMk (isInvertible X) e⟩

/-- The distinguished class of the structure sheaf. -/
noncomputable def one (X : Scheme.{u}) : PicardClass X := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  exact mk (.unit X.ringCatSheaf)

end PicardClass

end

end AlgebraicGeometry.Scheme.Modules
