/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.Core
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData

/-!
# Substacks cut out by local object properties, and the core of a stack

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a stack for a Grothendieck topology `J`.

* An object property `P` of `F` is *local* for `J` (`Pseudofunctor.ObjectProperty.IsLocal`) when
  it is preserved by the transition functors and an object whose pullbacks along a covering
  sieve satisfy `P` satisfies `P`. If `P` is moreover closed under isomorphisms, the full
  sub-pseudofunctor `P.fullsubcategory` is a stack. This answers the TODO of Mathlib's
  `Mathlib/CategoryTheory/Bicategory/Functor/Cat/ObjectProperty.lean`.
* The core `F.core`, whose fibres are the maximal groupoids of those of `F`, is a stack: it is a
  stack in groupoids.

## Main definitions

* `Pseudofunctor.DescentData.coreEquivalence f : F.core.DescentData f ≌ Core (F.DescentData f)`:
  descent data of the core are the descent data of `F` and their isomorphisms.
* `Pseudofunctor.ObjectProperty.IsLocal P J`.

## Main results

* `Pseudofunctor.isStack_core`: the core of a stack is a stack.
* `Pseudofunctor.ObjectProperty.isStack_fullsubcategory`: a local object property closed under
  isomorphisms cuts out a substack.

## Implementation notes

Locality is stated on sieves, as Mathlib's `IsStack` is. The gluing maps of a descent datum are
isomorphisms (`Pseudofunctor.DescentData.iso`), so a descent datum of `F` is one of `F.core`;
`coreEquivalence` is compatible with the restriction functors
(`Pseudofunctor.DescentData.toDescentDataCompCoreEquivalenceFunctorIso`), and
`Equivalence.core` transports the equivalence of `F`.

For the substack, a descent datum of `P.fullsubcategory` is mapped along the inclusion `P.ι`
(`Pseudofunctor.DescentData.map`), glued in `F`, and the glued object satisfies `P` by closure
under isomorphisms and locality. Its comparison isomorphism lifts along the fully faithful
functor `DescentData.map _ P.ι`. No equality of objects is used.

## References

* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU), Lemma 8.4.3: a full
  subcategory of a stack satisfying three closure conditions is a stack.
* [Stacks, Tag 03YI](https://stacks.math.columbia.edu/tag/03YI), Lemma 8.5.3: the category
  fibred in groupoids associated to a stack is a stack in groupoids.
* [Stacks, Tag 026F](https://stacks.math.columbia.edu/tag/026F), Definition 8.4.1.

## Tags

stack, substack, descent, core, groupoid, local property
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat
open scoped StrongTrans

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-! ## The core of a stack -/

/-- `pullHom` in the core of `F` is `pullHom` in `F` of the underlying morphism. -/
private lemma core_pullHom_iso_hom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.core.obj (.mk (op X₁))⦄
    ⦃M₂ : F.core.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.core.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.core.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).iso.hom =
      pullHom (F := F) φ.iso.hom g gf₁ gf₂ hgf₁ hgf₂ := by
  simp [pullHom]

namespace DescentData

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Auxiliary definition for `coreEquivalence`: a descent datum of the core is a descent datum
of `F`, and a morphism of descent data of the core is an isomorphism of descent data of `F`. -/
@[simps]
def coreFunctor : F.core.DescentData f ⥤ Core (F.DescentData f) where
  obj D := .mk
    { obj i := (D.obj i).of
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).iso.hom
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← core_pullHom_iso_hom, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self Y q i g hg := by
        rw [D.hom_self q g hg]
        rfl
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        rw [← D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]
        rfl }
  map {D₁ D₂} φ := .mk <| isoMk (fun i => (φ.hom i).iso) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => by
    simpa using congrArg (fun ψ => ψ.iso.hom) (φ.comm q f₁ f₂ hf₁ hf₂))

/-- Auxiliary definition for `coreEquivalence`: a descent datum of `F` is a descent datum of the
core, since its gluing maps are isomorphisms, and an isomorphism of descent data of `F` is a
morphism of descent data of the core. -/
@[simps]
def coreInverse : Core (F.DescentData f) ⥤ F.core.DescentData f where
  obj D :=
    { obj i := .mk (D.of.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := .mk (D.of.iso q f₁ f₂ hf₁ hf₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        apply Core.hom_ext
        rw [core_pullHom_iso_hom]
        exact D.of.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
      hom_self Y q i g hg := by
        apply Core.hom_ext
        exact D.of.hom_self q g hg
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        apply Core.hom_ext
        exact D.of.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃ }
  map {D₁ D₂} ψ :=
    { hom i := .mk
        { hom := ψ.iso.hom.hom i
          inv := ψ.iso.inv.hom i
          hom_inv_id := by rw [← comp_hom, ψ.iso.hom_inv_id, id_hom]
          inv_hom_id := by rw [← comp_hom, ψ.iso.inv_hom_id, id_hom] }
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        apply Core.hom_ext
        simpa using ψ.iso.hom.comm q f₁ f₂ hf₁ hf₂ }

/-- Descent data of the core of `F` are the descent data of `F` and their isomorphisms. -/
@[simps]
def coreEquivalence : F.core.DescentData f ≌ Core (F.DescentData f) where
  functor := coreFunctor f
  inverse := coreInverse f
  unitIso := NatIso.ofComponents (fun D => isoMk (fun i => Iso.refl _) (fun _ _ _ _ _ _ _ _ => by
    apply Core.hom_ext
    simp))
  counitIso := NatIso.ofComponents (fun D => Core.isoMk (isoMk (fun i => Iso.refl _)))

/-- The equivalence `coreEquivalence` is compatible with the restriction functors of `F.core`
and of `F`. -/
@[simps!]
def toDescentDataCompCoreEquivalenceFunctorIso :
    F.core.toDescentData f ⋙ (coreEquivalence f).functor ≅ (F.toDescentData f).core :=
  NatIso.ofComponents (fun M => Core.isoMk (isoMk (fun i => Iso.refl _)))

end DescentData

/-- The core of a stack is a stack: it is a stack in groupoids
([Stacks, Tag 03YI](https://stacks.math.columbia.edu/tag/03YI)).

The hypothesis `F.IsStack J` is needed: the core of the discrete pseudofunctor of a presheaf is
equivalent to it, so the core of the discrete pseudofunctor of a presheaf that is not a sheaf is
not a stack. -/
theorem isStack_core {J : GrothendieckTopology C} [F.IsStack J] : F.core.IsStack J := by
  refine IsStack.of_isStackFor fun S R hR => ?_
  rw [isStackFor_iff]
  let f := fun (a : R.arrows.category) => a.obj.hom
  have := (F.isStackFor' R hR).isEquivalence
  have : (F.toDescentData f).core.IsEquivalence :=
    (F.toDescentData f).asEquivalence.core.isEquivalence_functor
  have := Functor.isEquivalence_of_iso
    (DescentData.toDescentDataCompCoreEquivalenceFunctorIso (F := F) f).symm
  exact Functor.isEquivalence_of_comp_right _ (DescentData.coreEquivalence (F := F) f).functor

/-! ## Local object properties -/

namespace ObjectProperty

/-- An object property `P` of `F` is local for `J` when it is preserved by the transition
functors, and an object whose pullbacks along every arrow of a covering sieve satisfy `P`
satisfies `P`. -/
class IsLocal (P : F.ObjectProperty) (J : GrothendieckTopology C) : Prop
    extends P.IsClosedUnderMapObj where
  /-- An object satisfies `P` when its pullbacks along a covering sieve do. -/
  of_sieve {S : C} (M : F.obj (.mk (op S))) (R : Sieve S) (hR : R ∈ J S)
    (h : ∀ ⦃T : C⦄ (g : T ⟶ S), R g →
      P.prop (.mk (op T)) ((F.map g.op.toLoc).toFunctor.obj M)) :
    P.prop (.mk (op S)) M

/-- Locality for a finer topology gives locality for every coarser topology: a sieve covering
for `J₁` covers for `J₂`. -/
theorem IsLocal.of_le {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) (P : F.ObjectProperty)
    [P.IsLocal J₂] : P.IsLocal J₁ where
  of_sieve M R hR hM := IsLocal.of_sieve (J := J₂) M R (h _ hR) hM

/-- The property satisfied by every object is local. -/
instance isLocal_top {J : GrothendieckTopology C} :
    (⟨fun _ => ⊤⟩ : F.ObjectProperty).IsLocal J where
  map_obj _ _ := trivial
  of_sieve _ _ _ _ := trivial

instance core_isLocal (P : F.ObjectProperty) {J : GrothendieckTopology C} [P.IsLocal J] :
    P.core.IsLocal J where
  of_sieve M R hR hM := IsLocal.of_sieve (J := J) (M : Core (F.obj _)).of R hR hM

variable (P : F.ObjectProperty) {J : GrothendieckTopology C}

/-- A local object property closed under isomorphisms cuts out a substack: if `F` is a stack
for `J`, so is `P.fullsubcategory`. This is
[Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU), whose conditions (1) and (3)
are `IsLocal` with `IsClosedUnderIsomorphisms`, and condition (2) is fullness.

Each hypothesis is needed.
* `F.IsStack J`: for `P = ⊤` the inclusion `P.ι` has equivalences of categories as
  components, so `P.fullsubcategory` is a stack exactly when `F` is
  (`Pseudofunctor.isStack_iff_of_isEquivalence`); take `F` the discrete pseudofunctor of a
  presheaf that is not a sheaf.
* `P.IsLocal J`: on the open sets of the two-point discrete space `{p, q}` with the open-cover
  topology, let `F` be the discrete stack of the sheaf `U ↦ (U → Bool)` and `P` the property of
  being a constant function. `P` is preserved by restriction and closed under isomorphisms but
  not local, and the descent datum `true` on `{p}`, `false` on `{q}` does not glue inside `P`.
* `P.IsClosedUnderIsomorphisms`: let `C` be the walking arrow `f : U ⟶ S` with the topology
  generated by the sieve `⟨f⟩`, and `F` the strict pseudofunctor with `F(S)` the terminal
  category, `F(U)` the indiscrete category on `{a, b}` and `F(f)` picking `a`; `F` is a stack,
  since `F(f)` is an equivalence. Let `P` be empty over `S` and `{b}` over `U`. It is preserved
  by `F.map` and satisfies `IsLocal.of_sieve` vacuously, but the descent datum `b` over `U` has
  no preimage in the empty fibre over `S`.

Stating `IsLocal.of_sieve` and `IsClosedUnderMapObj` up to isomorphism, as conditions (1) and
(3) of Tag 04TU are, would make the last hypothesis unnecessary. -/
theorem isStack_fullsubcategory [F.IsStack J] [P.IsLocal J] [P.IsClosedUnderIsomorphisms] :
    P.fullsubcategory.IsStack J := by
  have (X : LocallyDiscrete Cᵒᵖ) : (P.ι.app X).toFunctor.Full :=
    inferInstanceAs (P.prop X).ι.Full
  have (X : LocallyDiscrete Cᵒᵖ) : (P.ι.app X).toFunctor.Faithful :=
    inferInstanceAs (P.prop X).ι.Faithful
  refine IsStack.of_isStackFor fun S R hR => ?_
  let f := fun (a : R.arrows.category) => a.obj.hom
  let e := toDescentDataCompMapIso f P.ι
  let hmap := Functor.FullyFaithful.ofFullyFaithful (DescentData.map f P.ι)
  have hff : (P.fullsubcategory.toDescentData f).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := DescentData.map f P.ι)
      (((P.prop _).fullyFaithfulι.comp (F.isPrestackFor' R hR).fullyFaithful).ofIso e.symm)
  have := hff.full
  have := hff.faithful
  have : (P.fullsubcategory.toDescentData f).EssSurj := ⟨fun D => by
    have := (F.isStackFor' R hR).essSurj
    let D' := (DescentData.map f P.ι).obj D
    let e' := (F.toDescentData f).objObjPreimageIso D'
    let M := (F.toDescentData f).objPreimage D'
    have hM : P.prop _ M := IsLocal.of_sieve (J := J) M R hR fun T g hg => by
      let i : R.arrows.category := ⟨Over.mk g, hg⟩
      exact (P.prop _).prop_of_iso
        { hom := e'.inv.hom i
          inv := e'.hom.hom i
          hom_inv_id := by rw [← DescentData.comp_hom, e'.inv_hom_id, DescentData.id_hom]
          inv_hom_id := by
            rw [← DescentData.comp_hom, e'.hom_inv_id, DescentData.id_hom]
            rfl }
        (D.obj i).property
    exact ⟨⟨M, hM⟩, ⟨hmap.preimageIso (e.app ⟨M, hM⟩ ≪≫ e')⟩⟩⟩
  rw [isStackFor_iff]
  exact { }

end ObjectProperty

end CategoryTheory.Pseudofunctor
