/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Isomorphism
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Zero
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Quot.Basic

/-!
# The functor of flat, finitely presented quotients

For a morphism of schemes `p : X ⟶ S` and a module sheaf `F` on `X`, `quotFunctor p F` sends a
scheme `T` over `S` to the set of quotients `F_T ↠ Q` on `X_T = X ×_S T`, where `F_T` is the
pullback of `F` and `Q` is of finite presentation and flat over `T`. Two quotients are the same
point when they are isomorphic under `F_T`. A morphism `T' ⟶ T` over `S` acts by pullback along
`X_{T'} ⟶ X_T`.

## Main definitions

* `AlgebraicGeometry.quotBaseChange` — the pullback `F_T` of `F` to `X ×_S T`.
* `AlgebraicGeometry.quotFunctor.baseChangeHom`, `AlgebraicGeometry.quotFunctor.baseChangeIso` —
  the morphism `X ×_S T' ⟶ X ×_S T` induced by `T' ⟶ T`, and `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T`.
* `AlgebraicGeometry.ModuleQuotient.IsFlatFinitePresentation` — a quotient whose target is of
  finite presentation and flat over a given base.
* `AlgebraicGeometry.quotFunctor` — the functor `(Over S)ᵒᵖ ⥤ Type u` of isomorphism classes of
  such quotients.
* `AlgebraicGeometry.quotFunctor.zeroPoint` — the zero quotient `F_T ↠ 0`, a point over every `T`.

## Main results

* `AlgebraicGeometry.ModuleQuotient.small_isIsomorphicSetoid` — isomorphism classes of quotients
  of one module sheaf form a `u`-small type, so the values of `quotFunctor` live in `Type u`.

## Implementation notes

The points over `T` are `Shrink.{u}` of the isomorphism classes, in Mathlib's
`isIsomorphicSetoid`, of the full subcategory of admissible quotients. Isomorphism classes of
quotients of `G` inject into the subobjects of `op G`. These are small: `X.Modules` is
Grothendieck abelian, hence well-powered, and an abelian well-powered category is co-well-powered
(`Abelian.wellPowered_opposite`).

Base change along `g : T' ⟶ T` pulls a quotient back along `X_{T'} ⟶ X_T` and reads it on
`F_{T'}` through the comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^* F_T` built from `pullbackComp` and
`pullbackCongr`. Flatness survives because `X_{T'}` is a pullback of `X_T ⟶ T` along `g`
(`IsFlatOver.of_isPullback`); finite presentation survives every pullback
(`isFinitePresentation_pullback`). The functor laws are Mathlib's pseudofunctor coherences for
pullback of module sheaves, `pseudofunctor_right_unitality` and
`pseudofunctor_associativity`.

The admissibility predicate is stated for any morphism `q : Y ⟶ T` and any module sheaf on `Y`;
the functor uses it for `X_T ⟶ T` and `F_T`.

## References

* [Stacks, Tag 082M](https://stacks.math.columbia.edu/tag/082M): Situation 99.7.1 defines the
  functor of quotients and, in Equation 0CZL, its subfunctor `Q^fp` of finitely presented
  quotients.
* [Stacks, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR): Situation 99.8.1 defines the
  Quot functor, whose quotients also have support proper over `T`.
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, §1, which
  identifies two quotients when they are isomorphic under the source and remarks that this is the
  condition `ker(q) = ker(q')`.

## Tags

Quot functor, quotient, flat, finite presentation, base change, moduli
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry

noncomputable section

section Admissible

variable {Y T : Scheme.{u}}

/-- A quotient presentation of a module sheaf on `Y` is admissible over `q : Y ⟶ T` when its
target is of finite presentation and flat over `T`. -/
def ModuleQuotient.IsFlatFinitePresentation (q : Y ⟶ T) {G : Y.Modules} :
    ObjectProperty (ModuleQuotient G) := fun r ↦
  SheafOfModules.IsFinitePresentation r.target ∧ Scheme.Modules.IsFlatOver q r.target

instance (q : Y ⟶ T) {G : Y.Modules} :
    (ModuleQuotient.IsFlatFinitePresentation q (G := G)).IsClosedUnderIsomorphisms where
  of_iso e h :=
    ⟨SheafOfModules.IsFinitePresentation.of_iso.{u}
      ((ModuleQuotient.targetFunctor G).mapIso e) h.1,
      h.2.of_iso ((ModuleQuotient.targetFunctor G).mapIso e)⟩

end Admissible



section BaseChange

open Scheme.Modules

variable {Y Y' Y'' : Scheme.{u}} {G : Y.Modules} {G' : Y'.Modules} {G'' : Y''.Modules}

/-- Pullback preserves admissible quotients along a pullback square. -/
private lemma isFlatFinitePresentation_pullbackVia {T T' : Scheme.{u}} {q : Y ⟶ T}
    {snd : Y' ⟶ T'} {h : T' ⟶ T} {b : Y' ⟶ Y} (H : IsPullback b snd q h)
    (e : G' ≅ (Scheme.Modules.pullback b).obj G) {r : ModuleQuotient G}
    (hr : ModuleQuotient.IsFlatFinitePresentation q r) :
    ModuleQuotient.IsFlatFinitePresentation snd (ModuleQuotient.pullbackVia b e r) :=
  ⟨isFinitePresentation_pullback b r.target hr.1, hr.2.of_isPullback H⟩

end BaseChange

variable {X S : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)

open Scheme.Modules quotFunctor

/-- The full subcategory of admissible quotients of `F_T`. -/
private abbrev Adm (T : Over S) :=
  (ModuleQuotient.IsFlatFinitePresentation (pullback.snd p T.hom)
    (G := quotBaseChange p F T)).FullSubcategory

/-- Base change of one admissible quotient along `g : T' ⟶ T`. -/
private def baseChangeObj {T' T : Over S} (g : T' ⟶ T) (r : Adm p F T) : Adm p F T' :=
  ⟨ModuleQuotient.pullbackVia (baseChangeHom p g) (baseChangeIso p F g) r.obj,
    isFlatFinitePresentation_pullbackVia (isPullback_baseChangeHom p g) _ r.property⟩

/-- Base change on isomorphism classes of admissible quotients. -/
private def baseChangeClass {T' T : Over S} (g : T' ⟶ T) :
    Quotient (isIsomorphicSetoid (Adm p F T)) → Quotient (isIsomorphicSetoid (Adm p F T')) :=
  Quotient.map (baseChangeObj p F g) fun _ _ ⟨i⟩ ↦
    ⟨ObjectProperty.isoMk _ (ModuleQuotient.pullbackViaIso _ _ ((ObjectProperty.ι _).mapIso i))⟩

private lemma baseChangeClass_id (T : Over S) (x : Quotient (isIsomorphicSetoid (Adm p F T))) :
    baseChangeClass p F (𝟙 T) x = x := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound
    ⟨ObjectProperty.isoMk _ (ModuleQuotient.pullbackViaId (baseChangeHom_id p T) _ ?_ r.obj)⟩
  have h := pullbackCongr_comp_pullbackId (pullback.fst p T.hom) (baseChangeHom_id p T)
    (baseChangeHom_fst p (𝟙 T)) F
  rw [baseChangeIso_hom, Category.assoc, h]
  simp [Scheme.Modules.pullbackCongr]

private lemma baseChangeClass_comp {T'' T' T : Over S} (k : T'' ⟶ T') (g : T' ⟶ T)
    (x : Quotient (isIsomorphicSetoid (Adm p F T))) :
    baseChangeClass p F (k ≫ g) x = baseChangeClass p F k (baseChangeClass p F g x) := by
  induction x using Quotient.inductionOn with | h r => ?_
  refine Quotient.sound ⟨ObjectProperty.isoMk _
    (ModuleQuotient.pullbackViaComp _ _ (baseChangeHom_comp p k g) _ _ _ ?_ r.obj).symm⟩
  rw [baseChangeIso_hom, baseChangeIso_hom, baseChangeIso_hom]
  exact pullbackCongr_comp_assoc _ _ (baseChangeHom_comp p k g) (pullback.fst p T.hom)
    (baseChangeHom_fst p g) (baseChangeHom_fst p k) (baseChangeHom_fst p (k ≫ g)) F

/-- **The functor of flat, finitely presented quotients.** For `p : X ⟶ S` and a module sheaf
`F` on `X`, it sends `T` over `S` to the isomorphism classes of quotients `F_T ↠ Q` on
`X_T = X ×_S T` with `Q` of finite presentation and flat over `T`; a morphism `T' ⟶ T` acts by
pullback along `X_{T'} ⟶ X_T`.

This is Stacks' `Q^fp_{F/X/S}` (Situation 082M, Equation 0CZL), with schemes in place of
algebraic spaces and no quasi-coherence assumed of `F`. Stacks identifies two quotients with the
same kernel; in an abelian category an epimorphism is the cokernel of its kernel, so this is
isomorphism under `F_T`, the relation used here and by Nitsure (§1).

When `p` is of finite presentation and proper this is Grothendieck's Quot functor
`Quot_{F/X/S}` (Situation 09TR), whose quotients must also have support proper over `T`: a module
of finite type has closed support, and a closed subscheme of `X_T` is proper over `T`. Without
properness the two differ. For `p : 𝔸¹_k ⟶ Spec k` and `F = 𝒪`, let `Z = V(tx - 1)` in
`𝔸¹ × Spec k[t]`. Then `𝒪_Z` is finitely presented as an `𝒪`-module, with one generator and one
relation, and `𝒪_Z ≅ k[t, t⁻¹]` is flat over `k[t]`, so `𝒪 ↠ 𝒪_Z` is a point over `Spec k[t]`.
Its support `Z` maps onto `D(t)`, which is not closed, so `Z` is not proper over `Spec k[t]`. -/
@[stacks 0CZL]
def quotFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (Quotient (isIsomorphicSetoid
    (ModuleQuotient.IsFlatFinitePresentation (pullback.snd p T.unop.hom)
      (G := quotBaseChange p F T.unop)).FullSubcategory))
  map g := TypeCat.ofHom fun x ↦
    equivShrink _ (baseChangeClass p F g.unop ((equivShrink _).symm x))
  map_id T := by
    ext x
    simp [baseChangeClass_id]
  map_comp f g := by
    ext x
    simp [baseChangeClass_comp]

/-- The zero quotient `F_T ↠ 0` is a point of `quotFunctor p F` over every `T`. -/
def quotFunctor.zeroPoint (T : Over S) : (quotFunctor p F).obj (op T) :=
  equivShrink _ (Quotient.mk _ ⟨ModuleQuotient.toZero _,
    (Scheme.coherent (Limits.pullback p T.hom)).prop_of_isZero (isZero_zero _),
    Scheme.Modules.IsFlatOver.of_isZero (isZero_zero _)⟩)

end

end AlgebraicGeometry
