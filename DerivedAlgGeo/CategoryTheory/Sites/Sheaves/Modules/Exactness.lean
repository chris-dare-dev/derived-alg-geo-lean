/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Adjunction.PreservesColimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The forgetful functor from sheaves of modules to abelian sheaves is exact

`SheafOfModules.toSheaf R : SheafOfModules R ⥤ Sheaf J AddCommGrpCat` is already known
upstream to be `Additive` and to preserve finite limits. This file supplies the other
half — it preserves finite colimits — and the two consequences the cohomology of a
scheme needs: it preserves epimorphisms, and it carries a short exact sequence to a short
exact sequence.

## Why this is needed

`Sheaf.H` is `Ext` from the constant sheaf, so the cohomology long exact sequence of a
short exact sequence of sheaves of modules is `Abelian.Ext.covariantSequence_exact`
applied to the *image* of that sequence in `Sheaf J AddCommGrpCat`. Nothing upstream says
the sequence survives the trip. Half of it does — `PreservesFiniteLimits` gives kernels and
monomorphisms — and the missing half is exactly this file.

## The argument

Both categories are built the same way, and the proof is to notice that the two
constructions agree on the nose. Writing `L` for `PresheafOfModules.sheafification α` and
`G` for its right adjoint, Mathlib gives:

* `L ⋙ SheafOfModules.toSheaf R = PresheafOfModules.toPresheaf R₀ ⋙ presheafToSheaf J _`
  — **definitionally**, not merely up to isomorphism;
* `PresheafOfModules.toPresheaf` preserves finite colimits, and `presheafToSheaf` is a left
  adjoint, so the right-hand side preserves finite colimits;
* the counit of `L ⊣ G` is an isomorphism.

The last point is what makes this enough. A functor out of the reflective target is
determined on colimits by its restriction along `L`: every diagram `d` there is isomorphic
to `(d ⋙ G) ⋙ L`, so a colimit of `d` is the image under `L` of a colimit computed
upstairs, and `L ⋙ toSheaf` preserving that colimit is the same statement as `toSheaf`
preserving this one. That transport is `Adjunction.preservesColimitsOfShape_of_comp_left`,
imported from the generic adjunction root because nothing in it is about sheaves.

## Not done here

Exactness is stated as preservation of finite limits and colimits and unpacked only as far
as `PreservesEpimorphisms` and short exactness. No homology or `Ext` computation happens
here; that is the caller's business.

Nothing here is stated for `AlgebraicGeometry.Scheme.Modules`. That is deliberate — this
file is Mathlib-shaped and `X.Modules` is a `def` wrapping `SheafOfModules X.ringCatSheaf`
with its own `Category` instance, so `Epi f` for `f` in `X.Modules` is not syntactically
the `Epi f` these instances discharge and does not transfer by `haveI`, even though the two
are definitionally equal. Working on `SheafOfModules X.ringCatSheaf` directly avoids it
entirely; bridging the wrapper is separate work.

## References

* [Stacks, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG) — sheafification is exact
-/

universe v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

include α in
/-- `SheafOfModules.toSheaf` preserves finite colimits.

The `α` argument is the comparison map from a presheaf of rings whose sheafification is
`R`; it is data of the *proof*, not of the statement, which is why it is explicit. Take
`α = 𝟙 R.obj` unless there is a reason not to. -/
lemma preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) where
  preservesFiniteColimits K _ _ := by
    haveI : PreservesColimitsOfShape K (PresheafOfModules.sheafification.{v} α ⋙
        toSheaf.{v} R) :=
      inferInstanceAs (PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf.{v} R₀ ⋙ presheafToSheaf J AddCommGrpCat.{v}))
    exact (PresheafOfModules.sheafificationAdjunction.{v} α).preservesColimitsOfShape_of_comp_left
      (toSheaf.{v} R)

/-- `SheafOfModules.toSheaf` preserves finite colimits. Registered at `α = 𝟙 R.obj`, which
is the only case anyone wants; the general statement above is what the proof needs. -/
noncomputable instance preservesFiniteColimits_toSheaf' :
    PreservesFiniteColimits (toSheaf.{v} R) :=
  preservesFiniteColimits_toSheaf (𝟙 R.obj)

/-- `SheafOfModules.toSheaf` preserves epimorphisms: a locally surjective map of sheaves of
modules stays locally surjective when the module structure is forgotten. This is the form
the cohomology long exact sequence consumes. -/
instance preservesEpimorphisms_toSheaf : (toSheaf.{v} R).PreservesEpimorphisms :=
  inferInstance

/-- A short exact sequence of sheaves of modules is short exact as a sequence of abelian
sheaves. Left exactness is upstream (`PreservesFiniteLimits`); the content is that the
epimorphism survives. -/
lemma shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{v} R)}
    (hS : S.ShortExact) : (S.map (toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact (toSheaf.{v} R)

end SheafOfModules

namespace SheafOfModules

section ReflectEpi

universe w

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}

/-- **A map of sheaves of modules that is locally surjective is an epimorphism.**

`preservesEpimorphisms_toSheaf` above goes the other way, and only that direction was
available: it turns an epimorphism of module sheaves into one of abelian sheaves. What a
locality argument produces is the opposite — local surjectivity, hence an epimorphism of
abelian sheaves — and to land back in `SheafOfModules` the functor must **reflect**
epimorphisms.

It does, and for a more elementary reason than preservation of cokernels: `toSheaf` is
faithful, and `reflectsEpimorphisms_of_faithful` makes every faithful functor reflect
epimorphisms. No exactness is involved. Both instances fire on their own; this lemma
exists to assemble the chain rather than to supply a missing step, and to record that the
chain is complete.

## The intended use

Combined with `isLocallySurjective_of_coversTop`
(`AlgebraicGeometry/Modules/Tensor/Basic.lean`), which builds
the hypothesis from local surjectivity on a `CoversTop` family, this is the step that
checks a map of module sheaves is an epimorphism chart by chart — Serre's surjection
`⊕ O(-d) ↠ F` being the case in view. The two are not combined into one statement here
because that would make this file depend on `Divisors/`, which is a different subject. -/
theorem epi_of_isLocallySurjective
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M N : SheafOfModules.{w} R} (f : M ⟶ N)
    (h : Presheaf.IsLocallySurjective J ((toSheaf R).map f).hom) : Epi f :=
  (toSheaf R).epi_of_epi_map
    ((Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{w}) _).mp h)

/-- `toSheaf` reflects epimorphisms, recorded as an instance so the chain above is
available to instance search as well as to explicit application. -/
instance reflectsEpimorphisms_toSheaf : (toSheaf.{w} R).ReflectsEpimorphisms :=
  inferInstance

end ReflectEpi

end SheafOfModules
