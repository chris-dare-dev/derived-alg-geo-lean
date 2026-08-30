/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Relative
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackCoherence
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.LeftDerivedPullback

/-!
# Pullback of universally-gluable relative-perfect complexes

This file records the first object-level base-change layer for the
relative-perfect moduli problem. A `RelativePerfectPullback` is not a
proposition asserting preservation: it contains an actual left-derived
pullback, the actual functor between the full categories of universally
gluable relative-perfect complexes, and a natural isomorphism identifying
the underlying functors.

The identity and composite constructions make these witnesses reusable in a
future pseudofunctor on the big Zariski site. The arbitrary pullback field has
Mathlib's left-derived universal property, so a K-flat construction can
inhabit it without changing this API. This file does not yet construct those
K-flat resolutions or prove preservation along every scheme morphism.

## Main definitions

- `RelativePerfectPullback`: an actual lift of left-derived pullback to the
  universally-gluable relative-perfect loci.
- `RelativePerfectPullback.identity`: the canonical identity lift.
- `RelativePerfectPullback.comp`: composition relative to an actual ambient
  compositor.
- `RelativePerfectPullback.compExact`: the canonical exact composite.
- `RelativePerfectPullback.congr`: transport along equality of base-change
  morphisms.

## Implementation notes

The ambient left-derived pullback is stored with the lift. The comparison is
oriented from the lifted functor to ambient derived pullback so composition
follows the contravariant order of scheme pullback.
-/

namespace AlgebraicGeometry

open CategoryTheory
open CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

noncomputable section

universe u

/-- Forget a universally-gluable relative-perfect object to the ambient
scheme-derived category. -/
def relativePerfectForget {S : Scheme.{u}} (T : SchemeBaseChange S) :
    SchemeUniversallyGluableCategory T.hom ⥤ T.DerivedFiber :=
  ObjectProperty.ι _ ⋙ SchemeQuasicoherentDerivedCategory.ι T.left

/-- An actual lift of left-derived pullback to universally-gluable
relative-perfect complexes.

The functor is the preservation theorem: its codomain ensures that every
pulled-back object remains pseudo-coherent, of finite Tor amplitude, and
universally gluable. `comparison` prevents an unrelated functor from being
presented as geometric pullback. -/
structure RelativePerfectPullback {S : Scheme.{u}}
    {T U : SchemeBaseChange S} (f : T ⟶ U) where
  /-- The actual ambient left-derived pullback and its universal property. -/
  ambient : SchemeBaseChange.LeftDerivedPullback f
  /-- Pullback on the actual universally-gluable relative-perfect loci. -/
  functor : SchemeUniversallyGluableCategory U.hom ⥤
    SchemeUniversallyGluableCategory T.hom
  /-- Forgetting the lifted functor agrees naturally with ambient derived
  pullback. -/
  comparison :
    functor ⋙ relativePerfectForget T ≅
      relativePerfectForget U ⋙ ambient.functor

namespace RelativePerfectPullback

variable {S : Scheme.{u}} {T U V : SchemeBaseChange S}

/-- The identity base change has the canonical relative-perfect pullback.
The underlying functor is the identity on the full relative-perfect locus;
the comparison uses the proved unit isomorphism for derived pullback. -/
def identity (T : SchemeBaseChange S) :
    RelativePerfectPullback (𝟙 T) where
  ambient := SchemeBaseChange.LeftDerivedPullback.identity T
  functor := 𝟭 _
  comparison :=
    Functor.leftUnitor (relativePerfectForget T) ≪≫
      (Functor.rightUnitor (relativePerfectForget T)).symm ≪≫
        Functor.isoWhiskerLeft (relativePerfectForget T)
          (SchemeBaseChange.derivedPullbackId T).symm

/-- Compose relative-perfect pullbacks in the contravariant order dictated
by scheme pullback. For `f : T ⟶ U` and `g : U ⟶ V`, objects over `V` are
first pulled back along `g` and then along `f`. -/
def comp {f : T ⟶ U} {g : U ⟶ V}
    (hf : RelativePerfectPullback f)
    (hg : RelativePerfectPullback g)
    (hfg : SchemeBaseChange.LeftDerivedPullback (f ≫ g))
    (ambientComp : hg.ambient.functor ⋙ hf.ambient.functor ≅ hfg.functor) :
    RelativePerfectPullback (f ≫ g) where
  ambient := hfg
  functor := hg.functor ⋙ hf.functor
  comparison :=
    Functor.associator hg.functor hf.functor
        (relativePerfectForget T) ≪≫
      Functor.isoWhiskerLeft hg.functor hf.comparison ≪≫
      (Functor.associator hg.functor (relativePerfectForget U)
        hf.ambient.functor).symm ≪≫
      Functor.isoWhiskerRight hg.comparison hf.ambient.functor ≪≫
      Functor.associator (relativePerfectForget V) hg.ambient.functor
        hf.ambient.functor ≪≫
      Functor.isoWhiskerLeft (relativePerfectForget V) ambientComp

/-- Compose two relative-perfect pullbacks when both ordinary pullbacks are
exact. Uniqueness of left-derived functors compares their stored ambient
functors with the repository's exact derived pullbacks. -/
def compExact {f : T ⟶ U} {g : U ⟶ V}
    [SchemeBaseChange.IsExactPullback f]
    [SchemeBaseChange.IsExactPullback g]
    (hf : RelativePerfectPullback f)
    (hg : RelativePerfectPullback g) :
    RelativePerfectPullback (f ≫ g) :=
  comp hf hg (SchemeBaseChange.LeftDerivedPullback.ofExact (f ≫ g))
    (Functor.isoWhiskerRight hg.ambient.exactComparison hf.ambient.functor ≪≫
      Functor.isoWhiskerLeft (SchemeBaseChange.derivedPullback g)
        hf.ambient.exactComparison ≪≫
      SchemeBaseChange.derivedPullbackComp f g)

/-- Transport a relative-perfect pullback lift along equality of the
underlying scheme base-change morphisms. -/
def congr {f g : T ⟶ U} (P : RelativePerfectPullback f) (h : f = g) :
    RelativePerfectPullback g := by
  subst g
  exact P

end RelativePerfectPullback

end

end AlgebraicGeometry
