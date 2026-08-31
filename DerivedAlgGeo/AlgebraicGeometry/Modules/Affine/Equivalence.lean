/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Exactness
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Crossing the `Scheme.Modules` wrapper

`AlgebraicGeometry.Scheme.Modules X` is a `def` for `SheafOfModules X.ringCatSheaf`, and
`Scheme.Modules.Hom` is a `def` for `SheafOfModules.Hom`. The `Category X.Modules` instance
therefore differs from `Category (SheafOfModules X.ringCatSheaf)` in its `Hom` field alone,
and the two are definitionally equal.

Instance search does not care. It unifies syntactically, so a class whose arguments include
the category instance — `Epi`, `Mono`, `Functor.PreservesZeroMorphisms`,
`PreservesFiniteLimits` — is a *different goal* on the two sides, and every result proved
about `SheafOfModules X.ringCatSheaf` is unreachable from `X.Modules` until it is
transported by hand. `haveI` does not help: the defeq is accepted when it is *checked*, but
search never gets far enough to check it.

## What this file does, and what it deliberately does not

The obvious fix is an equivalence `X.Modules ≌ SheafOfModules X.ringCatSheaf` — identity on
objects and morphisms — with transport lemmas hung off it. **That does not solve the
problem.** An equivalence `e` gives statements about `e.functor.obj M` and `e.functor.map f`,
which are again not syntactically the goals that come up; the caller still has to rewrite by
hand at every use, and has gained a functor to carry around for the privilege.

What actually closes the goals is two much smaller things:

1. **Transfer instances for `Epi` and `Mono`**, whose statements are the goals verbatim. An
   epimorphism in `X.Modules` is an epimorphism in `SheafOfModules X.ringCatSheaf` and the
   proof is `cancel_epi`, because composition agrees on the nose.
2. **A copy of `SheafOfModules.toSheaf` typed with domain `X.Modules`**, `Scheme.Modules.toSheaf`,
   carrying its own instances. This is the one that scales: downstream code writes
   `Scheme.Modules.toSheaf X` and never crosses the wrapper at all, so no further transfer is
   ever needed for it. Mathlib already sets the precedent with `Scheme.Modules.toPresheaf`.

Making `Scheme.Modules` and `Scheme.Modules.Hom` `@[reducible]` upstream would remove the
problem at the root and is the honest fix, but it is a Mathlib change with its own
performance question — `reducible` defs are unfolded during every instance search — and it is
not this library's to make.

## Not done here

No claim that the two categories are *equal*, and no equivalence. The transfers here cover
`Epi`, `Mono` and the functor to abelian sheaves, which is what the cohomology work needs. A
class not listed here has not been checked and will need its own line; that is a consequence
of the wrapper, not of this file.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Transfer of `Epi` and `Mono` across the wrapper

Composition in `X.Modules` is composition in `SheafOfModules X.ringCatSheaf`, so the
cancellation properties transport with no content. These are stated in the direction that
comes up: a hypothesis lives on the `X.Modules` side, a lemma about sheaves of modules wants
it on the other. -/

/-- An epimorphism of `𝒪ₓ`-modules is an epimorphism of sheaves of modules. -/
instance epi_sheafOfModules {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi (C := SheafOfModules.{u} X.ringCatSheaf) f :=
  ⟨fun _ _ H => (cancel_epi f).mp H⟩

/-- A monomorphism of `𝒪ₓ`-modules is a monomorphism of sheaves of modules. -/
instance mono_sheafOfModules {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Mono (C := SheafOfModules.{u} X.ringCatSheaf) f :=
  ⟨fun _ _ H => (cancel_mono f).mp H⟩

/-! ### The forgetful functor to abelian sheaves, typed at `X.Modules`

Everything below is `SheafOfModules.toSheaf X.ringCatSheaf` with its domain written as
`X.Modules`. The definitions are the same term; only the elaborated category instance
differs, which is exactly what search needs. -/

variable (X) in
/-- The forgetful functor from `𝒪ₓ`-modules to abelian sheaves on the Zariski site of `X`.

This is `SheafOfModules.toSheaf X.ringCatSheaf` retyped. Prefer it over the latter in
anything stated about `X.Modules`: it keeps the wrapper uncrossed, so the instances below
apply without transport. -/
noncomputable def toSheaf :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance additive_toSheaf : (toSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

noncomputable instance preservesFiniteLimits_toSheaf :
    PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

noncomputable instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))

instance preservesEpimorphisms_toSheaf : (toSheaf X).PreservesEpimorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesEpimorphisms

/-- The wrapper-typed forgetful functor reflects epimorphisms. -/
instance reflectsEpimorphisms_toSheaf : (toSheaf X).ReflectsEpimorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsEpimorphisms

/-- A short exact sequence of `𝒪ₓ`-modules is short exact as a sequence of abelian sheaves.

This is the `X.Modules`-level form of `SheafOfModules.shortExact_map_toSheaf`, and the shape
the cohomology long exact sequence consumes. -/
lemma shortExact_map_toSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toSheaf X)).ShortExact :=
  hS.map_of_exact (toSheaf X)

/-! ### The acceptance test

Issue #59 asked for exactly this goal to close by instance search. It does, through
`epi_sheafOfModules` — recorded here so a regression is a build failure rather than a
rediscovery. -/

example {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) := by infer_instance

end AlgebraicGeometry.Scheme.Modules
