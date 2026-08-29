/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Descent.Locality
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Finiteness

/-!
# Sections of a coherent sheaf over an affine open

Step 2 of `#586` — Serre's global generation — needs, for each chart of a finite affine cover,
*finitely many* sections of a coherent `F` generating it there. This file supplies the module-level
half: over an affine open, the sections of a coherent sheaf form a finite module over the chart's
coordinate ring.

## No Noetherian hypothesis, and that is the point

The natural guess is that this needs the chart's ring to be Noetherian, and it does not.
`moduleFinite_globalSections` concludes `Module.Finite R Γ(M)` from finite presentation alone —
the affine comparison does all the work and there is nothing left for a chain condition to do.
An `[IsLocallyNoetherian X]` hypothesis here is dead weight, which is how the `unusedArguments`
linter found it in the first version of this file.

Noetherianity is still on the road to `#586`, but it enters strictly later and for a different
reason: `Coh.affineEquivalence` requires `[IsNoetherianRing R]` because it identifies the
*category* `Coh (Spec R)` with `FGModuleCat R`, and that needs coherence to be preserved under
kernels. Finite generation of one module's sections needs none of it. Keeping the two apart is
worth the sentence, because `Pⁿ` satisfies both and a reader who sees them arrive together will
assume the wrong dependency.

## The two inputs, neither of them new

* **Coherence restricts along an open immersion.**
  `Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion` carries coherence along `hU.fromSpec`,
  which is an open immersion because `U` is affine. This is a **theorem, not an instance**, so
  `infer_instance` will not find the finite presentation of the restricted sheaf and every caller
  must pass coherence explicitly. That is the one non-obvious step in the file.
* **Finite presentation gives finite sections.** `moduleFinite_globalSections` is the affine
  comparison's finiteness consequence, stated for `Spec R` — which is why the restriction has to
  happen first.

## Why the statement is about `F.restrict hU.fromSpec`

`Γ(F, U)` and the sections of the restricted sheaf on the affine model are the same module, but
only the latter is what `moduleFinite_globalSections` is stated about, and restating it against
`Γ(F, U)` means transporting along `Scheme.Modules.restrictAppIso`. That transport is genuine work
and it belongs with the `GeneratingSections` half, so this file says what it can prove directly
and no more.

## The reduction: generating sections ARE an epi from a free sheaf

`GeneratingSections.ofFreeEpi` records that `SheafOfModules.GeneratingSections` carries no
information beyond an epimorphism `free I ⟶ M`: the structure's `s` field is `freeHomEquiv p` and
its `epi` field is the hypothesis. Mathlib has the other three directions — `ofEpi` along a map out
of `M`, `equivOfIso`, `map` along a functor — but not this one, and without it every attempt at
`#586` step 2 has to open the structure by hand.

It is stated at full site generality rather than for `X.Modules`, because nothing in it is about
schemes.

What it buys is a sharper remaining goal. Step 2 is no longer "produce generating sections",
which invites building the structure field by field; it is exactly

> an epimorphism `free I ⟶ F.over U` with `I` finite,

and `ofFreeEpi` closes the gap the moment one exists.

## What this file does not do

**It produces no such epimorphism.** `Module.Finite` gives a finite generating *set* of the module
of sections, and turning a spanning set into an epi of *sheaves* is the real content: on `Spec R`
it means checking surjectivity on each basic open, where quasi-coherence identifies the sections
with a localization and a spanning set stays spanning. `epi_of_isLocallySurjective`
(`Modules/Affine/Exactness.lean`) and `isLocallySurjective_of_coversTop`
(`Modules/Tensor/Basic.lean`)
are the two ends of that chain and both are in the tree; what is missing is the middle, and
Mathlib has no "locally surjective from surjectivity on a basis" lemma to shorten it. This is
also where `Coh.affineEquivalence`, and hence Noetherianity, would enter.

## Main results

* `moduleFinite_sections_restrict_of_isCoherent` — the finite-module statement.
* `SheafOfModules.GeneratingSections.ofFreeEpi` — the reduction above.
-/

universe u u₁ v₁

open CategoryTheory AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Sections of a coherent sheaf over an affine open form a finite module.**

`U` affine is what makes `hU.fromSpec` an open immersion, so that coherence restricts along it,
and it is what puts the conclusion on `Spec Γ(X, U)` where the affine comparison applies. No
Noetherian hypothesis is needed — see the module docstring, where the reason is recorded along
with where Noetherianity does enter.

Coherence is an explicit argument rather than an instance because
`Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion` is a theorem; nothing in the tree makes
the restricted sheaf's finite presentation available to instance search. -/
theorem moduleFinite_sections_restrict_of_isCoherent
    (F : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (hF : Scheme.Modules.IsCoherent X F) :
    Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec)) :=
  moduleFinite_globalSections _
    (Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion hU.fromSpec F hF)

end AlgebraicGeometry

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An epimorphism from a free sheaf of modules is a family of generating sections.**

The converse of `GeneratingSections.π`, and the direction Mathlib does not have. Nothing is
proved: `s` is `freeHomEquiv p` and the `epi` field is the hypothesis, transported across the
equivalence. Its value is that it lets a caller work with a map rather than with the structure. -/
noncomputable def GeneratingSections.ofFreeEpi (M : SheafOfModules.{u} R) {I : Type u}
    (p : free I ⟶ M) [Epi p] : M.GeneratingSections where
  I := I
  s := M.freeHomEquiv p
  epi := by simpa using (inferInstance : Epi p)

/-- Finiteness of the index type is finiteness of the generating family. -/
instance GeneratingSections.isFiniteType_ofFreeEpi (M : SheafOfModules.{u} R) {I : Type u}
    [Finite I] (p : free I ⟶ M) [Epi p] :
    (GeneratingSections.ofFreeEpi M p).IsFiniteType where
  finite := inferInstanceAs (Finite I)

/-- `ofFreeEpi` is a section of `π`: the epimorphism is recovered unchanged. -/
@[simp]
lemma GeneratingSections.ofFreeEpi_π (M : SheafOfModules.{u} R) {I : Type u}
    (p : free I ⟶ M) [Epi p] : (GeneratingSections.ofFreeEpi M p).π = p :=
  M.freeHomEquiv.symm_apply_apply p

end SheafOfModules
