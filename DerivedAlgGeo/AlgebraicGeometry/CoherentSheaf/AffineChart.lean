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

## What this file does not do

**It produces no generating sections.** `Module.Finite` gives a finite generating *set* of the
module; `SheafOfModules.GeneratingSections` wants a family with `Epi (freeHomEquiv.symm s)` on the
sheaf, and getting from one to the other runs through the tilde comparison and then back across
`opensRangeModulesEquivalence` to `F.over U`. That is the remaining half of `#586` step 2, it is
where `Coh.affineEquivalence` and hence Noetherianity enter, and none of it is claimed here.

## Main results

* `moduleFinite_sections_restrict_of_isCoherent` — the finite-module statement.
-/

universe u

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
