/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Definitions for coherent sheaves on a scheme

**Layer B, stage 1.** Mathlib already supplies the abelian category `X.Modules` of sheaves
of modules on a scheme `X`, together with `SheafOfModules.IsQuasicoherent` and
`SheafOfModules.IsFinitePresentation`. What is missing is coherence and the category
`Coh X`; this file adds them.

## Definition used

On a **locally noetherian** scheme, Serre's condition (finite type, and every locally
finitely generated subsheaf of every restriction is finitely presented) is equivalent to
finite presentation. Since the target of this development is smooth projective varieties
over a field — always noetherian — `IsCoherent` is *defined* as finite presentation.

That is a genuine restriction of generality, recorded here rather than hidden: on a
non-noetherian scheme this definition is finite presentation, which is strictly stronger
than Serre-coherence. Do not use `Coh` outside the locally noetherian setting without
revisiting this.

## Stage 1 status

`Coh X` is defined here and inherits its category structure. Closure under kernels and cokernels
in `X.Modules` is proved in
`DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Kernels`. Generic finite-presentation
closure under extensions is proved in
`DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Extensions`, and its coherent
specialization is installed by `DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Extensions`.
The module
`DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Basic` installs the abelian instance and
packages the inclusion as an exact functor.

The affine equivalence `Coh (Spec R) ≌ FGModuleCat R` is proved in
`DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Affine.Comparison`.

Downstream developments should import
`DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Basic` for the completed stage-1 API.

## References

* [Stacks, Tag 01BU](https://stacks.math.columbia.edu/tag/01BU) — coherent modules
* [Stacks, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ) — coherent sheaves on
  locally noetherian schemes
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- A sheaf of modules on a scheme is **coherent** when it is of finite presentation.

On a locally noetherian scheme this agrees with Serre's condition; see the module
docstring for the caveat outside that setting. -/
def Modules.IsCoherent (M : X.Modules) : Prop :=
  SheafOfModules.IsFinitePresentation M

/-- Coherence, packaged as an `ObjectProperty` so that `Coh X` can be carved out as a full
subcategory of `X.Modules`. -/
def coherent : ObjectProperty X.Modules := fun M => Modules.IsCoherent X M

theorem coherent_iff (M : X.Modules) :
    coherent X M ↔ Modules.IsCoherent X M := Iff.rfl

end Scheme

/-- The category `Coh X` of coherent sheaves on a scheme `X`, as a full subcategory of
`X.Modules`.

Intended for locally noetherian `X`; the typeclass assumption is not imposed on the
definition itself so that the inclusion functor is available unconditionally. -/
def Coh (X : Scheme.{u}) : Type _ := (Scheme.coherent X).FullSubcategory

namespace Coh

variable (X : Scheme.{u})

instance : Category (Coh X) :=
  inferInstanceAs (Category (Scheme.coherent X).FullSubcategory)

/-- The inclusion `Coh X ⥤ X.Modules`. -/
def ι : Coh X ⥤ X.Modules := (Scheme.coherent X).ι

end Coh

end AlgebraicGeometry
