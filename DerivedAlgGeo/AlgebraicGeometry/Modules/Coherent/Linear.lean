/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Module sheaves on a variety are `k`-linear

On a variety over `k`, multiplication by a global function is an endomorphism of
every module sheaf, and it commutes with every morphism. Composing that with the
ring map `k → Γ(X, O_X)` supplied by the structure morphism makes every
`Hom`-group a `k`-module, compatibly with composition — that is, it makes
`X.Modules` a `k`-linear category, and `Coh X` with it.

Every ingredient was already here. `Cohomology.globalSectionSmul`,
`globalSectionAction`, `baseFieldToGlobalSections`, `varietyScalarAction` and
`varietyScalarAction_naturality` were built to give coherent cohomology its
`k`-structure; this file observes that the same action makes the *category*
linear, which is a strictly stronger statement and one nothing had recorded.

## Why this is worth its own file

Because of what it unlocks rather than what it says. Mathlib's
`DerivedCategory.Linear` gives `Linear R (DerivedCategory C)` from
`Linear R C`, and `Linear.fullSubcategory` propagates to
`DerivedCategory.Bounded C`, which is a `FullSubcategory` of it. So the single
instance below is the whole distance between "`Hom` in `Dᵇ(Coh X)` is an abelian
group" and "`Hom` in `Dᵇ(Coh X)` is a `k`-vector space".

That was the one obstruction to *stating* what a spherical object is:
`Hom(E, E⟦i⟧) ≅ k` is not expressible against an `AddCommGrp`, and
`Numerical/GrothendieckGroup/MukaiVector.lean`'s docstring names exactly this
gap when it says sphericity of an object needs an `Ext` that layer does not
have.

## What this does not give

Finite-dimensionality. `Linear k` says the `Hom`-groups are `k`-modules, not
that they are finite-dimensional, and nothing here bounds them.
`FiniteDimensionalCohomology` remains supplied data, and the projective case is
issue #332. A `Hom`-group being a `k`-vector space of unknown dimension is
exactly enough to *state* sphericity and not enough to prove anything about it.

Nor does it give a trace, a Serre functor, or any duality. Those need the
finiteness this file does not supply.

## Main results

* `Variety.modulesLinear` — `X.Modules` is `k`-linear.
* `Variety.cohLinear` — `Coh X` is `k`-linear, inherited as a full subcategory.
* `Variety.smul_eq_action_comp` — the scalar action unfolds to precomposition
  with multiplication by the corresponding global function, which is the only
  fact a caller needs in order to compute with it.
* `Variety.derivedLinear` — `Dᵇ(Coh X)` is `k`-linear, so `Hom(E, F⟦i⟧)` is a
  `k`-vector space.
-/

universe u

open CategoryTheory AlgebraicGeometry.Cohomology

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

namespace Scheme

variable (X : AlgebraicGeometry.Scheme.{u})

/-- **Morphisms of module sheaves are a module over the global functions.**

The scalar is a global section of the structure sheaf, not an element of a base
field: `globalSectionAction M : Γ(X, ⊤) →+* End M` is already a ring
homomorphism, and every clause below uses only that plus `Preadditive`. Nothing
here is specific to a variety, and no field appears.

`Variety.homModule` is this composed with `k → Γ(X, ⊤)`; it predates this and is
left as it is. -/
@[reducible]
noncomputable def homModuleGlobal (M N : X.Modules) :
    Module Γ(X, (⊤ : X.Opens)) (M ⟶ N) where
  smul r f := globalSectionAction M r ≫ f
  one_smul f := by
    show globalSectionAction M 1 ≫ f = f
    rw [map_one]
    exact Category.id_comp f
  mul_smul r s f := by
    show globalSectionAction M (r * s) ≫ f
      = globalSectionAction M r ≫ globalSectionAction M s ≫ f
    rw [mul_comm, map_mul, End.mul_def, Category.assoc]
  smul_zero r := by
    show globalSectionAction M r ≫ (0 : M ⟶ N) = 0
    exact Limits.comp_zero
  smul_add r f g := by
    show globalSectionAction M r ≫ (f + g)
      = globalSectionAction M r ≫ f + globalSectionAction M r ≫ g
    exact Preadditive.comp_add _ _ _ _ _ _
  add_smul r s f := by
    show globalSectionAction M (r + s) ≫ f
      = globalSectionAction M r ≫ f + globalSectionAction M s ≫ f
    rw [map_add]
    exact Preadditive.add_comp _ _ _ _ _ _
  zero_smul f := by
    show globalSectionAction M 0 ≫ f = 0
    rw [map_zero]
    exact Limits.zero_comp

/-- **Module sheaves on any scheme form a `Γ(X, ⊤)`-linear category.**

`comp_smul` is the clause with content, and it is `globalSectionSmul_naturality`:
multiplication by a global function is central on morphisms.

This is what lets a *section-valued* scalar be moved across a morphism. The
`Linear k` instance next door only ever moves elements of the base field, which
is not enough when the scalar is a function like `fⁿ/gⁿ` on a chart. -/
noncomputable instance modulesLinearGlobal :
    Linear Γ(X, (⊤ : X.Opens)) X.Modules where
  homModule M N := homModuleGlobal X M N
  smul_comp M N P r f g := by
    show (globalSectionAction M r ≫ f) ≫ g = globalSectionAction M r ≫ f ≫ g
    exact Category.assoc _ _ _
  comp_smul M N P f r g := by
    show f ≫ globalSectionAction N r ≫ g = globalSectionAction M r ≫ f ≫ g
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (globalSectionSmul_naturality f r).symm

end Scheme

namespace Variety

variable {k : Type u} [Field k] (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))] [IsVariety k Y]

/-- Morphisms of module sheaves on a variety form a `k`-module, by precomposing
with multiplication by the corresponding global function.

Precomposition rather than postcomposition is an arbitrary choice;
`varietyScalarAction_naturality` says the two agree, and `comp_smul` below is
where that is spent. -/
@[reducible]
noncomputable def homModule (M N : Y.Modules) : Module k (M ⟶ N) where
  smul r f := varietyScalarAction Y M r ≫ f
  one_smul f := by
    show varietyScalarAction Y M 1 ≫ f = f
    rw [map_one]
    exact Category.id_comp f
  mul_smul r s f := by
    show varietyScalarAction Y M (r * s) ≫ f
      = varietyScalarAction Y M r ≫ varietyScalarAction Y M s ≫ f
    rw [mul_comm, map_mul, End.mul_def, Category.assoc]
  smul_zero r := by
    show varietyScalarAction Y M r ≫ (0 : M ⟶ N) = 0
    exact Limits.comp_zero
  smul_add r f g := by
    show varietyScalarAction Y M r ≫ (f + g)
      = varietyScalarAction Y M r ≫ f + varietyScalarAction Y M r ≫ g
    exact Preadditive.comp_add _ _ _ _ _ _
  add_smul r s f := by
    show varietyScalarAction Y M (r + s) ≫ f
      = varietyScalarAction Y M r ≫ f + varietyScalarAction Y M s ≫ f
    rw [map_add]
    exact Preadditive.add_comp _ _ _ _ _ _
  zero_smul f := by
    show varietyScalarAction Y M 0 ≫ f = 0
    rw [map_zero]
    exact Limits.zero_comp

/-- **Module sheaves on a variety form a `k`-linear category.**

`smul_comp` is associativity. `comp_smul` is the only clause with content: it
says the action may be moved across a morphism, which is
`varietyScalarAction_naturality`, itself `globalSectionSmul_naturality` — the
statement that multiplication by a global function is central. -/
noncomputable instance modulesLinear : Linear k Y.Modules where
  homModule M N := homModule Y M N
  smul_comp M N P r f g := by
    show (varietyScalarAction Y M r ≫ f) ≫ g = varietyScalarAction Y M r ≫ f ≫ g
    exact Category.assoc _ _ _
  comp_smul M N P f r g := by
    show f ≫ varietyScalarAction Y N r ≫ g = varietyScalarAction Y M r ≫ f ≫ g
    rw [← Category.assoc, ← varietyScalarAction_naturality Y f r, Category.assoc]

omit [IsVariety k Y] in
/-- The scalar action, unfolded. This is the computation rule for everything
above; `Linear k` alone says a `k`-module structure exists but not which one. -/
theorem smul_eq_action_comp {M N : Y.Modules} (r : k) (f : M ⟶ N) :
    r • f = varietyScalarAction Y M r ≫ f :=
  rfl

/-- **Coherent sheaves on a variety form a `k`-linear category**, inherited from
the ambient module sheaves as a full subcategory.

Declared rather than inferred because `Coh` is a `def`, so instance search does
not see the `FullSubcategory` underneath it; the `Preadditive` and `Abelian`
instances next door are stated the same way. -/
noncomputable instance cohLinear : Linear k (Coh Y) :=
  inferInstanceAs (Linear k (Scheme.coherent Y).FullSubcategory)

/-! ### Propagation to the derived category

Mathlib's `DerivedCategory.instLinear` fires on its own, and the `inferInstance`
below is the whole of it. That was not always true: `Coh.abelian` used to obtain
its `toPreadditive` from the full subcategory's `Abelian` instance rather than
from `Coh.preadditive`, and search could not cross the gap, so this term had to
supply `cohLinear` by hand. Issue #662 closed that by pinning the field in
`CoherentSheaf/Abelian/Basic.lean`; see the docstring there for why the two are
not interchangeable and what keeps them pinned. -/

/-- Regression test for #662, in the shape that found it: search must reach
`cohLinear` from a `Preadditive` argument that arrived via `Abelian`. -/
noncomputable example :
    @Linear k _ (Coh Y) _ (Coh.abelian Y).toPreadditive :=
  inferInstance

/-- The derived category of coherent sheaves on a variety is `k`-linear. -/
noncomputable instance derivedLinear :
    Linear k (DerivedCategory (Coh Y)) :=
  inferInstance

end Variety

end AlgebraicGeometry
