/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Linear
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Linearity of the tensor product of scheme-module sheaves

The sheafified tensor product is additive in each variable.  It is also linear over the ring of
global functions, for the `Linear Γ(X, ⊤) X.Modules` structure, and over the base field for a scheme
over a field.  Consequently Mathlib's `tensorLeft` and `tensorRight` functors inherit `Linear`
instances.

The scalar calculation does not inspect sections of a sheafification.  Multiplication by a global
function is first identified with the canonical action of an endomorphism of the tensor unit.
Monoidal coherence then proves compatibility in the left tensor variable.  For the right variable,
the objectwise symmetry before sheafification gives a private comparison isomorphism; its
naturality reduces the result to the left-variable calculation.  This does not assert a
`SymmetricCategory X.Modules` instance: the hexagon laws for the sheafified associator are a
separate contract.

No coherence, quasi-coherence, noetherianity, properness, or finite-dimensionality hypothesis
enters.  In particular, this file supplies the categorical linearity needed to upgrade tensor-Hom
equivalences to linear equivalences, but it does not itself prove that any Hom space is finite.

## Main results

* `Scheme.Modules.modulesMonoidalPreadditive` -- tensor is additive in both variables;
* `Scheme.Modules.modulesMonoidalLinearGlobal` -- tensor is linear over `Γ(X, ⊤)`;
* `Variety.modulesMonoidalLinear` -- tensor is linear over the base field.
-/

open CategoryTheory Limits MonoidalCategory BraidedCategory
  AlgebraicGeometry.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

private noncomputable instance presheafMonoidalCategory :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

private noncomputable instance presheafSymmetricCategory :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private abbrev associatedSheaf (X : Scheme.{u}) :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/- Sheafification preserves finite limits, and the forgetful functor is a right adjoint.  Their
preservation of binary products therefore makes both functors additive. -/
private noncomputable instance associatedSheafAdditive :
    (associatedSheaf X).Additive :=
  Functor.additive_of_preserves_binary_products _

private noncomputable instance toPresheafOfModulesAdditive :
    (toPresheafOfModules X).Additive :=
  Functor.additive_of_preserves_binary_products _

/- The objectwise tensor product of presheaves of modules is additive in each variable. -/
private noncomputable instance presheafMonoidalPreadditive :
    MonoidalPreadditive X.PresheafOfModules where
  whiskerLeft_zero := by
    intro M N P
    ext U : 1
    exact MonoidalPreadditive.whiskerLeft_zero (C := ModuleCat (X.presheaf.obj U))
  zero_whiskerRight := by
    intro M N P
    ext U : 1
    exact MonoidalPreadditive.zero_whiskerRight (C := ModuleCat (X.presheaf.obj U))
  whiskerLeft_add := by
    intro M N P f g
    ext U : 1
    exact MonoidalPreadditive.whiskerLeft_add (C := ModuleCat (X.presheaf.obj U)) _ _
  add_whiskerRight := by
    intro M N P f g
    ext U : 1
    exact MonoidalPreadditive.add_whiskerRight (C := ModuleCat (X.presheaf.obj U)) _ _

/-- **Scheme-module sheaves are monoidal preadditive.**

Additivity holds before sheafification, objectwise on tensor products of modules.  The forgetful
functor to presheaves and module sheafification are additive, so the four identities descend to
the sheafified tensor product. -/
noncomputable instance modulesMonoidalPreadditive : MonoidalPreadditive X.Modules where
  whiskerLeft_zero := by
    intro M N P
    change tensorHom (𝟙 M) (0 : N ⟶ P) = 0
    unfold tensorHom
    rw [Functor.map_zero, MonoidalPreadditive.tensor_zero, Functor.map_zero]
    rfl
  zero_whiskerRight := by
    intro M N P
    change tensorHom (0 : N ⟶ P) (𝟙 M) = 0
    unfold tensorHom
    rw [Functor.map_zero, MonoidalPreadditive.zero_tensor, Functor.map_zero]
    rfl
  whiskerLeft_add := by
    intro M N P f g
    change tensorHom (𝟙 M) (f + g) = tensorHom (𝟙 M) f + tensorHom (𝟙 M) g
    unfold tensorHom
    rw [Functor.map_add, MonoidalPreadditive.tensor_add, Functor.map_add]
    rfl
  add_whiskerRight := by
    intro M N P f g
    change tensorHom (f + g) (𝟙 M) = tensorHom f (𝟙 M) + tensorHom g (𝟙 M)
    unfold tensorHom
    rw [Functor.map_add, MonoidalPreadditive.add_tensor, Functor.map_add]
    rfl

/-- **Multiplication by a global function is the tensor-unit action.**

The endomorphism of the unit is multiplication by `r`.  Its value on `1` over an open is the
restriction of `r`, so `unitorConj_app` identifies its canonical action on `M` with
`globalSectionSmul M r`. -/
theorem unitorConj_globalSectionSmul (M : X.Modules) (r : Γ(X, (⊤ : X.Opens))) :
    unitorConj M (globalSectionSmul (.unit X.ringCatSheaf) r) =
      globalSectionSmul M r := by
  apply SheafOfModules.hom_ext
  ext U t
  rw [unitorConj_app, globalSectionSmul_app, globalSectionSmul_app]
  let a : Γ(X, U.unop) := X.presheaf.map
    (homOfLE (show U.unop ≤ (⊤ : X.Opens) from le_top)).op r
  change (a • (1 : Γ(X, U.unop))) • t = a • t
  rw [smul_eq_mul, mul_one]

/-- **Tensoring multiplication by a global function on the left factor is multiplication on the
tensor product.**

After `unitorConj_globalSectionSmul`, this is a formal monoidal-coherence identity. -/
theorem tensorHom_id_globalSectionSmul (L M : X.Modules)
    (r : Γ(X, (⊤ : X.Opens))) :
    tensorHom (𝟙 L) (globalSectionSmul M r) =
      globalSectionSmul (tensorObj L M) r := by
  rw [← unitorConj_globalSectionSmul M r,
    ← unitorConj_globalSectionSmul (tensorObj L M) r]
  change L ◁ ((ρ_ M).inv ≫ (M ◁ globalSectionSmul (.unit X.ringCatSheaf) r) ≫
      (ρ_ M).hom) =
    (ρ_ (L ⊗ M)).inv ≫ ((L ⊗ M) ◁ globalSectionSmul (.unit X.ringCatSheaf) r) ≫
      (ρ_ (L ⊗ M)).hom
  monoidal

private lemma whiskerLeft_smul_global (L : X.Modules) {M N : X.Modules}
    (r : Γ(X, (⊤ : X.Opens))) (f : M ⟶ N) :
    L ◁ (r • f) = r • (L ◁ f) := by
  change tensorHom (𝟙 L) (globalSectionSmul M r ≫ f) =
    globalSectionSmul (tensorObj L M) r ≫ tensorHom (𝟙 L) f
  rw [tensorHom_id_comp, tensorHom_id_globalSectionSmul]

/- The presheaf braiding sheafifies to an isomorphism between the two orders of the tensor
product.  Only this isomorphism and its naturality are needed below; no sheaf-level braided or
symmetric monoidal instance is claimed. -/
private noncomputable def tensorSwapIso (M N : X.Modules) :
    tensorObj M N ≅ tensorObj N M :=
  (associatedSheaf X).mapIso
    (β_ ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N))

set_option backward.isDefEq.respectTransparency false in
private lemma tensorSwapIso_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorHom f g ≫ (tensorSwapIso M' N').hom =
      (tensorSwapIso M N).hom ≫ tensorHom g f := by
  unfold tensorHom tensorSwapIso
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp,
    BraidedCategory.braiding_naturality]

set_option backward.isDefEq.respectTransparency false in
private lemma smul_whiskerRight_global (r : Γ(X, (⊤ : X.Opens))) {M N : X.Modules}
    (f : M ⟶ N) (L : X.Modules) :
    (r • f) ▷ L = r • (f ▷ L) := by
  apply (cancel_mono (tensorSwapIso N L).hom).1
  change tensorHom (r • f) (𝟙 L) ≫ (tensorSwapIso N L).hom =
    (r • tensorHom f (𝟙 L)) ≫ (tensorSwapIso N L).hom
  rw [tensorSwapIso_naturality, Linear.smul_comp,
    tensorSwapIso_naturality, ← Linear.comp_smul]
  change (tensorSwapIso M L).hom ≫ L ◁ (r • f) =
    (tensorSwapIso M L).hom ≫ (r • (L ◁ f))
  rw [whiskerLeft_smul_global]

/-- **The sheafified tensor product is linear over global functions in both variables.**

This is the structure consumed by Mathlib's `tensorLeft_linear` and `tensorRight_linear`
instances. -/
noncomputable instance modulesMonoidalLinearGlobal :
    MonoidalLinear Γ(X, (⊤ : X.Opens)) X.Modules where
  whiskerLeft_smul := whiskerLeft_smul_global
  smul_whiskerRight := smul_whiskerRight_global

example (L : X.Modules) : (tensorLeft L).Linear Γ(X, (⊤ : X.Opens)) :=
  inferInstance

example (L : X.Modules) : (tensorRight L).Linear Γ(X, (⊤ : X.Opens)) :=
  inferInstance

end


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Variety

variable {k : Type u} [Field k] (Y : Scheme.{u})
  [Y.Over (Spec (CommRingCat.of k))]

noncomputable section

private lemma whiskerLeft_smul (L : Y.Modules) {M N : Y.Modules}
    (r : k) (f : M ⟶ N) :
    L ◁ (r • f) = r • (L ◁ f) := by
  change Scheme.Modules.tensorHom (𝟙 L)
      (globalSectionSmul M (baseFieldToGlobalSections Y r) ≫ f) =
    globalSectionSmul (Scheme.Modules.tensorObj L M) (baseFieldToGlobalSections Y r) ≫
      Scheme.Modules.tensorHom (𝟙 L) f
  exact Scheme.Modules.whiskerLeft_smul_global L (baseFieldToGlobalSections Y r) f

private lemma smul_whiskerRight (r : k) {M N : Y.Modules}
    (f : M ⟶ N) (L : Y.Modules) :
    (r • f) ▷ L = r • (f ▷ L) := by
  change Scheme.Modules.tensorHom
      (globalSectionSmul M (baseFieldToGlobalSections Y r) ≫ f) (𝟙 L) =
    globalSectionSmul (Scheme.Modules.tensorObj M L) (baseFieldToGlobalSections Y r) ≫
      Scheme.Modules.tensorHom f (𝟙 L)
  exact Scheme.Modules.smul_whiskerRight_global
    (baseFieldToGlobalSections Y r) f L

/-- **For a scheme over a field, tensoring module sheaves is linear over the base field.**

The base-field action factors through `k → Γ(Y, ⊤)`, so this is the global-function instance
restricted along `baseFieldToGlobalSections`.  No finite-type or separatedness hypothesis is
needed. -/
noncomputable instance modulesMonoidalLinear : MonoidalLinear k Y.Modules where
  whiskerLeft_smul := whiskerLeft_smul Y
  smul_whiskerRight := smul_whiskerRight Y

example (L : Y.Modules) : (tensorLeft L).Linear k := inferInstance

example (L : Y.Modules) : (tensorRight L).Linear k := inferInstance

end


end AlgebraicGeometry.Variety
