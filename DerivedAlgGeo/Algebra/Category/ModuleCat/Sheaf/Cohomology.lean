/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.Grp.ForgetCorepresentable
import DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf.Sections
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Exactness
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Generator
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# `Ext` from the unit module sheaf computes sheaf cohomology

For a sheaf of rings `R` on a site with a terminal object, `Ext^n (unit R) M` in sheaves of
`R`-modules is identified with the sheaf cohomology `H^n` of the underlying abelian sheaf of
`M`, provided injective sheaves of modules are acyclic for `H`. This is the classical
statement that cohomology of an `𝒪`-module may be computed in `𝒪`-modules or in abelian
sheaves (Hartshorne III.2.6), routed through `extComparisonAddEquiv`:

* the comparison morphism is `unitFromConstant : ℤ ⟶ toSheaf (unit R)`, the map from the
  constant sheaf sending `1` to `1`;
* in degree zero the comparison is `f ↦ unitFromConstant ≫ toSheaf.map f`, which is a
  bijection because both sides are the sections of `M` over the terminal object
  (`unitHomEquiv`, `sectionsEquivOfIsTerminal`, and the constant-sheaf adjunction);
* acyclicity of images of injectives is the hypothesis, supplied on a topological space by
  flasqueness (`Topology/Sheaves/ModulesCohomology.lean`).

## Main results

* `SheafOfModules.unitFromConstant`, `SheafOfModules.bijective_unitFromConstant_comp`.
* `SheafOfModules.extUnitAddEquivH`.
-/

universe w u

open CategoryTheory Category Limits Opposite Abelian

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {T : C} (hT : IsTerminal T)

/-- The map from the constant sheaf `ℤ` to the underlying abelian sheaf of `unit R` sending
`1` to `1`. -/
noncomputable def unitFromConstant :
    (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (toSheaf R).obj (unit R) :=
  ((constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ _).symm
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (1 : R.obj.obj (op T)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Under the constant-sheaf adjunction, `unitFromConstant ≫ toSheaf.map f` is the section
`f 1` over the terminal object. -/
lemma homEquiv_unitFromConstant_comp (M : SheafOfModules.{u} R) (f : unit R ⟶ M) :
    (constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ _
        (unitFromConstant R hT ≫ (toSheaf R).map f) =
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
        (f.val.app (op T) (1 : R.obj.obj (op T))) := by
  rw [Adjunction.homEquiv_naturality_right, unitFromConstant, Equiv.apply_symm_apply]
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  rw [AddEquiv.apply_symm_apply, AddCommGrpCat.uliftZMultiplesAddEquiv_comp,
    AddEquiv.apply_symm_apply]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Degree zero.** `f ↦ unitFromConstant ≫ toSheaf.map f` is a bijection from maps
`unit R ⟶ M` to maps `ℤ ⟶ toSheaf M`: both are the sections of `M` over the terminal
object. -/
theorem bijective_unitFromConstant_comp (M : SheafOfModules.{u} R) :
    Function.Bijective (fun f : unit R ⟶ M ↦ unitFromConstant R hT ≫ (toSheaf R).map f) := by
  let E : ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (toSheaf R).obj M) ≃ M.val.obj (op T) :=
    ((constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ _).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv
  have h : (fun f : unit R ⟶ M ↦ unitFromConstant R hT ≫ (toSheaf R).map f) =
      E.symm ∘ (M.val.sectionsEquivOfIsTerminal hT) ∘ M.unitHomEquiv := by
    funext f
    apply E.injective
    simp only [Function.comp, Equiv.apply_symm_apply]
    change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv _ _
        (unitFromConstant R hT ≫ (toSheaf R).map f)) = _
    rw [homEquiv_unitFromConstant_comp, AddEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact E.symm.bijective.comp
    ((M.val.sectionsEquivOfIsTerminal hT).bijective.comp M.unitHomEquiv.bijective)

variable [hExtM : HasExt.{w} (SheafOfModules.{u} R)] [hExtA : HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- The `Ext` comparison along `toSheaf` from `unitFromConstant` is bijective in degree
zero. -/
lemma bijective_extComparisonMap_unitFromConstant_zero (M : SheafOfModules.{u} R) :
    Function.Bijective
      (extComparisonMap (R := toSheaf R) (unitFromConstant R hT) (B := M) (n := 0)) :=
  (bijective_extComparisonMap_zero_iff _ _).2 (bijective_unitFromConstant_comp R hT M)

/-- **`Ext` from the unit computes sheaf cohomology.** `Ext^n (unit R) M ≃+ H^n (toSheaf M)`
for every `n`, once injective sheaves of modules are acyclic for `H`. -/
noncomputable def extUnitAddEquivH
    (hacyclic : ∀ (I : SheafOfModules.{u} R) [Injective I] (n : ℕ),
      Subsingleton (Sheaf.H ((toSheaf R).obj I) (n + 1)))
    (M : SheafOfModules.{u} R) (n : ℕ) :
    Ext.{w} (unit R) M n ≃+ Sheaf.H ((toSheaf R).obj M) n :=
  extComparisonAddEquiv (unitFromConstant R hT)
    (bijective_extComparisonMap_unitFromConstant_zero R hT) hacyclic M n

end SheafOfModules
