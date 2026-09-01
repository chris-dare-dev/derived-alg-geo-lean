/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Basic
import DerivedAlgGeo.LinearAlgebra.AlternatingFinsum
import Mathlib.Algebra.Exact.Sequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Additivity of the geometric Euler characteristic

This file proves that the finite coherent-cohomology Euler characteristic is additive in
short exact sequences. Mathlib supplies the additive `Ext` long exact sequence. The only
additional datum requested here is that its connecting homomorphisms are linear over the base
field; `LinearConnectingMaps` records precisely that compatibility and no exactness axiom.

The result is then descended explicitly to the Grothendieck group of coherent sheaves.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Cohomology

variable {k : Type u} [Field k]
variable {X : Variety k}

/-- The short exact sequence of abelian sheaves underlying a short exact sequence of coherent
sheaves. -/
noncomputable abbrev coherentSheafShortComplex (S : ShortComplex (Coh X.toScheme)) :=
  (S.map (Coh.ι X.toScheme)).map (Scheme.Modules.toSheaf X.toScheme)

/-- Exactness survives both forgetful functors from coherent module sheaves to abelian
sheaves. -/
theorem coherentSheafShortComplex_shortExact {S : ShortComplex (Coh X.toScheme)}
    (hS : S.ShortExact) : (coherentSheafShortComplex S).ShortExact :=
  Scheme.Modules.shortExact_map_toSheaf (Coh.shortExact_map_ι X.toScheme hS)

/-- The additive connecting homomorphism in the `Ext` long exact sequence underlying coherent
sheaf cohomology. -/
noncomputable def coherentConnectingMap (S : ShortComplex (Coh X.toScheme))
    (hS : S.ShortExact) (i : ℕ) :
    (coherentH X.toScheme i).obj S.X₃ ⟶ (coherentH X.toScheme (i + 1)).obj S.X₁ := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  exact AddCommGrpCat.ofHom (hT.extClass.postcomp
    ((constantSheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) rfl)

namespace FiniteCohomology

/-- The additive equivalence carried by an isomorphism of bundled additive groups. -/
private def isoToAddEquiv {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) : A ≃+ B where
  toFun := ConcreteCategory.hom e.hom
  invFun := ConcreteCategory.hom e.inv
  left_inv := e.hom_inv_id_apply
  right_inv := e.inv_hom_id_apply
  map_add' x y := map_add (ConcreteCategory.hom e.hom) x y

/-- A linear lift of the connecting maps in the actual `Ext` long exact sequence.

Mathlib currently exposes the connecting morphisms only as additive group homomorphisms.
The compatibility field says that `δ` forgets to exactly that morphism. Exactness is proved
below from `Abelian.Ext.covariant_sequence_exact₁/₂/₃`; it is not stored here. -/
structure LinearConnectingMaps (D : FiniteCohomology X)
    (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact) where
  /-- The degree-`i` linear connecting morphism. -/
  δ : ∀ i : ℕ, (D.moduleH i).obj S.X₃ ⟶ (D.moduleH (i + 1)).obj S.X₁
  /-- After forgetting scalars and applying `comparison`, `δ` is the `Ext` connecting map. -/
  commutes : ∀ i : ℕ,
    (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).map (δ i) ≫
        (D.comparison (i + 1)).hom.app S.X₁ =
      (D.comparison i).hom.app S.X₃ ≫ coherentConnectingMap S hS i

/-- Exactness at the middle cohomology group in each degree, transported from Mathlib's
`Ext` long exact sequence. -/
theorem exact₂ (D : FiniteCohomology X) {S : ShortComplex (Coh X.toScheme)}
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact ((D.moduleH i).map S.f) ((D.moduleH i).map S.g) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  have hExt := Abelian.Ext.covariant_sequence_exact₂'
    ((constantSheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) hT i
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (f₁₂ := ((D.moduleH i).map S.f).hom.toAddMonoidHom)
    (f₂₃ := ((D.moduleH i).map S.g).hom.toAddMonoidHom)
    (isoToAddEquiv ((D.comparison i).app S.X₁))
    (isoToAddEquiv ((D.comparison i).app S.X₂))
    (isoToAddEquiv ((D.comparison i).app S.X₃))
  · ext x
    exact ConcreteCategory.congr_hom ((D.comparison i).hom.naturality S.f).symm x
  · ext x
    exact ConcreteCategory.congr_hom ((D.comparison i).hom.naturality S.g).symm x
  · exact hExt

/-- Exactness between the quotient map in degree `i` and the connecting morphism. -/
theorem LinearConnectingMaps.exact₃ (D : FiniteCohomology X)
    {S : ShortComplex (Coh X.toScheme)} {hS : S.ShortExact}
    (L : D.LinearConnectingMaps S hS) (i : ℕ) :
    Function.Exact ((D.moduleH i).map S.g) (L.δ i) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  have hExt := Abelian.Ext.covariant_sequence_exact₃'
    ((constantSheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) hT i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (f₁₂ := ((D.moduleH i).map S.g).hom.toAddMonoidHom)
    (f₂₃ := (L.δ i).hom.toAddMonoidHom)
    (isoToAddEquiv ((D.comparison i).app S.X₂))
    (isoToAddEquiv ((D.comparison i).app S.X₃))
    (isoToAddEquiv ((D.comparison (i + 1)).app S.X₁))
  · ext x
    exact ConcreteCategory.congr_hom ((D.comparison i).hom.naturality S.g).symm x
  · ext x
    exact ConcreteCategory.congr_hom (L.commutes i).symm x
  · exact hExt

/-- Exactness between the connecting morphism out of degree `i` and the inclusion map in
degree `i + 1`. -/
theorem LinearConnectingMaps.exact₁ (D : FiniteCohomology X)
    {S : ShortComplex (Coh X.toScheme)} {hS : S.ShortExact}
    (L : D.LinearConnectingMaps S hS) (i : ℕ) :
    Function.Exact (L.δ i) ((D.moduleH (i + 1)).map S.f) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  have hExt := Abelian.Ext.covariant_sequence_exact₁'
    ((constantSheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) hT i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (f₁₂ := (L.δ i).hom.toAddMonoidHom)
    (f₂₃ := ((D.moduleH (i + 1)).map S.f).hom.toAddMonoidHom)
    (isoToAddEquiv ((D.comparison i).app S.X₃))
    (isoToAddEquiv ((D.comparison (i + 1)).app S.X₁))
    (isoToAddEquiv ((D.comparison (i + 1)).app S.X₂))
  · ext x
    exact ConcreteCategory.congr_hom (L.commutes i).symm x
  · ext x
    exact ConcreteCategory.congr_hom
      ((D.comparison (i + 1)).hom.naturality S.f).symm x
  · exact hExt

/-- The first map of the long exact sequence is injective in degree zero. -/
theorem injective_map_f_zero (D : FiniteCohomology X)
    {S : ShortComplex (Coh X.toScheme)} (hS : S.ShortExact) :
    Function.Injective ((D.moduleH 0).map S.f) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  letI : Mono (coherentSheafShortComplex S).f := hT.mono_f
  have hExt := Abelian.Ext.postcomp_mk₀_injective_of_mono
    ((constantSheaf (Opens.grothendieckTopology X.toScheme) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) (coherentSheafShortComplex S).f
  intro x y hxy
  apply (isoToAddEquiv ((D.comparison 0).app S.X₁)).injective
  apply hExt
  calc
    _ = (isoToAddEquiv ((D.comparison 0).app S.X₂))
        (((D.moduleH 0).map S.f) x) :=
      ConcreteCategory.congr_hom ((D.comparison 0).hom.naturality S.f).symm x
    _ = (isoToAddEquiv ((D.comparison 0).app S.X₂))
        (((D.moduleH 0).map S.f) y) := congrArg _ hxy
    _ = _ :=
      (ConcreteCategory.congr_hom ((D.comparison 0).hom.naturality S.f).symm y).symm

/-- The geometric Euler characteristic is additive on a short exact sequence of coherent
sheaves, provided the additive `Ext` connecting maps have the stated linear lifts. -/
theorem eulerCharacteristic_additive (D : FiniteCohomology X)
    {S : ShortComplex (Coh X.toScheme)} {hS : S.ShortExact}
    (L : D.LinearConnectingMaps S hS) :
    D.eulerCharacteristic S.X₂ =
      D.eulerCharacteristic S.X₁ + D.eulerCharacteristic S.X₃ := by
  let n := max (D.bound S.X₁) (max (D.bound S.X₂) (D.bound S.X₃))
  letI (i : ℕ) : Module.Finite k ((D.moduleH i).obj S.X₁) := D.finite i S.X₁
  letI (i : ℕ) : Module.Finite k ((D.moduleH i).obj S.X₂) := D.finite i S.X₂
  letI (i : ℕ) : Module.Finite k ((D.moduleH i).obj S.X₃) := D.finite i S.X₃
  letI : Subsingleton ((D.moduleH (n + 1)).obj S.X₁) :=
    D.vanishesAbove S.X₁ (n + 1) (Nat.lt_succ_of_le (le_max_left _ _))
  have hsum := DerivedAlgGeo.LinearAlgebra.alternating_finrank_eq_zero_of_exact
    (A := fun i ↦ (D.moduleH i).obj S.X₁)
    (B := fun i ↦ (D.moduleH i).obj S.X₂)
    (C := fun i ↦ (D.moduleH i).obj S.X₃)
    (f := fun i ↦ ((D.moduleH i).map S.f).hom)
    (g := fun i ↦ ((D.moduleH i).map S.g).hom)
    (δ := fun i ↦ (L.δ i).hom)
    (D.injective_map_f_zero hS)
    (fun i ↦ D.exact₂ hS i)
    (fun i ↦ LinearConnectingMaps.exact₃ D L i)
    (fun i ↦ LinearConnectingMaps.exact₁ D L i) n
  rw [D.eulerCharacteristic_eq_sum_of_bound S.X₁ n (le_max_left _ _),
    D.eulerCharacteristic_eq_sum_of_bound S.X₂ n
      (le_trans (le_max_left _ _) (le_max_right _ _)),
    D.eulerCharacteristic_eq_sum_of_bound S.X₃ n
      (le_trans (le_max_right _ _) (le_max_right _ _))]
  change ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      ((D.dimension S.X₁ i : ℤ) - D.dimension S.X₂ i + D.dimension S.X₃ i) = 0
    at hsum
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  omega

/-- Regard a short complex of module sheaves with coherent terms as a short complex in
`Coh X`. -/
def coherentShortComplex (S : ShortComplex X.toScheme.Modules)
    (h₁ : Scheme.Modules.IsCoherent X.toScheme S.X₁)
    (h₂ : Scheme.Modules.IsCoherent X.toScheme S.X₂)
    (h₃ : Scheme.Modules.IsCoherent X.toScheme S.X₃) :
    ShortComplex (Coh X.toScheme) where
  X₁ := ⟨S.X₁, h₁⟩
  X₂ := ⟨S.X₂, h₂⟩
  X₃ := ⟨S.X₃, h₃⟩
  f := ObjectProperty.homMk S.f
  g := ObjectProperty.homMk S.g
  zero := by
    apply ObjectProperty.hom_ext
    change S.f ≫ S.g = 0
    exact S.zero

@[simp]
theorem coherentShortComplex_map_inclusion (S : ShortComplex X.toScheme.Modules)
    (h₁ : Scheme.Modules.IsCoherent X.toScheme S.X₁)
    (h₂ : Scheme.Modules.IsCoherent X.toScheme S.X₂)
    (h₃ : Scheme.Modules.IsCoherent X.toScheme S.X₃) :
    (coherentShortComplex S h₁ h₂ h₃).map (Coh.ι X.toScheme) = S := rfl

/-- Exactness of a module-sheaf short complex reflects to the coherent full subcategory. -/
theorem coherentShortComplex_shortExact {S : ShortComplex X.toScheme.Modules}
    (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsCoherent X.toScheme S.X₁)
    (h₂ : Scheme.Modules.IsCoherent X.toScheme S.X₂)
    (h₃ : Scheme.Modules.IsCoherent X.toScheme S.X₃) :
    (coherentShortComplex S h₁ h₂ h₃).ShortExact := by
  letI : (Coh.ι X.toScheme).Faithful := by
    change (Scheme.coherent X.toScheme).ι.Faithful
    infer_instance
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (Coh.ι X.toScheme)
  change S.ShortExact
  exact hS

/-- `X.Modules`-level form of Euler additivity: coherent hypotheses on the three terms are
enough to apply the coherent-sheaf theorem. -/
theorem eulerCharacteristic_additive_modules (D : FiniteCohomology X)
    {S : ShortComplex X.toScheme.Modules} (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsCoherent X.toScheme S.X₁)
    (h₂ : Scheme.Modules.IsCoherent X.toScheme S.X₂)
    (h₃ : Scheme.Modules.IsCoherent X.toScheme S.X₃)
    (L : D.LinearConnectingMaps (coherentShortComplex S h₁ h₂ h₃)
      (coherentShortComplex_shortExact hS h₁ h₂ h₃)) :
    D.eulerCharacteristic ⟨S.X₂, h₂⟩ =
      D.eulerCharacteristic ⟨S.X₁, h₁⟩ + D.eulerCharacteristic ⟨S.X₃, h₃⟩ :=
  D.eulerCharacteristic_additive L

/-- Linear connecting maps, compatible with `Ext`, chosen for every short exact sequence.
This is the precise temporary input needed for a global Grothendieck-group factorization. -/
abbrev LinearConnectingSystem (D : FiniteCohomology X) :=
  ∀ (S : ShortComplex (Coh X.toScheme)) (hS : S.ShortExact),
    D.LinearConnectingMaps S hS

end FiniteCohomology

/-! ### The Euler homomorphism on `K₀(Coh X)`

`Coh X` is abelian for every `Variety k`, so its Grothendieck group is `K₀Ab`.
This file used to build a second one by hand -- generators, a relation subgroup,
a quotient, a class map and a bespoke universal property -- none of which was
needed. The `iso` generator it carried was redundant too: `K₀Ab.of_iso` is a
theorem, derived from the short exact sequence `X ≅ Y ⟶ 0`.
-/

namespace FiniteCohomology

/-- **The Euler characteristic as a homomorphism `K₀(Coh X) → ℤ`.**

`K₀Ab.liftOf` wants additivity and nothing else: `map_zero` and `map_iso` follow
from `of_isZero` and `of_iso`, which are theorems. The old route to this hom went
through `FreeAbelianGroup.lift`, an `AddSubgroup.closure_le` argument and
`QuotientAddGroup.lift`, all of which are now `K₀Ab`'s. -/
noncomputable def grothendieckEulerHom (D : FiniteCohomology X)
    (L : D.LinearConnectingSystem) : K₀Ab (Coh X.toScheme) →+ ℤ :=
  K₀Ab.liftOf D.eulerCharacteristic
    (fun S hS => D.eulerCharacteristic_additive (L S hS))

@[simp]
theorem grothendieckEulerHom_class (D : FiniteCohomology X)
    (L : D.LinearConnectingSystem) (F : Coh X.toScheme) :
    D.grothendieckEulerHom L (K₀Ab.of F) = D.eulerCharacteristic F :=
  K₀Ab.liftOf_of _ _ F

end FiniteCohomology

end Cohomology

end AlgebraicGeometry
