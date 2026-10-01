/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# Sections of the sheafified tensor product

The monoidal structure on `X.Modules` is the sheafification of the objectwise tensor product of
presheaves of modules. Everything that is known about it at the level of sections is routed
through `tmulSection M N U a b`, the image of a pure tensor under the sheafification unit.

This file collects the section-level calculus that lets coherence equations between morphisms
out of a sheafified tensor product be checked on pure tensors, without computing sheafification:

* `section_ext_of_locally`: sections of a module sheaf that agree locally agree;
* `tensorObj_hom_ext`, `tensorObj_tensorObj_hom_ext`: morphisms out of `M ⊗ N` (respectively
  `(M ⊗ N) ⊗ P`) are determined by their values on pure tensors;
* `tensorHom_tmulSection`, `tensorUnitLeftIso_hom_tmulSection`,
  `tensorUnitRightIso_hom_tmulSection`, `tensorAssocIso_hom_tmulSection`: the tensor of
  morphisms, the unitors and the associator, on pure tensors;
* `TensorLiftData`, `TensorLiftData.lift`: the universal property of `M ⊗ N` as the sheafified
  tensor product, i.e. a morphism out of `M ⊗ N` from sectionwise bilinear data that is
  compatible with restriction, with `TensorLiftData.lift_app_tmulSection`.

None of this is new mathematics; it is the interface that `tmulSection` always lacked, in the
form needed to build structure maps (lax and oplax monoidal comparisons) out of sections.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Sections of a module sheaf that agree locally agree.** -/
theorem section_ext_of_locally (G : X.Modules) {U : X.Opens} (s t : Γ(G, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      G.presheaf.map (homOfLE hV).op s = G.presheaf.map (homOfLE hV).op t) : s = t := by
  classical
  choose! V hV hxV hst using h
  let F : TopCat.Sheaf Ab X := ⟨G.presheaf, G.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : U => V x.1) U
    (fun x => homOfLE (hV x.1 x.2)) ?_ s t ?_
  · intro x hx
    exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩)
  · intro x
    exact hst x.1 x.2


/-- **A morphism out of a sheafified tensor product is determined by its values on pure
tensors.**

Locally a section of `M ⊗ N` is a finite sum of `tmulSection`s
(`exists_eq_sum_tmulSection`), and morphisms of module sheaves commute with restriction and
sums. -/
theorem tensorObj_hom_ext {A B C : X.Modules} (φ ψ : tensorObj A B ⟶ C)
    (h : ∀ (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)),
      φ.app U (tmulSection A B (op U) a b) = ψ.app U (tmulSection A B (op U) a b)) :
    φ = ψ := by
  have key : ∀ (U : X.Opens) (t : Γ(tensorObj A B, U)), φ.app U t = ψ.app U t := by
    intro U t
    apply section_ext_of_locally
    intro x hx
    obtain ⟨V, hV, hxV, s, hs⟩ := exists_eq_sum_tmulSection A B t x hx
    refine ⟨V, hV, hxV, ?_⟩
    rw [homApp_res φ hV t, homApp_res ψ hV t, hs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun p _ => h V p.1 p.2
  exact hom_ext φ ψ fun U => by ext t; exact key U t


noncomputable section

private local instance sectionsPresheafMonoidalCategory : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- **The pure tensor is additive in its second factor** -- the companion of
`tmulSection_add_left`. -/
theorem tmulSection_add_right (M N : X.Modules) (U : X.Opensᵒᵖ)
    (t : Γ(M, U.unop)) (y y' : Γ(N, U.unop)) :
    tmulSection M N U t (y + y') = tmulSection M N U t y + tmulSection M N U t y' := by
  unfold tmulSection
  set eta := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)).app U with heta
  have h1 : t ⊗ₜ[Γ(X, U.unop)] (y + y') = t ⊗ₜ[Γ(X, U.unop)] y + t ⊗ₜ[Γ(X, U.unop)] y' :=
    TensorProduct.tmul_add _ _ _
  exact (congrArg (ModuleCat.Hom.hom eta) h1).trans ((ModuleCat.Hom.hom eta).map_add _ _)

/-- **The tensor of two morphisms, on a pure tensor.** -/
theorem tensorHom_tmulSection {A A' B B' : X.Modules} (f : A ⟶ A') (g : B ⟶ B')
    (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    (tensorHom f g).app U (tmulSection A B (op U) a b) =
      tmulSection A' B' (op U) (f.app U a) (g.app U b) := by
  have hnat := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit).naturality
      ((toPresheafOfModules X).map f ⊗ₘ (toPresheafOfModules X).map g)
  let t₀ : (((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B).obj (op U)) :=
    a ⊗ₜ[Γ(X, U)] b
  have := DFunLike.congr_fun (congrArg (fun m => (ModuleCat.Hom.hom (m.app (op U)))) hnat) t₀
  exact this.symm


/-- The sheafification adjunction for a scheme. -/
private abbrev sheafAdj (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

/-- Naturality of the sheafification unit, on sections: sheafifying `h` is `h` on units. -/
private theorem sheafification_map_unit_app {P Q : X.PresheafOfModules} (h : P ⟶ Q) (U : X.Opens)
    (x : P.obj (op U)) :
    (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map h).val.app (op U)).hom
      (((sheafAdj X).unit.app P).app (op U) x) =
    ((sheafAdj X).unit.app Q).app (op U) (h.app (op U) x) := by
  have hnat := ((sheafAdj X).unit).naturality h
  exact (DFunLike.congr_fun (congrArg (fun m => (ModuleCat.Hom.hom (m.app (op U)))) hnat) x).symm

/-- The counit of sheafification undoes the unit, on sections. -/
private theorem counit_app_unit_app (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (((sheafAdj X).counit.app M).val.app (op U)).hom
      (((sheafAdj X).unit.app ((toPresheafOfModules X).obj M)).app (op U) m) = m := by
  have htri := (sheafAdj X).right_triangle_components M
  exact DFunLike.congr_fun (congrArg (fun m => (ModuleCat.Hom.hom (m.app (op U)))) htri) m

/-- **The left unitor, on a pure tensor, is scalar multiplication.** -/
theorem tensorUnitLeftIso_hom_tmulSection (M : X.Modules) (U : X.Opens)
    (r : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)) (m : Γ(M, U)) :
    (tensorUnitLeftIso M).hom.app U
      (tmulSection (SheafOfModules.unit X.ringCatSheaf) M (op U) r m) =
        (show Γ(X, U) from r) • m := by
  let t₀ : (((toPresheafOfModules X).obj (SheafOfModules.unit X.ringCatSheaf) ⊗
      (toPresheafOfModules X).obj M).obj (op U)) := r ⊗ₜ[Γ(X, U)] m
  have h1 := sheafification_map_unit_app (λ_ ((toPresheafOfModules X).obj M)).hom U t₀
  have h2 := counit_app_unit_app M U ((λ_ ((toPresheafOfModules X).obj M)).hom.app (op U) t₀)
  unfold tensorUnitLeftIso tmulSection
  exact (congrArg (fun z => (((sheafAdj X).counit.app M).val.app (op U)).hom z) h1).trans
    (h2.trans rfl)

/-- **The right unitor, on a pure tensor, is scalar multiplication.** -/
theorem tensorUnitRightIso_hom_tmulSection (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (r : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)) :
    (tensorUnitRightIso M).hom.app U
      (tmulSection M (SheafOfModules.unit X.ringCatSheaf) (op U) m r) =
        (show Γ(X, U) from r) • m := by
  let t₀ : (((toPresheafOfModules X).obj M ⊗
      (toPresheafOfModules X).obj (SheafOfModules.unit X.ringCatSheaf)).obj (op U)) :=
    m ⊗ₜ[Γ(X, U)] r
  have h1 := sheafification_map_unit_app (ρ_ ((toPresheafOfModules X).obj M)).hom U t₀
  have h2 := counit_app_unit_app M U ((ρ_ ((toPresheafOfModules X).obj M)).hom.app (op U) t₀)
  unfold tensorUnitRightIso tmulSection
  exact (congrArg (fun z => (((sheafAdj X).counit.app M).val.app (op U)).hom z) h1).trans
    (h2.trans rfl)


/-- **The associator, on iterated pure tensors, reassociates them.** -/
theorem tensorAssocIso_hom_tmulSection (L M N : X.Modules) (U : X.Opens)
    (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorAssocIso L M N).hom.app U
      (tmulSection (tensorObj L M) N (op U) (tmulSection L M (op U) l m) n) =
      tmulSection L (tensorObj M N) (op U) l (tmulSection M N (op U) m n) := by
  let P := (toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M
  let Q := (toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N
  let z : (P ⊗ (toPresheafOfModules X).obj N).obj (op U) := (l ⊗ₜ[Γ(X, U)] m) ⊗ₜ[Γ(X, U)] n
  let z' : ((toPresheafOfModules X).obj L ⊗ Q).obj (op U) := l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n)
  have hR : ((tensorSheafificationComparisonRight P N).val.app (op U)).hom
      (((sheafAdj X).unit.app (P ⊗ (toPresheafOfModules X).obj N)).app (op U) z) =
      tmulSection (tensorObj L M) N (op U) (tmulSection L M (op U) l m) n :=
    sheafification_map_unit_app _ U z
  have hα : (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (α_ ((toPresheafOfModules X).obj L)
        ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N)).hom).val.app (op U)).hom
      (((sheafAdj X).unit.app (P ⊗ (toPresheafOfModules X).obj N)).app (op U) z) =
      ((sheafAdj X).unit.app ((toPresheafOfModules X).obj L ⊗ Q)).app (op U) z' :=
    sheafification_map_unit_app _ U z
  have hL : ((tensorSheafificationComparisonLeft L Q).val.app (op U)).hom
      (((sheafAdj X).unit.app ((toPresheafOfModules X).obj L ⊗ Q)).app (op U) z') =
      tmulSection L (tensorObj M N) (op U) l (tmulSection M N (op U) m n) :=
    sheafification_map_unit_app _ U z'
  have hiso : IsIso (tensorSheafificationComparisonRight P N) :=
    isIso_tensorSheafificationComparisonRight _ _
  have hinv : ∀ w, ((inv (tensorSheafificationComparisonRight P N)).val.app (op U)).hom
      (((tensorSheafificationComparisonRight P N).val.app (op U)).hom w) = w := by
    intro w
    have := congrArg (fun φ => (φ.val.app (op U)).hom w)
      (IsIso.hom_inv_id (tensorSheafificationComparisonRight P N))
    exact this
  rw [← hR]
  change ((tensorSheafificationComparisonLeft L Q).val.app (op U)).hom
    ((((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (α_ ((toPresheafOfModules X).obj L)
        ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N)).hom).val.app (op U)).hom
      (((inv (tensorSheafificationComparisonRight P N)).val.app (op U)).hom
      (((tensorSheafificationComparisonRight P N).val.app (op U)).hom _))) = _
  rw [hinv, hα, hL]


/-- **A morphism out of an iterated sheafified tensor product is determined by its values on
iterated pure tensors.** -/
theorem tensorObj_tensorObj_hom_ext {A B C D : X.Modules}
    (φ ψ : tensorObj (tensorObj A B) C ⟶ D)
    (h : ∀ (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)),
      φ.app U (tmulSection (tensorObj A B) C (op U) (tmulSection A B (op U) a b) c) =
      ψ.app U (tmulSection (tensorObj A B) C (op U) (tmulSection A B (op U) a b) c)) :
    φ = ψ := by
  refine tensorObj_hom_ext φ ψ fun U t c => ?_
  apply section_ext_of_locally
  intro x hx
  obtain ⟨V, hV, hxV, s, hs⟩ := exists_eq_sum_tmulSection A B t x hx
  refine ⟨V, hV, hxV, ?_⟩
  have key : ∀ (χ : tensorObj (tensorObj A B) C ⟶ D),
      D.presheaf.map (homOfLE hV).op (χ.app U (tmulSection (tensorObj A B) C (op U) t c)) =
      ∑ p ∈ s, χ.app V (tmulSection (tensorObj A B) C (op V)
        (tmulSection A B (op V) p.1 p.2) (C.presheaf.map (homOfLE hV).op c)) := by
    intro χ
    rw [homApp_res χ hV, res_tmulSection, hs, tmulSection_finset_sum_left, map_sum]
  rw [key φ, key ψ]
  exact Finset.sum_congr rfl fun p _ => h V p.1 p.2 _

section TensorLift

variable {A B C : X.Modules}

/-- Bilinear data over the structure sheaf on sections, compatible with restriction. -/
structure TensorLiftData (A B C : X.Modules) where
  /-- The bilinear map on sections over each open. -/
  toFun : ∀ U : X.Opens, Γ(A, U) → Γ(B, U) → Γ(C, U)
  /-- Additivity in the first variable. -/
  add_left : ∀ U a a' b, toFun U (a + a') b = toFun U a b + toFun U a' b
  /-- Linearity over `Γ(X, U)` in the first variable. -/
  smul_left : ∀ U (r : Γ(X, U)) a b, toFun U (r • a) b = r • toFun U a b
  /-- Additivity in the second variable. -/
  add_right : ∀ U a b b', toFun U a (b + b') = toFun U a b + toFun U a b'
  /-- Linearity over `Γ(X, U)` in the second variable. -/
  smul_right : ∀ U (r : Γ(X, U)) a b, toFun U a (r • b) = r • toFun U a b
  /-- Compatibility with restriction to a smaller open. -/
  res : ∀ {U V : X.Opens} (h : V ≤ U) a b,
    C.presheaf.map (homOfLE h).op (toFun U a b) =
      toFun V (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b)

/-- The presheaf-level morphism attached to `TensorLiftData`. -/
def TensorLiftData.toPre (β : TensorLiftData A B C) :
    (toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B ⟶
      (toPresheafOfModules X).obj C where
  app U := ModuleCat.MonoidalCategory.tensorLift (β.toFun U.unop) (β.add_left U.unop)
    (β.smul_left U.unop) (β.add_right U.unop) (β.smul_right U.unop)
  naturality {U V} i := ModuleCat.MonoidalCategory.tensor_ext (fun a b => by
    exact (β.res i.unop.le a b).symm)

/-- The morphism out of the sheafified tensor product attached to `TensorLiftData`. -/
def TensorLiftData.lift (β : TensorLiftData A B C) : tensorObj A B ⟶ C :=
  ((sheafAdj X).homEquiv _ C).symm β.toPre

/-- **A morphism built by `TensorLiftData.lift` acts on a pure tensor by the given bilinear
data.** -/
theorem TensorLiftData.lift_app_tmulSection (β : TensorLiftData A B C) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    β.lift.app U (tmulSection A B (op U) a b) = β.toFun U a b := by
  let t₀ : (((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B).obj (op U)) :=
    a ⊗ₜ[Γ(X, U)] b
  have h1 := sheafification_map_unit_app β.toPre U t₀
  have h2 := counit_app_unit_app C U (β.toPre.app (op U) t₀)
  unfold TensorLiftData.lift tmulSection
  rw [Adjunction.homEquiv_counit]
  exact (congrArg (fun z => (((sheafAdj X).counit.app C).val.app (op U)).hom z) h1).trans
    (h2.trans rfl)

end TensorLift

end


end AlgebraicGeometry.Scheme.Modules
