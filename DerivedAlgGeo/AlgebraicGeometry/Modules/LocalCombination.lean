/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.LocallySurjective
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Sections that are locally combinations of a family of global sections

A finite family `σ` of global sections of a module sheaf `G` generates `G` exactly when every
section of `G` is, near every point, a structure-sheaf combination of the restrictions of `σ`.
This file names that condition on one section, `IsLocalCombination`, proves it closed under the
operations a sheafification argument produces -- zero, sums, restriction -- and turns it into the
conclusion a generation theorem wants: the map `free I ⟶ G` classifying `σ` is an epimorphism.

## Why a predicate on one section

Serre's global generation reaches the epimorphism through `epi_of_pointwise_preimages`, which asks
for a local preimage of one section at one point. The section to be handled arrives as a
restriction of a *finite sum of pure tensors* (`exists_eq_sum_tmulSection`), so the argument has to
pass through sums and restrictions before it reaches the pure tensor it can actually compute with.
Stating the condition on a single section, with `Finset.sum_induction` doing the sums, keeps every
one of those steps a lemma here rather than an inline bookkeeping block at the call site.

## The classifying map

`sectionsOfTop` reads a section over `⊤` as a global section in Mathlib's sense, a compatible
family over every open; `freeHomEquiv.symm` then packages the family `σ` as `free I ⟶ G`. The
preimage of a local combination `∑ cₐ • σₐ|_W` is `∑ cₐ • ιFree a (1)`, and that is the whole of
`epi_freeHomEquiv_symm_of_isLocalCombination`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A section over `⊤`, as a global section in Mathlib's sense**: the compatible family of its
restrictions to every open. -/
noncomputable def sectionsOfTop (G : X.Modules) (σ : Γ(G, ⊤)) :
    (show SheafOfModules X.ringCatSheaf from G).sections :=
  PresheafOfModules.sectionsMk (fun _ => G.presheaf.map (homOfLE le_top).op σ)
    (fun _ _ i => resSection_trans G le_top (leOfHom i.unop) σ)

@[simp]
theorem sectionsOfTop_val (G : X.Modules) (σ : Γ(G, ⊤)) (U : X.Opensᵒᵖ) :
    (sectionsOfTop G σ).val U = G.presheaf.map (homOfLE le_top).op σ := rfl

/-- **A section is a local combination of `σ`** when, near every point of its open, it is a
structure-sheaf combination of the restrictions of the family `σ` of sections over `⊤`. -/
def IsLocalCombination (G : X.Modules) {I : Type*} [Fintype I] (σ : I → Γ(G, ⊤))
    {U : X.Opens} (z : Γ(G, U)) : Prop :=
  ∀ x ∈ U, ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ ∃ c : I → Γ(X, W),
    G.presheaf.map (homOfLE hWU).op z = ∑ a, c a • G.presheaf.map (homOfLE le_top).op (σ a)

namespace IsLocalCombination

variable (G : X.Modules) {I : Type*} [Fintype I] (σ : I → Γ(G, ⊤))

theorem zero (U : X.Opens) : IsLocalCombination G σ (0 : Γ(G, U)) := fun x hx =>
  ⟨U, le_rfl, hx, 0, by
    rw [map_zero]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]⟩

variable {G σ}

theorem add {U : X.Opens} {z₁ z₂ : Γ(G, U)} (h₁ : IsLocalCombination G σ z₁)
    (h₂ : IsLocalCombination G σ z₂) : IsLocalCombination G σ (z₁ + z₂) := by
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, c₁, hc₁⟩ := h₁ x hx
  obtain ⟨W₂, hW₂, hxW₂, c₂, hc₂⟩ := h₂ x hx
  refine ⟨W₁ ⊓ W₂, inf_le_left.trans hW₁, ⟨hxW₁, hxW₂⟩, fun a =>
    X.presheaf.map (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)).op (c₁ a) +
      X.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (c₂ a), ?_⟩
  rw [map_add, ← resSection_trans G hW₁ inf_le_left z₁, ← resSection_trans G hW₂ inf_le_right z₂,
    hc₁, hc₂, map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [resSection_smul, resSection_smul, resSection_trans, resSection_trans, add_smul]

theorem finset_sum {U : X.Opens} {κ : Type*} (S : Finset κ) (f : κ → Γ(G, U))
    (h : ∀ p ∈ S, IsLocalCombination G σ (f p)) :
    IsLocalCombination G σ (∑ p ∈ S, f p) :=
  Finset.sum_induction f (fun z => IsLocalCombination G σ z) (fun _ _ => add) (zero G σ U) h

theorem res {U V : X.Opens} (hVU : V ≤ U) {z : Γ(G, U)} (h : IsLocalCombination G σ z) :
    IsLocalCombination G σ (G.presheaf.map (homOfLE hVU).op z) := by
  intro x hx
  obtain ⟨W, hWU, hxW, c, hc⟩ := h x (hVU hx)
  refine ⟨W ⊓ V, inf_le_right, ⟨hxW, hx⟩, fun a =>
    X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op (c a), ?_⟩
  rw [resSection_trans, ← resSection_trans G hWU inf_le_left z, hc, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [resSection_smul, resSection_trans]

end IsLocalCombination

/-- **The classifying map of `σ` evaluates `ιFree a` to the restriction of `σ a`.** -/
theorem freeHomEquiv_symm_sectionsOfTop_ιFree_app_one (G : X.Modules) {I : Type u}
    (σ : I → Γ(G, ⊤)) (a : I) (W : X.Opens) :
    ((SheafOfModules.ιFree a ≫ (show SheafOfModules X.ringCatSheaf from G).freeHomEquiv.symm
        (fun b => sectionsOfTop G (σ b))).val.app (op W)).hom (1 : Γ(X, W))
      = G.presheaf.map (homOfLE le_top).op (σ a) := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe (show SheafOfModules X.ringCatSheaf from G)
    (SheafOfModules.ιFree a ≫ (show SheafOfModules X.ringCatSheaf from G).freeHomEquiv.symm
      (fun b => sectionsOfTop G (σ b))) (op W)
  have h2 : (show SheafOfModules X.ringCatSheaf from G).unitHomEquiv
      (SheafOfModules.ιFree a ≫ (show SheafOfModules X.ringCatSheaf from G).freeHomEquiv.symm
        (fun b => sectionsOfTop G (σ b))) = sectionsOfTop G (σ a) :=
    congrFun ((show SheafOfModules X.ringCatSheaf from G).freeHomEquiv.apply_symm_apply
      (fun b => sectionsOfTop G (σ b))) a
  exact h1.symm.trans (congrArg (fun s => s.val (op W)) h2)

/-- **A family every section is locally a combination of classifies an epimorphism.**

The local preimage of `∑ cₐ • σₐ|_W` under `free I ⟶ G` is `∑ cₐ • ιFree a (1)`; the map is
linear on sections, and `ιFree a` composed with the classifying map is `σ a`. -/
theorem epi_freeHomEquiv_symm_of_isLocalCombination (G : X.Modules) {I : Type u} [Fintype I]
    (σ : I → Γ(G, ⊤))
    (h : ∀ (U : X.Opens) (z : Γ(G, U)), IsLocalCombination G σ z) :
    Epi ((show SheafOfModules X.ringCatSheaf from G).freeHomEquiv.symm
      (fun a => sectionsOfTop G (σ a))) := by
  apply epi_of_pointwise_preimages
  intro U t x hx
  obtain ⟨W, hWU, hxW, c, hc⟩ := h U t x hx
  refine ⟨W, hWU, hxW,
    ∑ a, c a • ((SheafOfModules.ιFree (R := X.ringCatSheaf) a).val.app (op W)).hom
      (1 : X.ringCatSheaf.obj.obj (op W)), ?_⟩
  rw [hc, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Hom.app_smul _ (c a) _).trans
    (congrArg (fun z => c a • z) (freeHomEquiv_symm_sectionsOfTop_ιFree_app_one G σ a W))

end AlgebraicGeometry.Scheme.Modules
