/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The pullback of a constant sheaf is constant

`Sheaf.H` is `Ext` out of the constant sheaf `ℤ`, so comparing the cohomology of a space with
that of a closed subspace means moving that constant sheaf across the adjunction
`f⁻¹ ⊣ f_*`. This file supplies the half of that comparison which says the constant sheaf is
where it should be after the move.

## What the pin has, and what it does not

`Sites/ConstantSheaf.lean` commutes `constantSheaf` with a change of *coefficients*
(`constantCommuteCompose`) and across an *equivalence* of sites (`equivCommuteConstant'`).
Neither covers a general continuous functor, which is what a morphism of spaces induces, and
that is the gap this file closes.

## Both proofs are adjoint uniqueness

`constantSheaf` is a left adjoint, with right adjoint the global sections functor
(`constantSheafΓAdj`), and `sheafPullback` is a left adjoint, with right adjoint
`sheafPushforwardContinuous`. So `constantSheaf ⋙ sheafPullback` is a left adjoint to
`sheafPushforwardContinuous ⋙ Γ`, and the only thing to check is that this composite is the
global sections functor of the second site. It is, for the reason global sections always
survive a pushforward: `Γ` is sections over the terminal object and the pushforward evaluates
at `G.obj ⊤`, so the two agree exactly when `G.obj ⊤` is again terminal. `leftAdjointUniq`
then does the rest.

That hypothesis is what a morphism of spaces supplies and why it is stated rather than
assumed away: for `Opens.map f` the top open pulls back to the top open.
-/

universe u v u₂ v₂

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J K]
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasLeftKanExtension F]

/-- **Global sections do not see the pushforward.** `Γ` is sections over the terminal object and
the pushforward evaluates at `G.obj ⊤`, so the two agree once `G.obj ⊤` is again terminal; the
middle comparison is the identity because `(G_* F)` at `⊤` *is* `F` at `G.obj ⊤`. -/
noncomputable def sheafPushforwardΓIso [HasTerminal C] [HasTerminal D]
    (hG : IsTerminal (G.obj (⊤_ C))) :
    G.sheafPushforwardContinuous A J K ⋙ Sheaf.Γ J A ≅ Sheaf.Γ K A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections J A terminalIsTerminal) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    (Sheaf.ΓNatIsoSheafSections K A hG).symm

/-- **The pullback of a constant sheaf is constant.** Both sides are left adjoints — the first to
`sheafPushforwardContinuous ⋙ Γ`, the second to `Γ` — and `sheafPushforwardΓIso` identifies those
two right adjoints. -/
noncomputable def constantSheafCompSheafPullbackIso [HasTerminal C] [HasTerminal D]
    (hG : IsTerminal (G.obj (⊤_ C))) :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  (((constantSheafΓAdj J A).comp (G.sheafAdjunctionContinuous A J K)).ofNatIsoRight
    (sheafPushforwardΓIso G A hG)).leftAdjointUniq (constantSheafΓAdj K A)

end CategoryTheory
