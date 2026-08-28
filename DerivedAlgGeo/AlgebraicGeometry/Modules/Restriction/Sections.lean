/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion

/-!
# Restricting a section of a module sheaf

Four facts about `M.presheaf.map` on a scheme, each one or two lines and each stated at the
generality it actually has: any scheme, any `X.Modules`. Nothing here mentions `Proj`, a grading,
or quasi-coherence.

## Why they are named at all

They are the kind of step a proof takes without comment until it takes it forty times. The
`#585` glue composes restrictions constantly, and `rw` cannot be used on goals carrying
`show`-ascription residue, so each composition has to be available as a term. `presheaf_map_square_eq`
has the same origin on the coherence side: in a clean context its rewrites fire, while at the use
site the goal carries a transparency defect and only `exact` works.

## Why they are here rather than where they were first needed

`#824`. `resSection_trans`, `resSection_smul` and `homApp_res` were stated inside
`Proj/Modules/Glue.lean` and `presheaf_map_square_eq` inside
`CoherentSheaf/Pushforward/BaseChange.lean`, in each case because that was the proof that first
wanted them. Three of the four were then stated over `Proj 𝒜` despite the proofs never using the
grading — `resSection_smul` is `Scheme.Modules.map_smul` verbatim — so the next lane needing them
elsewhere would have re-proved them rather than found them.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Restriction composes.** -/
theorem resSection_trans (F : X.Modules) {U V W : X.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op x)
      = F.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **Restriction is semilinear over restriction of scalars.** -/
theorem resSection_smul (F : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) (x : Γ(F, U)) :
    F.presheaf.map (homOfLE h).op (r • x)
      = X.presheaf.map (homOfLE h).op r • F.presheaf.map (homOfLE h).op x :=
  Scheme.Modules.map_smul F _ r x

/-- **A morphism of module sheaves commutes with restriction.** -/
theorem homApp_res {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U)
    (x : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U x) = φ.app V (M.presheaf.map (homOfLE h).op x) :=
  (NatTrans.naturality_apply φ.mapPresheaf (homOfLE h).op x).symm

/-- **Any two ways round a square of restrictions agree.**

`Opens` is a poset, so the two composites are `M.presheaf.map` of parallel morphisms and
`Subsingleton.elim` settles it. -/
theorem presheaf_map_square_eq (M : X.Modules) {A B C D : X.Opens}
    (α : op A ⟶ op B) (β : op B ⟶ op C) (γ : op A ⟶ op D) (δ : op D ⟶ op C) (x : Γ(M, A)) :
    (M.presheaf.map β).hom ((M.presheaf.map α).hom x)
      = (M.presheaf.map δ).hom ((M.presheaf.map γ).hom x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  exact congrArg (fun φ => (M.presheaf.map φ).hom x) (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Modules
