/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Flat.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-!
# Flatness of a module sheaf over a morphism

`Scheme.Modules.IsFlatOver p M` says that `M` is flat over the base along
`p : X ⟶ S`, stalkwise: at every point of `X`, the stalk of `M` is flat as a
module over the corresponding stalk of `S`, restricted along the local-ring
map `p` induces.

This is a property of one module sheaf and one morphism. It needs no derived
category, no moduli problem and no perfectness notion, and it is used before
any of them: Tor-amplitude models, geometric fibers and base-change arguments
all ask for flat terms. It lives with `X.Modules` for that reason — the
carrier in its public type is a module sheaf, and `moduleStalkFunctor`, the
only other repository construction it mentions, is the neighbouring
`Modules/Pullback/Stalk.lean`.

Flatness over the identity is equivalent to flatness at each module stalk,
and is preserved by indexed coproducts of module sheaves.

It previously sat in `Moduli/PerfectComplex/Relative.lean`, where its first
consumer was; see `docs/architecture/cutover-ledger.md`, finding 11.

## Not a morphism-flatness predicate

`Mathlib.AlgebraicGeometry.Morphisms.Flat` is a different subject: it asks
that the *morphism* be flat, which is this condition for the structure sheaf
alone. Nothing here specializes to or is implied by that class, and no
instance relates them.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

namespace Scheme

/-- A module sheaf on `X` is flat over `S` when every stalk, restricted along
the local-ring map induced by `p`, is a flat module over the corresponding
stalk of `S`. -/
def Modules.IsFlatOver {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) : Prop :=
  ∀ x : X, Module.Flat (S.presheaf.stalk (p x))
    ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((Scheme.Modules.moduleStalkFunctor X x).obj M))

/-- Flatness over the identity morphism is ordinary flatness at every module stalk. -/
theorem Modules.isFlatOverId_iff_stalkwiseFlat
    (X : Scheme.{u}) (M : X.Modules) :
    Modules.IsFlatOver (𝟙 X) M ↔
      ∀ x : X, Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := by
  constructor
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver] at h
    rw [Scheme.Hom.stalkMap_id] at h
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M)) at h
    letI : Module.Flat (X.presheaf.stalk x)
        ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
          ((Modules.moduleStalkFunctor X x).obj M)) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv.symm
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver]
    rw [Scheme.Hom.stalkMap_id]
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M))
    letI : Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv

/-- The stalk of a sheaf coproduct is a direct sum of its module stalks.
Direct sums of flat modules are flat, so identity-relative flatness is closed under coproducts. -/
theorem Modules.isFlatOverId_coprod (X : Scheme.{u}) {I : Type u}
    (G : I → X.Modules) (hG : ∀ i, Modules.IsFlatOver (𝟙 X) (G i)) :
    Modules.IsFlatOver (𝟙 X) (∐ G) := by
  apply (Modules.isFlatOverId_iff_stalkwiseFlat X (∐ G)).2
  intro x
  letI : DecidableEq I := Classical.decEq I
  let F : Discrete I ⥤ X.Modules := Discrete.functor G
  let Z : I → ModuleCat.{u} (X.presheaf.stalk x) :=
    fun i => (Modules.moduleStalkFunctor X x).obj (G i)
  haveI : PreservesColimitsOfShape (Discrete I) (Modules.moduleStalkFunctor X x) :=
    Modules.moduleStalkFunctor_preservesColimitsOfShape X x I
  let e₁ : (Modules.moduleStalkFunctor X x).obj (colimit F) ≅
      colimit (F ⋙ Modules.moduleStalkFunctor X x) :=
    preservesColimitIso (Modules.moduleStalkFunctor X x) F
  let e₂ : colimit (F ⋙ Modules.moduleStalkFunctor X x) ≅
      colimit (Discrete.functor Z) :=
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete G (Modules.moduleStalkFunctor X x))
  let e₃ := ModuleCat.coprodIsoDirectSum Z
  let e : (Modules.moduleStalkFunctor X x).obj (colimit F) ≅
      ModuleCat.of (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) :=
    e₁ ≪≫ e₂ ≪≫ e₃
  have hflat : Module.Flat (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) := by
    apply Module.Flat.directSum_iff.mpr
    intro i
    exact ((Modules.isFlatOverId_iff_stalkwiseFlat X (G i)).mp (hG i)) x
  change Module.Flat (X.presheaf.stalk x)
    ((Modules.moduleStalkFunctor X x).obj (colimit F))
  letI : Module.Flat (X.presheaf.stalk x) (DirectSum I (fun i => ↑(Z i))) := hflat
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end Scheme

end AlgebraicGeometry
