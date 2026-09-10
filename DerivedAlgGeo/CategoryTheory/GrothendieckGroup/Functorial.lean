/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Functoriality of the Grothendieck group of an abelian category

`K₀Ab` had no functoriality at all: every map out of it in the tree lands in a fixed abelian group
through `liftOf`, and there was no `K₀Ab A →+ K₀Ab B`. This file supplies it.

## Why the hypothesis is short exactness, not exactness

`K₀Ab` is presented by short exact sequences, so the only thing a functor has to do to induce a map
is carry a short exact sequence to a short exact one. That is weaker than being exact, and it is
exactly what `liftOf` consumes, so `map` takes it as a plain hypothesis in the style of the rest of
this directory. `mapOfExact` is the convenience wrapper for a functor that preserves finite limits
and colimits, where Mathlib's `ShortExact.map_of_exact` discharges it.

## The equivalence case, and what it is for

`congr` upgrades an equivalence of abelian categories to an isomorphism of Grothendieck groups. The
inverse is the equivalence's own inverse functor, and the round trips are `hom_ext` against
`of_iso` on the unit and counit — no computation.

This is the first half of transporting numerical data along an equivalence. The motivating case is
identifying coherent sheaves with the heart of the standard t-structure on their derived category:
the μ-slope data of the Gieseker lane lives on `Coh X`, while the Mukai tilt assembly wants it on a
heart, and a rank or degree homomorphism moves between them by precomposition with `congr`.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {D : Type u₃} [Category.{v₃} D] [Abelian D]

namespace K₀Ab

/-- **The map induced by a functor that preserves short exactness.** -/
noncomputable def map (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact) :
    K₀Ab A →+ K₀Ab B :=
  liftOf (fun X ↦ of (F.obj X)) (fun S hS ↦ of_shortExact (S.map F) (hF S hS))

@[simp]
theorem map_of (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact) (X : A) :
    map F hF (of X) = of (F.obj X) :=
  liftOf_of _ _ X

/-- The identity functor induces the identity. -/
@[simp]
theorem map_id (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map (𝟭 A)).ShortExact) :
    map (𝟭 A) hF = AddMonoidHom.id (K₀Ab A) := by
  ext X
  simp

/-- Induced maps compose. -/
theorem map_comp (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact)
    (G : B ⥤ D) [G.PreservesZeroMorphisms]
    (hG : ∀ S : ShortComplex B, S.ShortExact → (S.map G).ShortExact)
    (hFG : ∀ S : ShortComplex A, S.ShortExact → (S.map (F ⋙ G)).ShortExact) :
    map (F ⋙ G) hFG = (map G hG).comp (map F hF) := by
  ext X
  simp

/-- Naturally isomorphic functors induce the same map. -/
theorem map_congr {F G : A ⥤ B} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact)
    (hG : ∀ S : ShortComplex A, S.ShortExact → (S.map G).ShortExact)
    (e : F ≅ G) : map F hF = map G hG := by
  ext X
  simpa using of_iso (e.app X)

/-- **The map induced by an exact functor.** `ShortExact.map_of_exact` discharges the hypothesis of
`map`, so a functor preserving finite limits and colimits needs no side condition. -/
noncomputable def mapOfExact (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    K₀Ab A →+ K₀Ab B :=
  map F (fun _ hS ↦ hS.map_of_exact F)

@[simp]
theorem mapOfExact_of (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A) :
    mapOfExact F (of X) = of (F.obj X) :=
  map_of _ _ X

section Equivalence

variable (e : A ≌ B)
  [e.functor.PreservesZeroMorphisms] [e.inverse.PreservesZeroMorphisms]

/-- **An equivalence of abelian categories induces an isomorphism of Grothendieck groups.**

Both directions are `mapOfExact`; an equivalence preserves all limits and colimits, so no exactness
side condition survives. The round trips are `of_iso` against the unit and counit. -/
noncomputable def congr : K₀Ab A ≃+ K₀Ab B where
  toFun := mapOfExact e.functor
  invFun := mapOfExact e.inverse
  left_inv := by
    intro x
    have h : (mapOfExact e.inverse).comp (mapOfExact e.functor) = AddMonoidHom.id (K₀Ab A) := by
      ext X
      simpa using (of_iso (e.unitIso.app X)).symm
    exact congrArg (fun (f : K₀Ab A →+ K₀Ab A) ↦ f x) h
  right_inv := by
    intro y
    have h : (mapOfExact e.functor).comp (mapOfExact e.inverse) = AddMonoidHom.id (K₀Ab B) := by
      ext Y
      simpa using of_iso (e.counitIso.app Y)
    exact congrArg (fun (f : K₀Ab B →+ K₀Ab B) ↦ f y) h
  map_add' := map_add _

@[simp]
theorem congr_of (X : A) : congr e (of X) = of (e.functor.obj X) :=
  mapOfExact_of _ X

@[simp]
theorem congr_symm_of (Y : B) : (congr e).symm (of Y) = of (e.inverse.obj Y) :=
  mapOfExact_of _ Y

/-- The isomorphism as an additive hom, for precomposition. -/
noncomputable abbrev congrHom : K₀Ab A →+ K₀Ab B := (congr e).toAddMonoidHom

theorem congrHom_of (X : A) : congrHom e (of X) = of (e.functor.obj X) :=
  congr_of e X

end Equivalence

end K₀Ab

end CategoryTheory
