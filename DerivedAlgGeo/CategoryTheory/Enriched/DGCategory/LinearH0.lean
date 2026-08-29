/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Linear.LinearFunctor
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.H0
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory.Linear

/-!
# Linearity of `H⁰`

A `k`-linear dg category has a canonically `k`-linear homotopy category. The
construction uses Mathlib's ordinary `CategoryTheory.Linear` root: degree-zero
cocycles form a submodule, coboundaries form a submodule of the cocycles, and
the Hom-modules of `H⁰` are the resulting quotient modules.

A scalar-preserving dg functor therefore induces a Mathlib-linear functor on
`H⁰`. No separate ordinary category structure is introduced.

This leaf deliberately does not package exactness. The present `DGFunctor` API
does not yet express preservation of the chosen dg shifts and cones from which
`Functor.IsTriangulated` could be proved. Likewise, identifying a general
`H⁰`-Hom quotient with Mathlib's chosen homology object is a separate seam
needed before `IsQuasiEquivalence` can supply full faithfulness on `H⁰`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' w

namespace CategoryTheory

open DGCategoryStruct

namespace H0

variable {k : Type w} [CommRing k] {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)] [DGLinear k C]

/-- Degree-zero cocycles as a `k`-submodule of the degree-zero part of the
Hom-complex. -/
def cocyclesSubmodule (X Y : C) : Submodule k ((dgHom X Y).X 0) where
  carrier := cocycles X Y
  zero_mem' := (cocycles X Y).zero_mem
  add_mem' := (cocycles X Y).add_mem
  smul_mem' c f hf := by
    change ((dgHom X Y).d 0 1).hom (c • f) = 0
    change ((dgHom X Y).d 0 1).hom f = 0 at hf
    rw [DGLinear.d_smul, hf, smul_zero]

/-- The cocycles inherit their module structure from the ambient degree-zero
piece of the Hom-complex. -/
instance cocyclesModule (X Y : C) : Module k (cocycles X Y) := by
  change Module k (cocyclesSubmodule (k := k) X Y)
  infer_instance

/-- Degree-zero coboundaries as a `k`-submodule of the cocycles. -/
def coboundariesSubmodule (X Y : C) : Submodule k (cocycles X Y) where
  carrier := coboundariesIn X Y
  zero_mem' := (coboundariesIn X Y).zero_mem
  add_mem' := (coboundariesIn X Y).add_mem
  smul_mem' c f hf := by
    change ∃ h, ((dgHom X Y).d (-1) 0).hom h = (c • f : cocycles X Y).1
    change ∃ h, ((dgHom X Y).d (-1) 0).hom h = f.1 at hf
    obtain ⟨h, hh⟩ := hf
    refine ⟨c • h, ?_⟩
    rw [DGLinear.d_smul, hh]
    rfl

/-- Each Hom-group of `H⁰ C` is the quotient module of degree-zero cocycles by
degree-zero coboundaries. -/
instance homModule (X Y : H0 C) : Module k (X ⟶ Y) := by
  change Module k
    ((cocyclesSubmodule (k := k) (of C X) (of C Y)) ⧸
      coboundariesSubmodule (k := k) (of C X) (of C Y))
  infer_instance

/-- The canonical Mathlib `k`-linear structure on `H⁰` of a `k`-linear dg
category. -/
instance linear : Linear k (H0 C) where
  smul_comp X Y Z c f g := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g =>
        have h :
            (⟨dgComp 0 0 0 (by omega) (c • f.1) g.1, Z0.comp_mem (c • f).2 g.2⟩ :
                cocycles (of C X) (of C Z)) =
              c • (⟨dgComp 0 0 0 (by omega) f.1 g.1, Z0.comp_mem f.2 g.2⟩ :
                cocycles (of C X) (of C Z)) := by
          apply Subtype.ext
          exact DGLinear.comp_smul_left 0 0 0 (by omega) c f.1 g.1
        exact congrArg
          (fun z : cocycles (of C X) (of C Z) => QuotientAddGroup.mk z) h
  comp_smul X Y Z f c g := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g =>
        have h :
            (⟨dgComp 0 0 0 (by omega) f.1 (c • g.1), Z0.comp_mem f.2 (c • g).2⟩ :
                cocycles (of C X) (of C Z)) =
              c • (⟨dgComp 0 0 0 (by omega) f.1 g.1, Z0.comp_mem f.2 g.2⟩ :
                cocycles (of C X) (of C Z)) := by
          apply Subtype.ext
          exact DGLinear.comp_smul_right 0 0 0 (by omega) c f.1 g.1
        exact congrArg
          (fun z : cocycles (of C X) (of C Z) => QuotientAddGroup.mk z) h

end H0

namespace DGFunctor

variable {k : Type w} [CommRing k] {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [∀ (X Y : D) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [DGLinear k D]

/-- `H⁰` of a scalar-preserving dg functor is a Mathlib-linear functor. -/
instance h0Linear (F : DGFunctor C D) [F.Linear k] : F.h0.Linear k where
  map_smul {X Y} f c := by
    induction f using Quotient.ind with
    | _ f =>
      exact congrArg
        (fun z : cocycles (F.obj (H0.of C X)) (F.obj (H0.of C Y)) => QuotientAddGroup.mk z)
        (Subtype.ext (F.map_smul 0 c f.1))

end DGFunctor

section API

variable {k : Type w} [CommRing k] {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [∀ (X Y : D) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [DGLinear k D]

example : Linear k (H0 C) := inferInstance

example : (DGFunctor.id C).Linear k := inferInstance

example (F : DGFunctor C D) [F.Linear k] : F.h0.Linear k := inferInstance

example {E : Type u'} [DGCategory.{v} E]
    [∀ (X Y : E) (p : ℤ), Module k ((dgHom X Y).X p)] [DGLinear k E]
    (F : DGFunctor C D) (G : DGFunctor D E) [F.Linear k] [G.Linear k] :
    (F.comp G).Linear k := inferInstance

end API

end CategoryTheory
