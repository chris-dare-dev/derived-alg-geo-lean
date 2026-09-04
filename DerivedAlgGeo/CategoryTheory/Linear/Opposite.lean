/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# `R`-linearity of the opposite category

The `R`-linear counterparts of `instPreadditiveOpposite` and `Functor.op_additive`
(`Mathlib/CategoryTheory/Preadditive/Opposite.lean`): `Linear R Cᵒᵖ`, `Functor.op_linear`,
and the scalar simp lemmas relating `op` and `unop`. Mathlib lacks them at the pin; they
are written to be upstreamable to `Mathlib/CategoryTheory/Linear/`. The linearity of the
opposite shift is in `CategoryTheory/Triangulated/Opposite/Linear.lean`.
-/


namespace CategoryTheory

open Opposite

section LinearOpposite

variable (R : Type*) [Semiring R] (C : Type*) [Category C] [Preadditive C]
  [Linear R C]

/-- The `R`-module structure on `X ⟶ Y` in `Cᵒᵖ`, built over the `AddCommGroup`
that `Preadditive Cᵒᵖ` already installed.

Split out from `linearOpposite` rather than inlined so that each axiom can be
stated with an explicit `show`: inside a structure instance the `smul` field is
not yet available to `simp`, which therefore makes no progress on any of the
six goals. -/
instance homModuleOpposite (X Y : Cᵒᵖ) : Module R (X ⟶ Y) where
  smul r f := (r • f.unop).op
  one_smul f := Quiver.Hom.unop_inj (by
    show (1 : R) • f.unop = f.unop
    rw [one_smul])
  mul_smul r s f := Quiver.Hom.unop_inj (by
    show (r * s) • f.unop = r • (s • f.unop)
    rw [mul_smul])
  smul_zero r := Quiver.Hom.unop_inj (by
    show r • (0 : X ⟶ Y).unop = (0 : X ⟶ Y).unop
    simp)
  smul_add r f g := Quiver.Hom.unop_inj (by
    show r • (f + g).unop = ((r • f.unop).op + (r • g.unop).op).unop
    simp [smul_add])
  add_smul r s f := Quiver.Hom.unop_inj (by
    show (r + s) • f.unop = ((r • f.unop).op + (s • f.unop).op).unop
    simp [add_smul])
  zero_smul f := Quiver.Hom.unop_inj (by
    show (0 : R) • f.unop = (0 : X ⟶ Y).unop
    simp)

/-- **The opposite of an `R`-linear category is `R`-linear.**

The `R`-linear counterpart of `Preadditive Cᵒᵖ`, and the missing instance
`ShiftedHom.opEquiv`'s `smul` lemmas and the `k`-linear Yoneda `ShiftSequence`
both need. Scalars act through `unop`; the two compatibility fields swap
pre- and post-composition, because composition in `Cᵒᵖ` does. -/
instance linearOpposite : Linear R Cᵒᵖ where
  homModule := homModuleOpposite R C
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (by
    show g.unop ≫ (r • f.unop) = r • (g.unop ≫ f.unop)
    rw [Linear.comp_smul])
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (by
    show (r • g.unop) ≫ f.unop = r • (g.unop ≫ f.unop)
    rw [Linear.smul_comp])

variable {R C}

@[simp]
theorem unop_smul {X Y : Cᵒᵖ} (r : R) (f : X ⟶ Y) : (r • f).unop = r • f.unop :=
  rfl

@[simp]
theorem op_smul {X Y : C} (r : R) (f : X ⟶ Y) : (r • f).op = r • f.op :=
  rfl

end LinearOpposite

section OppositeFunctor

/-- The opposite of an `R`-linear functor is `R`-linear.

The counterpart of `Functor.op_additive`, and like it the proof body is empty:
with `linearOpposite` in scope, scalars on both sides are the ones on `C` and
`D` wrapped in `op`, so the field is closed by the tactic default.

Two spelling constraints, both worth recording because neither is obvious.
Section variables are included in order of first use, so an `[F.Linear R]`
binder introduces `R` only *after* `[Linear R C]` would have had to be
included — hence every binder is written out rather than taken from a
`variable` block. And declaring into the `Functor` namespace makes a bare
`Linear` resolve to `Functor.Linear`, so the category-level instances have to
be qualified. -/
instance Functor.op_linear {R : Type*} [Semiring R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Linear R] : F.op.Linear R where

end OppositeFunctor

end CategoryTheory
