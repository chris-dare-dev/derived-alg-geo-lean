/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport

/-!
# Strict autoequivalence groups acting on slicings

`Aut(D)` is not a group in Lean: `C ≌ C` under composition is associative only
up to natural isomorphism, so it carries no `Group` instance and `MulAction` is
not available. This file takes the cheap way out, deliberately: instead of
quotienting to isomorphism classes, it asks for a group that maps into
endofunctors **strictly**.

That works because **functor composition in Lean *is* strictly associative** —
`C ⥤ C` is an honest monoid under `⋙`. So `StrictAut G C` below is just a
monoid homomorphism `G → (C ⥤ C)` whose functors are triangulated, and the
resulting `MulAction G (Slicing C)` needs no coherence bookkeeping at all.

## What this deliberately does NOT cover

`map_one` and `map_mul` are **equalities of functors**, so `F g ⋙ F g⁻¹ = 𝟭 C`
on the nose: each `F g` is an *isomorphism of categories*, not merely an
equivalence. Many autoequivalences one actually cares about — Serre functors,
spherical twists — satisfy that only up to natural isomorphism, and are
therefore **out of scope here**.

So this is a real restriction, not a reformulation. It buys a strict
`MulAction` today at the cost of generality; the general `Aut(D)` action still
wants the quotient. Do not cite this as "the `Aut` action is formalized". The
stability-foundation ownership record notes this deliberate restriction.

## What it does cover

Everything hard is already in `WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/Slicing/Transport.lean` — `PostnikovTower.mapF`,
`HNFiltration.mapF`, `Slicing.mapEquiv`. This file only supplies the group
packaging: `StrictAut.equiv` turns the strict data into an honest
`Equivalence` (unit and counit are `eqToIso`, and the coherence field
discharges automatically), and the `MulAction` laws are then two `simp`s.

The `MulAction` is a `def`, not an `instance` — `ρ` is unrecoverable by
instance search, so as an `instance` it was dead code. See
`mulActionSlicing`'s own docstring.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

universe w u

/-- A **strict** action of a group `G` on `C` by triangulated autoequivalences:
a monoid hom into `C ⥤ C`, which is a strict monoid under `⋙`.

`map_mul` is contravariant (`F (g * h) = F h ⋙ F g`) because `⋙` is
diagrammatic order: `(F h ⋙ F g).obj = F g ∘ F h`. -/
structure StrictAut (G : Type*) [Group G] (C : Type u) [Category.{w} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The endofunctor attached to a group element. -/
  F : G → (C ⥤ C)
  /-- The unit acts as the identity functor, on the nose. -/
  map_one : F 1 = 𝟭 C
  /-- Multiplication is composition, on the nose. -/
  map_mul : ∀ g h : G, F (g * h) = F h ⋙ F g
  /-- Every `F g` is additive. -/
  additive : ∀ g, (F g).Additive
  /-- Every `F g` commutes with the shift. Unlike its neighbours this field is
  **data**, not a proof — `Functor.CommShift` carries the comparison
  isomorphism — which is why `docBlame` asks for a docstring here and not for
  the `Prop`-valued fields around it. -/
  commShift : ∀ g, (F g).CommShift ℤ
  /-- Every `F g` sends distinguished triangles to distinguished triangles. -/
  triangulated : ∀ g, (F g).IsTriangulated

namespace StrictAut

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {G : Type*} [Group G] (ρ : StrictAut G C)

theorem comp_inv (g : G) : ρ.F g ⋙ ρ.F g⁻¹ = 𝟭 C := by
  rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]

theorem inv_comp (g : G) : ρ.F g⁻¹ ⋙ ρ.F g = 𝟭 C := by
  rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]

theorem obj_inv (g : G) (X : C) : (ρ.F g⁻¹).obj ((ρ.F g).obj X) = X :=
  congrArg (fun H => H.obj X) (ρ.comp_inv g)

theorem obj_self (g : G) (X : C) : (ρ.F g).obj ((ρ.F g⁻¹).obj X) = X :=
  congrArg (fun H => H.obj X) (ρ.inv_comp g)

theorem F_inv_one : ρ.F (1 : G)⁻¹ = 𝟭 C := by rw [inv_one, ρ.map_one]

theorem F_inv_mul (g h : G) : ρ.F (g * h)⁻¹ = ρ.F g⁻¹ ⋙ ρ.F h⁻¹ := by
  rw [mul_inv_rev, ρ.map_mul]

/-- Each `ρ.F g` is an equivalence, with `ρ.F g⁻¹` as a strict inverse.

Unit and counit are `eqToIso`; `Equivalence.mk`'s coherence field discharges
automatically. -/
noncomputable def equiv (g : G) : C ≌ C :=
  CategoryTheory.Equivalence.mk (ρ.F g) (ρ.F g⁻¹)
    (eqToIso (ρ.comp_inv g).symm) (eqToIso (ρ.inv_comp g))

@[simp] theorem equiv_functor (g : G) : (ρ.equiv g).functor = ρ.F g := rfl
@[simp] theorem equiv_inverse (g : G) : (ρ.equiv g).inverse = ρ.F g⁻¹ := rfl

/-- `g` acts on a slicing by moving objects: `(g • s).P φ X = s.P φ (g⁻¹ X)`.

Dual to `relabel`, which moves phases and fixes objects. The `letI`s must state
each instance at the `(ρ.equiv g).functor` form — instance search will not
unfold it to `ρ.F g` — and must be `letI`, not `haveI`, because
`Functor.IsTriangulated` depends on the `CommShift` instance and an opaque
`haveI` breaks the match. -/
noncomputable def actSlicing (g : G) (s : Slicing C) : Slicing C :=
  letI : (ρ.equiv g).functor.Additive := ρ.additive g
  letI : (ρ.equiv g).inverse.Additive := ρ.additive g⁻¹
  letI : (ρ.equiv g).functor.CommShift ℤ := ρ.commShift g
  letI : (ρ.equiv g).inverse.CommShift ℤ := ρ.commShift g⁻¹
  letI : (ρ.equiv g).functor.IsTriangulated := ρ.triangulated g
  letI : (ρ.equiv g).inverse.IsTriangulated := ρ.triangulated g⁻¹
  s.mapEquiv (ρ.equiv g)

@[simp] theorem actSlicing_P (g : G) (s : Slicing C) (φ : ℝ) (X : C) :
    (ρ.actSlicing g s).P φ X = s.P φ ((ρ.F g⁻¹).obj X) := rfl

/-- A strict group of triangulated autoequivalences acts on slicings.

**A `def`, not an `instance`, and that is forced rather than stylistic.** `ρ`
is explicit data appearing neither in the return type `MulAction G (Slicing C)`
nor in any instance-implicit argument, so instance search has nothing to infer
it from: as an `instance` this was unreachable and could never have fired —
the `impossibleInstance` linter's finding, and a real defect, not a style nit.

It would also be the wrong thing to register globally even if it worked, since
the head `MulAction G (Slicing C)` claims *every* group acts on the slicings of
*every* pretriangulated category, for whatever `ρ` search happened to pick.

Bring it into scope at the use site with `letI := ρ.mulActionSlicing`. For an
action `•` can find on its own, use `AutQuot`
(`WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/Slicing/Quotient.lean`), where
the acting object *is* the group.

`@[reducible]` because Lean requires it of any `def` whose type is a class —
Mathlib's reducible-non-instance convention, and what makes the `letI` above
transparent to later instance search. -/
@[reducible]
noncomputable def mulActionSlicing : MulAction G (Slicing C) where
  smul := ρ.actSlicing
  one_smul s := Slicing.ext C (by
    funext φ; funext X
    show (ρ.actSlicing 1 s).P φ X = s.P φ X
    simp [inv_one, ρ.map_one])
  mul_smul g h s := Slicing.ext C (by
    funext φ; funext X
    show (ρ.actSlicing (g * h) s).P φ X = (ρ.actSlicing g (ρ.actSlicing h s)).P φ X
    simp [mul_inv_rev, ρ.map_mul])

end StrictAut

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
