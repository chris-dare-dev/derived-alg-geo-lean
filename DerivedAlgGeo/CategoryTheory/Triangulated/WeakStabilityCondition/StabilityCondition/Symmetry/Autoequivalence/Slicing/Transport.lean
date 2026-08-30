/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseBounds
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Transporting slicings along a triangulated auto-equivalence

Groundwork for §8's *other* half: the `Aut(D)` action. `G̃L⁺(2, ℝ)` acts by
moving phases while fixing objects; an autoequivalence does the opposite.

The base slicing API has only `HNFiltration.ofIso`, which moves a filtration
along an isomorphism of its *object*. So the three transport definitions here
are built directly, and they are
the substantial part:

* `PostnikovTower.mapF` — push a tower through a triangulated functor. Works
  because `ComposableArrows C n` is a functor category, so the transported
  chain is literally `chain ⋙ F`, and `Functor.IsTriangulated.map_distinguished`
  carries the distinguished triangles.
* `HNFiltration.mapF` — the tower plus unchanged phases; only `semistable`
  needs an argument.
* `Slicing.mapEquiv` — the slicing `X ↦ P φ (Φ⁻¹ X)`. `shift_iff` needs
  `Φ⁻¹` to commute with `⟦1⟧` (hence the `CommShift` hypotheses) and
  `hn_exists` pushes a filtration of `Φ⁻¹ E` forward and lands it on `E` via
  the counit.

The tower and HN operations are stated for `C ⥤ D`; `Slicing.mapEquiv` then
specializes them to the endofunctors needed by the action.

## Why there is no `MulAction` here

Unlike `GLTilde`, the acting object is **not** a group in Lean. `C ≌ C` under
composition is associative only up to natural isomorphism, so it carries no
`Group` instance and `MulAction` is the wrong target. Bridgeland's "`Aut(D)`
acts" is a statement about the induced action on isomorphism classes; a strict
formalisation would need to quotient, or to work with a strictified group of
autoequivalences. That is a design decision, not an oversight.

## What the full stability-condition action still needs

1. `K₀` functoriality — `K₀.map Φ`, via `K₀.lift` and an `IsTriangleAdditive`
   proof.
2. Class-map compatibility: an autoequivalence acts on `WithClassMap C v` only
   together with a `λ : Λ ≃+ Λ` satisfying `v ∘ K₀.map Φ = λ ∘ v`. For `v = id`
   this is forced; in general it is extra data, exactly as `Compatible` is for
   `GLTilde`.
3. Local finiteness under `mapEquiv`. Note this is a *different* problem from
   step 3c: the phase windows do not move at all here, so no uniform-continuity
   argument is needed. What is needed instead is that strict finite length is
   invariant under an equivalence of interval categories — and
   `interval_thinFiniteLength_of_inclusion_strict` does not apply, since it
   compares two `intervalProp`s on the *same* object.

## Why two `@[nolint unusedArguments]`s below, and one in
`CategoryTheory/Triangulated/GrothendieckGroup/Functorial.lean`

The environment linter reports `[F.Additive]` unused by `PostnikovTower.mapF`
and `[Φ.inverse.Additive]` unused by `Slicing.mapEquiv`. Both are true of the
proof terms, and both hypotheses are kept anyway.

Deleting them does not remove the finding — it **moves it one caller up**,
measured 2026-08-05 by doing exactly that and re-running the linter:

| deleted from | the linter then flags |
|---|---|
| `PostnikovTower.mapF` | `HNFiltration.mapF`, which passes it straight through |
| `Slicing.mapEquiv` | `Slicing.mapEquiv_P`, whose *statement* carries it |
| `isTriangleAdditive_of_isTriangulated` (retired, see below) | `K₀.map` |

Six errors before, six after; the build stayed green throughout.

The third row's subject was retired in #487: the stability track's
endofunctor-only `K₀.mapF` and the `isTriangleAdditive_of_isTriangulated`
instance that fed it are gone, superseded by the generic `K₀.map` and
`K₀.isTriangleAdditive_map`. The measurement above is left as recorded rather
than transplanted — it was taken against the retired instance on 2026-08-05 and
has not been re-run against its replacement. What carries over is only the
uncontroversial part: `K₀.isTriangleAdditive_map` carries the same
`@[nolint unusedArguments]` for the same stated reason.

Following the chase to its end amputates the hypothesis from `K₀.map_of`, from
`AutStabilityAction`, and finally from `TriEquiv.iAdd` — a structure field
whose whole purpose is to make the six instances of a triangulated
auto-equivalence travel together.

So the hypothesis set is the interface, not an artefact of how the fields were
discharged: "triangulated functor" here means `Additive` + `CommShift ℤ` +
`IsTriangulated`, every consumer supplies all three, and a later reproof that
does use additivity must not be a breaking signature change.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

universe w u w' u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u'} [Category.{w'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Push a Postnikov tower through a triangulated functor.

Everything is transported structurally: the chain is `chain ⋙ F`, each
triangle is `F.mapTriangle.obj`, and distinguishedness is
`F.map_distinguished`.

`[F.Additive]` is unused by this term and kept regardless — see the module
docstring, which records what deleting it actually does. -/
@[nolint unusedArguments]
noncomputable def PostnikovTower.mapF {E : C} (P : PostnikovTower C E)
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] :
    PostnikovTower D (F.obj E) where
  n := P.n
  chain := P.chain ⋙ F
  triangle := fun i => F.mapTriangle.obj (P.triangle i)
  triangle_dist := fun i => F.map_distinguished _ (P.triangle_dist i)
  triangle_obj₁ := fun i => ⟨F.mapIso (P.triangle_obj₁ i).some⟩
  triangle_obj₂ := fun i => ⟨F.mapIso (P.triangle_obj₂ i).some⟩
  base_isZero := F.map_isZero P.base_isZero
  top_iso := ⟨F.mapIso P.top_iso.some⟩

/-- Push an HN filtration through a triangulated functor.

The phases are untouched — the functor moves objects, not phases — so only
`semistable` carries a hypothesis. -/
noncomputable def HNFiltration.mapF {P : ℝ → ObjectProperty C}
    {P' : ℝ → ObjectProperty D} {E : C}
    (Fil : HNFiltration C P E) (F : C ⥤ D)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hP : ∀ φ X, P φ X → P' φ (F.obj X)) :
    HNFiltration D P' (F.obj E) where
  toPostnikovTower := PostnikovTower.mapF Fil.toPostnikovTower F
  φ := Fil.φ
  hφ := Fil.hφ
  semistable := fun j => hP _ _ (Fil.semistable j)

/-- Transport a slicing along a triangulated auto-equivalence:
`(Φ • s).P φ X = s.P φ (Φ⁻¹ X)`.

Dual to `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.relabel`, which moves phases
and fixes
objects.

`[Φ.inverse.Additive]` is unused by this term and kept regardless: without it
`Φ` is no longer an equivalence of *triangulated* categories, which is what
this definition transports along. See the module docstring. -/
@[nolint unusedArguments]
noncomputable def Slicing.mapEquiv (s : Slicing C) (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.inverse.Additive]
    [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
    [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated] : Slicing C where
  P φ := fun X => s.P φ (Φ.inverse.obj X)
  closedUnderIso φ := ⟨fun e h => ObjectProperty.prop_of_iso _ (Φ.inverse.mapIso e) h⟩
  zero_mem φ := s.zero_mem_of_isZero C φ _ (Φ.inverse.map_isZero (isZero_zero C))
  shift_iff φ X := by
    rw [s.shift_iff φ (Φ.inverse.obj X)]
    exact ⟨fun h => ObjectProperty.prop_of_iso _
             ((Φ.inverse.commShiftIso (1 : ℤ)).app X).symm h,
           fun h => ObjectProperty.prop_of_iso _
             ((Φ.inverse.commShiftIso (1 : ℤ)).app X) h⟩
  hom_vanishing φ₁ φ₂ A B hlt hA hB g := by
    have h := s.hom_vanishing φ₁ φ₂ _ _ hlt hA hB (Φ.inverse.map g)
    exact Φ.inverse.map_injective (by simpa using h)
  hn_exists E := by
    obtain ⟨Fil⟩ := s.hn_exists (Φ.inverse.obj E)
    exact ⟨CategoryTheory.Triangulated.HNFiltration.ofIso C
      (HNFiltration.mapF (P' := fun φ X => s.P φ (Φ.inverse.obj X)) Fil Φ.functor
        (fun φ X h => ObjectProperty.prop_of_iso _ (Φ.unitIso.app X) h))
      (Φ.counitIso.app E)⟩

@[simp]
theorem Slicing.mapEquiv_P (s : Slicing C) (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.inverse.Additive]
    [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
    [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated] (φ : ℝ) (X : C) :
    (s.mapEquiv Φ).P φ X = s.P φ (Φ.inverse.obj X) := rfl

end CategoryTheory.Triangulated
