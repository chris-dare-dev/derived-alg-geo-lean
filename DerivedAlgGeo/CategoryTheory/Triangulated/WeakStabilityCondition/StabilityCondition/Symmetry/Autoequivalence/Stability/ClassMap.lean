/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Slicing.Quotient
-- For `StabilityCondition.WithClassMap.ext`, which lives in `Basic.lean` and
-- is NOT reachable through `Defs.lean` — the structure and its usable
-- extensionality lemma are in different files. See CLAUDE.md §5.

/-!
# The class-map-compatible autoequivalence action

`WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/Stability/Transport.lean` produced `actStabAut`: a well-defined *map* on
`StabilityCondition.WithClassMap C v`, and said so carefully, because the thing
doing the acting was a **pair** `(Φ, lam)` and `AutQuot` groups the `Φ`s alone.

This file bundles the pair and closes that gap. `AutPairQuot v` is a `Group`
and it acts:

```
MulAction (AutPairQuot v) (StabilityCondition.WithClassMap C v)
```

## The class-lattice datum has to be invertible, and that is not a detail

`actStabAut` asks only for `lam : Λ →+ Λ`, which is all a single application
needs. A **group** needs `lam⁻¹`, and nothing produces one: `v` is an arbitrary
additive map, so `lam` is genuinely extra input rather than something recovered
from `Φ`. So the pair carries `lam : Λ ≃+ Λ`.

This is a real strengthening of the hypothesis, not repackaging. A `Φ` equipped
with a non-invertible compatible `lam` still acts as a map — `actStabAut` is
unchanged and still applies — but it is not a member of this group.

Where the inverse comes from is worth seeing, because it is the only step that
uses `Φ` being an equivalence rather than merely a triangulated endofunctor:
`Φ.functor ⋙ Φ.inverse ≅ 𝟭 C` via `unitIso`, and `K₀.map_congr` turns that
natural isomorphism into an *equality* of maps on `K₀`. That is what lets
`compat` be transported to `Φ.symm`.

## What is quotiented, and what deliberately is not

`Φ` is taken modulo natural isomorphism, exactly as in `AutQuot` and for the
same reason — `TriEquiv.act_congr`, resting on a slicing's `closedUnderIso`.

`lam` is **not** quotiented; the setoid asks for it on the nose. Two different
`lam`s can be compatible with the same `Φ` whenever `v` is not surjective, and
they give genuinely different central charges `σ.Z ∘ lam`. Identifying them
would make the action ill defined, so the relation is the conjunction and not a
condition on `Φ` alone.

## What this group is NOT

**It is not `Aut(D)`.** It is not even a quotient or a subgroup of `AutQuot C`
in any way proved here. The evident forgetful map `AutPairQuot v → AutQuot C`
is neither shown injective (different `lam` over the same `Φ`) nor surjective
(a `Φ` admitting no compatible `lam` at all has no preimage). Both statements
are about `v`, and `v` is arbitrary. Say "the group of autoequivalences
equipped with a compatible class-lattice automorphism", never "`Aut(D)` acts on
stability conditions".

The `Φ` component uses the usual relation on autoequivalences: natural
isomorphism of the forward functors. Natural isomorphism of the chosen
inverses follows from uniqueness of right adjoints.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

variable {Λ : Type u'} [AddCommGroup Λ]

/-- A triangulated auto-equivalence together with the class-lattice
automorphism that carries it, and the compatibility tying them to `v`.

`lam` is an `≃+` rather than a `→+` because this is going to be a group; see
the module docstring. -/
structure AutPair (v : K₀ C →+ Λ) where
  /-- The auto-equivalence, with its instances travelling alongside. -/
  Φ : TriEquiv C
  /-- The induced automorphism of the class lattice. Extra data, not recovered
  from `Φ`, because `v` is arbitrary. -/
  lam : Λ ≃+ Λ
  /-- `v ∘ K₀(Φ⁻¹) = lam ∘ v`. -/
  compat : ∀ x : K₀ C, v (K₀.map Φ.e.inverse x) = lam (v x)

namespace AutPair

variable {v : K₀ C →+ Λ}

/-- The identity pair. -/
def id (v : K₀ C →+ Λ) : AutPair v where
  Φ := TriEquiv.id
  lam := AddEquiv.refl Λ
  compat x := by
    show v (K₀.map (𝟭 C) x) = _
    rw [K₀.map_id]
    rfl

/-- `mul a b` is `a * b`: it acts by `b` first, matching
`(a * b) • σ = a • (b • σ)`.

Both components reverse, and they must reverse *together* — the `Φ`s compose
contravariantly through `Equivalence.trans` while the `lam`s compose
covariantly through `AddEquiv.trans`, and it is the two together that make
`compat` survive. -/
def mul (a b : AutPair v) : AutPair v where
  Φ := b.Φ.comp a.Φ
  lam := a.lam.trans b.lam
  compat x := by
    show v (K₀.map (a.Φ.e.inverse ⋙ b.Φ.e.inverse) x) = _
    rw [K₀.map_comp]
    show v (K₀.map b.Φ.e.inverse (K₀.map a.Φ.e.inverse x)) = _
    rw [b.compat, a.compat]
    rfl

/-- The inverse pair.

The only step in this file that uses `Φ` being an *equivalence*: `unitIso`
gives `Φ.functor ⋙ Φ.inverse ≅ 𝟭 C`, and `K₀.map_congr` promotes that
natural isomorphism to an equality of maps on `K₀`. Without it there is no way
to move `compat` across to `Φ⁻¹`. -/
def inv (a : AutPair v) : AutPair v where
  Φ := a.Φ.symm
  lam := a.lam.symm
  compat x := by
    -- `Φ⁻¹ ∘ Φ` is the identity ON `K₀`, as an equality of maps rather than
    -- merely a natural isomorphism. That upgrade is `K₀.map_congr`.
    have key : ∀ y : K₀ C, K₀.map a.Φ.e.inverse (K₀.map a.Φ.e.functor y) = y := by
      have h : (K₀.map a.Φ.e.inverse).comp (K₀.map a.Φ.e.functor)
          = AddMonoidHom.id (K₀ C) := by
        rw [← K₀.map_comp, K₀.map_congr a.Φ.e.unitIso.symm, K₀.map_id]
      exact fun y => DFunLike.congr_fun h y
    show v (K₀.map a.Φ.e.functor x) = a.lam.symm (v x)
    rw [AddEquiv.eq_symm_apply, ← a.compat, key]

/-- Isomorphism of pairs: the auto-equivalences are naturally isomorphic, and
the class-lattice automorphisms are **equal**.

`lam` on the nose, deliberately — see the module docstring. -/
instance setoid (v : K₀ C →+ Λ) : Setoid (AutPair v) where
  r a b := Nonempty (a.Φ.e.functor ≅ b.Φ.e.functor) ∧ a.lam = b.lam
  iseqv :=
    { refl := fun _ => ⟨⟨Iso.refl _⟩, rfl⟩
      symm := fun ⟨⟨p⟩, hl⟩ => ⟨⟨p.symm⟩, hl.symm⟩
      trans := fun ⟨⟨p⟩, hl⟩ ⟨⟨r⟩, hl'⟩ =>
        ⟨⟨p.trans r⟩, hl.trans hl'⟩ }

/-! ## The action -/

/-- The action of a pair, which is `actStabAut` with the datum bundled. -/
noncomputable def act (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  actStabAut a.Φ.e v a.lam.toAddMonoidHom a.compat σ

@[simp] theorem act_slicing (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    (a.act σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing a.Φ.e := rfl

@[simp] theorem act_Z (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    (a.act σ).Z x = σ.Z (a.lam x) := rfl

theorem act_id (σ : StabilityCondition.WithClassMap C v) : (AutPair.id v).act σ = σ := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · exact TriEquiv.act_id σ.slicing
  · ext x; rfl

theorem act_mul (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    (a.mul b).act σ = a.act (b.act σ) := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · exact TriEquiv.act_comp b.Φ a.Φ σ.slicing
  · ext x; rfl

/-- **Descent.** Isomorphic pairs act identically.

The slicing half is `TriEquiv.act_congr`; the charge half is immediate, because
the setoid fixed `lam` on the nose rather than up to anything. -/
theorem act_congr {a b : AutPair v} (h : a ≈ b)
    (σ : StabilityCondition.WithClassMap C v) : a.act σ = b.act σ := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · exact TriEquiv.act_congr h.1.some σ.slicing
  · ext x; rw [act_Z, act_Z, h.2]

end AutPair

/-- Autoequivalences carrying a compatible class-lattice automorphism, modulo
natural isomorphism of the auto-equivalence.

**Not `Aut(D)`** — see the module docstring before citing it as such. -/
def AutPairQuot (v : K₀ C →+ Λ) := _root_.Quotient (AutPair.setoid v)

namespace AutPairQuot

variable {v : K₀ C →+ Λ}

instance group : Group (AutPairQuot v) where
  mul := _root_.Quotient.map₂ AutPair.mul
    (by rintro a a' ⟨⟨p⟩, hl⟩ b b' ⟨⟨r⟩, hl'⟩
        exact ⟨⟨NatIso.hcomp r p⟩,
          show a.lam.trans b.lam = a'.lam.trans b'.lam by rw [hl, hl']⟩)
  one := _root_.Quotient.mk _ (AutPair.id v)
  inv := _root_.Quotient.map AutPair.inv
    (by rintro a a' ⟨⟨p⟩, hl⟩
        exact ⟨⟨TriEquiv.inverseIsoOfFunctorIso p⟩,
          show a.lam.symm = a'.lam.symm by rw [hl]⟩)
  -- As in `AutQuot`: functor composition is strictly associative and `𝟭` is a
  -- strict unit, so the `Φ` halves need only `Iso.refl`. The `lam` halves are
  -- the corresponding `AddEquiv` laws, and only inversion needs a genuine
  -- natural isomorphism -- which is the whole reason for quotienting.
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact _root_.Quotient.sound ⟨⟨Iso.refl _⟩, rfl⟩
  one_mul := by
    rintro ⟨a⟩; exact _root_.Quotient.sound ⟨⟨Iso.refl _⟩, by ext x; rfl⟩
  mul_one := by
    rintro ⟨a⟩; exact _root_.Quotient.sound ⟨⟨Iso.refl _⟩, by ext x; rfl⟩
  inv_mul_cancel := by
    rintro ⟨a⟩
    exact _root_.Quotient.sound
      ⟨⟨a.Φ.e.unitIso.symm⟩,
        show a.lam.symm.trans a.lam = AddEquiv.refl Λ by
          ext x; exact a.lam.apply_symm_apply x⟩

/-- The class of a pair. Explicit return type for the same reason as
`AutQuot.mk`: `AutPairQuot` is a plain `def`, so a bare `_root_.Quotient.mk` leaves
`•` unable to find its instance. -/
def mk (a : AutPair v) : AutPairQuot v := _root_.Quotient.mk _ a

/-- **The `Aut` half of §8, as a group action.**

This is the statement `WeakStabilityCondition/StabilityCondition/Symmetry/Autoequivalence/Stability/Transport.lean` could not make. -/
noncomputable instance mulAction :
    MulAction (AutPairQuot v) (StabilityCondition.WithClassMap C v) where
  smul q σ := _root_.Quotient.liftOn q (fun a => a.act σ) (fun _ _ h => AutPair.act_congr h σ)
  one_smul σ := AutPair.act_id σ
  mul_smul q r σ := by
    induction q using _root_.Quotient.inductionOn with | _ a =>
    induction r using _root_.Quotient.inductionOn with | _ b =>
    exact AutPair.act_mul a b σ

@[simp] theorem mk_smul_slicing (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    (mk a • σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing a.Φ.e := rfl

@[simp] theorem mk_smul_Z (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    (mk a • σ).Z x = σ.Z (a.lam x) := rfl

/-- The `Φ` component, forgetting the class-lattice datum.

A group homomorphism, and **neither injective nor surjective** in general —
both failures are about `v`. Recorded as a `MonoidHom` because it is useful,
not because it identifies this group with `AutQuot C`. -/
def toAutQuot : AutPairQuot v →* AutQuot C where
  toFun := _root_.Quotient.map (fun a => a.Φ) (by
    intro a b h
    change Nonempty (a.Φ.e.functor ≅ b.Φ.e.functor)
    exact h.1)
  map_one' := rfl
  map_mul' := by rintro ⟨a⟩ ⟨b⟩; rfl

end AutPairQuot

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
