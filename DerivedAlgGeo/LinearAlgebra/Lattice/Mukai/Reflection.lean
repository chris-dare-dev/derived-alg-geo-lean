/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.Reflection
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-!
# Reflection in a spherical class

For a vector `s` of a Mukai extension with `⟪s, s⟫ = -2`, the map

```
ρ_s(v) = v + ⟪v, s⟫ • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the lattice rather than on
its rationalisation. This is the only place `IsSpherical` is used below, and it
is used exactly once, in `reflect_reflect`.

**This is not the spherical twist.** On a K3 surface, the twist `T_E` of
Seidel–Thomas acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this file exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here. `reflect` is a map
of a lattice built from a bilinear form, and every theorem below is a theorem
about **an arbitrary symmetric bilinear `ℤ`-lattice**, true whether or not any
surface exists — the same discipline `Mukai/Basic.lean` states in its own
docstring.

Every argument below is bilinearity, symmetry, or the single hypothesis
`⟪s,s⟫ = -2`, and none of it is about this carrier. It is therefore proved
once, over an arbitrary form, in `BilinearForm/Reflection.lean`, and this file
specialises it at `pairingBilin b`. There is one reflection, not two, and the
record of which hypothesis does what lives with the general statement.

What stays here is the part that is genuinely about the Mukai extension:
`IsSpherical` as the name for `⟪s,s⟫ = -2`, and the preservation of the
distinguished classes `Mukai/Basic.lean` defines.

## Main results

* `reflectHom` — `ρ_s` as a `ℤ`-linear endomorphism, for arbitrary `s`.
* `reflect_reflect` — `ρ_s` is an involution when `s` is spherical.
* `pairing_reflect_reflect` — `ρ_s` preserves the pairing (symmetric `b`).
* `reflectEquiv` — the resulting `ℤ`-linear automorphism.
* `reflectIsometry` — the same map as an isometry of `pairingBilin`.
* `reflect_self` — `ρ_s s = -s`, and `reflect_of_pairing_eq_zero` — `ρ_s`
  fixes `s^⊥` pointwise. Together these say `ρ_s` is a *reflection* rather
  than merely an involutive isometry.
* `IsSpherical.reflect`, `IsIsotropic.reflect`, `expectedDim_reflect` — the
  distinguished classes of `Mukai/Basic.lean` are preserved.
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-! ### The map

`Mukai.reflect` is `BilinearForm.reflect` at `pairingBilin b`. The name is kept
because four `SphericalTwist` modules spell it, and because "reflection in a
spherical class" is the application's word for it. -/

/-- Reflection in `s`: `ρ_s(v) = v + ⟪v, s⟫ • s`, specialising
`BilinearForm.reflect` to the Mukai pairing. -/
def reflect (s v : MukaiLattice N) : MukaiLattice N :=
  BilinearForm.reflect (pairingBilin b) s v

/-- Not `@[simp]`: unfolding `reflect` everywhere would put `reflect_zero`,
`reflect_self` and `reflect_neg_left` out of simp-normal form. Rewrite with it
explicitly. -/
theorem reflect_apply (s v : MukaiLattice N) :
    reflect b s v = v + pairing b v s • s :=
  rfl

@[simp]
theorem reflect_zero (s : MukaiLattice N) : reflect b s 0 = 0 :=
  BilinearForm.reflect_zero _ s

theorem reflect_add (s v w : MukaiLattice N) :
    reflect b s (v + w) = reflect b s v + reflect b s w :=
  BilinearForm.reflect_add _ s v w

theorem reflect_smul (a : ℤ) (s v : MukaiLattice N) :
    reflect b s (a • v) = a • reflect b s v :=
  BilinearForm.reflect_smul _ a s v

theorem reflect_neg (s v : MukaiLattice N) :
    reflect b s (-v) = -reflect b s v :=
  BilinearForm.reflect_neg _ s v

/-- `ρ_s` as a `ℤ`-linear endomorphism of the Mukai extension.

No hypothesis on `s`: additivity is bilinearity of `pairing`, nothing more. -/
def reflectHom (s : MukaiLattice N) : MukaiLattice N →ₗ[ℤ] MukaiLattice N :=
  BilinearForm.reflectHom (pairingBilin b) s

@[simp]
theorem reflectHom_apply (s v : MukaiLattice N) :
    reflectHom b s v = reflect b s v :=
  rfl

/-! ### The pairing against `s`

`IsSpherical b s` is by definition `selfPairing b s = -2`, and
`pairingBilin b s s` reduces to `selfPairing b s`, so a sphericity hypothesis is
accepted directly wherever the general theory asks for `B s s = -2`. -/

/-- Reflecting reverses the pairing against `s` itself. This is where
`⟪s, s⟫ = -2` is spent. -/
theorem pairing_reflect_right (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = -pairing b v s :=
  BilinearForm.apply_reflect_right (pairingBilin b) s hs v

/-! ### Involutivity -/

/-- **`ρ_s` is an involution** when `s` is spherical. -/
theorem reflect_reflect (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflect b s (reflect b s v) = v :=
  BilinearForm.reflect_reflect (pairingBilin b) s hs v

theorem reflect_involutive (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Involutive (reflect b s) :=
  reflect_reflect b s hs

theorem reflect_bijective (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Bijective (reflect b s) :=
  (reflect_involutive b s hs).bijective

/-- `ρ_s` as a `ℤ`-linear automorphism, with itself as inverse. -/
def reflectEquiv (s : MukaiLattice N) (hs : IsSpherical b s) :
    MukaiLattice N ≃ₗ[ℤ] MukaiLattice N :=
  BilinearForm.reflectEquiv (pairingBilin b) s hs

@[simp]
theorem reflectEquiv_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflectEquiv b s hs v = reflect b s v :=
  rfl

@[simp]
theorem reflectEquiv_symm_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    (reflectEquiv b s hs).symm v = reflect b s v :=
  rfl

/-! ### The reflection property

`reflect_self` and `reflect_of_pairing_eq_zero` are what distinguish a
reflection from an arbitrary involutive isometry: the `-1` eigenspace is
spanned by `s` and the `+1` eigenspace contains `s^⊥`. -/

/-- `ρ_s s = -s`. Needs sphericity but not symmetry. -/
@[simp]
theorem reflect_self (s : MukaiLattice N) (hs : IsSpherical b s) :
    reflect b s s = -s :=
  BilinearForm.reflect_self (pairingBilin b) s hs

/-- `ρ_s` fixes `s^⊥` pointwise. No hypothesis on `s` at all. -/
theorem reflect_of_pairing_eq_zero {s v : MukaiLattice N}
    (h : pairing b v s = 0) :
    reflect b s v = v :=
  BilinearForm.reflect_of_apply_eq_zero (pairingBilin b) h

/-- The reflected vector lies in `s^⊥` exactly when the original one does. -/
theorem pairing_reflect_eq_zero_iff (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = 0 ↔ pairing b v s = 0 :=
  BilinearForm.apply_reflect_eq_zero_iff (pairingBilin b) s hs v

/-! ### Isometry

The first statements in this file to need symmetry of `b`. -/

/-- **`ρ_s` preserves the Mukai pairing.** -/
theorem pairing_reflect_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v w : MukaiLattice N) :
    pairing b (reflect b s v) (reflect b s w) = pairing b v w :=
  BilinearForm.apply_reflect_reflect (pairingBilin b)
    (fun x y => pairing_comm b hb x y) s hs v w

/-- `ρ_s` preserves `⟪v, v⟫`. -/
theorem selfPairing_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    selfPairing b (reflect b s v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing]
  exact pairing_reflect_reflect b hb s hs v v

/-- `ρ_s` as an isometry of the bundled Mukai form. -/
def reflectIsometry (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) :
    pairingBilin b →bᵢ pairingBilin b :=
  BilinearForm.reflectIsometry (pairingBilin b)
    (fun x y => pairing_comm b hb x y) s hs

@[simp]
theorem reflectIsometry_apply (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    reflectIsometry b hb s hs v = reflect b s v :=
  rfl

/-! ### The distinguished classes are preserved

This is the part that is genuinely about the Mukai extension rather than about
an arbitrary form: `Mukai/Basic.lean` names these conditions and downstream
code rewrites with them rather than unfolding to `selfPairing`. -/

theorem IsSpherical.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsSpherical b v) :
    IsSpherical b (Mukai.reflect b s v) := by
  rw [isSpherical_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem IsIsotropic.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsIsotropic b v) :
    IsIsotropic b (Mukai.reflect b s v) := by
  rw [isIsotropic_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem expectedDim_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    expectedDim b (reflect b s v) = expectedDim b v := by
  rw [expectedDim, expectedDim, selfPairing_reflect b hb s hs]

/-! ### Reflection in `-s`

`IsSpherical.neg` says `-s` is spherical whenever `s` is, so both reflections
exist; they are the same map, because the sign enters the formula twice. -/

@[simp]
theorem reflect_neg_left (s v : MukaiLattice N) :
    reflect b (-s) v = reflect b s v :=
  BilinearForm.reflect_neg_left (pairingBilin b) s v

end Mukai
