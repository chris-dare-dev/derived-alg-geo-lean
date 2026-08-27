/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Lattice
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

/-!
# The Euler radical against the kernel of the Mukai vector

`CategoricalCharge` records that the numerical quotient is bypassed: `N` is
documented as `K(X)/≡`, the lane quotients it again by `leftRadical`, and the
only geometric class map in the tree lands in that quotient while
`numericalCharge` is defined on `N`.  Closing that gap is the statement
`leftRadical ≤ ker mukaiVectorHom`, and this file settles what it costs.

## The two inclusions are not equally cheap

One is free.  `mukaiForm_eq_neg_chi₂` already identifies the Mukai form with
`−χ₂` under `SatisfiesHRR` and `IsK3`, so a class whose Mukai vector vanishes
pairs to zero against everything: `ker_le_leftRadical` needs no hypothesis
beyond those two.

The other is **not free, and it is not true as stated**.  Membership in
`leftRadical` gives `∀ F, mukaiForm E F = 0`, which says `mukaiVectorHom E`
pairs to zero against the *image* of `mukaiVectorHom` — not against all of
`Mukai.MukaiLattice Λ`.  Concluding `mukaiVectorHom E = 0` from that is exactly
a nondegeneracy statement about the Mukai pairing restricted to that image, and
nothing in this repository proves one: the only nondegeneracy results in the
tree are for the *real* form (`RealFormSignature`, `PeriodDomain`), and the
integral `pairingBilin` has none.

So it is carried as a named hypothesis, `DetectsRadical`, in the way
`rank_nonneg` and `degree_pos_of_rank_zero` are fields rather than pretended
theorems.  For an actual K3 it is discharged by unimodularity of the Mukai
lattice; that is geometry this lane does not have yet.

## What the hypothesis buys

`mukaiVectorQuotient` — the Mukai vector descended to
`NumericalVarietyData.NumericalQuotient`, which is the quotient the geometric
class map actually lands in.  That is the missing link named in
`CategoricalCharge`'s "what is still supplied, not proved" section.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace K3

variable {A : Type u} {N : Type v} {Λ : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [AddCommGroup Λ]
variable {V : NumericalVarietyData 2 A N}

namespace AdditiveMukaiData

variable (D : AdditiveMukaiData V Λ)

/-- The Mukai form vanishes against every class exactly when the Euler pairing
does.

This is `mukaiForm_eq_neg_chi₂` with the sign and the `ℚ`-cast discharged, and
it is the only bridge either inclusion below uses. -/
theorem mukaiForm_eq_zero_iff_chi₂_eq_zero
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E F : N) :
    D.mukaiForm E F = 0 ↔ V.chi₂ E F = 0 := by
  constructor
  · intro h
    have := D.mukaiForm_eq_neg_chi₂ hHRR hK3 E F
    rw [h] at this
    simpa using this.symm
  · intro h
    have := D.mukaiForm_eq_neg_chi₂ hHRR hK3 E F
    rw [h] at this
    exact_mod_cast this

/-- **The free inclusion.** A class whose Mukai vector vanishes lies in the
Euler radical.

No nondegeneracy is involved: the Mukai form is the pairing pulled back along
the Mukai vector, so a vanishing vector makes it vanish in the first argument
outright. -/
theorem ker_le_leftRadical (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) :
    AddSubgroup.toIntSubmodule D.mukaiVectorHom.ker ≤ V.leftRadical := by
  intro E hE
  rw [V.mem_leftRadical_iff]
  intro F
  rw [← D.mukaiForm_eq_zero_iff_chi₂_eq_zero hHRR hK3]
  have hE' : D.mukaiVectorHom E = 0 := AddMonoidHom.mem_ker.mp hE
  show Mukai.pairingBilin D.b (D.mukaiVectorHom E) (D.mukaiVectorHom F) = 0
  rw [hE', map_zero, LinearMap.zero_apply]

/-- **The hypothesis the other inclusion needs.** The Mukai vector detects the
Euler radical: a class pairing to zero against the whole image of the Mukai
vector has vanishing Mukai vector.

This is nondegeneracy of `Mukai.pairingBilin` restricted to the image of
`mukaiVectorHom`, phrased on `N` so that no submodule of the Mukai lattice has
to be named.  It is **supplied**, not proved — see the module docstring. -/
def DetectsRadical : Prop :=
  ∀ E : N, (∀ F : N, D.mukaiForm E F = 0) → D.mukaiVectorHom E = 0

/-- **`DetectsRadical` reduces to three concrete conditions**, so it is not
merely the conclusion renamed.

Read off the pairing formula
`⟨(r, c, s), (r', c', s')⟩ = b c c' − r·s' − r'·s`:

* pairing against a **point class** `(0, 0, 1)` returns `−r`, so `r = 0`;
* pairing against a **rank-one class with vanishing `c₁`** — `(1, 0, s')`, which
  is the structure sheaf, where `s' = 1` on a K3 — then returns `−s`, so `s = 0`;
* what survives is `b c (c₁ F) = 0` for every `F`, so nondegeneracy of `b`
  against realized Chern classes gives `c = 0`.

The first two are witnessed by actual sheaves and the third is a statement about
`b` alone. Note the second is stated for an arbitrary third coordinate: `O_X` has
Mukai vector `(1, 0, 1)`, not `(1, 0, 0)`, and demanding the latter would be a
condition no sheaf satisfies. -/
theorem detectsRadical_of
    (hpoint : ∃ E : N, D.mukaiVectorHom E = (0, 0, 1))
    (hline : ∃ (E : N) (s : ℤ), D.mukaiVectorHom E = (1, 0, s))
    (hb : ∀ c : Λ, (∀ F : N, D.b c (D.c₁ F) = 0) → c = 0) :
    D.DetectsRadical := by
  intro E hE
  have hpair : ∀ F : N,
      Mukai.pairing D.b (D.mukaiVectorHom E) (D.mukaiVectorHom F) = 0 := hE
  obtain ⟨Ept, hpt⟩ := hpoint
  obtain ⟨Eln, s', hln⟩ := hline
  have hr : (D.mukaiVectorHom E).1 = 0 := by
    have := hpair Ept
    rw [hpt] at this
    simp only [Mukai.pairing, map_zero] at this
    linarith
  have hs : (D.mukaiVectorHom E).2.2 = 0 := by
    have := hpair Eln
    rw [hln] at this
    simp only [Mukai.pairing, map_zero] at this
    rw [hr] at this
    linarith
  have hc : (D.mukaiVectorHom E).2.1 = 0 := by
    refine hb _ fun F => ?_
    have := hpair F
    simp only [Mukai.pairing] at this
    rw [hr, hs] at this
    simpa using this
  refine Prod.ext hr (Prod.ext hc hs)

/-- **The inclusion that closes the gap**, given `DetectsRadical`. -/
theorem leftRadical_le_ker (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V)
    (hdet : D.DetectsRadical) :
    V.leftRadical ≤ AddSubgroup.toIntSubmodule D.mukaiVectorHom.ker := by
  intro E hE
  refine AddMonoidHom.mem_ker.mpr (hdet E fun F => ?_)
  rw [D.mukaiForm_eq_zero_iff_chi₂_eq_zero hHRR hK3]
  exact (V.mem_leftRadical_iff E).mp hE F

/-- Under `DetectsRadical` the two submodules agree, so the Euler radical *is*
the kernel of the Mukai vector. -/
theorem leftRadical_eq_ker (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V)
    (hdet : D.DetectsRadical) :
    V.leftRadical = AddSubgroup.toIntSubmodule D.mukaiVectorHom.ker :=
  le_antisymm (D.leftRadical_le_ker hHRR hK3 hdet) (D.ker_le_leftRadical hHRR hK3)

/-- **The Mukai vector on the numerical quotient.**

The quotient the geometric class map lands in is `N ⧸ leftRadical`, and this is
the Mukai vector defined there.  It exists exactly because `leftRadical_le_ker`
does; without `DetectsRadical` the lift has no side condition to discharge. -/
noncomputable def mukaiVectorQuotient (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V)
    (hdet : D.DetectsRadical) :
    V.NumericalQuotient →+ Mukai.MukaiLattice Λ :=
  QuotientAddGroup.lift V.leftRadical.toAddSubgroup D.mukaiVectorHom <| by
    intro E hE
    exact AddMonoidHom.mem_ker.mp (D.leftRadical_le_ker hHRR hK3 hdet hE)

/-- The descent computes the Mukai vector on a representative. -/
@[simp]
theorem mukaiVectorQuotient_mk (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V)
    (hdet : D.DetectsRadical) (E : N) :
    D.mukaiVectorQuotient hHRR hK3 hdet (Submodule.Quotient.mk E)
      = D.mukaiVectorHom E :=
  rfl

end AdditiveMukaiData

end K3

end AlgebraicGeometry.Numerical
