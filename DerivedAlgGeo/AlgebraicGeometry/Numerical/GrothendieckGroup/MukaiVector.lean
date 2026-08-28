/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.EulerPairing
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic
import Mathlib.LinearAlgebra.BilinearForm.Isometry

/-!
# The Mukai vector, and the identification of the two Mukai pairings

`LinearAlgebra/Lattice/Mukai` builds the abstract Mukai extension `ℤ × Λ × ℤ`
of a symmetric bilinear lattice and says, in its own docstring, that the
identification with any geometric lattice **is not made there**.
`Numerical/GrothendieckGroup/EulerPairing` separately defines a `ℚ`-valued
`K3.mukaiPairing` on the numerical Grothendieck group by an explicit formula.
The two have never been connected.  This file connects them.

The obstruction is integrality, not content.  The abstract extension is
`ℤ`-valued; the numerical layer is `ℚ`-valued, because `degree` lands in `ℚ`.

The two coordinates behave differently, and the difference is the whole design
of this file.  The third coordinate is **not** a hypothesis: from explicit HRR and `IsK3`
witnesses, the existing `chi_eq_rank_add_mukaiS` gives `χ(E) = r(E) + mukaiS E`, so
`mukaiSInt E := χ(E) − r(E)` is an integer computing `mukaiS E`, proved in
`mukaiSInt_spec`.  Only the lattice-valued first Chern class is supplied, as
`IntegralMukaiData`.

Given it, `mukaiVector E = (r E, c₁ E, mukaiSInt E)` is a genuine element of
`Mukai.MukaiLattice Λ`, and everything the abstract lattice file proves about
sphericity, isotropy and expected dimension becomes a statement about `χ`.

## Main results

* `pairing_mukaiVector` — the abstract pairing computes `K3.mukaiPairing`.
* `chi₂_eq_neg_pairing` — `χ(E,F) = −⟪v(E), v(F)⟫`, now with `⟪-,-⟫` the
  abstract lattice form rather than the ad-hoc formula.
* `isSpherical_mukaiVector_iff` — `v(E)` is spherical exactly when `χ(E,E) = 2`.
* `expectedDim_mukaiVector` — `⟪v,v⟫ + 2 = 2 − χ(E,E)`.
* `AdditiveMukaiData` — the same data with `c₁` additive, and with it
  `mukaiVectorHom : N →+ ℤ × Λ × ℤ`, the symmetric bilinear form
  `mukaiForm : LinearMap.BilinForm ℤ N`, and `mukaiVectorIsometry`.

## What this file does not assert

* Nothing constructs an `IntegralMukaiData`, and nothing constructs an
  `AdditiveMukaiData`.  Producing either is the geometric obligation of
  exhibiting `NS(X)` with its intersection form; that is Layer B work, and the
  additive version needs the lattice-valued Chern class on top.
* **In `IntegralMukaiData`,** `c₁` is a bare function and so is `mukaiVector`.
  No additivity is assumed there, hence none is available there, and `b_spec`
  constrains `b` only on the image of `c₁` — it does not say `b` is the full
  intersection form.  Additivity is the single extra field of
  `AdditiveMukaiData`; `IntegralMukaiData.b_c₁_add` records precisely how much
  of it the weaker structure already implies, which is: additivity against the
  form, not additivity.
* Even with `AdditiveMukaiData`, nothing says `mukaiVector` is injective or
  surjective, so `mukaiVectorIsometry` is an isometric map and not an
  isometric equivalence.  A class is not claimed to be determined by its Mukai
  vector.
* `isSpherical_mukaiVector_iff` is a statement about the lattice, nothing more.
  Sphericity of an *object* on a K3 means the full graded self-Ext algebra is
  `k ⊕ k[-2]` — `Hom(E,E) = k`, `Ext¹(E,E) = 0`, `Ext²(E,E) = k` — and
  recovering that from `χ(E,E) = 2` needs simplicity and Serre duality on top
  of an `Ext` this layer does not have.  Neither direction of that equivalence
  is stated here.
* `expectedDim` is a definition in the abstract file, not the theorem that a
  moduli space has that dimension.  Nothing here upgrades it.
* No connection is made *in this file* to `CategoryTheory.Triangulated.K₀`.
  That bridge is `GrothendieckGroup/Realization.lean`, which supplies the class
  map rather than constructing it.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace K3

open NumericalRingData NumericalRingDualData NumericalVarietyData

variable {A : Type u} {N : Type v} {Λ : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [AddCommGroup Λ]
variable {V : NumericalVarietyData 2 A N}

/-- The integral third Mukai coordinate, `s(E) = χ(E) − r(E)`.

This is a **definition, not supplied data**: on a K3 the existing
`chi_eq_rank_add_mukaiS` already proves `χ(E) = r(E) + mukaiS E`, so the
integrality of `mukaiS` is a theorem rather than a hypothesis. An earlier draft
of `IntegralMukaiData` carried `s` and its specification as fields; that
overstated the trust boundary, and the review that caught it is the reason this
is a `def`. -/
noncomputable def mukaiSInt (V : NumericalVarietyData 2 A N) (E : N) : ℤ :=
  V.chi E - V.rank E

/-- `mukaiSInt` computes `mukaiS`, so the third Mukai coordinate really is an
integer. Proved from `chi_eq_rank_add_mukaiS`; nothing is assumed. -/
theorem mukaiSInt_spec (V : NumericalVarietyData 2 A N)
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (mukaiSInt V E : ℚ) = mukaiS V E := by
  have h := chi_eq_rank_add_mukaiS V hHRR hK3 E
  rw [mukaiSInt]
  push_cast
  linarith

/-- The integral structure that makes the numerical Mukai pairing a pairing in
the abstract Mukai extension.

`b_spec` is where the geometry goes: it says the integral form on the supplied
lattice `Λ` computes `∫c₁(E)·c₁(F)`. The third Mukai coordinate is **not** a
field — see `mukaiSInt`, which derives it.

Note what `b_spec` does and does not say. It constrains `b` only on the image
of `c₁`; it does not assert that `b` is the full intersection form of a
geometric lattice, and `c₁` is a bare function, not an additive map. This is
deliberately weaker than a geometric lattice package. `AdditiveMukaiData`
extends this structure with additivity of `c₁` when a caller can supply it;
`b_c₁_add` measures the gap.

Symmetry is **not** a field. On the image of `c₁` it is already a theorem —
`b_spec` and commutativity of `A` force it, see `b_comm_on_realized` — and
off the image it would be exactly the kind of global demand on `Λ` this
structure otherwise avoids; nothing downstream consumes it. An earlier draft
carried a `b_comm` field; the review that measured its use count (zero) is the
reason it is gone. -/
structure IntegralMukaiData (V : NumericalVarietyData 2 A N) (Λ : Type w)
    [AddCommGroup Λ] where
  /-- The first Chern class, valued in the supplied lattice. -/
  c₁ : N → Λ
  /-- The integral form on `Λ`.  Symmetry is not demanded: on the image of
  `c₁` it follows from `b_spec` (`b_comm_on_realized`), and off the image
  nothing here needs it. -/
  b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ
  /-- The form computes the intersection number of first Chern classes. -/
  b_spec : ∀ E F : N, (b (c₁ E) (c₁ F) : ℚ)
    = V.ring.degree (V.chComp E 1 * V.chComp F 1)

namespace IntegralMukaiData

variable (D : IntegralMukaiData V Λ)

/-- **On realized classes the form is symmetric**, with no symmetry field:
`b_spec` computes both sides as the same intersection number, `A` is
commutative, and the integer cast is injective. This is all the symmetry the
structure can see; symmetry off the image of `c₁` is neither demanded nor
available. -/
theorem b_comm_on_realized (E F : N) :
    D.b (D.c₁ E) (D.c₁ F) = D.b (D.c₁ F) (D.c₁ E) := by
  have h : (D.b (D.c₁ E) (D.c₁ F) : ℚ) = (D.b (D.c₁ F) (D.c₁ E) : ℚ) := by
    rw [D.b_spec, D.b_spec, mul_comm]
  exact_mod_cast h

/-- **`c₁` is additive as seen by the form**, with no additivity field:
`chComp` is additive in each degree and `degree` is `ℚ`-linear, so `b_spec`
computes both sides as the same intersection number.

This is exactly as much additivity as `IntegralMukaiData` can see, and saying
what it is not is the point of stating it. It says `c₁ (E + F) − c₁ E − c₁ F`
pairs to zero against every realized class — it lies in the radical of `b`
restricted to the image of `c₁`. It does **not** say that difference is zero,
and it cannot: `b` is not assumed nondegenerate anywhere, so a `c₁` that is
additive only up to a radical vector satisfies every field of this structure.

Making the difference actually zero is `AdditiveMukaiData.c₁_add`, and this
lemma is the reason that has to be supplied rather than derived. -/
theorem b_c₁_add (E F G : N) :
    D.b (D.c₁ (E + F)) (D.c₁ G)
      = D.b (D.c₁ E) (D.c₁ G) + D.b (D.c₁ F) (D.c₁ G) := by
  have h : (D.b (D.c₁ (E + F)) (D.c₁ G) : ℚ)
      = (D.b (D.c₁ E) (D.c₁ G) : ℚ) + (D.b (D.c₁ F) (D.c₁ G) : ℚ) := by
    rw [D.b_spec, D.b_spec, D.b_spec, V.chComp_add, add_mul, map_add]
  exact_mod_cast h

/-- The Mukai vector `v(E) = (r, c₁, s)` as an element of the abstract Mukai
extension of `Λ`. Not an additive map at this data level: no additivity of `c₁`
is assumed, so none is available here. `AdditiveMukaiData.mukaiVectorHom` is
the same function bundled as an `AddMonoidHom`, once the caller supplies the
missing field. -/
noncomputable def mukaiVector (E : N) : Mukai.MukaiLattice Λ :=
  (V.rank E, D.c₁ E, mukaiSInt V E)

/-- The integral Mukai construction retains numerical rank as its first coordinate
definitionally. -/
@[simp]
theorem mukaiVector_fst (E : N) : (D.mukaiVector E).1 = V.rank E := rfl

@[simp]
theorem mukaiVector_snd_fst (E : N) : (D.mukaiVector E).2.1 = D.c₁ E := rfl

@[simp]
theorem mukaiVector_snd_snd (E : N) :
    (D.mukaiVector E).2.2 = mukaiSInt V E := rfl

/-- **The abstract Mukai pairing computes the numerical one.**  This is the
identification the abstract lattice file declined to make, discharged from the
supplied integral data. -/
theorem pairing_mukaiVector (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E F : N) :
    (Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ)
      = mukaiPairing V E F := by
  rw [mukaiVector, mukaiVector, Mukai.pairing_mk, mukaiPairing]
  push_cast
  rw [D.b_spec, mukaiSInt_spec V hHRR hK3, mukaiSInt_spec V hHRR hK3]

/-- Specializing `pairing_mukaiVector` to the diagonal identifies the lattice norm used by
sphericity and expected-dimension results with the numerical self-pairing. -/
theorem selfPairing_mukaiVector (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (Mukai.selfPairing D.b (D.mukaiVector E) : ℚ)
      = mukaiSelfPairing V E := by
  rw [Mukai.selfPairing_eq_pairing, D.pairing_mukaiVector hHRR hK3,
    mukaiPairing_self V]

/-- **`χ(E,F) = −⟪v(E), v(F)⟫`**, with `⟪-,-⟫` the abstract Mukai-lattice form.

`K3.chi₂_eq_neg_mukaiPairing` states this against the explicit formula; this
version states it against the lattice, which is what makes the sphericity and
expected-dimension vocabulary of `LinearAlgebra/Lattice/Mukai` applicable to
the Euler form. -/
theorem chi₂_eq_neg_pairing (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E F : N) :
    V.chi₂ E F
      = -(Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ) := by
  rw [D.pairing_mukaiVector hHRR hK3, chi₂_eq_neg_mukaiPairing V hK3]

/-- The self-pairing of `v(E)`, cast to `ℚ`, is `−χ(E,E)`. -/
theorem selfPairing_mukaiVector_eq_neg_chi₂
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (Mukai.selfPairing D.b (D.mukaiVector E) : ℚ) = -V.chi₂ E E := by
  rw [Mukai.selfPairing_eq_pairing, D.chi₂_eq_neg_pairing hHRR hK3]
  ring

/-- **Bridgeland's Lemma 5.1, reduced to one inequality about `χ`.**

Lemma 5.1 is `v(E)² ≥ −2` for a `μ`-stable sheaf on a K3, and it is the hypothesis that
`Mukai.re_expCharge_pos_of_neg_one` takes as `−1 ≤ realForm b v` — the last thing standing
between `ChargePositivity.lean` and case 4 of Lemma 6.2.

This theorem **proves none of it**. It is a rewrite of `selfPairing_mukaiVector_eq_neg_chi₂`,
and its only content is to state the remaining gap in its sharpest form: **Lemma 5.1 is exactly
`χ(E,E) ≤ 2`**, a single inequality about the Euler form, rather than prose spread over three
docstrings.

Why the inequality is not available here, recorded so the next reader does not re-derive it:

* `chi₂` is `∫ ch(E)ᵛ · ch(F) · td(X)`, with no `Ext` in it. The identity
  `χ₂ E F = Σᵢ (−1)ⁱ dim Extⁱ(E,F)` is the bilinear Hirzebruch–Riemann–Roch, which
  `EulerPairing.lean` records as belonging to a later layer and which `EulerTransfer.lean`
  supplies as the hypothesis `IsRiemannRoch` rather than proving.
* The classical argument is `χ(E,E) = hom − ext¹ + ext² = 2 − ext¹`, using simplicity of a
  stable sheaf and Serre duality on a K3. Neither exists in this repository: there is no
  `SerreDuality` and no "stable implies simple", and the stability here is numerical and is not
  tied to `Hom` at all.

See #332. -/
theorem neg_two_le_selfPairing_mukaiVector_iff
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    -2 ≤ Mukai.selfPairing D.b (D.mukaiVector E) ↔ V.chi₂ E E ≤ 2 := by
  rw [← @Int.cast_le ℚ, D.selfPairing_mukaiVector_eq_neg_chi₂ hHRR hK3]
  push_cast
  constructor <;> intro h <;> linarith

/-- **A Mukai vector is spherical exactly when `χ(E,E) = 2`.**

This is `Mukai.IsSpherical` — a property of the *lattice vector*, meaning
`⟪v,v⟫ = -2`.  It is not sphericity of the object, which on a K3 asks that the
graded self-Ext algebra be `k ⊕ k[-2]` (so also `Ext¹(E,E) = 0`) and which
would need simplicity and Serre duality to recover from `χ(E,E) = 2`. -/
theorem isSpherical_mukaiVector_iff
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    Mukai.IsSpherical D.b (D.mukaiVector E) ↔ V.chi₂ E E = 2 := by
  rw [Mukai.isSpherical_iff, ← @Int.cast_inj ℚ,
    D.selfPairing_mukaiVector_eq_neg_chi₂ hHRR hK3]
  push_cast
  constructor <;> intro h <;> linarith

/-- A Mukai vector is isotropic exactly when `χ(E,E) = 0`. -/
theorem isIsotropic_mukaiVector_iff
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    Mukai.IsIsotropic D.b (D.mukaiVector E) ↔ V.chi₂ E E = 0 := by
  rw [Mukai.isIsotropic_iff, ← @Int.cast_inj ℚ,
    D.selfPairing_mukaiVector_eq_neg_chi₂ hHRR hK3]
  push_cast
  constructor <;> intro h <;> linarith

/-- The expected dimension attached to `v(E)` is `2 − χ(E,E)`.

`Mukai.expectedDim` is a definition, not the moduli-dimension theorem; this
identity relocates it onto the Euler form and asserts nothing geometric. -/
theorem expectedDim_mukaiVector
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (Mukai.expectedDim D.b (D.mukaiVector E) : ℚ) = 2 - V.chi₂ E E := by
  rw [Mukai.expectedDim]
  push_cast
  rw [D.selfPairing_mukaiVector_eq_neg_chi₂ hHRR hK3]
  ring

end IntegralMukaiData

/-! ## Additive `c₁`, and the Mukai form as a genuine bilinear form

Everything above treats `c₁` as a bare function, and that ceiling is real: with
`mukaiVector` a bare function, `(E, F) ↦ ⟪v E, v F⟫` is a function of two
arguments and nothing more. It is not a bilinear form, so no map can be an
isometry of it, and the review record's "no map of Mukai lattices exists here"
was a statement about this data level.

Adding one field lifts the ceiling. `AdditiveMukaiData` demands that `c₁` be
additive on the nose; `IntegralMukaiData.b_c₁_add` shows why that is a genuine
demand and not a repackaging. From it, `mukaiVector` becomes an
`AddMonoidHom`, `mukaiForm` becomes a `LinearMap.BilinForm ℤ N`, and
`Realization`'s pairing results become isometry statements in Mathlib's sense
of the word.

The bare layer stays exactly as it was. It asks for less, it is what everything
downstream currently consumes, and nothing here is required to use the stronger
structure. -/

/-- `IntegralMukaiData` with **additive** first Chern class.

The one new field is genuinely stronger geometric input, not bookkeeping: see
`IntegralMukaiData.b_c₁_add` for the precise gap. Additivity of `c₁` on the
nose is what the lattice-valued Chern class of an actual variety has and what
`b_spec` alone cannot detect.

`rank` and `chi` are already bundled `AddMonoidHom`s in `NumericalVarietyData`, and
`mukaiSInt = chi − rank`, so the other two Mukai coordinates need no
hypothesis. `c₁` is the only obstruction and this is the only field. -/
structure AdditiveMukaiData (V : NumericalVarietyData 2 A N) (Λ : Type w)
    [AddCommGroup Λ] extends IntegralMukaiData V Λ where
  /-- The first Chern class is additive. -/
  c₁_add : ∀ E F : N, c₁ (E + F) = c₁ E + c₁ F

namespace AdditiveMukaiData

variable (D : AdditiveMukaiData V Λ)

/-- The first Chern class as a homomorphism.

No `toIntegralMukaiData_c₁` accompanies this: `D.c₁` and
`D.toIntegralMukaiData.c₁` are the same term, so such a lemma is a syntactic
tautology and the linter rejects it. Parent-field access needs no rewriting. -/
def c₁Hom : N →+ Λ := AddMonoidHom.mk' D.c₁ D.c₁_add

@[simp]
theorem c₁Hom_apply (E : N) : D.c₁Hom E = D.c₁ E := rfl

/-- **The Mukai vector as a homomorphism** `N →+ ℤ × Λ × ℤ`.

Built from the three coordinates separately: `rank` and `chi − rank` are
`AddMonoidHom`s already, and `c₁Hom` is the new field. -/
noncomputable def mukaiVectorHom : N →+ Mukai.MukaiLattice Λ :=
  V.rank.prod (D.c₁Hom.prod (V.chi - V.rank))

@[simp]
theorem mukaiVectorHom_apply (E : N) :
    D.mukaiVectorHom E = D.toIntegralMukaiData.mukaiVector E := rfl

/-- **The Mukai form on `N`**: the abstract Mukai pairing pulled back along the
Mukai vector.

This is the declaration that could not be written before. `compl₁₂` needs its
two legs to be linear maps, and `mukaiVectorHom` is the first version of the
Mukai vector that is one. The result is a `LinearMap.BilinForm ℤ N` — a real
bilinear form on the numerical Grothendieck group, not a two-argument
function. -/
noncomputable def mukaiForm : LinearMap.BilinForm ℤ N :=
  (Mukai.pairingBilin D.b).compl₁₂ D.mukaiVectorHom.toIntLinearMap
    D.mukaiVectorHom.toIntLinearMap

@[simp]
theorem mukaiForm_apply (E F : N) :
    D.mukaiForm E F = Mukai.pairing D.b (D.toIntegralMukaiData.mukaiVector E)
      (D.toIntegralMukaiData.mukaiVector F) := rfl

/-- **The Mukai form is symmetric.**

From `b_comm_on_realized`, so no global symmetry of `b` is demanded — the form
only ever sees `b` on the image of `c₁`, which is where symmetry is already a
theorem. A bilinear form being symmetric is what makes "isometry" the right
word downstream rather than a one-sided condition. -/
theorem mukaiForm_comm (E F : N) : D.mukaiForm E F = D.mukaiForm F E := by
  simp only [mukaiForm_apply, Mukai.pairing, IntegralMukaiData.mukaiVector]
  rw [D.toIntegralMukaiData.b_comm_on_realized E F]
  ring

/-- The Mukai form computes `−χ`, the `AdditiveMukaiData` restatement of
`IntegralMukaiData.chi₂_eq_neg_pairing`. -/
theorem mukaiForm_eq_neg_chi₂
    (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E F : N) :
    (D.mukaiForm E F : ℚ) = -V.chi₂ E F := by
  rw [mukaiForm_apply,
    D.toIntegralMukaiData.chi₂_eq_neg_pairing hHRR hK3 E F, neg_neg]

/-- **The Mukai vector is an isometry into the Mukai extension.**

True by construction — `mukaiForm` is defined as the pullback — but worth
naming, because it is the first statement in this development that produces a
`LinearMap.BilinForm.Isometry`. That is Mathlib's structure, so the word
carries its standard meaning: a linear map under which the two forms agree.

It is **not** claimed injective or surjective, so this is an isometric map, not
an isometric equivalence. Injectivity would say a class is determined by its
Mukai vector, which is a statement about the numerical Grothendieck group that
nothing here proves. -/
noncomputable def mukaiVectorIsometry : D.mukaiForm →bᵢ Mukai.pairingBilin D.b where
  toLinearMap := D.mukaiVectorHom.toIntLinearMap
  map_app' _ _ := rfl

@[simp]
theorem mukaiVectorIsometry_apply (E : N) :
    D.mukaiVectorIsometry E = D.toIntegralMukaiData.mukaiVector E := rfl

end AdditiveMukaiData

end K3

end AlgebraicGeometry.Numerical
