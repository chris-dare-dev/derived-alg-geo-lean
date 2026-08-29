/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.SlicingDistance
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import MathFormalContract

/-!
# The `Aut` action preserves the phase distance

Lemma 8.2 says `Aut(D)` acts on `Stab(D)` **by isometries**. This module proves
the phase half of that clause, and is deliberate about which half it is.

The distance it uses is `slicingDist`
(`WeakStabilityCondition/StabilityCondition/Foundation/Deformation/SlicingDistance.lean`), built for
the deformation theory of §7 and not, on its own, the §8 metric.

```
slicingDist C s₁ s₂ = ⨆ (E : C) (_ : ¬IsZero E),
  ENNReal.ofReal (max |φ⁺₁ E - φ⁺₂ E| |φ⁻₁ E - φ⁻₂ E|)
```

`mapEquiv_slicingDist` proves the action preserves it, on the nose and with no
finiteness hypothesis. Both sides may be `⊤`; the equality still holds.

## This is not Bridgeland's `d`, and the gap is not a technicality

`d(σ₁, σ₂)` is a supremum of **three** quantities. `slicingDist` carries two of
them — the `φ⁺` and `φ⁻` discrepancies — and omits
`|log (m_{σ₂}(E) / m_{σ₁}(E))|`, the mass ratio. The omitted term is the only
one that sees the central charge, and therefore the only one that could move
under `Φ` at all, since `actStabAut` replaces `Z` by `Z ∘ lam`.

This module itself does not close it: **the slicing foundation has no mass
function** — `m_σ(E) = Σ|Z(A_i)|` over the HN factors is not defined anywhere
under `Foundation/`. The downstream `Metric/Mass/Basic.lean`,
`Metric/Mass/Uniqueness.lean`, `Metric/Distance/Basic.lean`, and
`Metric/Isometry/Full.lean` define the HN mass, prove independence from the
chosen filtration and finiteness, and prove preservation of the resulting
three-coordinate distance.

So the relation to Lemma 8.2 is `no_claim`, not `one_way`, and the reason is a
genuine non-implication rather than modesty. A sup of three terms being
preserved does not give that each term is preserved, so the paper's statement
does **not** imply this one; and this one plainly does not imply the paper's.
The same call, for the same reason, as `gltildeSlicingMulAction`.

## Why the supremum is bounded twice rather than reindexed

The obvious proof — reindex the supremum along `Φ` — does not typecheck, and
the reason is worth keeping. `Φ.functor.obj` is a function on the **object
type** of `C`, and an equivalence of categories makes it injective only *up to
isomorphism*. Two distinct terms of the type `C` can be isomorphic objects, and
`Φ.functor.obj` is free to identify them. There is no `Equiv` to rewrite along.

What is true is that each side dominates the other pointwise, which is all a
supremum needs. `≤` sends `E` to `Φ⁻¹ E`; `≥` sends `E` to `Φ E` and then needs
`phiPlus_congr` to move back along the unit isomorphism. That last step is why
`phiPlus_congr` exists at all.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated

universe w u

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## The intrinsic phases are invariant under isomorphism of the object

The deformation modules need this repeatedly and never state it —
`Foundation/Deformation/PhaseConfinement.lean` and its neighbours inline the
`HNFiltration.ofIso` argument instead. Stated once here, because the `≥` half
of the isometry cannot be written without it. -/

/-- `φ⁺` depends on the object only up to isomorphism. -/
theorem Slicing.phiPlus_congr (s : Slicing C) {E E' : C} (e : E ≅ E')
    (hE : ¬IsZero E) (hE' : ¬IsZero E') :
    s.phiPlus C E hE = s.phiPlus C E' hE' := by
  obtain ⟨F, hn, hfirst, _⟩ := s.exists_hn_nonzero_boundaries C hE
  rw [s.phiPlus_eq C E hE F hn hfirst,
    s.phiPlus_eq C E' hE'
      (CategoryTheory.Triangulated.HNFiltration.ofIso C F e) hn hfirst]
  -- `ofIso` retargets `top_iso` and copies everything else, `φ` included.
  rfl

/-- `φ⁻` depends on the object only up to isomorphism. -/
theorem Slicing.phiMinus_congr (s : Slicing C) {E E' : C} (e : E ≅ E')
    (hE : ¬IsZero E) (hE' : ¬IsZero E') :
    s.phiMinus C E hE = s.phiMinus C E' hE' := by
  obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  rw [s.phiMinus_eq C E hE F hn hlast,
    s.phiMinus_eq C E' hE'
      (CategoryTheory.Triangulated.HNFiltration.ofIso C F e) hn hlast]
  rfl

section Aut

variable (Φ : C ≌ C)
  [Φ.functor.Additive] [Φ.inverse.Additive]
  [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated]

/-! ## An equivalence neither creates nor destroys the zero object

Both directions are needed: `≤` moves a nonzero `E` to a nonzero `Φ⁻¹ E`, and
`≥` moves it to a nonzero `Φ E`. Neither is `Functor.map_isZero`, which only
goes one way. -/

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated] in
/-- `Φ⁻¹ E` is zero exactly when `E` is. -/
theorem isZero_inverse_iff (E : C) : IsZero (Φ.inverse.obj E) ↔ IsZero E :=
  ⟨fun h => IsZero.of_iso (Φ.functor.map_isZero h) (Φ.counitIso.app E).symm,
   fun h => Φ.inverse.map_isZero h⟩

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated] in
/-- `Φ E` is zero exactly when `E` is. -/
theorem isZero_functor_iff (E : C) : IsZero (Φ.functor.obj E) ↔ IsZero E :=
  ⟨fun h => IsZero.of_iso (Φ.inverse.map_isZero h) (Φ.unitIso.app E),
   fun h => Φ.functor.map_isZero h⟩

/-! ## The phases transport along the action

`Slicing.mapEquiv` moves objects and fixes phases, so `φ⁺` of the moved slicing
at `E` is `φ⁺` of the original at `Φ⁻¹ E`, *exactly* — no `ε`, no continuity.
Contrast `relabel`, where a phase relabelling `f` sends `φ⁺` to `f φ⁺` and the
distance is not preserved at all. -/

/-- `φ⁺_{Φ · s}(E) = φ⁺_s(Φ⁻¹ E)`. -/
theorem mapEquiv_phiPlus (s : Slicing C) (E : C)
    (hE : ¬IsZero E) (hE' : ¬IsZero (Φ.inverse.obj E)) :
    (s.mapEquiv Φ).phiPlus C E hE = s.phiPlus C (Φ.inverse.obj E) hE' := by
  obtain ⟨F, hn, hfirst, _⟩ := s.exists_hn_nonzero_boundaries C hE'
  -- Push `F` forward through `Φ` and land it on `E` via the counit. This is the
  -- same filtration `mapEquiv.hn_exists` builds; `mapF` and `ofIso` both leave
  -- `n`, `φ` and the triangles alone, so its phases are literally `F.φ`.
  set G := CategoryTheory.Triangulated.HNFiltration.ofIso C
      (CategoryTheory.Triangulated.HNFiltration.mapF F
        (P' := fun φ X => s.P φ (Φ.inverse.obj X)) Φ.functor
        (fun _ X h => ObjectProperty.prop_of_iso _ (Φ.unitIso.app X) h))
      (Φ.counitIso.app E) with hG
  have hnG : 0 < G.n := hn
  have hneG : ¬IsZero (G.triangle ⟨0, hnG⟩).obj₃ := fun h =>
    hfirst ((isZero_functor_iff Φ _).mp h)
  rw [(s.mapEquiv Φ).phiPlus_eq C E hE G hnG hneG,
      s.phiPlus_eq C (Φ.inverse.obj E) hE' F hn hfirst]
  -- `mapF` and `ofIso` copy `φ` across verbatim, so the two sides are the same term.
  rfl

/-- `φ⁻_{Φ · s}(E) = φ⁻_s(Φ⁻¹ E)`. -/
theorem mapEquiv_phiMinus (s : Slicing C) (E : C)
    (hE : ¬IsZero E) (hE' : ¬IsZero (Φ.inverse.obj E)) :
    (s.mapEquiv Φ).phiMinus C E hE = s.phiMinus C (Φ.inverse.obj E) hE' := by
  obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE'
  set G := CategoryTheory.Triangulated.HNFiltration.ofIso C
      (CategoryTheory.Triangulated.HNFiltration.mapF F
        (P' := fun φ X => s.P φ (Φ.inverse.obj X)) Φ.functor
        (fun _ X h => ObjectProperty.prop_of_iso _ (Φ.unitIso.app X) h))
      (Φ.counitIso.app E) with hG
  have hnG : 0 < G.n := hn
  have hneG : ¬IsZero (G.triangle ⟨G.n - 1, by lia⟩).obj₃ := fun h =>
    hlast ((isZero_functor_iff Φ _).mp h)
  rw [(s.mapEquiv Φ).phiMinus_eq C E hE G hnG hneG,
      s.phiMinus_eq C (Φ.inverse.obj E) hE' F hn hlast]
  rfl

/-! ## The isometry -/

/-- **The `Aut` action preserves `slicingDist`.** The phase half of Lemma 8.2's
isometry clause.

No finiteness hypothesis: both sides live in `ℝ≥0∞` and the equality holds when
they are `⊤`. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "The ISOMETRY clause of Lemma 8.2, for a DIFFERENT distance, so neither statement implies the other. The paper's d is a sup of THREE quantities; this library's slicingDist carries the two phase discrepancies and omits |log(m2/m1)|, the mass ratio -- the only term that sees the central charge, hence the only one Z-composed-with-lam could move. A sup of three being preserved does not give that each term is, so isometry for d does NOT imply this; and preserving slicingDist plainly does not imply isometry for d. Separately, slicingDist is a distance on Slicing C, not on Stab(D). Downstream files construct a three-coordinate envelope distance, but this phase-only theorem remains distinct.")]
theorem mapEquiv_slicingDist (s₁ s₂ : Slicing C) :
    slicingDist C (s₁.mapEquiv Φ) (s₂.mapEquiv Φ) = slicingDist C s₁ s₂ := by
  apply le_antisymm
  · -- `E ↦ Φ⁻¹ E`: the term at `E` on the left IS the term at `Φ⁻¹ E` on the right.
    refine iSup₂_le fun E hE => ?_
    have hE' : ¬IsZero (Φ.inverse.obj E) := fun h => hE ((isZero_inverse_iff Φ E).mp h)
    rw [mapEquiv_phiPlus Φ s₁ E hE hE', mapEquiv_phiPlus Φ s₂ E hE hE',
        mapEquiv_phiMinus Φ s₁ E hE hE', mapEquiv_phiMinus Φ s₂ E hE hE']
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) =>
      ENNReal.ofReal (max |s₁.phiPlus C X hX - s₂.phiPlus C X hX|
                          |s₁.phiMinus C X hX - s₂.phiMinus C X hX|)) _ hE'
  · -- `E ↦ Φ E`, then back along the unit isomorphism `E ≅ Φ⁻¹ (Φ E)`.
    refine iSup₂_le fun E hE => ?_
    have hFE : ¬IsZero (Φ.functor.obj E) := fun h => hE ((isZero_functor_iff Φ E).mp h)
    have hIFE : ¬IsZero (Φ.inverse.obj (Φ.functor.obj E)) := fun h =>
      hFE ((isZero_inverse_iff Φ (Φ.functor.obj E)).mp h)
    have hp : ∀ s : Slicing C,
        s.phiPlus C E hE = (s.mapEquiv Φ).phiPlus C (Φ.functor.obj E) hFE := fun s => by
      rw [mapEquiv_phiPlus Φ s _ hFE hIFE]
      exact s.phiPlus_congr (Φ.unitIso.app E) hE hIFE
    have hm : ∀ s : Slicing C,
        s.phiMinus C E hE = (s.mapEquiv Φ).phiMinus C (Φ.functor.obj E) hFE := fun s => by
      rw [mapEquiv_phiMinus Φ s _ hFE hIFE]
      exact s.phiMinus_congr (Φ.unitIso.app E) hE hIFE
    rw [hp s₁, hp s₂, hm s₁, hm s₂]
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) =>
      ENNReal.ofReal (max |(s₁.mapEquiv Φ).phiPlus C X hX - (s₂.mapEquiv Φ).phiPlus C X hX|
                          |(s₁.mapEquiv Φ).phiMinus C X hX - (s₂.mapEquiv Φ).phiMinus C X hX|))
      _ hFE

end Aut

/-! ## On stability conditions

`mapEquiv_slicingDist` is about slicings. These two carry it to the objects §8
is actually about — first for `actStabAut`, the general map, then for the
`MulAction` of `AutPairQuot v`, which is as close to "the group acts by
isometries" as this repo gets.

Both are one-liners, and that is the point: the content is all in
`mapEquiv_slicingDist`, and the acted slicing is *definitionally*
`σ.slicing.mapEquiv Φ` in both packagings. -/

section StabilityConditions

variable [IsTriangulated C]

variable (Φ : C ≌ C)
  [Φ.functor.Additive] [Φ.inverse.Additive]
  [Φ.functor.CommShift ℤ] [Φ.inverse.CommShift ℤ]
  [Φ.functor.IsTriangulated] [Φ.inverse.IsTriangulated]

universe u'

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- `actStabAut` preserves the phase distance between the underlying slicings.

Note what does **not** appear on either side: `lam`. The class-lattice datum
moves the central charge and nothing else, and `slicingDist` does not see the
central charge — which is exactly why the mass term, which does, is out of
scope here. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "Same non-implication as mapEquiv_slicingDist: the distance is slicingDist, not Bridgeland's d, and d omits nothing while slicingDist omits the mass ratio. What this adds over that theorem is only the carrier -- the statement is now about stability conditions rather than bare slicings, matching the paper's Stab(D). It is still not the paper's isometry claim.")]
theorem actStabAut_slicingDist (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (K₀.map Φ.inverse x) = lam (v x))
    (σ τ : StabilityCondition.WithClassMap C v) :
    slicingDist C (actStabAut Φ v lam hlam σ).slicing
        (actStabAut Φ v lam hlam τ).slicing
      = slicingDist C σ.slicing τ.slicing :=
  mapEquiv_slicingDist Φ σ.slicing τ.slicing

/-- **The group acts by phase isometries.** Every element of `AutPairQuot v`
preserves `slicingDist` on the underlying slicings.

`_root_.Quotient.inductionOn` is safe here without a well-definedness side goal: the
statement is an equation between two `ℝ≥0∞`s, so it is a `Prop` and proof
irrelevance discharges the descent. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "The closest this repo gets to 'Aut(D) acts by isometries', and still not it, for two independent reasons already recorded elsewhere in this repo. (1) The distance is slicingDist, not Bridgeland's d -- see mapEquiv_slicingDist's note; neither statement implies the other. (2) AutPairQuot v is NOT Aut(D): its elements are pairs (Phi, lam), and the forgetful map to AutQuot C is proved neither injective nor surjective. Cite this as 'the group of autoequivalences carrying a compatible class-lattice automorphism preserves the phase distance'.")]
theorem AutPairQuot_smul_slicingDist
    (g : CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot v)
    (σ τ : StabilityCondition.WithClassMap C v) :
    slicingDist C (g • σ).slicing (g • τ).slicing = slicingDist C σ.slicing τ.slicing := by
  induction g using _root_.Quotient.inductionOn with
  | h a => exact mapEquiv_slicingDist a.Φ.e σ.slicing τ.slicing

end StabilityConditions

end CategoryTheory.Triangulated
