/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Phase
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.SlicingDistance
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial

/-!
# Transfer of pre-stability conditions along a phase-detecting functor

Definitions 3.1 and 3.6 of arXiv:2607.28411v1 transport a stability condition
`σ = (Z, 𝒫)` on `Dᵇ(Y)` to `Dᵇ(X)` through a functor `F` between the two
derived categories: the slicing is the preimage `𝒫_F(φ) = {E | F E ∈ 𝒫(φ)}`,
the class map is precomposed with the induced map on Grothendieck groups,
and the central charge is unchanged.  The pullback `f^♯σ` uses `F = f_*`, the
pushforward `f_♯σ` uses `F = f^*`; Definition 3.1 of arXiv:2601.22994 is the
same pair of constructions for a finite morphism of smooth projective
varieties.  Both are instances of one categorical operation, which this file
defines on `PreStabilityCondition.WithClassMap` once the slicing-level witness
`Slicing.PreimageData` of `Phase.Transfer.Basic` has been supplied.

## Main definitions

* `PreStabilityCondition.WithClassMap.preimage`: the transported pre-stability
  condition, with class map `v ∘ K₀(F)` and the original charge.
* `PreStabilityCondition.WithClassMap.pullback` and
  `PreStabilityCondition.WithClassMap.pushforward`: the source-facing names of
  Definitions 3.1(3) and 3.6(3).

## Main results

* `Slicing.PreimageData.reflectsZeroObjects`: the slicing-lifting witness
  already forces the detecting functor to reflect zero objects, so the
  conservativity that Remarks 3.2 and 3.7 add by hand is a consequence of the
  Hom-vanishing axiom rather than an extra hypothesis.
* `Slicing.Precedes.preimage_of_preimageData` and its weak form: the slicing
  orders are preserved by transfer, given only the two lifting witnesses
  involved.  This is Lemma 3.3 of arXiv:2601.22994 and Remark 3.14(3) of
  arXiv:2607.28411v1 without the family-wide hypothesis of
  `Slicing.Precedes.preimage`.
* `slicingDist_preimage_le`: transfer does not increase the generalized
  distance between slicings, Lemma 3.5(3) and Lemma 3.9(3).
* `PreStabilityCondition.WithClassMap.preimage_phiPlus` and
  `preimage_phiMinus`: extreme phases are computed after applying the
  functor, Lemma 3.5(2) and Lemma 3.9(2).

## Implementation notes

The transported class map is `v.comp (K₀.map F)`.  The paper writes it as
`f^♯v = v ∘ f_*` or `f_♯v = v ∘ f^*`; no separate carrier is introduced for it
because the composite of an additive homomorphism with the functorial map on
`K₀` is already the canonical object.

The compatibility field of the transported condition is proved from that of
`σ` at the image `F.obj E`.  The only non-formal input is that `F.obj E` is
nonzero when `E` is, which is exactly what `reflectsZeroObjects` extracts from
the Hom-vanishing half of `Slicing.PreimageData`.

Support-property transfer lives in `Support/Transfer.lean`, beside the
support predicates it is about.

## References

* arXiv:2607.28411v1, Definitions 3.1 and 3.6, Remarks 3.2 and 3.7,
  Lemmas 3.5 and 3.9, Remark 3.14.
* arXiv:2601.22994, Definition 3.1 and Lemma 3.3.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂ u'

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Conservativity is a consequence of the lifting witness

Remarks 3.2 and 3.7 of arXiv:2607.28411v1 assume the detecting functor is
conservative before transporting a stability condition.  At the level of
objects, that assumption is already implied by `Slicing.PreimageData`: an
object with zero image is semistable of every phase for the preimage
collection, so Hom-vanishing between two distinct phases kills its identity. -/

/-- The Hom-vanishing half of the slicing-lifting witness forces the detecting
functor to reflect zero objects.  Take `E` with `F.obj E` zero; then `E` lies
in the preimage slices of phases `1` and `0` at once, and Hom-vanishing from
the higher to the lower phase forces `𝟙 E = 0`. -/
theorem Slicing.PreimageData.reflectsZeroObjects {s : Slicing D} {F : C ⥤ D}
    (h : s.PreimageData F) : ReflectsZeroObjects F := by
  intro E hFE
  rw [IsZero.iff_id_eq_zero]
  exact h.hom_vanishing 1 0 E E zero_lt_one
    (s.zero_mem_of_isZero D 1 (F.obj E) hFE)
    (s.zero_mem_of_isZero D 0 (F.obj E) hFE) (𝟙 E)

/-- The image of a nonzero object under a functor carrying slicing-lifting
data is nonzero. -/
theorem Slicing.PreimageData.not_isZero_obj {s : Slicing D} {F : C ⥤ D}
    (h : s.PreimageData F) {E : C} (hE : ¬IsZero E) : ¬IsZero (F.obj E) :=
  fun hFE => hE (h.reflectsZeroObjects E hFE)

section Slicing

variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]

/-! ### Order and distance under transfer

`Slicing.Precedes.preimage` in `Phase.Transfer.Phase` asks for lifting data on
every slicing of the target.  The paper's statements only ever involve the two
slicings being compared, so the two-witness forms below are the ones a
geometric consumer can discharge. -/

/-- Transfer preserves the strict slicing order, given lifting witnesses for
the two slicings involved.  This is Lemma 3.3 of arXiv:2601.22994: an object
semistable for the transferred `s` maps to an object semistable for `s`, whose
HN phases for `t` are strictly below its phase, and those phases are the HN
phases for the transferred `t`. -/
theorem Slicing.Precedes.preimage_of_preimageData {s t : Slicing D}
    (hs : s.PreimageData F) (ht : t.PreimageData F) (hst : s.Precedes D t) :
    (s.preimage F hs).Precedes C (t.preimage F ht) := by
  intro phi E hE
  exact (t.preimage_ltProp_iff F ht ht.reflectsZeroObjects phi E).mpr
    (hst phi (F.obj E) hE)

/-- Transfer preserves the weak slicing order, given lifting witnesses for the
two slicings involved. -/
theorem Slicing.PrecedesWeak.preimage_of_preimageData {s t : Slicing D}
    (hs : s.PreimageData F) (ht : t.PreimageData F) (hst : s.PrecedesWeak D t) :
    (s.preimage F hs).PrecedesWeak C (t.preimage F ht) := by
  intro phi E hE
  exact (t.preimage_leProp_iff F ht ht.reflectsZeroObjects phi E).mpr
    (hst phi (F.obj E) hE)

/-- Transfer does not increase the generalized distance between slicings,
Lemma 3.5(3) and Lemma 3.9(3) of arXiv:2607.28411v1.  Every phase discrepancy
on the source is a phase discrepancy on the target at the image object, so the
source supremum runs over a subset of the target terms. -/
theorem slicingDist_preimage_le (s t : Slicing D)
    (hs : s.PreimageData F) (ht : t.PreimageData F) :
    slicingDist C (s.preimage F hs) (t.preimage F ht) ≤ slicingDist D s t := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  rw [s.preimage_phiPlus F hs hs.reflectsZeroObjects E hE,
    t.preimage_phiPlus F ht ht.reflectsZeroObjects E hE,
    s.preimage_phiMinus F hs hs.reflectsZeroObjects E hE,
    t.preimage_phiMinus F ht ht.reflectsZeroObjects E hE]
  exact slicingDistTerm_le D s t (F.obj E) (hs.not_isZero_obj hE)

end Slicing

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ D →+ Λ}
variable (σ : WithClassMap D v) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : σ.slicing.PreimageData F)

/-! ### The transported pre-stability condition -/

/-- The pre-stability condition transported along a phase-detecting functor:
Definitions 3.1(2)--(3) and 3.6(2)--(3) of arXiv:2607.28411v1 in one
categorical operation.  The slicing is the preimage slicing, the class map is
`v ∘ K₀(F)`, and the central charge is unchanged.

The positivity axiom holds because the class of `E` under the new class map is
the class of `F.obj E` under the old one, `F.obj E` is semistable of the same
phase by definition of the preimage slicing, and it is nonzero by
`Slicing.PreimageData.not_isZero_obj`. -/
def preimage : WithClassMap C (v.comp (K₀.map F)) :=
  ofStrict (σ.slicing.preimage F h) σ.Z (by
    intro φ E hP hE
    obtain ⟨m, hm, hZ⟩ := σ.compatible φ (F.obj E) hP (h.not_isZero_obj hE)
    refine ⟨m, hm, ?_⟩
    change σ.Z (v (K₀.map F (K₀.of C E))) = _
    rw [K₀.map_of]
    exact hZ)

/-- The slicing of the transported condition is the preimage slicing.
Definitional; recorded so that `simp` can pass from the stability-level
construction to the slicing-level API of `Phase.Transfer.Basic`. -/
@[simp]
theorem preimage_slicing : (σ.preimage F h).slicing = σ.slicing.preimage F h := rfl

/-- Transfer leaves the central charge on `Λ` untouched; only the class map
changes.  Definitional; recorded for `simp`. -/
@[simp]
theorem preimage_Z : (σ.preimage F h).Z = σ.Z := rfl

/-- Semistability for the transported condition is detected by the functor. -/
theorem preimage_P_iff (φ : ℝ) (E : C) :
    (σ.preimage F h).slicing.P φ E ↔ σ.slicing.P φ (F.obj E) :=
  Iff.rfl

/-- The transported central charge of an object is the original charge of its
image.  This is the identity `(f^♯Z)(E) = Z(f_* E)` that the paper leaves
implicit in Definition 3.1(3). -/
@[simp]
theorem preimage_charge (E : C) :
    (σ.preimage F h).charge E = σ.charge (F.obj E) := by
  change σ.Z (v (K₀.map F (K₀.of C E))) = σ.Z (v (K₀.of D (F.obj E)))
  rw [K₀.map_of]

/-- The highest HN phase for the transported condition is the highest HN phase
of the image, Lemma 3.5(2) and Lemma 3.9(2) of arXiv:2607.28411v1.  Unlike
`Slicing.preimage_phiPlus`, no separate conservativity hypothesis is taken:
the lifting witness supplies it. -/
theorem preimage_phiPlus (E : C) (hE : ¬IsZero E) :
    (σ.preimage F h).slicing.phiPlus C E hE =
      σ.slicing.phiPlus D (F.obj E) (h.not_isZero_obj hE) :=
  σ.slicing.preimage_phiPlus F h h.reflectsZeroObjects E hE

/-- The lowest HN phase for the transported condition is the lowest HN phase
of the image. -/
theorem preimage_phiMinus (E : C) (hE : ¬IsZero E) :
    (σ.preimage F h).slicing.phiMinus C E hE =
      σ.slicing.phiMinus D (F.obj E) (h.not_isZero_obj hE) :=
  σ.slicing.preimage_phiMinus F h h.reflectsZeroObjects E hE

/-- Definition 3.1(3) of arXiv:2607.28411v1, source-facing.  The pullback
`f^♯σ` of a stability condition on `Dᵇ(Y)` along a proper morphism
`f : X → Y` is computed through the direct image `f_* : Dᵇ(X) ⥤ Dᵇ(Y)`,
which is the `push` argument; its class map is `f^♯v = v ∘ f_*`.  The lifting
witness is the conclusion of Proposition 3.3, not an input this definition can
manufacture. -/
abbrev pullback (push : C ⥤ D) [push.Additive] [push.CommShift ℤ]
    [push.IsTriangulated] (h : σ.slicing.PreimageData push) :
    WithClassMap C (v.comp (K₀.map push)) :=
  σ.preimage push h

/-- Definition 3.6(3) of arXiv:2607.28411v1, source-facing.  The pushforward
`f_♯σ` of a stability condition on `Dᵇ(X)` along a morphism of finite
Tor-dimension `f : X → Y` is computed through the inverse image
`f^* : Dᵇ(Y) ⥤ Dᵇ(X)`, which is the `pull` argument; its class map is
`f_♯v = v ∘ f^*`.  The lifting witness is the conclusion of Proposition 3.8. -/
abbrev pushforward (pull : C ⥤ D) [pull.Additive] [pull.CommShift ℤ]
    [pull.IsTriangulated] (h : σ.slicing.PreimageData pull) :
    WithClassMap C (v.comp (K₀.map pull)) :=
  σ.preimage pull h

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
