/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.PreStability
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.FirstStrictSES
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Slicing.IntervalFiniteTransfer

/-!
# Local finiteness under transfer, and transfer of stability conditions

Bridgeland's stability conditions are the locally finite pre-stability
conditions.  This file shows that local finiteness survives transfer along a
phase-detecting functor, and therefore upgrades
`PreStabilityCondition.WithClassMap.preimage` to
`StabilityCondition.WithClassMap.preimage`.

## Main definitions

* `Slicing.PreimageData.intervalFunctor`: the detecting functor restricted to
  a thin phase window, the carrier of the whole finite-length argument.
* `Slicing.PreimageData.strictImage`: the induced map on strict subobjects,
  an instance of the Foundation-level `strictImage`.
* `StabilityCondition.WithClassMap.preimage`: the transported stability
  condition, with its source-facing names `pullback` and `pushforward`.

## Main results

* `Slicing.PreimageData.reflectsIsomorphisms`: a functor carrying
  slicing-lifting data reflects isomorphisms.  The cone of a morphism is
  killed by the functor exactly when the morphism becomes invertible, and the
  functor reflects zero objects.
* `Slicing.preimage_intervalProp_iff`: thin-interval membership for the
  preimage slicing is detected by the functor, because both extreme phases
  are.
* `Slicing.PreimageData.strictImage_strictMono`: the image map on strict
  subobjects is strictly monotone, without fullness or faithfulness.
* `Slicing.PreimageData.isLocallyFinite`: the preimage of a locally finite
  slicing is locally finite, with the same radius.

## Implementation notes

The proof follows `mapEquiv_isLocallyFinite` in
`Symmetry/Autoequivalence/Stability/Transport.lean`, with one genuine
difference.  There the functor was an equivalence, so the image map on strict
subobjects was injective by fullness (`strictImage_injective`).  A
phase-detecting functor need not be full or faithful, so injectivity is
replaced by the argument that a strictly smaller subobject stays strictly
smaller: if the images of `B₁ < B₂` agreed, the comparison `B₁ ⟶ B₂` would
become invertible, and a functor that reflects isomorphisms would make it
invertible already, contradicting `B₁ ≠ B₂`.  This is exactly the place where
the Hom-vanishing half of `Slicing.PreimageData` is used, through
`reflectsZeroObjects`.  The image map itself and its monotonicity are the
Foundation-level `strictImage` and `strictImage_monotone`, which need only
preservation of strict monos; the well-foundedness transfer is
`isStrictArtinianObject_of_strictMono` and its Noetherian twin.

The image map is built on strict subobjects rather than on the intrinsic
admissible subobjects.  The two orders agree in a thin interval by
`admissibleStrictSubobjectOrderIso`, and strict subobjects are the ones for
which the functor's action on canonical arrows is available.

## References

* arXiv:2607.28411v1, Remarks 3.2 and 3.7, which take conservativity as an
  input; here it is derived.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat

universe v₁ u₁ v₂ u₂ u'

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Thin-interval membership for the preimage slicing is detected by the
functor: both extreme phases are computed on the image
(`Slicing.preimage_phiPlus`, `Slicing.preimage_phiMinus`), and zero objects
are reflected by the lifting witness.  The direct analogue of
`Slicing.preimage_ltProp_iff` for the two-sided window. -/
theorem Slicing.preimage_intervalProp_iff (s : Slicing D) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F) (a b : ℝ) (E : C) :
    (s.preimage F h).intervalProp C a b E ↔ s.intervalProp D a b (F.obj E) := by
  by_cases hE : IsZero E
  · exact iff_of_true (Or.inl hE) (Or.inl (F.map_isZero hE))
  · rw [(s.preimage F h).intervalProp_iff_intrinsic_phases C hE,
      s.intervalProp_iff_intrinsic_phases D (h.not_isZero_obj hE),
      s.preimage_phiPlus F h h.reflectsZeroObjects E hE,
      s.preimage_phiMinus F h h.reflectsZeroObjects E hE]

namespace Slicing.PreimageData

variable {s : Slicing D} {F : C ⥤ D} [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
  (h : s.PreimageData F)

/-! ### Reflecting isomorphisms -/

omit [F.Additive] in
include h in
/-- A functor carrying slicing-lifting data reflects isomorphisms.  Complete
`f` to a distinguished triangle; its image is distinguished with first map
`F.map f`, so the image of the cone is zero, so the cone is zero by
`reflectsZeroObjects`, so `f` is an isomorphism. -/
theorem reflectsIsomorphisms : F.ReflectsIsomorphisms := by
  refine ⟨fun {X Y} f hf => ?_⟩
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hFT := F.map_distinguished _ hT
  have hFZ : IsZero (F.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ hFT).mpr hf
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).mp (h.reflectsZeroObjects Z hFZ)

/-! ### Thin intervals -/

/-- The detecting functor restricted to a thin interval of the preimage
slicing, landing in the same thin interval of the target slicing.

An `abbrev`, as `autIntervalFunctor` is, so that instance search sees the
underlying `ObjectProperty.lift`. -/
abbrev intervalFunctor (a b : ℝ) :
    (s.preimage F h).IntervalCat C a b ⥤ s.IntervalCat D a b :=
  (s.intervalProp D a b).lift (((s.preimage F h).intervalProp C a b).ι ⋙ F)
    (fun X => (s.preimage_intervalProp_iff F h a b X.obj).mp X.property)

variable [IsTriangulated C] [IsTriangulated D]

section ThinInterval

variable (a b : ℝ) [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The restricted functor preserves strict monomorphisms, by the cone route:
a strict mono and its cokernel extend to an ambient distinguished triangle,
the functor keeps it distinguished with all three vertices in the target
interval, and a distinguished triangle on a thin interval is a strict short
exact sequence there. -/
theorem intervalFunctor_map_strictMono
    {X Y : (s.preimage F h).IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    IsStrictMono ((h.intervalFunctor a b).map f) := by
  let S : ShortComplex ((s.preimage F h).IntervalCat C a b) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hsse : StrictShortExact S := strictShortExact_cokernel C f hf
  obtain ⟨δ, hδ⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C (s.preimage F h) hsse
  let G := h.intervalFunctor a b
  let SG := S.map G
  have hmap : Triangle.mk SG.f.hom SG.g.hom
      (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app X.obj) ∈ distTriang D :=
    F.map_distinguished _ hδ
  have hSG := Slicing.IntervalCat.strictShortExact_of_distinguished (S := SG) D s hmap
  exact ⟨hSG.shortExact.mono_f, hSG.strict_f⟩

/-- The image of a strict subobject under the restricted functor, taken as a
*strict* subobject rather than a bare `Subobject`: `intervalFunctor_map_strictMono`
is what makes the canonical representative arrow strict, and strictness is
what the finite-length orders are stated about.  This is the Foundation-level
`strictImage` at the restricted functor, so `strictImage_monotone` applies
verbatim.  Unlike `strictSubobjectImageOfFullFaithful`, this map is not
injective in general, since the detecting functor need not be faithful; that
is why `strictImage_strictMono` below goes through reflection of
isomorphisms instead. -/
abbrev strictImage {E : (s.preimage F h).IntervalCat C a b} :
    StrictSubobject E → StrictSubobject ((h.intervalFunctor a b).obj E) :=
  CategoryTheory.Triangulated.strictImage (h.intervalFunctor a b)
    (fun f hf => h.intervalFunctor_map_strictMono a b f hf)
    (fun f _ hf => intervalSubobject_arrow_strictMono (C := D) f hf)

/-- The image map on strict subobjects is strictly monotone.  Monotonicity
gives `≤`; if the images of `B₁ < B₂` were equal, the comparison morphism
`B₁ ⟶ B₂` would map to an isomorphism, hence be an isomorphism because the
functor reflects them, hence identify `B₁` with `B₂`. -/
theorem strictImage_strictMono {E : (s.preimage F h).IntervalCat C a b} :
    StrictMono (h.strictImage a b (E := E)) := by
  intro B₁ B₂ hlt
  refine lt_of_le_of_ne (strictImage_monotone _ _ _ hlt.le) ?_
  intro hEq
  apply hlt.ne
  letI hs₁ : IsStrictMono ((h.intervalFunctor a b).map B₁.1.arrow) :=
    h.intervalFunctor_map_strictMono a b B₁.1.arrow B₁.2
  letI hs₂ : IsStrictMono ((h.intervalFunctor a b).map B₂.1.arrow) :=
    h.intervalFunctor_map_strictMono a b B₂.1.arrow B₂.2
  letI : Mono ((h.intervalFunctor a b).map B₁.1.arrow) := hs₁.mono
  letI : Mono ((h.intervalFunctor a b).map B₂.1.arrow) := hs₂.mono
  have hEq' : Subobject.mk ((h.intervalFunctor a b).map B₁.1.arrow) =
      Subobject.mk ((h.intervalFunctor a b).map B₂.1.arrow) :=
    congrArg Subtype.val hEq
  let j := Subobject.ofLE B₁.1 B₂.1 hlt.le
  have hj : j ≫ B₂.1.arrow = B₁.1.arrow := Subobject.ofLE_arrow hlt.le
  have hGj : (h.intervalFunctor a b).map j =
      (Subobject.isoOfMkEqMk ((h.intervalFunctor a b).map B₁.1.arrow)
        ((h.intervalFunctor a b).map B₂.1.arrow) hEq').hom := by
    rw [← cancel_mono ((h.intervalFunctor a b).map B₂.1.arrow), ← Functor.map_comp, hj,
      Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]
  haveI : IsIso ((h.intervalFunctor a b).map j) := by
    rw [hGj]
    infer_instance
  haveI : IsIso (F.map j.hom) :=
    (inferInstance : IsIso ((s.intervalProp D a b).ι.map ((h.intervalFunctor a b).map j)))
  haveI := h.reflectsIsomorphisms
  haveI : IsIso (((s.preimage F h).intervalProp C a b).ι.map j) :=
    isIso_of_reflects_iso j.hom F
  haveI : IsIso j := isIso_of_reflects_iso j ((s.preimage F h).intervalProp C a b).ι
  exact Subtype.ext (Subobject.eq_of_comm (asIso j) (by simpa using hj))

/-- Strict finite length descends along the restricted functor: both chain
conditions on strict subobjects of the image pull back through the strictly
monotone image map, by `isStrictArtinianObject_of_strictMono` and its
Noetherian twin. -/
theorem isStrictFiniteLengthObject_of_intervalFunctor_obj
    {E : (s.preimage F h).IntervalCat C a b}
    (hE : IsStrictFiniteLengthObject ((h.intervalFunctor a b).obj E)) :
    IsStrictFiniteLengthObject E := by
  letI : IsStrictArtinianObject ((h.intervalFunctor a b).obj E) := hE.1
  letI : IsStrictNoetherianObject ((h.intervalFunctor a b).obj E) := hE.2
  exact ⟨isStrictArtinianObject_of_strictMono _ (h.strictImage_strictMono a b),
    isStrictNoetherianObject_of_strictMono _ (h.strictImage_strictMono a b)⟩

end ThinInterval

/-- **Local finiteness survives transfer, with the same radius.**  The
interval windows do not move, so the radius of the target slicing works
verbatim; the content is the descent of strict finite length along the
restricted functor, converted to and from the intrinsic admissible-subobject
formulation by `admissibleStrictSubobjectOrderIso`. -/
theorem isLocallyFinite (hs : s.IsLocallyFinite D) :
    (s.preimage F h).IsLocallyFinite C := by
  obtain ⟨η, hη, hη2, hlf⟩ := hs.intervalFinite
  refine ⟨⟨η, hη, hη2, fun t E => ?_⟩⟩
  haveI : Fact (t - η < t + η) := ⟨by linarith⟩
  haveI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
  have hbig : s.IsFiniteLength D ((h.intervalFunctor (t - η) (t + η)).obj E) :=
    hlf t _
  exact Slicing.IntervalCat.isFiniteLength_of_isStrictFiniteLength C (s.preimage F h)
    (h.isStrictFiniteLengthObject_of_intervalFunctor_obj (t - η) (t + η)
      (isStrictFiniteLength_of_isFiniteLength D hbig))

end Slicing.PreimageData

namespace StabilityCondition.WithClassMap

variable [IsTriangulated C] [IsTriangulated D]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ D →+ Λ}
variable (σ : StabilityCondition.WithClassMap D v) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : σ.slicing.PreimageData F)

/-- The stability condition transported along a phase-detecting functor.  The
pre-stability data is `PreStabilityCondition.WithClassMap.preimage`; local
finiteness is `Slicing.PreimageData.isLocallyFinite`.  This is the
Bridgeland-definition form of Remarks 3.2 and 3.7 of arXiv:2607.28411v1: once
the preimage collection is a slicing, transfer produces a stability condition
with respect to `(Λ, v ∘ K₀(F))`. -/
def preimage : StabilityCondition.WithClassMap C (v.comp (K₀.map F)) where
  toWithClassMap := σ.toWithClassMap.preimage F h
  locallyFinite := h.isLocallyFinite σ.locallyFinite

/-- Forgetting local finiteness commutes with transfer.  Definitional;
recorded so that every pre-stability result about `preimage` applies to the
stability-level construction through one `simp` step. -/
@[simp]
theorem preimage_toWithClassMap :
    (σ.preimage F h).toWithClassMap = σ.toWithClassMap.preimage F h := rfl

/-- The slicing of the transported stability condition is the preimage
slicing.  Restated at the stability-condition level so callers need not go
through `preimage_toWithClassMap`. -/
@[simp]
theorem preimage_slicing : (σ.preimage F h).slicing = σ.slicing.preimage F h := rfl

/-- Transfer leaves the central charge on `Λ` untouched.  Restated at the
stability-condition level so callers need not go through
`preimage_toWithClassMap`. -/
@[simp]
theorem preimage_Z : (σ.preimage F h).Z = σ.Z := rfl

/-- The transported central charge of an object is the original charge of its
image.  Not a `simp` lemma: `simp` already derives it from
`preimage_toWithClassMap` and the pre-stability `preimage_charge`, so it is
recorded only as the direct restatement a caller can `rw` with. -/
theorem preimage_charge (E : C) :
    (σ.preimage F h).charge E = σ.charge (F.obj E) :=
  σ.toWithClassMap.preimage_charge F h E

/-- Definition 3.1(3) of arXiv:2607.28411v1 for stability conditions: the
pullback `f^♯σ` is computed through the direct image `push = f_*`.  The name
follows `Slicing.pullback` in `Phase.Transfer.Basic`. -/
abbrev pullback (push : C ⥤ D) [push.Additive] [push.CommShift ℤ]
    [push.IsTriangulated] (h : σ.slicing.PreimageData push) :
    StabilityCondition.WithClassMap C (v.comp (K₀.map push)) :=
  σ.preimage push h

/-- Definition 3.6(3) of arXiv:2607.28411v1 for stability conditions: the
pushforward `f_♯σ` is computed through the inverse image `pull = f^*`.  The
name follows `Slicing.pushforward` in `Phase.Transfer.Basic`. -/
abbrev pushforward (pull : C ⥤ D) [pull.Additive] [pull.CommShift ℤ]
    [pull.IsTriangulated] (h : σ.slicing.PreimageData pull) :
    StabilityCondition.WithClassMap C (v.comp (K₀.map pull)) :=
  σ.preimage pull h

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
