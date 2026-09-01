/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.StructureModule
import DerivedAlgGeo.Algebra.Module.GradedModule.TwistLocalization

/-!
# Nonnegative twists on degree-one Proj charts

Multiplication and division by a degree-one homogeneous element `f` identify `A(d)` with `A`
over `D₊(f)`.  This file lifts the localization equivalence to the locally fractional sheaves and
then identifies the canonical map

`(A(d)₍f₎)₀ ⟶ Γ(D₊(f), A(d)̃)`

as an equivalence.  Thus the degree-one charts used by polynomial projective space no longer
require a `BasicOpenSectionData` certificate.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- The pointwise trivialization of `A(d)` at a point lying in `D₊(f)`.

The membership proof is taken directly rather than through a bundled element of the chart, so
that one equivalence serves every open contained in `D₊(f)`. -/
noncomputable def natShiftFiberLinearEquivOfMem {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (natShift 𝒜 d) x ≃ₗ[
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 𝒜 x :=
  DegreeZeroLocalization.natShiftLinearEquivOfMem 𝒜 hf d hx

/-- The pointwise trivialization of `A(d)` at a point of `D₊(f)`. -/
noncomputable def natShiftFiberLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (natShift 𝒜 d) x.1 ≃ₗ[
      HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 𝒜 x.1 :=
  natShiftFiberLinearEquivOfMem 𝒜 hf d x.2

/-! ## Integer twists, pointwise

The trivialization of an integer twist is the same construction, with the sign of `d` decided
once inside `DegreeZeroLocalization.intShiftZeroLinearEquiv`. It lands at `A(0)` rather than at
`A`; the identification of `A(0)` with `A` is the separate zero-normalization already available
as `sheafTwistZeroIso` at the sheaf level. -/

/-- The pointwise trivialization of `A(d)` at a point lying in `D₊(f)`, for an integer twist. -/
noncomputable def intShiftFiberLinearEquivOfMem {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (intShift 𝒜 d) x ≃ₗ[
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 (intShift 𝒜 0) x :=
  DegreeZeroLocalization.intShiftZeroLinearEquiv 𝒜 hf d hx

/-- The pointwise trivialization of `A(d)` at a point of `D₊(f)`, for an integer twist. -/
noncomputable def intShiftFiberLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (intShift 𝒜 d) x.1 ≃ₗ[
      HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 (intShift 𝒜 0) x.1 :=
  intShiftFiberLinearEquivOfMem 𝒜 hf d x.2

/-! ## Integer twists, on sections

The same construction as the nonnegative case, pointwise, with the certificate rebuilt by the
single computation rules `intShiftZeroLinearEquiv_apply_mk` and its `symm` sibling. Because
those rules are uniform in the sign of `d`, nothing here splits on it. -/

/-- Trivialize a locally fractional section of `A(d)̃`, over any open contained in `D₊(f)`. -/
noncomputable def intShiftSectionToZeroOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op U) := by
  refine ⟨fun x => intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2) (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + d.toNat,
    ⟨(r : A) * f ^ (-d).toNat,
      DegreeZeroLocalization.mul_pow_toNat_mem_intShift_zero 𝒜 hf d e (r : A) r.2⟩,
    ⟨(t : A) * f ^ d.toNat,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded d.toNat hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) d.toNat)),
    fun y => ?_⟩
  change intShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2) (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.intShiftZeroLinearEquiv_apply_mk 𝒜 hf d (hU (i y).2) _

/-- The inverse trivialization on sections, over any open contained in `D₊(f)`. -/
noncomputable def intShiftSectionFromZeroOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op U)) :
    (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U) := by
  refine ⟨fun x => (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + (-d).toNat,
    ⟨(r : A) * f ^ d.toNat,
      DegreeZeroLocalization.mul_pow_toNat_mem_intShift 𝒜 hf d e (r : A) r.2⟩,
    ⟨(t : A) * f ^ (-d).toNat,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded (-d).toNat hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) (-d).toNat)),
    fun y => ?_⟩
  change (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2)).symm (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.intShiftZeroLinearEquiv_symm_apply_mk 𝒜 hf d (hU (i y).2) _

@[simp]
theorem intShiftSectionToZeroOn_apply {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) (x : U) :
    (intShiftSectionToZeroOn 𝒜 hf d hU s).1 x =
      intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2) (s.1 x) :=
  rfl

@[simp]
theorem intShiftSectionFromZeroOn_apply {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op U)) (x : U) :
    (intShiftSectionFromZeroOn 𝒜 hf d hU s).1 x =
      (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm (s.1 x) :=
  rfl

/-- The pointwise inverse trivialization on a homogeneous fraction. -/
theorem intShiftFiberLinearEquivOfMem_symm_apply_mk {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f)
    (c : NumDenSameDeg 𝒜 (intShift 𝒜 0) x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (intShiftFiberLinearEquivOfMem 𝒜 hf d hx).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + (-d).toNat
          num := ⟨(c.num : A) * f ^ d.toNat,
            DegreeZeroLocalization.mul_pow_toNat_mem_intShift 𝒜 hf d c.deg (c.num : A) c.num.2⟩
          den := ⟨(c.den : A) * f ^ (-d).toNat, by
            simpa using SetLike.mul_mem_graded c.den.2
              (SetLike.pow_mem_graded (-d).toNat hf)⟩
          den_mem := Submonoid.mul_mem _ c.den_mem
            (Submonoid.pow_mem _ hx (-d).toNat) } :=
  DegreeZeroLocalization.intShiftZeroLinearEquiv_symm_apply_mk 𝒜 hf d hx c

/-- Over any open contained in `D₊(f)`, an integer twist is trivial on sections. -/
noncomputable def intShiftSectionAddEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op U) where
  toFun := intShiftSectionToZeroOn 𝒜 hf d hU
  invFun := intShiftSectionFromZeroOn 𝒜 hf d hU
  left_inv s := by
    apply section_ext
    funext x
    exact (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm_apply_apply (s.1 x)
  right_inv s := by
    apply section_ext
    funext x
    exact (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply section_ext
    funext x
    exact (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_add (s.1 x) (t.1 x)

/-- The integer chart trivialization is linear over the structure-sheaf sections. -/
noncomputable def intShiftSectionLinearEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 (intShift 𝒜 0)).1.obj (op U) :=
  { intShiftSectionAddEquivOn 𝒜 hf d hU with
    map_smul' := fun r s => by
      apply section_ext
      funext x
      exact (intShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (s.1 x) }

/-- Divide a locally fractional section of `A(d)̃` by `f ^ d`, over any open contained in
`D₊(f)`.

The trivialization is pointwise, so nothing in the construction refers to the chart itself: only
membership in `D₊(f)` is used, and `hU` supplies exactly that. -/
noncomputable def natShiftSectionToSelfOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 𝒜).1.obj (op U) := by
  refine ⟨fun x => natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2) (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + d, r,
    ⟨(t : A) * f ^ d,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded d hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) d)),
    fun y => ?_⟩
  · change natShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2) (s.1 (i y)) = _
    have hy := h y
    change s.1 (i y) = _ at hy
    rw [hy]
    exact DegreeZeroLocalization.natShiftLinearEquivOfMem_apply_mk
      𝒜 hf d (hU (i y).2) _

/-- Multiply a locally fractional section of `Ã` by `f ^ d`, over any open contained in
`D₊(f)`. -/
noncomputable def natShiftSectionFromSelfOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj (op U)) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) := by
  refine ⟨fun x => (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e,
    ⟨(r : A) * f ^ d,
      by simpa using SetLike.mul_mem_graded r.2 (SetLike.pow_mem_graded d hf)⟩,
    t, ht, fun y => ?_⟩
  change (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2)).symm (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.natShiftLinearEquivOfMem_symm_apply_mk
    𝒜 hf d (hU (i y).2) _

/-- Divide a locally fractional section of `A(d)̃` by `f ^ d`. -/
noncomputable def natShiftSectionToSelf {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (associatedSheafInType 𝒜 𝒜).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionToSelfOn 𝒜 hf d le_rfl s

/-- Multiply a locally fractional section of `Ã` by `f ^ d`. -/
noncomputable def natShiftSectionFromSelf {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionFromSelfOn 𝒜 hf d le_rfl s

/-- Dividing by `f ^ d` commutes with restriction to a smaller open.

This is what makes the pointwise trivialization a map of presheaves rather than a family of
unrelated maps: restriction in `M̃` is precomposition of the underlying function, and the
trivialization is applied pointwise, so the two operations do not interact. -/
theorem natShiftSectionToSelfOn_map {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U U' : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (hU' : U' ≤ U)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 𝒜).1.map (homOfLE hU').op
        (natShiftSectionToSelfOn 𝒜 hf d hU s) =
      natShiftSectionToSelfOn 𝒜 hf d (hU'.trans hU)
        ((associatedSheafInType 𝒜 (natShift 𝒜 d)).1.map (homOfLE hU').op s) := by
  apply section_ext
  funext x
  rfl

/-- Multiplying by `f ^ d` commutes with restriction to a smaller open. -/
theorem natShiftSectionFromSelfOn_map {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U U' : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (hU' : U' ≤ U)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj (op U)) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.map (homOfLE hU').op
        (natShiftSectionFromSelfOn 𝒜 hf d hU s) =
      natShiftSectionFromSelfOn 𝒜 hf d (hU'.trans hU)
        ((associatedSheafInType 𝒜 𝒜).1.map (homOfLE hU').op s) := by
  apply section_ext
  funext x
  rfl

/-- Pointwise value of the chart trivialization on sections.

Stated here, in the generic grading, rather than unfolded at each use. A caller working over a
concrete grading — the polynomial one, say — has types large enough that asking `change` to see
through `natShiftSectionFromSelfOn` exhausts the `isDefEq` budget, while rewriting with this
costs nothing. -/
@[simp]
theorem natShiftSectionFromSelfOn_apply {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj (op U)) (x : U) :
    (natShiftSectionFromSelfOn 𝒜 hf d hU s).1 x =
      (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm (s.1 x) :=
  rfl

/-- Value of the inverse pointwise trivialization on a homogeneous fraction.

`natShiftFiberLinearEquivOfMem` is `natShiftLinearEquivOfMem` at the prime complement, so this is
that lemma transported; it exists so callers can rewrite without unfolding the fiber
abbreviation. -/
@[simp]
theorem natShiftFiberLinearEquivOfMem_symm_apply_mk {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f)
    (c : NumDenSameDeg 𝒜 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (natShiftFiberLinearEquivOfMem 𝒜 hf d hx).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem } :=
  DegreeZeroLocalization.natShiftLinearEquivOfMem_symm_apply_mk 𝒜 hf d hx c

/-- Over any open contained in `D₊(f)`, a nonnegative twist is additively equivalent to the
structure module when `f` has degree one. -/
noncomputable def natShiftSectionAddEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 𝒜).1.obj (op U) where
  toFun := natShiftSectionToSelfOn 𝒜 hf d hU
  invFun := natShiftSectionFromSelfOn 𝒜 hf d hU
  left_inv s := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm_apply_apply (s.1 x)
  right_inv s := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_add (s.1 x) (t.1 x)

/-- Over any open contained in `D₊(f)`, the chart trivialization is linear over the
structure-sheaf sections of that open. -/
noncomputable def natShiftSectionLinearEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 𝒜).1.obj (op U) :=
  { natShiftSectionAddEquivOn 𝒜 hf d hU with
    map_smul' := fun r s => by
      apply section_ext
      funext x
      exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (s.1 x) }

/-- Untwisting a canonical structure-module section is the canonical twisted section.

This is the pointwise heart of every "the constructed comparison is the canonical one" argument
for a nonnegative twist, isolated in the generic grading on purpose. Stated here the types stay
small and the proof is a chain of rewrites; instantiated at a concrete grading — the polynomial
one, where a Čech denominator is a product of variables — the same reasoning done inline
exhausts the `isDefEq` budget. Callers should rewrite with this rather than unfold.

`g` cuts out the open and needs positive degree; `f` is the degree-one element doing the
trivializing, and only has to be invertible there, which `hle` records. -/
theorem natShiftSectionFromSelfOn_selfBasicOpenSectionAddEquiv_mk
    {f g : A} (hf : f ∈ 𝒜 1) {m : ℕ} (hg : g ∈ 𝒜 m) (hm : 0 < m) (d : ℕ)
    (hle : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (c : NumDenSameDeg 𝒜 𝒜 (.powers g)) :
    natShiftSectionFromSelfOn 𝒜 hf d hle
        (selfBasicOpenSectionAddEquiv 𝒜 hg hm (DegreeZeroLocalization.mk c)) =
      moduleAwayToSection 𝒜 (natShift 𝒜 d) g (DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem }) := by
  apply section_ext
  funext y
  rw [natShiftSectionFromSelfOn_apply, selfBasicOpenSectionAddEquiv_apply_mk,
    moduleAwayToSection_apply, moduleAwayToSection_apply,
    DegreeZeroLocalization.mapOfLE_mk, DegreeZeroLocalization.mapOfLE_mk,
    natShiftFiberLinearEquivOfMem_symm_apply_mk]

/-- Over `D₊(f)`, a nonnegative twist is additively equivalent to the structure module when
`f` has degree one. -/
noncomputable def natShiftSectionAddEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ≃+
      (associatedSheafInType 𝒜 𝒜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionAddEquivOn 𝒜 hf d le_rfl

/-- The chart trivialization is linear over the structure-sheaf sections on `D₊(f)`. -/
noncomputable def natShiftSectionLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ≃ₗ[
      𝒪.1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))]
      (associatedSheafInType 𝒜 𝒜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionLinearEquivOn 𝒜 hf d le_rfl

/-! ## The canonical basic-open map -/

/-- The algebraic chart trivialization, the structure-module comparison, and the sheaf chart
trivialization combine to identify the localized shift with its sections on `D₊(f)`. -/
noncomputable def natShiftBasicOpenSectionAddEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃+
      (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  (DegreeZeroLocalization.natShiftSelfLinearEquiv 𝒜 hf d).toAddEquiv |>.trans
    (selfBasicOpenSectionAddEquiv 𝒜 hf Nat.zero_lt_one) |>.trans
      (natShiftSectionAddEquiv 𝒜 hf d).symm

/-- The chart equivalence above is the canonical homogeneous-fraction section map. -/
theorem natShiftBasicOpenSectionAddEquiv_apply_mk {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) (.powers f)) :
    natShiftBasicOpenSectionAddEquiv 𝒜 hf d (DegreeZeroLocalization.mk c) =
      moduleAwayToSection 𝒜 (natShift 𝒜 d) f (DegreeZeroLocalization.mk c) := by
  change natShiftSectionFromSelf 𝒜 hf d
    (selfBasicOpenSectionAddEquiv 𝒜 hf Nat.zero_lt_one
      (DegreeZeroLocalization.natShiftSelfLinearEquiv 𝒜 hf d
        (DegreeZeroLocalization.mk c))) = _
  rw [DegreeZeroLocalization.natShiftSelfLinearEquiv_apply_mk,
    selfBasicOpenSectionAddEquiv_apply_mk]
  apply section_ext
  funext x
  change (natShiftFiberLinearEquiv 𝒜 hf d x).symm
      ((moduleAwayToSection 𝒜 𝒜 f (DegreeZeroLocalization.mk _)).1 x) =
    (moduleAwayToSection 𝒜 (natShift 𝒜 d) f (DegreeZeroLocalization.mk c)).1 x
  rw [moduleAwayToSection_apply, moduleAwayToSection_apply,
    DegreeZeroLocalization.mapOfLE_mk, DegreeZeroLocalization.mapOfLE_mk]
  let x' : ProjectiveSpectrum.basicOpen 𝒜 f := ⟨x.1, x.2⟩
  change (DegreeZeroLocalization.natShiftLinearEquivOfMem 𝒜 hf d x'.2).symm
      (DegreeZeroLocalization.mk _) = DegreeZeroLocalization.mk _
  rw [DegreeZeroLocalization.natShiftLinearEquivOfMem_symm_apply_mk]
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul]
  change (c.den : A) * ((c.num : A) * f ^ d) =
    ((c.den : A) * f ^ d) * (c.num : A)
  ac_rfl

/-- As an additive map, the constructed chart equivalence is exactly the canonical map from
homogeneous fractions to locally fractional sections. -/
theorem natShiftBasicOpenSectionAddEquiv_toAddMonoidHom {f : A}
    (hf : f ∈ 𝒜 1) (d : ℕ) :
    (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).toAddMonoidHom =
      moduleAwayToSection 𝒜 (natShift 𝒜 d) f :=
  moduleAwayToSection_unique 𝒜 (natShift 𝒜 d) f _
    (natShiftBasicOpenSectionAddEquiv_apply_mk 𝒜 hf d)

/-- For a nonnegative twist, the canonical basic-open section map is bijective on every
degree-one chart. -/
theorem moduleAwayToSection_natShift_degreeOne_bijective {f : A}
    (hf : f ∈ 𝒜 1) (d : ℕ) :
    Function.Bijective (moduleAwayToSection 𝒜 (natShift 𝒜 d) f) := by
  rw [← moduleAwayToSection_unique 𝒜 (natShift 𝒜 d) f
    (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).toAddMonoidHom
    (natShiftBasicOpenSectionAddEquiv_apply_mk 𝒜 hf d)]
  exact (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).bijective

/-! ## The same trivialization, for a graded module

`TwistLocalization.lean`'s `GradedModule` section trivializes an integer twist of an arbitrary
graded module on any localization containing a degree-one element. The fiber at a point of `D₊(f)`
is such a localization, so the pointwise statement costs nothing beyond naming it — exactly as
`intShiftFiberLinearEquivOfMem` costs nothing over `intShiftZeroLinearEquiv`.

Everything above this section is `𝒜` as a module over itself, which is all the twisting sheaf
needs. `#584`'s tensor comparison `F ⊗ O(d) ≅ F(d)` needs the module case, and this is the fiber
half of it. The section and `.over` halves are not here.
-/

section GradedModule

variable {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
variable (𝓜 : ℕ → σM) [SetLike.GradedSMul 𝒜 𝓜]

/-- The pointwise trivialization of `M(d)` at a point lying in `D₊(f)`, for an integer twist. -/
noncomputable def intShiftModuleFiberLinearEquivOfMem {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (intShift 𝓜 d) x ≃ₗ[
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 (intShift 𝓜 0) x :=
  DegreeZeroLocalization.intShiftZeroModuleLinearEquiv 𝒜 𝓜 hf d hx

/-- The pointwise trivialization of `M(d)` at a point of `D₊(f)`, for an integer twist. -/
noncomputable def intShiftModuleFiberLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (intShift 𝓜 d) x.1 ≃ₗ[
      HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 (intShift 𝓜 0) x.1 :=
  intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d x.2

/-! ### The same, on sections

The section-level port of the fiber trivialization above. The shape is
`intShiftSectionToZeroOn`'s exactly: apply the fiber equivalence pointwise, then rebuild the
local-fraction certificate with the `_apply_mk` rule. The numerator becomes `f ^ k • r` rather than
`r * f ^ k`, which is the order `LocalizedModule.mk_smul_mk` produces; the denominator is
unchanged, because it lives in `𝒜` either way. -/

/-- Divide a locally fractional section of `M(d)~` by `f ^ d`, over any open inside `D₊(f)`. -/
noncomputable def intShiftModuleSectionToZeroOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 (intShift 𝓜 0)).1.obj (op U) := by
  refine ⟨fun x => intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2) (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + d.toNat,
    ⟨f ^ (-d).toNat • (r : M),
      DegreeZeroLocalization.pow_smul_mem_intShift_zero 𝒜 𝓜 hf d e (r : M) r.2⟩,
    ⟨(t : A) * f ^ d.toNat,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded d.toNat hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) d.toNat)),
    fun y => ?_⟩
  change intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU (i y).2) (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.intShiftZeroModuleLinearEquiv_apply_mk 𝒜 𝓜 hf d (hU (i y).2) _

/-- The inverse trivialization on sections, over any open contained in `D₊(f)`. -/
noncomputable def intShiftModuleSectionFromZeroOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (intShift 𝓜 0)).1.obj (op U)) :
    (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) := by
  refine ⟨fun x => (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2)).symm (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + (-d).toNat,
    ⟨f ^ d.toNat • (r : M),
      DegreeZeroLocalization.pow_smul_mem_intShift 𝒜 𝓜 hf d e (r : M) r.2⟩,
    ⟨(t : A) * f ^ (-d).toNat,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded (-d).toNat hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) (-d).toNat)),
    fun y => ?_⟩
  change (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU (i y).2)).symm (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.intShiftZeroModuleLinearEquiv_symm_apply_mk
    𝒜 𝓜 hf d (hU (i y).2) _

/-- Over any open contained in `D₊(f)`, an integer twist of a module is trivial on sections. -/
noncomputable def intShiftModuleSectionAddEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 (intShift 𝓜 0)).1.obj (op U) where
  toFun := intShiftModuleSectionToZeroOn 𝒜 𝓜 hf d hU
  invFun := intShiftModuleSectionFromZeroOn 𝒜 𝓜 hf d hU
  left_inv s := by
    apply section_ext
    funext x
    exact (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2)).symm_apply_apply (s.1 x)
  right_inv s := by
    apply section_ext
    funext x
    exact (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2)).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply section_ext
    funext x
    exact (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2)).map_add (s.1 x) (t.1 x)

/-- The module chart trivialization is linear over the structure-sheaf sections. -/
noncomputable def intShiftModuleSectionLinearEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 (intShift 𝓜 0)).1.obj (op U) :=
  { intShiftModuleSectionAddEquivOn 𝒜 𝓜 hf d hU with
    map_smul' := fun r s => by
      apply section_ext
      funext x
      exact (intShiftModuleFiberLinearEquivOfMem 𝒜 𝓜 hf d (hU x.2)).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (s.1 x) }

end GradedModule

end AlgebraicGeometry.Proj
