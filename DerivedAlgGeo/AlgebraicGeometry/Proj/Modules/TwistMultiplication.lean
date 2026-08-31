/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Shift
import DerivedAlgGeo.Algebra.Module.GradedModule.TwistLocalization
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.AssociatedSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The twisted multiplication `A(d) ⊗ M → M(d)`, at a localization

`#584`'s remaining piece is the comparison `F ⊗ O(d) ≅ F(d)` — *tensoring with `O(d)` is shifting
the grading by `d`*. Both routes to it need the same thing first: a map, and the map is
multiplication of homogeneous fractions. This file supplies it at one localization, with the
bilinearity a tensor lift consumes.

## Why it is short

Because of a fact about the model rather than a construction. `DegreeZeroLocalization 𝒜 𝓝 S` is a
submodule of `LocalizedModule S M`, and for `𝓝` over the ring itself the ambient is
`LocalizedModule S A`, which **is** `Localization S`. So an element of
`DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S` is already a scalar acting on `LocalizedModule S M`:
no multiplication has to be defined on representatives, and no well-definedness argument is
needed. All that is left is to check the product lands in the right submodule, which is
`smul_mem_intShift` on the numerator and `SetLike.mul_mem_graded` on the denominator.

This is the same observation that made `#689` and `#692` tractable — the grading is a property of
subobjects of one ambient, not extra structure the ambient knows about.

## The one thing that does not come free

`twistMul_smul_right` needs `SMulCommClass (HomogeneousLocalization 𝒜 S) (LocalizedModule S A)
(LocalizedModule S M)`, which is not an instance. The `HomogeneousLocalization 𝒜 S`-action is
`Module.compHom` along `algebraMap` into `Localization S`, so naming that map moves the goal into
`Localization S` where commutativity is free. The same gap appeared in `#695`'s `map_smul'`.

## Up to the presheaf

`sectionTwistMul` is the same product on sections. Its local-fraction certificate is the product of
the two factors' certificates on the intersection of their opens, rebuilt by `twistMul_mk` — which
is what that rule exists for. Three details carry the proof: the neighbourhood must be `V₁ ⊓ V₂`,
because each factor's fraction is valid only on its own open; the denominator misses the point by
primality, since neither factor's does; and the degree is `e₂ + e₁` in that order, because
`twistMul` takes the `A(d)` factor first.

`twistMultiplicationHom` is then `ModuleCat.MonoidalCategory.tensorLift` fed the four laws
`LinearMap.mk₂` asks for. Note the scalar changes ring between the two levels: a section-level
scalar lives in `Γ(U, 𝒪)` and a fibre-level one in `HomogeneousLocalization 𝒜 (primeCompl x)`, so
the two `smul` laws push it through `openToLocalization`. The argument order flips with it —
section-level *left* linearity is fibre-level `twistMul_*_right`.

## What the chart sees

`intShiftZeroModuleLinearEquiv_twistMul` is the identity the isomorphism proof turns on. On a
localization containing a degree-one `f`, the module trivialization and the ring trivialization are
multiplication by the *same* scalar, so they commute with the product by associativity of that
action and nothing else. Read the other way: over a degree-one chart the twisted multiplication
*is* the untwisted one, conjugated by two isomorphisms — which is why the local half of
`Presheaf.W_of_coversTop` should not need the generator machinery
`Divisors/AssociatedSheaf/Construction.lean` builds for the corresponding Cartier statement.

## Scope

The map, and what it looks like on a chart. That it is an **isomorphism** is not here:
`TwistComparison.lean` lifts the chart identity to sections, reads the untwisted multiplication as
the right unitor, and feeds the result to `Presheaf.W_of_coversTop` over
`degreeOneCharts_coversTop`.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace MonoidalCategory

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
variable (S : Submonoid A) (d : ℤ)

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- The monoidal structure on presheaves of modules over the structure presheaf.

Needed to write `⊗` in `twistMultiplicationHom`, and `local` for the same reason
`Divisors/AssociatedSheaf/Construction.lean` keeps its copy local: it is a choice of structure on
a category this file does not own. Named rather than anonymous because the generated name for this
type carries an underscore, which the naming linter rejects. -/
noncomputable local instance monoidalCategoryAssociatedPresheaf :
    MonoidalCategory (PresheafOfModules (𝒪.1 ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.monoidalCategory (R := 𝒪.1)

/-- **Multiplication by a section of `A(d)`, landing in `M(d)`.**

The underlying element is the scalar action of `LocalizedModule S A = Localization S` on
`LocalizedModule S M`; only the certificate is new. -/
noncomputable def twistMul
    (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    DegreeZeroLocalization 𝒜 (intShift 𝓜 d) S := by
  refine ⟨(w : LocalizedModule S A) • (z : LocalizedModule S M), ?_⟩
  obtain ⟨cw, hw⟩ := w.property
  obtain ⟨cz, hz⟩ := z.property
  refine ⟨{ deg := cw.deg + cz.deg
            num := ⟨(cw.num : A) • (cz.num : M),
              smul_mem_intShift 𝒜 𝓜 d cw.deg cz.deg cw.num.2 cz.num.2⟩
            den := ⟨(cw.den : A) * (cz.den : A),
              SetLike.mul_mem_graded cw.den.2 cz.den.2⟩
            den_mem := S.mul_mem cw.den_mem cz.den_mem }, ?_⟩
  rw [← hw, ← hz]
  show LocalizedModule.mk ((cw.num : A) • (cz.num : M))
      (⟨(cw.den : A) * (cz.den : A), _⟩ : S) =
    LocalizedModule.mk (cw.num : A) (⟨(cw.den : A), cw.den_mem⟩ : S) •
      LocalizedModule.mk (cz.num : M) (⟨(cz.den : A), cz.den_mem⟩ : S)
  exact (LocalizedModule.mk_smul_mk (cw.num : A) (cz.num : M)
    (⟨(cw.den : A), cw.den_mem⟩ : S) (⟨(cz.den : A), cz.den_mem⟩ : S)).symm

@[simp]
theorem coe_twistMul (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    ((twistMul 𝒜 𝓜 S d w z : DegreeZeroLocalization 𝒜 (intShift 𝓜 d) S) :
        LocalizedModule S M) =
      (w : LocalizedModule S A) • (z : LocalizedModule S M) := rfl

/-- The twisted multiplication in explicit fractions.

The rule a caller needs to rebuild a local-fraction certificate downstream, in the same role
`intShiftZeroLinearEquiv_apply_mk` plays for the chart trivialization. -/
@[simp]
theorem twistMul_mk (cw : NumDenSameDeg 𝒜 (intShift 𝒜 d) S) (cz : NumDenSameDeg 𝒜 𝓜 S) :
    twistMul 𝒜 𝓜 S d (DegreeZeroLocalization.mk cw) (DegreeZeroLocalization.mk cz) =
      DegreeZeroLocalization.mk
        { deg := cw.deg + cz.deg
          num := ⟨(cw.num : A) • (cz.num : M),
            smul_mem_intShift 𝒜 𝓜 d cw.deg cz.deg cw.num.2 cz.num.2⟩
          den := ⟨(cw.den : A) * (cz.den : A),
            SetLike.mul_mem_graded cw.den.2 cz.den.2⟩
          den_mem := S.mul_mem cw.den_mem cz.den_mem } := by
  apply DegreeZeroLocalization.ext
  simp only [coe_twistMul, DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
  exact LocalizedModule.mk_smul_mk _ _ _ _

theorem twistMul_add_left (w w' : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    twistMul 𝒜 𝓜 S d (w + w') z = twistMul 𝒜 𝓜 S d w z + twistMul 𝒜 𝓜 S d w' z := by
  apply DegreeZeroLocalization.ext
  simp only [coe_twistMul, DegreeZeroLocalization.coe_add]
  exact add_smul _ _ _

theorem twistMul_add_right (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z z' : DegreeZeroLocalization 𝒜 𝓜 S) :
    twistMul 𝒜 𝓜 S d w (z + z') = twistMul 𝒜 𝓜 S d w z + twistMul 𝒜 𝓜 S d w z' := by
  apply DegreeZeroLocalization.ext
  simp only [coe_twistMul, DegreeZeroLocalization.coe_add]
  exact smul_add _ _ _

theorem twistMul_smul_left (a : HomogeneousLocalization 𝒜 S)
    (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    twistMul 𝒜 𝓜 S d (a • w) z = a • twistMul 𝒜 𝓜 S d w z := by
  apply DegreeZeroLocalization.ext
  simp only [coe_twistMul, DegreeZeroLocalization.coe_smul]
  exact mul_smul _ _ _

theorem twistMul_smul_right (a : HomogeneousLocalization 𝒜 S)
    (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    twistMul 𝒜 𝓜 S d w (a • z) = a • twistMul 𝒜 𝓜 S d w z := by
  apply DegreeZeroLocalization.ext
  simp only [coe_twistMul, DegreeZeroLocalization.coe_smul]
  exact smul_comm (w : LocalizedModule S A)
    (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S) a)
    (z : LocalizedModule S M)

/-- **The twisted multiplication on sections.** -/
noncomputable def sectionTwistMul {U : Opens X}
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 (intShift 𝓜 d)).1.obj (op U) := by
  refine ⟨fun x => twistMul 𝒜 𝓜 _ d (t.1 x) (s.1 x), ?_⟩
  intro x
  obtain ⟨V₁, hxV₁, i₁, e₁, r₁, u₁, hu₁, h₁⟩ := s.2 x
  obtain ⟨V₂, hxV₂, i₂, e₂, r₂, u₂, hu₂, h₂⟩ := t.2 x
  refine ⟨V₁ ⊓ V₂, ⟨hxV₁, hxV₂⟩,
    homOfLE (le_trans inf_le_left (leOfHom i₁)), e₂ + e₁,
    ⟨(r₂ : A) • (r₁ : M),
      smul_mem_intShift 𝒜 𝓜 d e₂ e₁ r₂.2 r₁.2⟩,
    ⟨(u₂ : A) * (u₁ : A), SetLike.mul_mem_graded u₂.2 u₁.2⟩, ?_, ?_⟩
  · rintro ⟨y, hy₁, hy₂⟩
    intro hc
    rcases y.isPrime.mem_or_mem hc with hc2 | hc1
    · exact hu₂ ⟨y, hy₂⟩ hc2
    · exact hu₁ ⟨y, hy₁⟩ hc1
  · rintro ⟨y, hy₁, hy₂⟩
    have hs : s.1 (i₁ ⟨y, hy₁⟩) =
        DegreeZeroLocalization.mk
          { deg := e₁, num := r₁, den := u₁, den_mem := hu₁ ⟨y, hy₁⟩ } := h₁ ⟨y, hy₁⟩
    have ht : t.1 (i₂ ⟨y, hy₂⟩) =
        DegreeZeroLocalization.mk
          { deg := e₂, num := r₂, den := u₂, den_mem := hu₂ ⟨y, hy₂⟩ } := h₂ ⟨y, hy₂⟩
    show twistMul 𝒜 𝓜 _ d (t.1 (i₂ ⟨y, hy₂⟩)) (s.1 (i₁ ⟨y, hy₁⟩)) = _
    rw [hs, ht, twistMul_mk]


@[simp]
theorem sectionTwistMul_apply {U : Opens X}
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) (x : U) :
    (sectionTwistMul 𝒜 𝓜 d s t).1 x = twistMul 𝒜 𝓜 _ d (t.1 x) (s.1 x) := rfl

theorem sectionTwistMul_add_left {U : Opens X}
    (s₁ s₂ : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    sectionTwistMul 𝒜 𝓜 d (s₁ + s₂) t =
      sectionTwistMul 𝒜 𝓜 d s₁ t + sectionTwistMul 𝒜 𝓜 d s₂ t := by
  apply section_ext
  funext x
  exact twistMul_add_right 𝒜 𝓜 _ d (t.1 x) (s₁.1 x) (s₂.1 x)

theorem sectionTwistMul_add_right {U : Opens X}
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t₁ t₂ : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    sectionTwistMul 𝒜 𝓜 d s (t₁ + t₂) =
      sectionTwistMul 𝒜 𝓜 d s t₁ + sectionTwistMul 𝒜 𝓜 d s t₂ := by
  apply section_ext
  funext x
  exact twistMul_add_left 𝒜 𝓜 _ d (t₁.1 x) (t₂.1 x) (s.1 x)

theorem sectionTwistMul_smul_left {U : Opens X} (r : 𝒪.1.obj (op U))
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    sectionTwistMul 𝒜 𝓜 d (r • s) t = r • sectionTwistMul 𝒜 𝓜 d s t := by
  apply section_ext
  funext x
  exact twistMul_smul_right 𝒜 𝓜 _ d
    (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (t.1 x) (s.1 x)

theorem sectionTwistMul_smul_right {U : Opens X} (r : 𝒪.1.obj (op U))
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U))
    (t : (associatedSheafInType 𝒜 (intShift 𝒜 d)).1.obj (op U)) :
    sectionTwistMul 𝒜 𝓜 d s (r • t) = r • sectionTwistMul 𝒜 𝓜 d s t := by
  apply section_ext
  funext x
  exact twistMul_smul_left 𝒜 𝓜 _ d
    (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (t.1 x) (s.1 x)

/-- **The twisted multiplication as a map of presheaves of modules.** -/
noncomputable def twistMultiplicationHom :
    associatedPresheaf 𝒜 𝓜 ⊗ associatedPresheaf 𝒜 (intShift 𝒜 d) ⟶
      associatedPresheaf 𝒜 (intShift 𝓜 d) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t => sectionTwistMul 𝒜 𝓜 d s t)
    (fun s₁ s₂ t => sectionTwistMul_add_left 𝒜 𝓜 d s₁ s₂ t)
    (fun r s t => sectionTwistMul_smul_left 𝒜 𝓜 d r s t)
    (fun s t₁ t₂ => sectionTwistMul_add_right 𝒜 𝓜 d s t₁ t₂)
    (fun r s t => sectionTwistMul_smul_right 𝒜 𝓜 d r s t)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    apply section_ext
    funext x
    rfl

/-- **The chart trivializations intertwine the twisted multiplication.**

Both are multiplication by the same scalar, so this is associativity of that action and nothing
more. Over a degree-one chart it says the twisted multiplication is the untwisted one conjugated by
the two trivializations, which is the local statement the comparison's isomorphism proof needs. -/
theorem intShiftZeroModuleLinearEquiv_twistMul {f : A} (hf : f ∈ 𝒜 1) (hfS : f ∈ S)
    (w : DegreeZeroLocalization 𝒜 (intShift 𝒜 d) S)
    (z : DegreeZeroLocalization 𝒜 𝓜 S) :
    DegreeZeroLocalization.intShiftZeroModuleLinearEquiv 𝒜 𝓜 hf d hfS
        (twistMul 𝒜 𝓜 S d w z) =
      twistMul 𝒜 𝓜 S 0 (DegreeZeroLocalization.intShiftZeroLinearEquiv 𝒜 hf d hfS w) z := by
  apply DegreeZeroLocalization.ext
  show _ • ((w : LocalizedModule S A) • (z : LocalizedModule S M)) =
    ((_ • (w : LocalizedModule S A) : LocalizedModule S A)) • (z : LocalizedModule S M)
  rw [← mul_smul]
  rfl

end AlgebraicGeometry.Proj
