/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Category
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic

/-!
# Convolution of Fourier--Mukai kernels

Geometrically, for `P ∈ D(X × Y)` and `Q ∈ D(Y × Z)` the composite
`Φ_Q ∘ Φ_P` is again a Fourier--Mukai transform, with kernel the convolution

`Q ∗ P = Rπ_{XZ*}(π_{XY}^* P ⊗^L π_{YZ}^* Q) ∈ D(X × Z)`

which is the classical composition law.  Proving it from the three-projection
description
needs the projection formula and flat base change on a triple product, none of
which the abstract `Correspondence` of `FourierMukai.Basic` carries.

## Main definitions

* `CategoryTheory.Triangulated.FourierMukai.ConvolutionData`: a kernel-level
  operation with the composition isomorphisms of Prop. 5.10.
* `CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData`: convolution
  for endocorrespondences as a monoidal structure on the kernel category, with
  `CoherentConvolutionData.toConvolutionData` forgetting it.
* `CategoryTheory.Triangulated.FourierMukai.ConvolutionAssocData`,
  `CategoryTheory.Triangulated.FourierMukai.ConvolutionLeftUnitData` and
  `CategoryTheory.Triangulated.FourierMukai.ConvolutionRightUnitData`: the
  kernel-level associativity and unit laws, as supplied data.
* `CategoryTheory.Triangulated.FourierMukai.convolutionTransformAssoc`,
  `CategoryTheory.Triangulated.FourierMukai.convolutionTransformUnitLeft` and
  `CategoryTheory.Triangulated.FourierMukai.convolutionTransformUnitRight`: the
  same laws at the transform level, derived from `compIso`.

## Main results

* `CategoryTheory.Triangulated.FourierMukai.ConvolutionData.isKernelFunctor_comp`:
  kernel functors are closed under composition.
* `CategoryTheory.Triangulated.FourierMukai.ConvolutionData.transformMapConvIso`:
  isomorphic kernels convolve to kernels with isomorphic transforms.
* `CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.pentagon` and
  `CategoryTheory.Triangulated.FourierMukai.CoherentConvolutionData.triangle`:
  the coherence laws of a coherent convolution presentation.

## Implementation notes

### Convolution as supplied data

Convolution enters here as *supplied data*, not as a theorem.  A
`ConvolutionData` names a kernel-level operation together with the family of
isomorphisms that Prop. 5.10 asserts, for three correspondences that share
their outer categories in the pattern `𝒳 → 𝒴 → 𝒵`.  What this file then proves
are the consequences: that kernel functors are closed under composition, and
that convolution is well behaved under isomorphism of either kernel.

This is the same division of labour as
`StabilityCondition.Families.Basic`, where the geometric tests are supplied by
a caller and the file proves what follows from them.  The value is that a
later geometric realization has one named obligation to discharge rather than
an implicit one, and that everything downstream of Prop. 5.10 is already
available once it is. For endocorrespondences whose kernels genuinely form a
monoidal category, `CoherentConvolutionData` is the stable root: it makes the
operation functorial and packages its associator, unitors, pentagon, and
triangle together. It forgets one-way to `ConvolutionData`.

### What this file does not assert

* Nothing constructs a `ConvolutionData` or `CoherentConvolutionData`, and no
  example is exhibited. That is not an omission for want of trying: `compIso`
  is required to hold
  *uniformly in* `Q`, so the cheap degenerate constructions — fold the middle
  transform into `C₃.push`, or take `conv P Q = P` — all fail, because they
  produce a `C₃` whose transform has one fixed `Q` baked into it and so cannot
  meet the requirement for any other. The uniformity is what gives the
  structure content, and discharging it is a geometric obligation.
* The weaker interface's `ConvolutionData.conv` is a bare function
  `𝒲₁ → 𝒲₂ → 𝒲₃`, not a functor. It is not assumed
  to be additive, exact, or even to send isomorphic kernels to isomorphic
  kernels — only to send them to kernels with *isomorphic transforms*, which
  is what `transformMapConvIso` proves and is strictly weaker.
* Associativity of convolution **splits**.  At the transform level it is a
  theorem, `convolutionTransformAssoc`, derived from the four `compIso`
  families alone — no new input.  At the kernel level it is
  `ConvolutionAssocData`, a second layer of *supplied* data: recovering the
  kernel-level isomorphism from the transform-level one would need a kernel
  to be determined by its transform (Orlov uniqueness), which is not
  available here.  No result here depends on the kernel-level layer, and
  nothing constructs it. `CoherentConvolutionData` is the stronger alternative
  when a caller can supply the full monoidal kernel structure.
* Triangulatedness does not transport across `compIso`.  Moving
  `IsTriangulated` along a natural isomorphism needs that isomorphism to
  commute with the shift (`NatTrans.CommShift`), which is an extra hypothesis
  on the supplied data rather than a consequence of it.
* No kernel is claimed to be determined by its transform, so `conv` is not
  claimed to be the unique operation satisfying `compIso`.

## References

* Prop. 5.10, the composition of Fourier--Mukai transforms, as stated by the
  field `CategoryTheory.Triangulated.FourierMukai.ConvolutionData.compIso`.
* Orlov's uniqueness of Fourier--Mukai kernels, which this file does not use.
* Mathlib's `CategoryTheory.MonoidalCategory`.

## Tags

Fourier--Mukai kernel, convolution, composition of transforms, monoidal category
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory

universe v₁ v₂ v₃ w₁ w₂ w₃ u₁ u₂ u₃ t₁ t₂ t₃

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
  {𝒲₁ : Type t₁} {𝒲₂ : Type t₂} {𝒲₃ : Type t₃}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]
  [Category.{w₁} 𝒲₁] [Category.{w₂} 𝒲₂] [Category.{w₃} 𝒲₃]

/-- Convolution data for three correspondences arranged as `𝒳 → 𝒴 → 𝒵`.

`conv` is the kernel-level operation and `compIso` is the classical
composition law for it: composing the transform with kernel `P` and the
transform with kernel
`Q` gives the transform with kernel `conv P Q`.  Both are supplied; neither is
derived. -/
structure ConvolutionData (C₁ : Correspondence 𝒳 𝒴 𝒲₁)
    (C₂ : Correspondence 𝒴 𝒵 𝒲₂) (C₃ : Correspondence 𝒳 𝒵 𝒲₃) where
  /-- The convolution of two kernels. -/
  conv : 𝒲₁ → 𝒲₂ → 𝒲₃
  /-- Prop. 5.10: the composite of the two transforms is the transform of the
  convolved kernel. -/
  compIso (P : 𝒲₁) (Q : 𝒲₂) :
    C₁.transform P ⋙ C₂.transform Q ≅ C₃.transform (conv P Q)

/-- Coherent convolution for endocorrespondences.

Unlike `ConvolutionData`, whose kernel operation is a bare function, this
root carries an explicit Mathlib `MonoidalCategory` presentation of the
kernel category. Consequently the associator, both unitors, their naturality,
the pentagon, and the triangle are one inseparable datum. The presentation is
an explicit field rather than a global instance, so two convolution
presentations on the same kernel category can coexist.

`toConvolutionData` below is the one-way compatibility map to the older,
law-free interface. -/
structure CoherentConvolutionData (C : Correspondence 𝒳 𝒳 𝒲₁) where
  /-- The complete monoidal structure underlying kernel convolution. -/
  monoidal : MonoidalCategory 𝒲₁
  /-- Composition of transforms agrees with monoidal convolution. -/
  compIso : letI := monoidal
    ∀ P Q : 𝒲₁, C.transform P ⋙ C.transform Q ≅
      C.transform (MonoidalCategory.tensorObj P Q)

namespace CoherentConvolutionData

open MonoidalCategory

variable {C : Correspondence 𝒳 𝒳 𝒲₁}

/-- Kernel convolution selected by a coherent presentation. -/
def conv (D : CoherentConvolutionData C) (P Q : 𝒲₁) : 𝒲₁ :=
  letI := D.monoidal
  P ⊗ Q

/-- The coherent convolution unit. -/
def unit (D : CoherentConvolutionData C) : 𝒲₁ :=
  letI := D.monoidal
  𝟙_ 𝒲₁

/-- The convolution associator, derived from the coherent root. -/
def assocIso (D : CoherentConvolutionData C) (P Q R : 𝒲₁) :
    D.conv (D.conv P Q) R ≅ D.conv P (D.conv Q R) := by
  letI := D.monoidal
  exact α_ P Q R

/-- The left convolution unitor, derived from the coherent root. -/
def leftUnitIso (D : CoherentConvolutionData C) (P : 𝒲₁) :
    D.conv D.unit P ≅ P := by
  letI := D.monoidal
  exact λ_ P

/-- The right convolution unitor, derived from the coherent root. -/
def rightUnitIso (D : CoherentConvolutionData C) (P : 𝒲₁) :
    D.conv P D.unit ≅ P := by
  letI := D.monoidal
  exact ρ_ P

/-- The pentagon proposition for a coherent convolution presentation. -/
def Pentagon (D : CoherentConvolutionData C) (P Q R T : 𝒲₁) : Prop :=
  letI := D.monoidal
  MonoidalCategory.Pentagon P Q R T

/-- Every coherent convolution presentation satisfies the pentagon. -/
theorem pentagon (D : CoherentConvolutionData C) (P Q R T : 𝒲₁) :
    D.Pentagon P Q R T := by
  letI := D.monoidal
  exact MonoidalCategory.pentagon P Q R T

/-- The triangle proposition for a coherent convolution presentation. -/
def Triangle (D : CoherentConvolutionData C) (P Q : 𝒲₁) : Prop :=
  letI := D.monoidal
  (α_ P (𝟙_ 𝒲₁) Q).hom ≫ P ◁ (λ_ Q).hom = (ρ_ P).hom ▷ Q

/-- Every coherent convolution presentation satisfies the triangle. -/
theorem triangle (D : CoherentConvolutionData C) (P Q : 𝒲₁) :
    D.Triangle P Q := by
  letI := D.monoidal
  exact MonoidalCategory.triangle P Q

/-- Forget coherent convolution to the weaker operation-and-comparison
interface. No adapter exists in the opposite direction. -/
def toConvolutionData (D : CoherentConvolutionData C) :
    ConvolutionData C C C := by
  letI := D.monoidal
  exact
    { conv := MonoidalCategory.tensorObj
      compIso := D.compIso }

end CoherentConvolutionData

namespace ConvolutionData

variable {C₁ : Correspondence 𝒳 𝒴 𝒲₁} {C₂ : Correspondence 𝒴 𝒵 𝒲₂}
  {C₃ : Correspondence 𝒳 𝒵 𝒲₃}

/-- The composite of two transforms is a kernel functor for the third
correspondence, witnessed by the convolved kernel. -/
theorem isKernelFunctor_transform_comp (D : ConvolutionData C₁ C₂ C₃)
    (P : 𝒲₁) (Q : 𝒲₂) :
    C₃.IsKernelFunctor (C₁.transform P ⋙ C₂.transform Q) :=
  ⟨D.conv P Q, ⟨D.compIso P Q⟩⟩

/-- Kernel functors are closed under composition.  This is the reason to name
`ConvolutionData` at all: the property of *being* of Fourier--Mukai type,
rather than any particular transform, is what composes. -/
theorem isKernelFunctor_comp (D : ConvolutionData C₁ C₂ C₃)
    {Φ : 𝒳 ⥤ 𝒴} {Ψ : 𝒴 ⥤ 𝒵}
    (hΦ : C₁.IsKernelFunctor Φ) (hΨ : C₂.IsKernelFunctor Ψ) :
    C₃.IsKernelFunctor (Φ ⋙ Ψ) := by
  obtain ⟨P, ⟨eP⟩⟩ := hΦ
  obtain ⟨Q, ⟨eQ⟩⟩ := hΨ
  exact ⟨D.conv P Q,
    ⟨Functor.isoWhiskerRight eP Ψ ≪≫
      Functor.isoWhiskerLeft (C₁.transform P) eQ ≪≫ D.compIso P Q⟩⟩

/-- Isomorphic kernels convolve to kernels with isomorphic transforms.

This is weaker than `conv P Q ≅ conv P' Q'`, and deliberately so: recovering
that would need a kernel to be determined by its transform, which is Orlov's
uniqueness statement and is not available here. -/
def transformMapConvIso (D : ConvolutionData C₁ C₂ C₃) {P P' : 𝒲₁} (eP : P ≅ P')
    {Q Q' : 𝒲₂} (eQ : Q ≅ Q') :
    C₃.transform (D.conv P Q) ≅ C₃.transform (D.conv P' Q') :=
  (D.compIso P Q).symm ≪≫
    Functor.isoWhiskerRight (C₁.transformMapIso eP) (C₂.transform Q) ≪≫
      Functor.isoWhiskerLeft (C₁.transform P') (C₂.transformMapIso eQ) ≪≫
        D.compIso P' Q'

/-- Convolving with isomorphisms that are both the identity leaves the
transform alone. -/
@[simp]
theorem transformMapConvIso_refl (D : ConvolutionData C₁ C₂ C₃) (P : 𝒲₁)
    (Q : 𝒲₂) :
    D.transformMapConvIso (Iso.refl P) (Iso.refl Q) =
      Iso.refl (C₃.transform (D.conv P Q)) := by
  ext E
  simp [transformMapConvIso]

end ConvolutionData

section Assoc

universe v₄ u₄ w₁₂ w₂₃ w₀ t₁₂ t₂₃ t₀

variable {𝒱 : Type u₄} [Category.{v₄} 𝒱]
  {𝒲₁₂ : Type t₁₂} {𝒲₂₃ : Type t₂₃} {𝒲 : Type t₀}
  [Category.{w₁₂} 𝒲₁₂] [Category.{w₂₃} 𝒲₂₃] [Category.{w₀} 𝒲]
  {C₁ : Correspondence 𝒳 𝒴 𝒲₁} {C₂ : Correspondence 𝒴 𝒵 𝒲₂}
  {C₃ : Correspondence 𝒵 𝒱 𝒲₃}
  {C₁₂ : Correspondence 𝒳 𝒵 𝒲₁₂} {C₂₃ : Correspondence 𝒴 𝒱 𝒲₂₃}
  {C : Correspondence 𝒳 𝒱 𝒲}

/-- **Associativity of convolution at the transform level — a theorem, not
data.**

For three composable correspondences with convolution data for both
bracketings landing in a common outer correspondence, the transforms of the
two associated kernels are isomorphic: each side is isomorphic to
`Φ_P ⋙ Φ_Q ⋙ Φ_R` by Prop. 5.10 twice.  No input beyond the four `compIso`
families is consumed.

What this does **not** give is an isomorphism of the kernels themselves; that
is `ConvolutionAssocData`, and the gap between the two is genuine — see its
docstring. -/
def convolutionTransformAssoc
    (D₁₂ : ConvolutionData C₁ C₂ C₁₂) (D₂₃ : ConvolutionData C₂ C₃ C₂₃)
    (Dl : ConvolutionData C₁₂ C₃ C) (Dr : ConvolutionData C₁ C₂₃ C)
    (P : 𝒲₁) (Q : 𝒲₂) (R : 𝒲₃) :
    C.transform (Dl.conv (D₁₂.conv P Q) R) ≅
      C.transform (Dr.conv P (D₂₃.conv Q R)) :=
  (Dl.compIso (D₁₂.conv P Q) R).symm ≪≫
    Functor.isoWhiskerRight (D₁₂.compIso P Q).symm (C₃.transform R) ≪≫
      Functor.associator (C₁.transform P) (C₂.transform Q) (C₃.transform R) ≪≫
        Functor.isoWhiskerLeft (C₁.transform P) (D₂₃.compIso Q R) ≪≫
          Dr.compIso P (D₂₃.conv Q R)

/-- **Associativity of convolution at the kernel level — supplied data.**

An isomorphism `(P ∗ Q) ∗ R ≅ P ∗ (Q ∗ R)` between the two bracketings, in
the kernel category of the common outer correspondence.

Strictly stronger than `convolutionTransformAssoc`, and the gap is Orlov's
uniqueness statement: the transforms of the two kernels are always isomorphic
(the theorem above), but recovering an isomorphism of the *kernels* from an
isomorphism of their transforms needs a kernel to be determined by its
transform, which nothing in this repository provides.

Geometrically the classical proof works on the quadruple product, by the same
projection-formula and base-change arguments that derive Prop. 5.10 on the
triple product.  That derivation is a geometric obligation, and this
structure is the layer it would discharge.  Nothing here constructs one,
and no result in this file depends on it. -/
structure ConvolutionAssocData
    (D₁₂ : ConvolutionData C₁ C₂ C₁₂) (D₂₃ : ConvolutionData C₂ C₃ C₂₃)
    (Dl : ConvolutionData C₁₂ C₃ C) (Dr : ConvolutionData C₁ C₂₃ C) where
  /-- The two bracketings of three kernels agree at the kernel level. -/
  assocIso (P : 𝒲₁) (Q : 𝒲₂) (R : 𝒲₃) :
    Dl.conv (D₁₂.conv P Q) R ≅ Dr.conv P (D₂₃.conv Q R)

end Assoc

section Unit

/-- **The left unit law at the transform level — a theorem, not data.**

Given convolution data composing a self-correspondence with `C₂`, and a
kernel presenting the identity as a transform of the self-correspondence, the
transform of `conv U P` is the transform of `P`. Free from `compIso` and the
unit witness; no constraint on the outer correspondence. -/
def convolutionTransformUnitLeft {C₁ : Correspondence 𝒳 𝒳 𝒲₁}
    {C₂ : Correspondence 𝒳 𝒴 𝒲₂} {C₃ : Correspondence 𝒳 𝒴 𝒲₃}
    (D : ConvolutionData C₁ C₂ C₃) (U : 𝒲₁)
    (unitIso : 𝟭 𝒳 ≅ C₁.transform U) (P : 𝒲₂) :
    C₃.transform (D.conv U P) ≅ C₂.transform P :=
  (D.compIso U P).symm ≪≫
    Functor.isoWhiskerRight unitIso.symm (C₂.transform P) ≪≫
      (C₂.transform P).leftUnitor

/-- **The right unit law at the transform level — a theorem, not data.**
The mirror of `convolutionTransformUnitLeft`. -/
def convolutionTransformUnitRight {C₁ : Correspondence 𝒴 𝒴 𝒲₁}
    {C₂ : Correspondence 𝒳 𝒴 𝒲₂} {C₃ : Correspondence 𝒳 𝒴 𝒲₃}
    (D : ConvolutionData C₂ C₁ C₃) (U : 𝒲₁)
    (unitIso : 𝟭 𝒴 ≅ C₁.transform U) (P : 𝒲₂) :
    C₃.transform (D.conv P U) ≅ C₂.transform P :=
  (D.compIso P U).symm ≪≫
    Functor.isoWhiskerLeft (C₂.transform P) unitIso.symm ≪≫
      (C₂.transform P).rightUnitor

/-- **The left unit law at the kernel level — supplied data.**

`conv U P ≅ P` for a convolution datum whose outer correspondence *is* `C₂`.
Strictly stronger than `convolutionTransformUnitLeft` for the same Orlov gap
as `ConvolutionAssocData`: the transforms are always isomorphic, but
recovering an isomorphism of kernels needs a kernel to be determined by its
transform. Nothing here constructs one, and no result depends on it. -/
structure ConvolutionLeftUnitData {C₁ : Correspondence 𝒳 𝒳 𝒲₁}
    {C₂ : Correspondence 𝒳 𝒴 𝒲₂} (D : ConvolutionData C₁ C₂ C₂) (U : 𝒲₁) where
  /-- Convolving with the unit kernel on the left is the identity. -/
  leftUnitIso (P : 𝒲₂) : D.conv U P ≅ P

/-- **The right unit law at the kernel level — supplied data.**
The mirror of `ConvolutionLeftUnitData`; same gap, same caveats. -/
structure ConvolutionRightUnitData {C₁ : Correspondence 𝒴 𝒴 𝒲₁}
    {C₂ : Correspondence 𝒳 𝒴 𝒲₂} (D : ConvolutionData C₂ C₁ C₂) (U : 𝒲₁) where
  /-- Convolving with the unit kernel on the right is the identity. -/
  rightUnitIso (P : 𝒲₂) : D.conv P U ≅ P

end Unit

namespace CoherentConvolutionData

variable {C : Correspondence 𝒳 𝒳 𝒲₁}

/-- Forget coherent convolution to the supplied kernel associativity layer. -/
def toConvolutionAssocData (D : CoherentConvolutionData C) :
    ConvolutionAssocData D.toConvolutionData D.toConvolutionData
      D.toConvolutionData D.toConvolutionData where
  assocIso := D.assocIso

/-- Forget coherent convolution to the supplied left-unit layer. -/
def toConvolutionLeftUnitData (D : CoherentConvolutionData C) :
    ConvolutionLeftUnitData D.toConvolutionData D.unit where
  leftUnitIso := D.leftUnitIso

/-- Forget coherent convolution to the supplied right-unit layer. -/
def toConvolutionRightUnitData (D : CoherentConvolutionData C) :
    ConvolutionRightUnitData D.toConvolutionData D.unit where
  rightUnitIso := D.rightUnitIso

end CoherentConvolutionData

end CategoryTheory.Triangulated.FourierMukai
