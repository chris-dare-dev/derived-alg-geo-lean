/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.FirstStrictSES

/-!
# Strict finite length along inclusions of owner slicing intervals

This is the foundation-level transfer needed by deformation local finiteness.
It embeds strict-subobject orders along a full faithful interval inclusion and
pulls both well-foundedness conditions back.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

open WeakStabilityCondition.StabilityCondition.Deformation.Slicing.IntervalCat

section General

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasKernels A] [HasCokernels A]
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasKernels D] [HasCokernels D]

variable (F : A ⥤ D) [F.Full] [F.Faithful]
  (hF : ∀ {X Y : A} (f : X ⟶ Y), IsStrictMono f → IsStrictMono (F.map f))
  (harr : ∀ {Y Z : D} (f : Y ⟶ Z) [Mono f], IsStrictMono f →
    IsStrictMono (Subobject.mk f).arrow)

/-- The image of a strict subobject, landing in **strict** subobjects — which
is what lets the hypothesis be strict rather than ordinary. -/
noncomputable def strictImage {E : A} :
    StrictSubobject E → StrictSubobject (F.obj E) := fun B =>
  letI hs : IsStrictMono (F.map B.1.arrow) := hF B.1.arrow B.2
  letI : Mono (F.map B.1.arrow) := hs.mono
  ⟨Subobject.mk (F.map B.1.arrow), harr _ hs⟩

omit [F.Full] [F.Faithful] in
theorem strictImage_monotone {E : A} :
    Monotone (strictImage F hF harr (E := E)) := by
  intro B₁ B₂ hB
  letI hs₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  letI hs₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hs₁.mono
  letI : Mono (F.map B₂.1.arrow) := hs₂.mono
  have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
    simpa [Subobject.mk_arrow] using (show B₁.1 ≤ B₂.1 from hB)
  exact Subobject.mk_le_mk_of_comm
    (F.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      rw [← F.map_comp]
      exact congrArg F.map (Subobject.ofMkLEMk_comp hmk))

theorem strictImage_injective {E : A} :
    Function.Injective (strictImage F hF harr (E := E)) := by
  intro B₁ B₂ hEq
  letI hs₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  letI hs₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hs₁.mono
  letI : Mono (F.map B₂.1.arrow) := hs₂.mono
  apply Subtype.ext
  have hEq' : Subobject.mk (F.map B₁.1.arrow) =
      Subobject.mk (F.map B₂.1.arrow) := congrArg Subtype.val hEq
  simpa [Subobject.mk_arrow] using
    (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (F.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
      (F.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq'.le)))

/-- Monotone + injective on a partial order is strictly monotone, which is what
pulls well-foundedness back. -/
theorem strictImage_strictMono {E : A} {a b : StrictSubobject E}
    (hab : a < b) : strictImage F hF harr a < strictImage F hF harr b :=
  lt_of_le_of_ne (strictImage_monotone F hF harr hab.le)
    (fun h => absurd (strictImage_injective F hF harr h) (ne_of_lt hab))

include hF harr in
private theorem isStrictArtinian_of_image {E : A}
    [IsStrictArtinianObject (F.obj E)] : IsStrictArtinianObject E :=
  ObjectProperty.is_of_prop _
    (show WellFoundedLT (StrictSubobject E) from
      ⟨Subrelation.wf (strictImage_strictMono F hF harr)
        (InvImage.wf _ IsWellFounded.wf)⟩)

include hF harr in
private theorem isStrictNoetherian_of_image {E : A}
    [IsStrictNoetherianObject (F.obj E)] : IsStrictNoetherianObject E := by
  refine ObjectProperty.is_of_prop _ ⟨?_⟩
  have hw : WellFounded (InvImage
      (· > · : StrictSubobject (F.obj E) → _ → Prop)
      (strictImage F hF harr)) := InvImage.wf _ IsWellFounded.wf
  refine Subrelation.wf ?_ hw
  intro a b hab
  exact strictImage_strictMono F hF harr hab

end General

section Interval

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- Inclusion of one thin owner interval in another preserves strict
monomorphisms. -/
theorem intervalInclusion_map_strictMono
    {s₁ s₂ : Slicing C} {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    {X Y : s₁.IntervalCat C a₁ b₁} (f : X ⟶ Y)
    (hf : IsStrictMono f) :
    IsStrictMono ((ObjectProperty.ιOfLE h).map f) := by
  let S : ShortComplex (s₁.IntervalCat C a₁ b₁) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : StrictShortExact S :=
    strictShortExact_cokernel C f hf
  obtain ⟨δ, hT⟩ := Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s₁ hS
  let I := ObjectProperty.ιOfLE h
  let SI := S.map I
  have hTI : Triangle.mk SI.f.hom SI.g.hom δ ∈ distTriang C := by
    change Triangle.mk f.hom (cokernel.π f).hom δ ∈ distTriang C
    exact hT
  have hSI := Slicing.IntervalCat.strictShortExact_of_distinguished C s₂ hTI
  exact ⟨hSI.shortExact.mono_f, hSI.strict_f⟩

/-- The canonical representative arrow of a strict interval subobject is
strict. -/
theorem intervalSubobject_arrow_strictMono
    {s : Slicing C} {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) [Mono f]
    (hf : IsStrictMono f) : IsStrictMono (Subobject.mk f).arrow := by
  let e := Subobject.underlyingIso f
  have he : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ f) :=
    Slicing.IntervalCat.comp_strictMono C s e.hom f he hf
  simpa [e, IsStrictSubobject] using hcomp

/-- Strict finite length pulls back along an inclusion of thin owner slicing
intervals. -/
theorem interval_strictFiniteLength_of_inclusion
    {s₁ s₂ : Slicing C} {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)]
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X := by
  intro X
  let I := ObjectProperty.ιOfLE h
  have hBig := hFinite (I.obj X)
  letI : IsStrictArtinianObject (I.obj X) := hBig.1
  letI : IsStrictNoetherianObject (I.obj X) := hBig.2
  have hmap : ∀ {A B : s₁.IntervalCat C a₁ b₁} (f : A ⟶ B),
      IsStrictMono f → IsStrictMono (I.map f) := by
    intro A B f hf
    exact intervalInclusion_map_strictMono C h f hf
  have harr : ∀ {A B : s₂.IntervalCat C a₂ b₂} (f : A ⟶ B) [Mono f],
      IsStrictMono f → IsStrictMono (Subobject.mk f).arrow := by
    intro A B f _ hf
    exact intervalSubobject_arrow_strictMono C f hf
  exact ⟨isStrictArtinian_of_image I hmap harr,
    isStrictNoetherian_of_image I hmap harr⟩

end Interval

end CategoryTheory.Triangulated
