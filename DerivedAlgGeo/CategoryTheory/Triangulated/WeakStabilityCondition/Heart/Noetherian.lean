/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Basic.Definitions
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.TorsionPair.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Noetherian torsion subcategories (Definition 14.6)

The noetherian-torsion layer of §14 of arXiv:1902.08184v4: subobject chains
in the heart, the termination condition, noetherian torsion subcategories,
and the identification of a torsion pair's free class with the right
orthogonal of its torsion class — the place `free_of_orthogonal` (#94) was
built for.

## The design decision, recorded (Remark 14.7 as the definition)

Definition 14.6 calls `B ⊆ A` a *noetherian torsion subcategory* if `B` is an
abelian subcategory, `B` is a noetherian abelian category, and `(B, B^⊥)` is
a torsion pair in `A`. The pin supplies an abelian instance on the full heart,
but `B` here is an object property inside the ambient category; there is no
bundled abelian-category/noetherian structure on that property whose
equivalence with the chain condition is available. Remark 14.7 characterises
the notion for extension-closed
`B`: **every increasing chain of `B`-subobjects of a fixed `E ∈ A`
terminates.** That chain condition is statable — a subobject is a heart
monomorphism, which is a map whose cone is again in the heart — and it is
what every use in §14 consumes (Lemmas 14.8, 14.11, Remark 14.14, and the
proof of Proposition 14.16 all run on chain termination, never on the
abstract noetherian-ness). So the chain condition **is the definition
here**, the torsion-pair half is carried as a `HeartTorsionPair`, and the
equivalence of Remark 14.7 is *not* claimed — it is the textbook
justification for the choice, not a theorem of this file.

## What is deliberately NOT declared here

Lemmas 14.8 and 14.11 are **statable but left undeclared**, per the standing
rule that absent beats sorry-backed. What their proofs need, precisely:

* **Lemma 14.8** (`A⁰` noetherian torsion + `Z` over `ℚ[i]` ⟹ `A`
  noetherian): the proof runs on surjection chains, kernels of composites,
  maximal subobjects with `ℑZ = 0` extracted from HN filtrations, and a
  discreteness argument for the charge image. Missing at the pin: kernel and
  image lemmas needed by the maximal-subobject construction and a
  formalization decision for "Z defined over ℚ[i]" that makes the
  discreteness step honest.  The abelian weak-HN package and its existence for
  the slicing heart are now available in `HarderNarasimhan.lean`.
* **Lemma 14.11** (bounded-slope chains terminate): the statement needs only
  `slope` and the chains below; the proof needs `μ⁺`/`μ⁻` from HN data, the
  compact-parallelogram argument, and the finitely-many-HN-classes input of
  Remark 12.3, which is support-property infrastructure.

The remaining kernel/image, discreteness and support inputs should be added in
focused modules before these two lemmas are attempted; #108 records the
definitions and the boundary.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated ZeroObject
open CategoryTheory.Triangulated.Tilting

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (t : TStructure C)

/-! ### Heart monomorphisms and subobject chains -/

/-- A map between heart objects is a **heart monomorphism** when its cone is
again in the heart: for heart objects, a distinguished triangle
`A ⟶ E ⟶ Q` with `Q` in the heart is a short exact sequence
`0 → A → E → Q → 0`, so this is exactly "`A` is a subobject of `E` with
quotient `Q`". -/
def IsHeartMono {A E : C} (f : A ⟶ E) : Prop :=
  t.heart A ∧ t.heart E ∧
    ∃ (Q : C) (_ : t.heart Q) (g : E ⟶ Q) (h : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C

/-- An increasing chain of `B`-subobjects of a fixed heart object `E`
(Remark 14.7's data): objects `obj i` of class `B`, each a heart subobject
of the next and of `E`, compatibly. -/
structure SubobjectChain (B : ObjectProperty C) (E : C) where
  /-- The chain objects. -/
  obj : ℕ → C
  /-- Every chain object is of class `B`. -/
  prop : ∀ i, B (obj i)
  /-- The inclusion of each chain object into the next. -/
  step : ∀ i, obj i ⟶ obj (i + 1)
  /-- The inclusion of each chain object into `E`. -/
  toAmbient : ∀ i, obj i ⟶ E
  /-- Each step is a heart monomorphism. -/
  step_mono : ∀ i, IsHeartMono t (step i)
  /-- Each inclusion into `E` is a heart monomorphism. -/
  toAmbient_mono : ∀ i, IsHeartMono t (toAmbient i)
  /-- The inclusions are compatible with the steps. -/
  comm : ∀ i, step i ≫ toAmbient (i + 1) = toAmbient i

/-- A chain **terminates** when all steps are eventually isomorphisms. -/
def SubobjectChain.Terminates {B : ObjectProperty C} {E : C}
    (c : SubobjectChain t B E) : Prop :=
  ∃ N, ∀ i, N ≤ i → IsIso (c.step i)

/-! ### Definition 14.6, in the chain form -/

/-- A **noetherian torsion subcategory** of the heart of `t`
(Definition 14.6, with Remark 14.7's chain characterisation as the
noetherian-ness — see the module docstring for why): a torsion pair on the
heart whose torsion class satisfies the ascending chain condition on
subobjects of every heart object. -/
structure NoetherianTorsionSubcategory where
  /-- The torsion pair `(B, B^⊥)`. -/
  pair : HeartTorsionPair t
  /-- Chain termination: every increasing chain of torsion subobjects of a
  heart object terminates. -/
  noetherian : ∀ (E : C), t.heart E →
    ∀ c : SubobjectChain t pair.tors E, c.Terminates

/-- The right orthogonal of a class inside the heart: heart objects
receiving no nonzero map from the class. This is Definition 14.6's `B^⊥`. -/
def rightOrthogonal (B : ObjectProperty C) : ObjectProperty C :=
  fun X => t.heart X ∧ ∀ T : C, B T → ∀ f : T ⟶ X, f = 0

/-- Right orthogonality is invariant under isomorphism of the target. -/
theorem rightOrthogonal_of_iso {B : ObjectProperty C} {X Y : C}
    (e : X ≅ Y) (hY : rightOrthogonal t B Y) : rightOrthogonal t B X := by
  refine ⟨ObjectProperty.prop_of_iso t.heart e.symm hY.1, ?_⟩
  intro T hT f
  apply (cancel_mono e.hom).mp
  rw [hY.2 T hT (f ≫ e.hom), zero_comp]

/-- **A torsion pair's free class is the right orthogonal of its torsion
class** — so the pair carried by `NoetherianTorsionSubcategory` really is
`(B, B^⊥)` in Definition 14.6's sense. The forward inclusion is the
`hom_eq_zero` axiom; the reverse is `free_of_orthogonal`, the dual
characterisation added for the #86 review's finding F1. -/
theorem free_iff_rightOrthogonal (P : HeartTorsionPair t) (X : C) :
    P.free X ↔ rightOrthogonal t P.tors X := by
  constructor
  · intro hX
    haveI := P.free_isLE X hX
    haveI := P.free_isGE X hX
    exact ⟨(TStructure.mem_heart_iff t X).mpr ⟨inferInstance, inferInstance⟩,
      fun T hT f => P.hom_eq_zero hT hX f⟩
  · rintro ⟨hheart, horth⟩
    obtain ⟨hle, hge⟩ := (TStructure.mem_heart_iff t X).mp hheart
    exact P.free_of_orthogonal hle hge horth

/-! ### Constructing the zero-charge torsion pair -/

/-- The constructive datum needed to make the zero-charge class a torsion
class: every heart object has a zero-charge subobject with right-orthogonal
quotient.  This is the exact output of the maximal-subobject argument in the
proof of Proposition 14.16. -/
def WeakStabilityFunction.HasZeroChargeDecompositions
    (W : WeakStabilityFunction t) : Prop :=
  ∀ E : C, t.heart E →
    ∃ (A Q : C) (_ : W.zeroCharge A) (_ : rightOrthogonal t W.zeroCharge Q)
      (i : A ⟶ E) (p : E ⟶ Q) (d : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C

/-- Zero-charge decompositions assemble into the torsion pair
`(A⁰, (A⁰)⊥)` on the heart. -/
noncomputable def WeakStabilityFunction.zeroChargeTorsionPair
    (W : WeakStabilityFunction t) (hdec : W.HasZeroChargeDecompositions) :
    HeartTorsionPair t where
  tors := W.zeroCharge
  free := rightOrthogonal t W.zeroCharge
  tors_isLE X hX := ((TStructure.mem_heart_iff t X).mp hX.1).1
  tors_isGE X hX := ((TStructure.mem_heart_iff t X).mp hX.1).2
  free_isLE X hX := ((TStructure.mem_heart_iff t X).mp hX.1).1
  free_isGE X hX := ((TStructure.mem_heart_iff t X).mp hX.1).2
  tors_isClosedUnderIsomorphisms := W.zeroCharge_isClosedUnderIsomorphisms
  free_isClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    refine ⟨ObjectProperty.prop_of_iso t.heart e hX.1, ?_⟩
    intro A hA f
    have hz := hX.2 A hA (f ≫ e.inv)
    calc
      f = (f ≫ e.inv) ≫ e.hom := by simp
      _ = 0 := by rw [hz, zero_comp]⟩
  hom_eq_zero := fun _ _ hA hQ f ↦ hQ.2 _ hA f
  exists_triangle E hLE hGE := by
    obtain ⟨A, Q, hA, hQ, i, p, d, hd⟩ :=
      hdec E ((TStructure.mem_heart_iff t E).mpr ⟨hLE, hGE⟩)
    exact ⟨A, Q, hA, hQ, i, p, d, hd⟩

@[simp]
theorem WeakStabilityFunction.zeroChargeTorsionPair_tors
    (W : WeakStabilityFunction t) (hdec : W.HasZeroChargeDecompositions) :
    (W.zeroChargeTorsionPair t hdec).tors = W.zeroCharge := rfl

@[simp]
theorem WeakStabilityFunction.zeroChargeTorsionPair_free
    (W : WeakStabilityFunction t) (hdec : W.HasZeroChargeDecompositions) :
    (W.zeroChargeTorsionPair t hdec).free = rightOrthogonal t W.zeroCharge := rfl

/-! ### Zero charge as a Serre class in the full heart -/

/-- The zero-charge property transported from ambient objects to objects of
the abelian full heart. -/
def WeakStabilityFunction.heartZeroCharge
    (W : WeakStabilityFunction t) : ObjectProperty t.heart.FullSubcategory :=
  fun E => W.zeroCharge E.obj

/-- Zero-charge heart objects form a Serre class: they are closed under
subobjects, quotients, and extensions. -/
noncomputable instance WeakStabilityFunction.heartZeroCharge_isSerreClass
    [IsTriangulated C] (W : WeakStabilityFunction t) :
    W.heartZeroCharge.IsSerreClass where
  exists_zero := by
    refine ⟨(0 : t.heart.FullSubcategory), isZero_zero _, ?_⟩
    exact ⟨(0 : t.heart.FullSubcategory).property,
      W.charge_isZero ((t.heart).ι.map_isZero (isZero_zero _))⟩
  prop_of_mono {X Y} f _ hY := by
    let Q := cokernel f
    let p : Y ⟶ Q := cokernel.π f
    have hfp : f ≫ p = 0 := cokernel.condition f
    have hshort : (ShortComplex.mk f p hfp).ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_cokernel f) inferInstance inferInstance
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) t f p hfp (fun {A} a ha => by
        exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
          hshort.fIsKernel.fac (KernelFork.ofι a ha)
            WalkingParallelPair.zero⟩)
    exact W.zeroCharge_left X.property Q.property hY hd
  prop_of_epi {X Y} f _ hX := by
    let K := kernel f
    let i : K ⟶ X := kernel.ι f
    have hif : i ≫ f = 0 := kernel.condition f
    have hshort : (ShortComplex.mk i f hif).ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_kernel f) inferInstance inferInstance
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) t i f hif (fun {A} a ha => by
        exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
          hshort.fIsKernel.fac (KernelFork.ofι a ha)
            WalkingParallelPair.zero⟩)
    exact W.zeroCharge_right K.property Y.property hX hd
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    letI : Mono S.f := hS.mono_f
    letI : Epi S.g := hS.epi_g
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) t S.f S.g S.zero (fun {A} a ha => by
        exact ⟨hS.fIsKernel.lift (KernelFork.ofι a ha),
          hS.fIsKernel.fac (KernelFork.ofι a ha)
            WalkingParallelPair.zero⟩)
    exact W.zeroCharge_extension h₁ h₃ S.X₂.property hd

/-! ### Nonvacuity

The zero subcategory is noetherian torsion for every t-structure: the
torsion pair is `({0}, A)` with the inverse-rotated contractible triangle as
decomposition, and a chain of zero subobjects has every step an isomorphism
already. -/

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Maps between zero objects are isomorphisms. -/
theorem isIso_of_isZero {A B : C} (f : A ⟶ B) (hA : IsZero A) (hB : IsZero B) :
    IsIso f :=
  ⟨0, hA.eq_of_tgt _ _, hB.eq_of_tgt _ _⟩

/-- The degenerate torsion pair with the zero objects as torsion class and
the whole heart torsion-free. -/
def zeroTorsionPair : HeartTorsionPair t where
  tors X := IsZero X
  free X := t.heart X
  tors_isLE _ h := t.isLE_of_isZero h 0
  tors_isGE _ h := t.isGE_of_isZero h 0
  free_isLE _ h := ((TStructure.mem_heart_iff t _).mp h).1
  free_isGE _ h := ((TStructure.mem_heart_iff t _).mp h).2
  tors_isClosedUnderIsomorphisms := ⟨fun {_ _} e h => h.of_iso e.symm⟩
  free_isClosedUnderIsomorphisms := ⟨fun {_ _} e h =>
    ObjectProperty.prop_of_iso t.heart e h⟩
  hom_eq_zero := fun _ _ hX _ f => hX.eq_of_src f 0
  exists_triangle X hle hge :=
    ⟨0, X, isZero_zero C, (TStructure.mem_heart_iff t X).mpr ⟨hle, hge⟩,
      0, 𝟙 X, 0, contractible_distinguished₁ X⟩

/-- **`NoetherianTorsionSubcategory` is nonvacuous for every t-structure**:
the zero subcategory qualifies. -/
def zeroNoetherianTorsion : NoetherianTorsionSubcategory t where
  pair := zeroTorsionPair t
  noetherian _ _ c :=
    ⟨0, fun i _ => isIso_of_isZero _ (c.prop i) (c.prop (i + 1))⟩

/-! ### Inheritance -/

/-- Chain termination passes to sub-properties: a chain in `B'` with
`B' ≤ B` is a chain in `B`. Recorded because the intended instantiation is
`A⁰ ⊆` a larger torsion class, as in the proof of Proposition 14.16. -/
theorem noetherian_mono {B B' : ObjectProperty C} (hBB : ∀ X, B' X → B X)
    (hB : ∀ (E : C), t.heart E → ∀ c : SubobjectChain t B E, c.Terminates)
    (E : C) (hE : t.heart E) (c : SubobjectChain t B' E) : c.Terminates := by
  obtain ⟨N, hN⟩ := hB E hE
    { obj := c.obj
      prop := fun i => hBB _ (c.prop i)
      step := c.step
      toAmbient := c.toAmbient
      step_mono := c.step_mono
      toAmbient_mono := c.toAmbient_mono
      comm := c.comm }
  exact ⟨N, hN⟩

/-! ### From the relative chain condition to noetherian heart objects -/

section HeartObjects

variable [IsTriangulated C]

/-- For composable monomorphisms `X ⟶ Y ⟶ Z`, the canonical sequence
`coker(X ⟶ Y) ⟶ coker(X ⟶ Z) ⟶ coker(Y ⟶ Z)` extracted from the
kernel--cokernel sequence of a composition. -/
noncomputable def cokernelCompShortComplex
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) : ShortComplex A :=
  (kernelCokernelCompSequence_exact f g).sc 3

/-- The canonical cokernel-of-a-composite sequence is short exact when the
second map is a monomorphism. -/
theorem cokernelCompShortComplex_shortExact
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (cokernelCompShortComplex f g).ShortExact := by
  let L := kernelCokernelCompSequence f g
  have hL := kernelCokernelCompSequence_exact f g
  have hmono : Mono (L.map' 3 4) := by
    apply (hL.exact 2).mono_g
    exact (isZero_kernel_of_mono g).eq_of_src _ _
  have hepi : Epi (L.map' 4 5) := inferInstance
  exact ShortComplex.ShortExact.mk' (hL.exact 3) hmono hepi

/-- The middle three terms
`ker g ⟶ coker f ⟶ coker (f ≫ g)` of the kernel--cokernel sequence. -/
noncomputable def kernelCokernelCompMiddleShortComplex
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) : ShortComplex A :=
  (kernelCokernelCompSequence_exact f g).sc 2

/-- The middle kernel--cokernel sequence is short exact when `f ≫ g` is
monic and `g` is epic.  This is the 3×3 fragment used when a
zero-charge subobject of an extension maps monomorphically to its right-hand
term. -/
theorem kernelCokernelCompMiddleShortComplex_shortExact
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono (f ≫ g)] [Epi g] :
    (kernelCokernelCompMiddleShortComplex f g).ShortExact := by
  let L := kernelCokernelCompSequence f g
  have hL := kernelCokernelCompSequence_exact f g
  have hmono : Mono (L.map' 2 3) := by
    apply (hL.exact 1).mono_g
    exact (isZero_kernel_of_mono (f ≫ g)).eq_of_src _ _
  have hepi : Epi (L.map' 3 4) := by
    apply (hL.exact 3).epi_f
    exact (isZero_cokernel_of_epi g).eq_of_tgt _ _
  exact ShortComplex.ShortExact.mk' (hL.exact 2) hmono hepi

/-- The first three terms
`ker f ⟶ ker (f ≫ g) ⟶ ker g` of the kernel--cokernel sequence. -/
noncomputable def kernelCompShortComplex
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) : ShortComplex A :=
  (kernelCokernelCompSequence_exact f g).sc 0

/-- If `f` is epic, the first three kernels in the composition sequence form
a short exact sequence. -/
theorem kernelCompShortComplex_shortExact
    {A : Type*} [Category A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    (kernelCompShortComplex f g).ShortExact := by
  let L := kernelCokernelCompSequence f g
  have hL := kernelCokernelCompSequence_exact f g
  have hmono : Mono (L.map' 0 1) := inferInstance
  have hepi : Epi (L.map' 1 2) := by
    apply (hL.exact 1).epi_f
    exact (isZero_cokernel_of_epi f).eq_of_tgt _ _
  exact ShortComplex.ShortExact.mk' (hL.exact 0) hmono hepi

/-- Saturating a semistable object by a zero-charge quotient preserves
semistability provided the saturated middle term receives no maps from
zero-charge objects.

For a test subobject `X ⟶ E`, pull it back to the semistable subobject
`F ⟶ E`.  The quotient of the pullback inside `X` embeds into the
zero-charge quotient `V`, so it has zero charge.  Consequently the two
charges in the semistability comparison for `E` agree with those in the
corresponding comparison for `F`. -/
theorem WeakStabilityFunction.isSemistable_middle_of_zeroCharge_quotient
    (W : WeakStabilityFunction t) {F E V : C}
    (hF : W.IsSemistable F) (hE : t.heart E) (hV : W.zeroCharge V)
    (hHom : ∀ A : C, W.zeroCharge A → ∀ f : A ⟶ E, f = 0)
    {i : F ⟶ E} {p : E ⟶ V} {d : V ⟶ F⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) : W.IsSemistable E := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FH : t.heart.FullSubcategory := ⟨F, hF.1⟩
  let EH : t.heart.FullSubcategory := ⟨E, hE⟩
  let VH : t.heart.FullSubcategory := ⟨V, hV.1⟩
  let iH : FH ⟶ EH := ObjectProperty.homMk i
  let pH : EH ⟶ VH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hOuter : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) t (A := FH) (B := EH) (Q := VH)
        (f := iH) (g := pH) (δ := d) hd
  letI : Mono iH := hOuter.mono_f
  refine ⟨hE, ?_⟩
  intro X Y hX hY hX0 hY0 x y delta hXY
  let XH : t.heart.FullSubcategory := ⟨X, hX⟩
  let YH : t.heart.FullSubcategory := ⟨Y, hY⟩
  let xH : XH ⟶ EH := ObjectProperty.homMk x
  let yH : EH ⟶ YH := ObjectProperty.homMk y
  have hxy : xH ≫ yH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hXY
  have hInner : (ShortComplex.mk xH yH hxy).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) t (A := XH) (B := EH) (Q := YH)
        (f := xH) (g := yH) (δ := delta) hXY
  letI : Mono xH := hInner.mono_f
  let PB : t.heart.FullSubcategory := pullback iH xH
  let kF : PB ⟶ FH := pullback.fst iH xH
  let kX : PB ⟶ XH := pullback.snd iH xH
  let sq : IsPullback kF kX iH xH := IsPullback.of_hasPullback iH xH
  let IX : t.heart.FullSubcategory := cokernel kX
  let cIX : IX ⟶ cokernel iH :=
    cokernel.map kX iH kF xH sq.w.symm
  haveI : Mono cIX := Abelian.mono_cokernel_map_of_isPullback sq.flip
  let eV : cokernel iH ≅ VH :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel iH)
      hOuter.gIsCokernel
  have hVcan : W.heartZeroCharge t (cokernel iH) :=
    ObjectProperty.prop_of_iso (W.heartZeroCharge t) eV.symm hV
  have hIX : W.heartZeroCharge t IX :=
    (W.heartZeroCharge t).prop_of_mono cIX hVcan
  let πX : XH ⟶ IX := cokernel.π kX
  have hkXπ : kX ≫ πX = 0 := cokernel.condition kX
  have hKX : (ShortComplex.mk kX πX hkXπ).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel kX)
      inferInstance inferInstance
  obtain ⟨dX, hdX⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t kX πX hkXπ (fun {A} a ha => by
      exact ⟨hKX.fIsKernel.lift (KernelFork.ofι a ha),
        hKX.fIsKernel.fac (KernelFork.ofι a ha)
          WalkingParallelPair.zero⟩)
  have hchargeX : W.charge X = W.charge PB.obj := by
    have hsum := W.charge_triangle' hdX
    rw [hIX.2, add_zero] at hsum
    exact hsum
  have hPB0 : ¬IsZero PB.obj := by
    intro hPB
    have hXcharge0 : W.charge X = 0 := by
      rw [hchargeX]
      exact W.charge_isZero hPB
    have hxzero : x = 0 := hHom X ⟨hX, hXcharge0⟩ x
    letI : Mono xH := hInner.mono_f
    have hXHzero : IsZero XH := IsZero.of_mono_eq_zero xH (by ext; exact hxzero)
    exact hX0 ((t.heart).ι.map_isZero hXHzero)
  let QF : t.heart.FullSubcategory := cokernel kF
  let πF : FH ⟶ QF := cokernel.π kF
  have hkFπ : kF ≫ πF = 0 := cokernel.condition kF
  have hKF : (ShortComplex.mk kF πF hkFπ).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel kF)
      inferInstance inferInstance
  obtain ⟨dF, hdF⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t kF πF hkFπ (fun {A} a ha => by
      exact ⟨hKF.fIsKernel.lift (KernelFork.ofι a ha),
        hKF.fIsKernel.fac (KernelFork.ofι a ha)
          WalkingParallelPair.zero⟩)
  have hchargeOuter := W.charge_triangle' hd
  have hchargeInner := W.charge_triangle' hXY
  have hchargeF := W.charge_triangle' hdF
  have hchargeY : W.charge Y = W.charge QF.obj := by
    apply add_left_cancel (a := W.charge PB.obj)
    calc
      W.charge PB.obj + W.charge Y = W.charge X + W.charge Y := by rw [hchargeX]
      _ = W.charge E := hchargeInner.symm
      _ = W.charge F := by rw [hchargeOuter, hV.2, add_zero]
      _ = W.charge PB.obj + W.charge QF.obj := hchargeF
  by_cases hQF0 : IsZero QF.obj
  · have hYcharge0 : W.charge Y = 0 := hchargeY.trans (W.charge_isZero hQF0)
    unfold WeakStabilityFunction.slope
    rw [hYcharge0]
    simp only [Complex.zero_im, lt_self_iff_false, ↓reduceIte]
    exact le_top
  · have hslope := hF.2 PB.property QF.property hPB0 hQF0
        kF.hom πF.hom dF hdF
    unfold WeakStabilityFunction.slope at hslope ⊢
    rwa [hchargeX, hchargeY]

/-- A quotient of a semistable heart object by a zero-charge subobject is
semistable.

For a test subobject `X ⟶ B` of the quotient, pull it back along
`E ⟶ B`.  The pullback is the kernel of the composite `E ⟶ B ⟶ Y`.
The three resulting short exact sequences show that the pullback has the
same charge as `X`; semistability of `E` therefore gives precisely the
required comparison for `B`. -/
theorem WeakStabilityFunction.isSemistable_quotient_of_zeroCharge_subobject
    (W : WeakStabilityFunction t) {A E B : C}
    (hA : W.zeroCharge A) (hE : W.IsSemistable E) (hB : t.heart B)
    {i : A ⟶ E} {p : E ⟶ B} {d : B ⟶ A⟦(1 : ℤ)⟧}
    (hd : Triangle.mk i p d ∈ distTriang C) : W.IsSemistable B := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let AH : t.heart.FullSubcategory := ⟨A, hA.1⟩
  let EH : t.heart.FullSubcategory := ⟨E, hE.1⟩
  let BH : t.heart.FullSubcategory := ⟨B, hB⟩
  let iH : AH ⟶ EH := ObjectProperty.homMk i
  let pH : EH ⟶ BH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hOuter : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) t (A := AH) (B := EH) (Q := BH)
        (f := iH) (g := pH) (δ := d) hd
  letI : Epi pH := hOuter.epi_g
  refine ⟨hB, ?_⟩
  intro X Y hX hY hX0 hY0 x y delta hXY
  let XH : t.heart.FullSubcategory := ⟨X, hX⟩
  let YH : t.heart.FullSubcategory := ⟨Y, hY⟩
  let xH : XH ⟶ BH := ObjectProperty.homMk x
  let yH : BH ⟶ YH := ObjectProperty.homMk y
  have hxy : xH ≫ yH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hXY
  have hInner : (ShortComplex.mk xH yH hxy).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) t (A := XH) (B := BH) (Q := YH)
        (f := xH) (g := yH) (δ := delta) hXY
  letI : Mono xH := hInner.mono_f
  letI : Epi yH := hInner.epi_g
  let PB : t.heart.FullSubcategory := pullback pH xH
  let j : PB ⟶ EH := pullback.fst pH xH
  let q : PB ⟶ XH := pullback.snd pH xH
  let e : EH ⟶ YH := pH ≫ yH
  have hje : j ≫ e = 0 := by
    dsimp [j, e]
    rw [pullback.condition_assoc, hxy, comp_zero]
  let hKernel : IsLimit (KernelFork.ofι j hje) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hkp : (k ≫ pH) ≫ yH = 0 := by
      simpa [e, Category.assoc] using hk
    let lX : Z ⟶ XH :=
      hInner.fIsKernel.lift (KernelFork.ofι (k ≫ pH) hkp)
    have hlX : lX ≫ xH = k ≫ pH :=
      hInner.fIsKernel.fac (KernelFork.ofι (k ≫ pH) hkp)
        WalkingParallelPair.zero
    exact ⟨pullback.lift k lX hlX.symm, pullback.lift_fst _ _ _⟩
  haveI : Epi e := by
    dsimp [e]
    infer_instance
  have hMiddle : (ShortComplex.mk j e hje).ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.mk j e hje).exact_of_f_is_kernel hKernel)
        inferInstance inferInstance
  haveI : Epi q := by
    dsimp [q]
    infer_instance
  have hPB0 : ¬IsZero PB.obj := by
    intro hPB
    have hqzero : q = 0 := by
      ext
      exact hPB.eq_of_src q.hom 0
    have hXHzero : IsZero XH := IsZero.of_epi_eq_zero q hqzero
    exact hX0 ((t.heart).ι.map_isZero hXHzero)
  obtain ⟨dPB, hdPB⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t j e hje (fun {Z} k hk => by
      exact ⟨hMiddle.fIsKernel.lift (KernelFork.ofι k hk),
        hMiddle.fIsKernel.fac (KernelFork.ofι k hk)
          WalkingParallelPair.zero⟩)
  have hchargeOuter := W.charge_triangle' hd
  have hchargeInner := W.charge_triangle' hXY
  have hchargeMiddle := W.charge_triangle' hdPB
  have hchargePB : W.charge PB.obj = W.charge X := by
    apply add_right_cancel (b := W.charge Y)
    calc
      W.charge PB.obj + W.charge Y = W.charge E := hchargeMiddle.symm
      _ = W.charge B := by rw [hchargeOuter, hA.2, zero_add]
      _ = W.charge X + W.charge Y := hchargeInner
  have hslope := hE.2 PB.property YH.property hPB0 hY0
    j.hom e.hom dPB hdPB
  unfold WeakStabilityFunction.slope at hslope ⊢
  rwa [hchargePB] at hslope

/-- A monomorphism in the abelian full heart gives a heart monomorphism in
the ambient triangle formulation used by `SubobjectChain`. -/
theorem isHeartMono_of_mono {A E : t.heart.FullSubcategory}
    (f : A ⟶ E) [Mono f] : IsHeartMono t f.hom := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let Q : t.heart.FullSubcategory := cokernel f
  let p : E ⟶ Q := cokernel.π f
  have hp : f ≫ p = 0 := cokernel.condition f
  have hshort : (ShortComplex.mk f p hp).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f)
      inferInstance inferInstance
  obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t f p hp (fun {W} a ha => by
      exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
        hshort.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
  exact ⟨A.property, E.property, Q.obj, Q.property, p.hom, d, hd⟩

/-- A heart monomorphism between objects of the full heart is a
monomorphism in that abelian category. -/
theorem mono_of_isHeartMono {A E : t.heart.FullSubcategory}
    (f : A ⟶ E) (hf : IsHeartMono t f.hom) : Mono f := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  obtain ⟨-, -, Q, hQ, g, d, hd⟩ := hf
  let Q' : t.heart.FullSubcategory := ⟨Q, hQ⟩
  let g' : E ⟶ Q' := ObjectProperty.homMk g
  have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
    (C := C) t (A := A) (B := E) (Q := Q') (f := f) (g := g')
      (δ := d) hd
  exact hshort.mono_f

/-- If the torsion class of a noetherian torsion subcategory is the
zero-charge class of a weak stability function, then every zero-charge
object is noetherian in the ordinary abelian-heart sense.

This is the bridge from Definition 14.6's relative chain formulation to the
well-founded subobject order used to choose maximal zero-charge subobjects in
the proof of Proposition 14.16.  Closure of zero charge under heart
subobjects supplies the hypothesis that a general subobject chain lies in
the torsion class. -/
theorem WeakStabilityFunction.isNoetherianObject_of_zeroCharge
    (W : WeakStabilityFunction t) (N : NoetherianTorsionSubcategory t)
    (hN : N.pair.tors = W.zeroCharge) (E : t.heart.FullSubcategory)
    (hE : W.zeroCharge E.obj) : IsNoetherianObject E := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let step (i : ℕ) :
      (f i : t.heart.FullSubcategory) ⟶
        (f (i + 1) : t.heart.FullSubcategory) :=
    Subobject.ofLE (f i) (f (i + 1)) (f.monotone (Nat.le_succ i))
  have step_mono (i : ℕ) : IsHeartMono t (step i).hom :=
    isHeartMono_of_mono t (step i)
  have toAmbient_mono (i : ℕ) : IsHeartMono t (f i).arrow.hom :=
    isHeartMono_of_mono t (f i).arrow
  have prop (i : ℕ) :
      N.pair.tors (f i : t.heart.FullSubcategory).obj := by
    rw [hN]
    let Q : t.heart.FullSubcategory := cokernel (f i).arrow
    let p : E ⟶ Q := cokernel.π (f i).arrow
    have hp : (f i).arrow ≫ p = 0 := cokernel.condition (f i).arrow
    have hshort :
        (ShortComplex.mk (f i).arrow p hp).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f i).arrow)
        inferInstance inferInstance
    obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
      (C := C) t (f i).arrow p hp (fun {X} a ha => by
        exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
          hshort.fIsKernel.fac (KernelFork.ofι a ha) WalkingParallelPair.zero⟩)
    exact W.zeroCharge_left (f i : t.heart.FullSubcategory).property
      Q.property hE hd
  let c : SubobjectChain t N.pair.tors E.obj :=
    { obj := fun i => (f i : t.heart.FullSubcategory).obj
      prop := prop
      step := fun i => (step i).hom
      toAmbient := fun i => (f i).arrow.hom
      step_mono := step_mono
      toAmbient_mono := toAmbient_mono
      comm := fun i => by
        exact congrArg
          (fun k : (f i : t.heart.FullSubcategory) ⟶ E => k.hom)
          (Subobject.ofLE_arrow (f.monotone (Nat.le_succ i))) }
  obtain ⟨n, hn⟩ := N.noetherian E.obj E.property c
  refine ⟨n, fun m hnm => ?_⟩
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      rw [ih]
      let u : (f m : t.heart.FullSubcategory) ⟶
          (f (m + 1) : t.heart.FullSubcategory) := step m
      haveI : IsIso u.hom := hn m hnm
      let e : (f m : t.heart.FullSubcategory) ≅
          (f (m + 1) : t.heart.FullSubcategory) :=
        { hom := u
          inv := ObjectProperty.homMk (inv u.hom)
          hom_inv_id := by ext; simp
          inv_hom_id := by ext; simp }
      exact Subobject.eq_of_comm e (by
        exact Subobject.ofLE_arrow (f.monotone (Nat.le_succ m)))

/-- If zero-charge subobject chains terminate in a fixed heart object, then
that object has a maximal zero-charge subobject and the corresponding quotient
is right-orthogonal.

The right-orthogonality proof takes the image of a hypothetical map into the
quotient and pulls it back to a larger zero-charge subobject. -/
theorem WeakStabilityFunction.hasZeroChargeDecomposition_of_chainCondition
    (W : WeakStabilityFunction t) (E : C) (hE : t.heart E)
    (hacc : ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates) :
    ∃ (A Q : C) (_ : W.zeroCharge A) (_ : rightOrthogonal t W.zeroCharge Q)
      (i : A ⟶ E) (p : E ⟶ Q) (d : Q ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk i p d ∈ distTriang C := by
  let EH : t.heart.FullSubcategory := ⟨E, hE⟩
  let ZSub := {S : Subobject EH // W.heartZeroCharge t (S : t.heart.FullSubcategory)}
  have hwf : WellFoundedGT ZSub := by
    rw [wellFoundedGT_iff_monotone_chain_condition]
    intro f
    let step (j : ℕ) :
        (f j : t.heart.FullSubcategory) ⟶
          (f (j + 1) : t.heart.FullSubcategory) :=
      Subobject.ofLE (f j).1 (f (j + 1)).1
        (show (f j).1 ≤ (f (j + 1)).1 from f.monotone (Nat.le_succ j))
    let c : SubobjectChain t W.zeroCharge E :=
      { obj := fun j => (f j : t.heart.FullSubcategory).obj
        prop := fun j => (f j).2
        step := fun j => (step j).hom
        toAmbient := fun j => (f j).1.arrow.hom
        step_mono := fun j => isHeartMono_of_mono t (step j)
        toAmbient_mono := fun j => isHeartMono_of_mono t (f j).1.arrow
        comm := fun j => by
          exact congrArg
            (fun k : (f j : t.heart.FullSubcategory) ⟶ EH => k.hom)
            (Subobject.ofLE_arrow (f.monotone (Nat.le_succ j))) }
    obtain ⟨n, hn⟩ := hacc c
    refine ⟨n, fun m hnm => ?_⟩
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
        rw [ih]
        let u : (f m : t.heart.FullSubcategory) ⟶
            (f (m + 1) : t.heart.FullSubcategory) := step m
        haveI : IsIso u.hom := hn m hnm
        let e : (f m : t.heart.FullSubcategory) ≅
            (f (m + 1) : t.heart.FullSubcategory) :=
          { hom := u
            inv := ObjectProperty.homMk (inv u.hom)
            hom_inv_id := by ext; simp
            inv_hom_id := by ext; simp }
        apply Subtype.ext
        exact Subobject.eq_of_comm e
          (Subobject.ofLE_arrow (f.monotone (Nat.le_succ m)))
  letI : WellFoundedGT ZSub := hwf
  have hbot : W.heartZeroCharge t ((⊥ : Subobject EH) : t.heart.FullSubcategory) := by
    apply (W.heartZeroCharge t).prop_of_isZero
    exact (isZero_zero t.heart.FullSubcategory).of_iso Subobject.botCoeIsoZero
  obtain ⟨M, hMmax⟩ :=
    exists_maximal_of_wellFoundedGT (fun _ : ZSub => True)
      ⟨⟨⊥, hbot⟩, trivial⟩
  let MH : t.heart.FullSubcategory := (M.1 : t.heart.FullSubcategory)
  let iH : MH ⟶ EH := M.1.arrow
  let QH : t.heart.FullSubcategory := cokernel iH
  let pH : EH ⟶ QH := cokernel.π iH
  have hip : iH ≫ pH = 0 := cokernel.condition iH
  have hshort : (ShortComplex.mk iH pH hip).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel iH)
      inferInstance inferInstance
  have hQorth : rightOrthogonal t W.zeroCharge QH.obj := by
    refine ⟨QH.property, ?_⟩
    intro A0 hA0 f
    let A0H : t.heart.FullSubcategory := ⟨A0, hA0.1⟩
    let fH : A0H ⟶ QH := ObjectProperty.homMk f
    let I : Subobject QH := imageSubobject fH
    have hI : W.heartZeroCharge t (I : t.heart.FullSubcategory) := by
      exact (W.heartZeroCharge t).prop_of_epi
        (factorThruImageSubobject fH) hA0
    let PB : t.heart.FullSubcategory := pullback pH I.arrow
    let pbToI : PB ⟶ (I : t.heart.FullSubcategory) := pullback.snd pH I.arrow
    let pbToE : PB ⟶ EH := pullback.fst pH I.arrow
    let sq : IsPullback pbToI pbToE I.arrow pH :=
      (IsPullback.of_hasPullback pH I.arrow).flip
    let kmap : kernel pbToI ⟶ kernel pH :=
      kernel.map pbToI pH pbToE I.arrow sq.w
    haveI : IsIso kmap := isIso_kernel_map_of_isPullback sq
    let eKM : kernel pH ≅ MH :=
      IsLimit.conePointUniqueUpToIso (kernelIsKernel pH) hshort.fIsKernel
    let eK : kernel pbToI ≅ MH := asIso kmap ≪≫ eKM
    have hK : W.heartZeroCharge t (kernel pbToI) :=
      ObjectProperty.prop_of_iso (W.heartZeroCharge t) eK.symm M.2
    haveI : Epi pbToI := inferInstance
    let SPB : ShortComplex t.heart.FullSubcategory :=
      ShortComplex.mk (kernel.ι pbToI) pbToI (kernel.condition pbToI)
    have hSPB : SPB.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_kernel pbToI) inferInstance inferInstance
    have hPB : W.heartZeroCharge t PB :=
      (W.heartZeroCharge t).prop_X₂_of_shortExact hSPB hK hI
    let Psub : Subobject EH := Subobject.mk pbToE
    have hPsub : W.heartZeroCharge t (Psub : t.heart.FullSubcategory) :=
      ObjectProperty.prop_of_iso (W.heartZeroCharge t)
        (Subobject.underlyingIso pbToE).symm hPB
    have hip' : iH ≫ pH = (0 : MH ⟶ (I : t.heart.FullSubcategory)) ≫ I.arrow := by
      simpa using hip
    let mLift : MH ⟶ PB := pullback.lift iH 0 hip'
    have hle : M.1 ≤ Psub := by
      simpa [Psub, pbToE, mLift, iH] using
        Subobject.mk_le_mk_of_comm mLift (pullback.lift_fst iH 0 hip')
    let PZ : ZSub := ⟨Psub, hPsub⟩
    have hMP : M = PZ := hMmax.eq_of_le trivial hle
    have hsubeq : M.1 = Psub := congrArg Subtype.val hMP
    let r : (Psub : t.heart.FullSubcategory) ⟶ MH :=
      Subobject.ofLE Psub M.1 (le_of_eq hsubeq.symm)
    let fac : PB ⟶ MH := (Subobject.underlyingIso pbToE).inv ≫ r
    have hfac : fac ≫ iH = pbToE := by
      apply (t.heart).ι.map_injective
      simp [fac, r, iH, pbToE, Psub]
    have hpullzero : pbToE ≫ pH = 0 := by
      rw [← hfac, Category.assoc, hip, comp_zero]
    have hpbzero : pbToI = 0 := by
      apply (cancel_mono I.arrow).mp
      rw [sq.w, hpullzero]
      simp
    have hIzero : IsZero (I : t.heart.FullSubcategory) := by
      rw [IsZero.iff_id_eq_zero]
      apply (cancel_epi pbToI).mp
      rw [hpbzero]
      simp
    have hIarrow : I.arrow.hom = 0 :=
      congrArg InducedCategory.Hom.hom (hIzero.eq_of_src I.arrow 0)
    calc
      f = (factorThruImageSubobject fH).hom ≫ I.arrow.hom := by
        symm
        exact congrArg InducedCategory.Hom.hom (imageSubobject_arrow_comp fH)
      _ = 0 := by rw [hIarrow, comp_zero]
  obtain ⟨d, hd⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t iH pH hip (fun {A} a ha => by
      exact ⟨hshort.fIsKernel.lift (KernelFork.ofι a ha),
        hshort.fIsKernel.fac (KernelFork.ofι a ha)
          WalkingParallelPair.zero⟩)
  exact ⟨MH.obj, QH.obj, M.2, hQorth, iH.hom, pH.hom, d, hd⟩

/-- A zero-charge decomposition lifts across a short exact sequence whose
kernel has zero charge.  Concretely, the zero-charge subobject of the
quotient is pulled back to the middle term; its pullback is again
zero-charge because it is an extension of the old kernel by that subobject.

This is the abelian pullback step used after the envelope reduction in the
proof of Proposition 14.16. -/
theorem WeakStabilityFunction.hasZeroChargeDecomposition_of_reduction
    (W : WeakStabilityFunction t)
    (S : ShortComplex t.heart.FullSubcategory) (hS : S.ShortExact)
    (hA : W.zeroCharge S.X₁.obj)
    (hred : ∃ (B Q : C) (_ : W.zeroCharge B)
      (_ : rightOrthogonal t W.zeroCharge Q)
      (i : B ⟶ S.X₃.obj) (p : S.X₃.obj ⟶ Q)
      (d : Q ⟶ B⟦(1 : ℤ)⟧), Triangle.mk i p d ∈ distTriang C) :
    ∃ (B Q : C) (_ : W.zeroCharge B)
      (_ : rightOrthogonal t W.zeroCharge Q)
      (i : B ⟶ S.X₂.obj) (p : S.X₂.obj ⟶ Q)
      (d : Q ⟶ B⟦(1 : ℤ)⟧), Triangle.mk i p d ∈ distTriang C := by
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  obtain ⟨B, Q, hB, hQ, i, p, d, hd⟩ := hred
  let BH : t.heart.FullSubcategory := ⟨B, hB.1⟩
  let QH : t.heart.FullSubcategory := ⟨Q, hQ.1⟩
  let iH : BH ⟶ S.X₃ := ObjectProperty.homMk i
  let pH : S.X₃ ⟶ QH := ObjectProperty.homMk p
  have hip : iH ≫ pH = 0 := by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hd
  have hT : (ShortComplex.mk iH pH hip).ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) t (A := BH) (B := S.X₃) (Q := QH)
        (f := iH) (g := pH) (δ := d) hd
  letI : Mono iH := hT.mono_f
  letI : Epi pH := hT.epi_g
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  let PB : t.heart.FullSubcategory := pullback S.g iH
  let j : PB ⟶ S.X₂ := pullback.fst S.g iH
  let q : PB ⟶ BH := pullback.snd S.g iH
  let e : S.X₂ ⟶ QH := S.g ≫ pH
  have hje : j ≫ e = 0 := by
    dsimp [j, e]
    rw [pullback.condition_assoc, hip, comp_zero]
  let hKernel : IsLimit (KernelFork.ofι j hje) := by
    apply KernelFork.IsLimit.ofι'
    intro X k hk
    have hkp : (k ≫ S.g) ≫ pH = 0 := by
      simpa [e, Category.assoc] using hk
    let lB : X ⟶ BH := hT.fIsKernel.lift (KernelFork.ofι (k ≫ S.g) hkp)
    have hlB : lB ≫ iH = k ≫ S.g :=
      hT.fIsKernel.fac (KernelFork.ofι (k ≫ S.g) hkp)
        WalkingParallelPair.zero
    exact ⟨pullback.lift k lB hlB.symm, pullback.lift_fst _ _ _⟩
  haveI : Epi e := by
    dsimp [e]
    infer_instance
  have hMiddle : (ShortComplex.mk j e hje).ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.mk j e hje).exact_of_f_is_kernel hKernel)
        inferInstance inferInstance
  haveI : Epi q := by
    dsimp [q]
    infer_instance
  let a : S.X₁ ⟶ PB := pullback.lift S.f 0 (by simp)
  letI : Mono a :=
    mono_of_mono_fac (pullback.lift_fst S.f (0 : S.X₁ ⟶ BH) _)
  have haq : a ≫ q = 0 := by
    exact pullback.lift_snd S.f (0 : S.X₁ ⟶ BH) _
  let hAKernel : IsLimit (KernelFork.ofι a haq) := by
    apply KernelFork.IsLimit.ofι'
    intro X k hk
    have hkg : (k ≫ j) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      simpa [q] using congrArg (fun u ↦ u ≫ iH) hk
    let lA : X ⟶ S.X₁ :=
      hS.fIsKernel.lift (KernelFork.ofι (k ≫ j) hkg)
    have hlA : lA ≫ S.f = k ≫ j :=
      hS.fIsKernel.fac (KernelFork.ofι (k ≫ j) hkg)
        WalkingParallelPair.zero
    refine ⟨lA, ?_⟩
    apply pullback.hom_ext
    · calc
        (lA ≫ a) ≫ j = lA ≫ (a ≫ j) := Category.assoc _ _ _
        _ = lA ≫ S.f := by rw [show a ≫ j = S.f from pullback.lift_fst _ _ _]
        _ = k ≫ j := hlA
    · calc
        (lA ≫ a) ≫ q = lA ≫ (a ≫ q) := Category.assoc _ _ _
        _ = 0 := by rw [haq, comp_zero]
        _ = k ≫ q := hk.symm
  have hLeft : (ShortComplex.mk a q haq).ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.mk a q haq).exact_of_f_is_kernel hAKernel)
        inferInstance inferInstance
  have hPBzero : W.zeroCharge PB.obj := by
    have hPBheartZero : W.heartZeroCharge t PB :=
      (W.heartZeroCharge t).prop_X₂_of_shortExact hLeft hA hB
    exact hPBheartZero
  obtain ⟨delta, hdelta⟩ := TStructure.heartFullSubcategory_shortExact_triangle
    (C := C) t j e hje (fun {X} k hk => by
      exact ⟨hMiddle.fIsKernel.lift (KernelFork.ofι k hk),
        hMiddle.fIsKernel.fac (KernelFork.ofι k hk)
          WalkingParallelPair.zero⟩)
  exact ⟨PB.obj, Q, hPBzero, hQ, j.hom, e.hom, delta, hdelta⟩

/-- If zero-charge subobject chains terminate in every heart object, then
every object has a maximal zero-charge subobject and the corresponding
quotient is right-orthogonal.  Thus the relative chain condition constructs
the zero-charge torsion pair, rather than merely verifying noetherianity after
the pair has been supplied. -/
theorem WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition
    (W : WeakStabilityFunction t)
    (hacc : ∀ (E : C), t.heart E →
      ∀ c : SubobjectChain t W.zeroCharge E, c.Terminates) :
    W.HasZeroChargeDecompositions := by
  intro E hE
  exact W.hasZeroChargeDecomposition_of_chainCondition (t := t) E hE (hacc E hE)

end HeartObjects

end CategoryTheory.Triangulated.WeakStabilityCondition
