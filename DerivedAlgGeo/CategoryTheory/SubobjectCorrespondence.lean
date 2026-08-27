/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The subobject correspondence for a quotient, without a charge

For a subobject `M ≤ S` of an object `E` of an abelian category, the subobject of `E/M` cut out
by `S` pulls back to `S` again.  This is the classical correspondence between subobjects of
`E/M` and subobjects of `E` containing `M` — one half of it, in the form the
Harder--Narasimhan truncation consumes.

## Why this file exists

`StabilityCondition/Foundation/StabilityFunction/Uniqueness/SubobjectLattice.lean` already has
this statement, as `AbelianHNFiltration.pullback_imageSubobject_eq`.  Its proof, however, runs
through a **central charge**: it shows the offending cokernel has charge `0` and concludes it
vanishes, by `semiClosedUpperHalfPlane_ne_zero` — a nonzero object has nonzero charge.

That implication is exactly what *weak* stability drops, and it fails on exactly the object the
surface case of Bridgeland's Lemma 6.2 is about: a skyscraper on a surface is nonzero with
charge `0`.  So the charge proof cannot be reused for the weak Harder--Narasimhan theory, and
the truncation `tailAt` that depends on it does not port — which is what currently blocks the
weak torsion pair, and with it the tilt.

The statement, though, has nothing to do with stability.  It is true in any abelian category.
This file proves it that way, so the weak lane can use it.

## Method: pseudoelements

The proof is a diagram chase, carried out with `CategoryTheory.Abelian.Pseudoelement`.  This is
the first use of pseudoelements in this repository, which is a deliberate choice: the
alternative is an explicit five-lemma argument on the two short exact sequences
`0 → M → S → S/M → 0` and `0 → M → T → T/M → 0`, and the chase is both shorter and closer to
the textbook proof.

**Pseudoelements are not elements, and two of their failures matter here.**

* `pseudo_pullback`'s witness is **not unique**.  Mathlib says so and ships
  `Counterexamples/Pseudoelement.lean`; Borceux claims uniqueness and is wrong.
* There is **no subtraction**.  `sub_of_eq_image` is the only sanctioned "difference": from
  `f x = f y` it produces `z` with `f z = 0` such that `g z = g x` for every `g` killing `y`.

Nothing below reaches outside `eq_zero_iff`, `pseudo_surjective_of_epi`,
`pseudo_exact_of_exact` and `sub_of_eq_image`.  A chase that needs more than those is probably
unsound.

## Relationship to the existing lemma

The signature of `AbelianHNFiltration.pullback_imageSubobject_eq` is deliberately left alone —
it takes a `StabilityFunction` argument, and `Uniqueness/Tail.lean` calls it that way.  Dropping
that argument is a rename across the strict development.  This file supplies the charge-free
statement under its own name; wiring the existing lemma to delegate is a separate edit.
-/

noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian.Pseudoelement
open scoped Pseudoelement

universe u v

namespace CategoryTheory.Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- If a subobject maps trivially to the quotient by another subobject, it is contained in that
subobject.

Stated here so this file depends on Mathlib alone; the identical statement in
`Uniqueness/SubobjectLattice.lean` is charge-free too, but lives under `StabilityCondition`,
which a `CategoryTheory` leaf must not import. -/
theorem le_of_arrow_comp_cokernel_zero {E : A} {B M : Subobject E}
    (h : B.arrow ≫ cokernel.π M.arrow = 0) : B ≤ M := by
  have hkernel : kernelSubobject (cokernel.π M.arrow) = M := by
    simpa [imageSubobject_mono, Subobject.mk_arrow] using
      ((ShortComplex.mk M.arrow (cokernel.π M.arrow)
        (cokernel.condition M.arrow)).exact_iff_image_eq_kernel.mp
        (ShortComplex.exact_cokernel M.arrow)).symm
  rw [← hkernel]
  exact Subobject.le_of_comm
    (factorThruKernelSubobject _ B.arrow h)
    (factorThruKernelSubobject_comp_arrow _ _ _)

/-- The image of `S` in `E/M` pulls back to something containing `S`.

This half is formal — it is the unit of the `exists ⊣ pullback` adjunction, here written out
through the pullback square — and the existing charge-based proof already had it charge-free. -/
theorem le_pullback_imageSubobject {E : A} (M S : Subobject E) :
    S ≤ (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) :=
  Subobject.le_of_comm
    ((Subobject.isPullback (cokernel.π M.arrow)
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow))).isLimit.lift
      (PullbackCone.mk
        (factorThruImageSubobject (S.arrow ≫ cokernel.π M.arrow)) S.arrow
        (imageSubobject_arrow_comp (f := S.arrow ≫ cokernel.π M.arrow))))
    ((Subobject.isPullback (cokernel.π M.arrow)
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow))).isLimit.fac _
      WalkingCospan.right)

/-- **The subobject correspondence, charge-free.**

For `M ≤ S`, pulling the image of `S` in `E/M` back along the quotient map recovers `S`.

The containment `S ≤ pullback (image …)` is formal.  The reverse is the chase: a pseudoelement
of the pullback agrees with one of `S` after applying the quotient map, so their `sub_of_eq_image`
difference dies in `E/M`, hence comes from `M`, hence from `S` — and `S`'s own cokernel kills
it.  `M ≤ S` is used exactly once, at that last step, and it is the only place it is needed. -/
theorem pullback_imageSubobject_eq {E : A} {M S : Subobject E} (hMS : M ≤ S) :
    (Subobject.pullback (cokernel.π M.arrow)).obj
      (imageSubobject (S.arrow ≫ cokernel.π M.arrow)) = S := by
  set p : E ⟶ cokernel M.arrow := cokernel.π M.arrow with hp
  set I : Subobject (cokernel M.arrow) := imageSubobject (S.arrow ≫ p) with hI
  set T : Subobject E := (Subobject.pullback p).obj I with hT
  refine le_antisymm ?_ (le_pullback_imageSubobject M S)
  -- `T ≤ S`, via the cokernel criterion.
  refine le_of_arrow_comp_cokernel_zero ?_
  refine (eq_zero_iff _).mpr fun t => ?_
  -- The pullback square: `T.arrow ≫ p` factors through `I`.
  have hsq : Subobject.pullbackπ p I ≫ I.arrow = T.arrow ≫ p :=
    (Subobject.isPullback p I).w
  -- The image factorisation is epi, so the `I`-component comes from `S`.
  obtain ⟨s, hs⟩ :=
    pseudo_surjective_of_epi (factorThruImageSubobject (S.arrow ≫ p))
      (Subobject.pullbackπ p I t)
  -- Hence `T.arrow t` and `S.arrow s` agree after `p`.
  have hagree : p (T.arrow t) = p (S.arrow s) := by
    have h₁ : p (T.arrow t) = I.arrow (Subobject.pullbackπ p I t) := by
      rw [← Pseudoelement.comp_apply, ← Pseudoelement.comp_apply, hsq]
    have h₂ : I.arrow (Subobject.pullbackπ p I t) = p (S.arrow s) := by
      rw [← hs, ← Pseudoelement.comp_apply, imageSubobject_arrow_comp,
        Pseudoelement.comp_apply]
    rw [h₁, h₂]
  -- Their difference dies in `E/M`, so it comes from `M`.
  obtain ⟨z, hz0, hzg⟩ := sub_of_eq_image p (T.arrow t) (S.arrow s) hagree
  obtain ⟨m, hm⟩ :=
    pseudo_exact_of_exact (ShortComplex.exact_cokernel M.arrow) z hz0
  have hm' : M.arrow m = z := hm
  -- `S`'s cokernel kills `S.arrow s`, hence kills `z`, hence kills `T.arrow t`.
  have hkillS : (cokernel.π S.arrow) (S.arrow s) = 0 := by
    rw [← Pseudoelement.comp_apply, cokernel.condition, Pseudoelement.zero_apply]
  have hz : (cokernel.π S.arrow) z = 0 := by
    rw [← hm', ← Pseudoelement.comp_apply, ← Subobject.ofLE_arrow hMS,
      Category.assoc, cokernel.condition, comp_zero, Pseudoelement.zero_apply]
  rw [Pseudoelement.comp_apply, ← hzg _ (cokernel.π S.arrow) hkillS, hz]

/-! ## The pulled-back sequence, and the third isomorphism

`0 → M → (pullback p).obj B → B → 0` is exact for every subobject `B` of `E/M`.  From it the
comparison of successive quotients follows, which is the second half of what the
Harder--Narasimhan truncation needs. -/

variable {E : A}

/-- Every pullback of a subobject of `E/M` contains `M`: the composite `M → E → E/M` is zero,
so it lifts through the pullback. -/
theorem le_pullback_cokernel (M : Subobject E) (B : Subobject (cokernel M.arrow)) :
    M ≤ (Subobject.pullback (cokernel.π M.arrow)).obj B :=
  Subobject.le_of_comm
    ((Subobject.isPullback (cokernel.π M.arrow) B).isLimit.lift
      (PullbackCone.mk (0 : (M : A) ⟶ (B : A)) M.arrow
        (by rw [zero_comp, cokernel.condition])))
    ((Subobject.isPullback (cokernel.π M.arrow) B).isLimit.fac _ WalkingCospan.right)

/-- The restricted quotient map out of a pullback is epi. -/
instance epi_pullbackπ (M : Subobject E) (B : Subobject (cokernel M.arrow)) :
    Epi (Subobject.pullbackπ (cokernel.π M.arrow) B) := by
  rw [← (Subobject.isPullback (cokernel.π M.arrow) B).isoPullback_hom_fst]
  infer_instance

/-- The kernel inclusion followed by the restricted quotient map is zero. -/
theorem ofLE_pullbackπ_cokernel_eq_zero (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    Subobject.ofLE M _ (le_pullback_cokernel M B) ≫
      Subobject.pullbackπ (cokernel.π M.arrow) B = 0 := by
  apply (cancel_mono B.arrow).mp
  simp only [zero_comp, Category.assoc]
  rw [(Subobject.isPullback (cokernel.π M.arrow) B).w, ← Category.assoc,
    Subobject.ofLE_arrow, cokernel.condition]

/-- **`0 → M → (pullback p).obj B → B → 0` is exact.** -/
theorem shortExact_ofLE_pullbackπ (M : Subobject E)
    (B : Subobject (cokernel M.arrow)) :
    (ShortComplex.mk (Subobject.ofLE M _ (le_pullback_cokernel M B))
      (Subobject.pullbackπ (cokernel.π M.arrow) B)
      (ofLE_pullbackπ_cokernel_eq_zero M B)).ShortExact := by
  set p := cokernel.π M.arrow with hp
  set pbB := (Subobject.pullback p).obj B with hpbB
  have hquotient :
      (ShortComplex.mk M.arrow p (cokernel.condition M.arrow)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel M.arrow)
      inferInstance inferInstance
  have hkernel := hquotient.fIsKernel
  apply ShortComplex.ShortExact.mk' _ inferInstance inferInstance
  apply ShortComplex.exact_of_f_is_kernel
  have hw := (Subobject.isPullback p B).w
  have key : ∀ {W : A} (g : W ⟶ (pbB : A)),
      g ≫ Subobject.pullbackπ p B = 0 → (g ≫ pbB.arrow) ≫ p = 0 := by
    intro W g hg
    rw [Category.assoc, ← hw, ← Category.assoc, hg, zero_comp]
  exact KernelFork.IsLimit.ofι' (Subobject.ofLE M pbB (le_pullback_cokernel M B))
    (ofLE_pullbackπ_cokernel_eq_zero M B)
    (fun g hg => ⟨hkernel.lift (KernelFork.ofι (g ≫ pbB.arrow) (key g hg)), by
      apply (cancel_mono pbB.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow]
      exact hkernel.fac (KernelFork.ofι (g ≫ pbB.arrow) (key g hg))
        WalkingParallelPair.zero⟩)

/-- Pulling back is natural in the subobject: the inclusion of pullbacks commutes with the
restricted quotient maps. -/
theorem ofLE_pullback_comp_pullbackπ (M : Subobject E)
    {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    Subobject.ofLE _ _ (Functor.monotone (Subobject.pullback (cokernel.π M.arrow)) h) ≫
        Subobject.pullbackπ (cokernel.π M.arrow) B₂ =
      Subobject.pullbackπ (cokernel.π M.arrow) B₁ ≫ Subobject.ofLE B₁ B₂ h := by
  apply (cancel_mono B₂.arrow).mp
  rw [Category.assoc, Category.assoc, (Subobject.isPullback (cokernel.π M.arrow) B₂).w,
    Subobject.ofLE_arrow, ← Category.assoc, Subobject.ofLE_arrow,
    (Subobject.isPullback (cokernel.π M.arrow) B₁).w]

/-- **Successive quotients are unchanged by pulling back, charge-free.**

The comparison map is epi because the restricted quotient map is; it is mono by the same chase
as `pullback_imageSubobject_eq`, with `shortExact_ofLE_pullbackπ` supplying the preimage in `M`
and `M ≤ (pullback p).obj B₁` absorbing it. -/
noncomputable def cokernelPullbackIso (M : Subobject E)
    {B₁ B₂ : Subobject (cokernel M.arrow)} (h : B₁ ≤ B₂) :
    cokernel (Subobject.ofLE _ _
        (Functor.monotone (Subobject.pullback (cokernel.π M.arrow)) h)) ≅
      cokernel (Subobject.ofLE B₁ B₂ h) := by
  set p := cokernel.π M.arrow with hp
  set pbB₁ := (Subobject.pullback p).obj B₁ with hpb₁
  set pbB₂ := (Subobject.pullback p).obj B₂ with hpb₂
  set hpull : pbB₁ ≤ pbB₂ := Functor.monotone _ h with hpullDef
  have hnat := ofLE_pullback_comp_pullbackπ M h
  have hfactor : Subobject.ofLE pbB₁ pbB₂ hpull ≫
      (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h)) = 0 := by
    rw [← Category.assoc, hnat, Category.assoc, cokernel.condition, comp_zero]
  set f := cokernel.desc (Subobject.ofLE pbB₁ pbB₂ hpull)
    (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h)) hfactor with hf
  haveI : Epi f := by
    have hfac : cokernel.π (Subobject.ofLE pbB₁ pbB₂ hpull) ≫ f =
        Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h) :=
      cokernel.π_desc _ _ _
    exact epi_of_epi_fac hfac
  haveI : Mono f := by
    refine mono_of_zero_of_map_zero f fun a ha => ?_
    obtain ⟨x, hx⟩ :=
      pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE pbB₁ pbB₂ hpull)) a
    -- `f a = 0` says the `B`-side class of `x` vanishes.
    have hxB : (cokernel.π (Subobject.ofLE B₁ B₂ h)) (Subobject.pullbackπ p B₂ x) = 0 := by
      rw [← Pseudoelement.comp_apply, ← cokernel.π_desc (Subobject.ofLE pbB₁ pbB₂ hpull)
        (Subobject.pullbackπ p B₂ ≫ cokernel.π (Subobject.ofLE B₁ B₂ h)) hfactor,
        Pseudoelement.comp_apply, hx]
      exact ha
    -- So it comes from `B₁`, and `pullbackπ` for `B₁` is epi, so from `pbB₁`.
    obtain ⟨y, hy⟩ := pseudo_exact_of_exact
      (ShortComplex.exact_cokernel (Subobject.ofLE B₁ B₂ h)) _ hxB
    obtain ⟨w, hw⟩ := pseudo_surjective_of_epi (Subobject.pullbackπ p B₁) y
    -- `x` and `ofLE w` agree after `pullbackπ`, so differ by something from `M`.
    have hagree : Subobject.pullbackπ p B₂ (Subobject.ofLE pbB₁ pbB₂ hpull w) =
        Subobject.pullbackπ p B₂ x := by
      rw [← Pseudoelement.comp_apply, hnat, Pseudoelement.comp_apply, hw, hy]
    obtain ⟨z, hz0, hzg⟩ :=
      sub_of_eq_image (Subobject.pullbackπ p B₂) x
        (Subobject.ofLE pbB₁ pbB₂ hpull w) hagree.symm
    obtain ⟨m, hm⟩ :=
      pseudo_exact_of_exact (shortExact_ofLE_pullbackπ M B₂).exact z hz0
    have hm' : Subobject.ofLE M pbB₂ (le_pullback_cokernel M B₂) m = z := hm
    -- The cokernel of `pbB₁ ↪ pbB₂` kills both, so it kills `x`.
    have hkill : (cokernel.π (Subobject.ofLE pbB₁ pbB₂ hpull))
        (Subobject.ofLE pbB₁ pbB₂ hpull w) = 0 := by
      rw [← Pseudoelement.comp_apply, cokernel.condition, Pseudoelement.zero_apply]
    have hzz : (cokernel.π (Subobject.ofLE pbB₁ pbB₂ hpull)) z = 0 := by
      have hsplit : Subobject.ofLE M pbB₂ (le_pullback_cokernel M B₂) =
          Subobject.ofLE M pbB₁ (le_pullback_cokernel M B₁) ≫
            Subobject.ofLE pbB₁ pbB₂ hpull :=
        (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm
      rw [← hm', ← Pseudoelement.comp_apply, hsplit, Category.assoc,
        cokernel.condition, comp_zero, Pseudoelement.zero_apply]
    rw [← hx, ← hzg _ _ hkill, hzz]
  haveI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

end CategoryTheory.Abelian
