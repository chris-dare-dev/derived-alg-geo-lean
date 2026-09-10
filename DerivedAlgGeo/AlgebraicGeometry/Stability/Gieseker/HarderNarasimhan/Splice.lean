/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.StrictDrop

/-!
# Lifting a filtration of a quotient back to the ambient object

The Harder–Narasimhan recursion removes the maximal destabilizing subobject `B ⊆ E`, filters the
quotient `E / B`, and splices the two together. This file supplies the lattice-level facts that
splice needs, all of them about the subobject correspondence and none of them about slopes.

* `pullback_bot` — the bottom subobject of `E / B` pulls back to `B` itself, so the spliced chain
  really does begin `⊥ < B < …`. It is `pullback_imageSubobject_eq` at `S = B`, where the image
  of `B.arrow ≫ cokernel.π B.arrow = 0` is `⊥`.
* `pullback_lt_of_lt` — strict inclusions pull back to strict inclusions. This is not formal
  monotonicity: it is proved from the fact that a chain step with a nonzero successive quotient
  cannot be an equality, using `cokernelPullbackIso` to identify that quotient with the one
  upstairs.
* `cokernelOfLEBotIso` — the first successive quotient of the spliced chain, `cokernel (⊥ ⟶ B)`,
  is `B` itself, which is what lets the first factor's slope and semistability be read off the
  maximal destabilizing subobject.

Nothing here mentions a polarization; it is the correspondence, specialised to what the splice
consumes.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **The bottom of the quotient pulls back to the subobject itself.** -/
theorem pullback_bot {F : Coh X} (B : Subobject F) :
    (Subobject.pullback (cokernel.π B.arrow)).obj ⊥ = B := by
  have hzero : B.arrow ≫ cokernel.π B.arrow = 0 := cokernel.condition _
  have h := CategoryTheory.Abelian.pullback_imageSubobject_eq (le_refl B)
  rwa [hzero, imageSubobject_zero] at h

/-- The inclusion of the bottom subobject into any subobject is the zero morphism. -/
theorem ofLE_bot_eq_zero {F : Coh X} (B : Subobject F) (h : (⊥ : Subobject F) ≤ B) :
    Subobject.ofLE ⊥ B h = 0 := by
  have hz : IsZero ((⊥ : Subobject F) : Coh X) :=
    IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
  exact hz.eq_zero_of_src _

/-- **The first successive quotient of a spliced chain is the subobject itself.** -/
noncomputable def cokernelOfLEBotIso {F : Coh X} (B : Subobject F)
    (h : (⊥ : Subobject F) ≤ B) :
    cokernel (Subobject.ofLE ⊥ B h) ≅ (B : Coh X) := by
  refine (?_ : cokernel (Subobject.ofLE ⊥ B h) ≅ cokernel (0 : ((⊥ : Subobject F) : Coh X) ⟶
    (B : Coh X))).trans cokernelZeroIsoTarget
  exact cokernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp [ofLE_bot_eq_zero B h])

/-- A strict inclusion of subobjects has a nonzero successive quotient: a zero cokernel would
make the inclusion an isomorphism. This is `AbelianWeakHNFiltration.factor_not_isZero`'s
argument, stated for a bare pair of subobjects. -/
theorem cokernel_not_isZero_of_lt {Y : Coh X} {C₁ C₂ : Subobject Y} (hlt : C₁ < C₂) :
    ¬IsZero (cokernel (Subobject.ofLE C₁ C₂ hlt.le)) := fun hzero ↦ by
  haveI : Epi (Subobject.ofLE C₁ C₂ hlt.le) :=
    Preadditive.epi_of_isZero_cokernel _ hzero
  haveI : IsIso (Subobject.ofLE C₁ C₂ hlt.le) := isIso_of_mono_of_epi _
  have hle : C₂ ≤ C₁ :=
    Subobject.le_of_comm (inv (Subobject.ofLE C₁ C₂ hlt.le)) (by simp)
  exact absurd hle (not_le_of_gt hlt)

/-- **Strict inclusions pull back to strict inclusions.**

Monotonicity is formal; strictness is not. If the pullbacks agreed, the inclusion between them
would be an isomorphism and its cokernel zero, but `cokernelPullbackIso` identifies that cokernel
with the successive quotient upstairs, which a strict inclusion makes nonzero. -/
theorem pullback_lt_of_lt {F : Coh X} (B : Subobject F)
    {C₁ C₂ : Subobject (cokernel B.arrow)} (hlt : C₁ < C₂) :
    (Subobject.pullback (cokernel.π B.arrow)).obj C₁ <
      (Subobject.pullback (cokernel.π B.arrow)).obj C₂ := by
  have hle : C₁ ≤ C₂ := hlt.le
  have hne : ¬IsZero (cokernel (Subobject.ofLE C₁ C₂ hle)) := cokernel_not_isZero_of_lt hlt
  refine lt_of_le_of_ne (Functor.monotone _ hle) ?_
  intro heq
  apply hne
  set p := cokernel.π B.arrow with hp
  set pb₁ := (Subobject.pullback p).obj C₁ with hpb₁
  set pb₂ := (Subobject.pullback p).obj C₂ with hpb₂
  have hmono : pb₁ ≤ pb₂ := Functor.monotone _ hle
  have hback : pb₂ ≤ pb₁ := le_of_eq heq.symm
  haveI : IsIso (Subobject.ofLE pb₁ pb₂ hmono) :=
    ⟨⟨Subobject.ofLE pb₂ pb₁ hback,
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl],
      by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]⟩⟩
  have hcokzero : IsZero (cokernel (Subobject.ofLE pb₁ pb₂ hmono)) :=
    (Preadditive.epi_iff_isZero_cokernel _).mp inferInstance
  exact hcokzero.of_iso (CategoryTheory.Abelian.cokernelPullbackIso B hle).symm

end AlgebraicGeometry.Stability.Gieseker
