/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.Extrema

/-!
# The maximally destabilizing subobject and the extremal phase functions

This file owns the public interface built on the uniqueness argument: the
canonical maximally destabilizing subobject of a nonzero object, its
destabilizing quotient and the short exact sequence they form, and the extremal
phase functions `phiPlus` and `phiMinus` with the characterisation of
semistability as their equality.

This is the module a consumer of the uniqueness milestone should import.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- The canonical maximally destabilizing subobject of a nonzero object. -/
noncomputable def maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : Subobject E :=
  let F := Classical.choice (hHN E hE)
  F.chain ⟨1, by have := F.nonempty; lia⟩

/-- The canonical maximally destabilizing subobject agrees with the first
nonzero term of every owner HN filtration. -/
theorem maxDestabilizingSubobject_eq_filtration (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (F : AbelianHNFiltration Z E) :
    Z.maxDestabilizingSubobject hHN E hE =
      F.chain ⟨1, by have := F.nonempty; lia⟩ :=
  (Classical.choice (hHN E hE)).chain_one_eq F

/-- The canonical maximally destabilizing subobject is nonzero. -/
theorem maxDestabilizingSubobject_ne_bot (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE ≠ ⊥ :=
  (Classical.choice (hHN E hE)).chain_one_ne_bot

/-- The canonical maximally destabilizing subobject is semistable. -/
theorem maxDestabilizingSubobject_isSemistable (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable (Z.maxDestabilizingSubobject hHN E hE : A) :=
  (Classical.choice (hHN E hE)).chain_one_isSemistable

/-- A nonzero object is semistable exactly when its canonical maximally
destabilizing subobject is the whole object. -/
theorem maxDestabilizingSubobject_eq_top_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.maxDestabilizingSubobject hHN E hE = ⊤ ↔ Z.IsSemistable E := by
  let F := Classical.choice (hHN E hE)
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  constructor
  · intro htop
    have htopsemistable : Z.IsSemistable ((⊤ : Subobject E) : A) :=
      htop ▸ F.chain_one_isSemistable
    exact Z.isSemistable_of_iso (asIso (⊤ : Subobject E).arrow)
      htopsemistable
  · intro hEsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hEsemistable
    have hindex : (⟨1, by have := F.nonempty; lia⟩ : Fin (F.n + 1)) =
        ⟨F.n, by lia⟩ := Fin.ext (by lia)
    rw [hindex, F.chain_top]

/-- The quotient left after removing the canonical maximally destabilizing
subobject. -/
noncomputable def destabilizingQuotient (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : A :=
  cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow

/-- The destabilizing quotient is zero exactly for semistable objects. -/
theorem isZero_destabilizingQuotient_iff_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    IsZero (Z.destabilizingQuotient hHN E hE) ↔ Z.IsSemistable E := by
  rw [← Z.maxDestabilizingSubobject_eq_top_iff_isSemistable hHN E hE]
  constructor
  · intro hquotient
    haveI : Epi (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      Preadditive.epi_of_isZero_cokernel _ hquotient
    haveI : IsIso (Z.maxDestabilizingSubobject hHN E hE).arrow :=
      isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow _
  · intro htop
    change IsZero (cokernel (Z.maxDestabilizingSubobject hHN E hE).arrow)
    rw [htop]
    exact isZero_cokernel_of_epi (⊤ : Subobject E).arrow

/-- A non-semistable object has a nonzero destabilizing quotient. -/
theorem destabilizingQuotient_not_isZero_of_not_isSemistable
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) (hnot : ¬Z.IsSemistable E) :
    ¬IsZero (Z.destabilizingQuotient hHN E hE) :=
  fun hzero => hnot ((Z.isZero_destabilizingQuotient_iff_isSemistable
    hHN E hE).1 hzero)

/-- The canonical short complex presenting an object as an extension of its
maximally destabilizing subobject by the destabilizing quotient. -/
noncomputable def destabilizingShortComplex (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) : ShortComplex A :=
  ShortComplex.mk (Z.maxDestabilizingSubobject hHN E hE).arrow
    (cokernel.π (Z.maxDestabilizingSubobject hHN E hE).arrow)
    (cokernel.condition (Z.maxDestabilizingSubobject hHN E hE).arrow)

/-- The canonical destabilizing short complex is short exact. -/
theorem destabilizingShortComplex_shortExact (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    (Z.destabilizingShortComplex hHN E hE).ShortExact := by
  change (ShortComplex.mk _ _ _).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel
      (Z.maxDestabilizingSubobject hHN E hE).arrow)
    inferInstance inferInstance

/-- The central charge splits across the canonical destabilizing short exact
sequence. -/
theorem charge_eq_maxDestabilizingSubobject_add_destabilizingQuotient
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.charge E = Z.charge (Z.maxDestabilizingSubobject hHN E hE : A) +
      Z.charge (Z.destabilizingQuotient hHN E hE) :=
  Z.additive (Z.destabilizingShortComplex hHN E hE)
    (Z.destabilizingShortComplex_shortExact hHN E hE)

/-- The intrinsic highest HN phase of a nonzero object. -/
noncomputable def phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiPlus

/-- The intrinsic lowest HN phase of a nonzero object. -/
noncomputable def phiMinus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) : ℝ :=
  (Classical.choice (hHN E hE)).phiMinus

/-- The intrinsic highest phase agrees with every owner HN filtration. -/
theorem phiPlus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiPlus hHN E hE = F.phiPlus :=
  (Classical.choice (hHN E hE)).phiPlus_eq F

/-- The canonical maximally destabilizing subobject has the intrinsic highest
HN phase. -/
theorem phase_maxDestabilizingSubobject (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.phase (Z.maxDestabilizingSubobject hHN E hE : A) =
      Z.phiPlus hHN E hE :=
  (Classical.choice (hHN E hE)).phase_chain_one

/-- Every semistable subobject at the intrinsic highest HN phase lies in the
canonical maximally destabilizing subobject. -/
theorem le_maxDestabilizingSubobject_of_semistable_phase_eq_phiPlus
    (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) {B : Subobject E}
    (hB : Z.IsSemistable (B : A))
    (hphase : Z.phase (B : A) = Z.phiPlus hHN E hE) :
    B ≤ Z.maxDestabilizingSubobject hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F] at hphase
  rw [Z.maxDestabilizingSubobject_eq_filtration hHN hE F]
  exact F.le_chain_one_of_semistable_phase_eq_phiPlus hB hphase

/-- The intrinsic lowest phase agrees with every owner HN filtration. -/
theorem phiMinus_eq_filtration (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    {E : A} (hE : ¬IsZero E) (F : AbelianHNFiltration Z E) :
    Z.phiMinus hHN E hE = F.phiMinus :=
  (Classical.choice (hHN E hE)).phiMinus_eq F

/-- The intrinsic lowest HN phase is at most the intrinsic highest phase. -/
theorem phiMinus_le_phiPlus (Z : StabilityFunction A) (hHN : Z.HasHNProperty)
    (E : A) (hE : ¬IsZero E) :
    Z.phiMinus hHN E hE ≤ Z.phiPlus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiMinus_eq_filtration hHN hE F,
    Z.phiPlus_eq_filtration hHN hE F]
  exact F.phiMinus_le_phiPlus

/-- A nonzero object is semistable exactly when its intrinsic HN phase
interval degenerates to a point. -/
theorem isSemistable_iff_phiPlus_eq_phiMinus (Z : StabilityFunction A)
    (hHN : Z.HasHNProperty) (E : A) (hE : ¬IsZero E) :
    Z.IsSemistable E ↔ Z.phiPlus hHN E hE = Z.phiMinus hHN E hE := by
  let F := Classical.choice (hHN E hE)
  rw [Z.phiPlus_eq_filtration hHN hE F,
    Z.phiMinus_eq_filtration hHN hE F]
  constructor
  · intro hsemistable
    have hn : F.n = 1 := F.n_eq_one_of_semistable hsemistable
    apply congrArg F.phase
    apply Fin.ext
    lia
  · intro hextrema
    apply F.isSemistable_of_n_eq_one
    by_contra hn
    have hn_gt : 1 < F.n := by
      have := F.nonempty
      lia
    have hlast_lt : F.phiMinus < F.phiPlus := by
      exact F.phase_strictAnti (Fin.mk_lt_mk.mpr (by lia))
    exact (ne_of_lt hlast_lt) hextrema.symm

end StabilityFunction

end CategoryTheory.Triangulated
