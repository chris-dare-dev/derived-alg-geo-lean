/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Uniqueness.MonoDescent

/-!
# Slope-indexed Harder--Narasimhan filtrations for weak stability functions

`HarderNarasimhan.lean` stores the successive **phases** of an HN filtration in
`ℝ`.  That is available for a strict stability function, whose charges avoid
`0`, and unavailable for a weak one, whose charges do not: a skyscraper on a
surface has charge exactly `0`, and `arg 0 = 0` is not its phase.

This file stores the successive **slopes** in `WithTop ℝ` instead, exactly as
`WeakStabilityCondition.WeakAbelianHNFiltration` already does on the heart side.
The difference from that structure is the class datum, not the indexing: this
one is at `abelianDatum A`, with classes in `K₀Ab A` and subobject data in the
abelian category itself, where `Uniqueness/` and `Cutoff.lean` live.  The heart
structure is at `heartDatum t`, with classes in the ambient `K₀ C`.  The two
groups differ, so neither is an instance of the other.

The extrema are `μPlus` (the first, largest slope) and `μMinus` (the last,
smallest).  Note the direction: slopes **decrease** along the filtration and
`⊤` is the largest value, so `μPlus = ⊤` exactly when the first factor has
charge on the real boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A **slope-indexed weak Harder--Narasimhan filtration** of a nonzero object
for a weak stability function on an abelian category: a strictly increasing
finite chain of subobjects whose successive quotients are weak-semistable with
strictly decreasing slopes in `WithTop ℝ`. -/
structure AbelianWeakHNFiltration (W : WeakStabilityFunctionOn (abelianDatum A))
    (E : A) where
  /-- Number of weak-semistable factors. -/
  n : ℕ
  /-- An HN filtration has at least one factor. -/
  nonempty : 0 < n
  /-- The chain from zero to the whole object. -/
  chain : Fin (n + 1) → Subobject E
  /-- The chain is strictly increasing. -/
  chain_strictMono : StrictMono chain
  /-- The initial term is zero. -/
  chain_bot : chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥
  /-- The final term is the whole object. -/
  chain_top : chain ⟨n, n.lt_succ_iff.mpr le_rfl⟩ = ⊤
  /-- Slopes of successive quotients, in `WithTop ℝ`. -/
  μ : Fin n → WithTop ℝ
  /-- Successive slopes strictly decrease. -/
  μ_anti : StrictAnti μ
  /-- The declared slope is the intrinsic slope of each quotient. -/
  factor_slope : ∀ j : Fin n,
    W.slope (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ)))) = μ j
  /-- Each successive quotient is weak-semistable. -/
  factor_semistable : ∀ j : Fin n,
    W.IsSemistable (cokernel (Subobject.ofLE (chain j.castSucc) (chain j.succ)
      (le_of_lt (chain_strictMono j.castSucc_lt_succ))))

namespace AbelianWeakHNFiltration

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {E : A}

/-- The `j`-th successive quotient. -/
abbrev factor (F : AbelianWeakHNFiltration W E) (j : Fin F.n) : A :=
  cokernel (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
    (le_of_lt (F.chain_strictMono j.castSucc_lt_succ)))

/-- The **highest** HN slope, at the first factor.  It is `⊤` exactly when the
maximal destabilizing factor has charge on the real boundary. -/
def μPlus (F : AbelianWeakHNFiltration W E) : WithTop ℝ :=
  F.μ ⟨0, F.nonempty⟩

/-- The **lowest** HN slope, at the last factor. -/
def μMinus (F : AbelianWeakHNFiltration W E) : WithTop ℝ :=
  F.μ ⟨F.n - 1, Nat.sub_lt F.nonempty (by decide)⟩

/-- Every factor slope lies between the HN extrema.  The proof is the order
argument of `AbelianHNFiltration.phase_mem_range`, unchanged: `StrictAnti`
supplies `antitone` over any preorder, so nothing here is specific to `ℝ`. -/
theorem μ_mem_range (F : AbelianWeakHNFiltration W E) (i : Fin F.n) :
    F.μMinus ≤ F.μ i ∧ F.μ i ≤ F.μPlus := by
  constructor
  · exact F.μ_anti.antitone (Fin.mk_le_mk.mpr (by lia))
  · exact F.μ_anti.antitone (Fin.mk_le_mk.mpr (by lia))

/-- The lowest HN slope does not exceed the highest. -/
theorem μMinus_le_μPlus (F : AbelianWeakHNFiltration W E) :
    F.μMinus ≤ F.μPlus :=
  (F.μ_mem_range ⟨0, F.nonempty⟩).1

/-- Every factor of an HN filtration is nonzero: a zero cokernel would make the
chain step an isomorphism, contradicting strictness. -/
theorem factor_not_isZero (F : AbelianWeakHNFiltration W E) (j : Fin F.n) :
    ¬IsZero (F.factor j) := fun hzero => by
  let f := Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
    (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))
  haveI : Epi f := Preadditive.epi_of_isZero_cokernel f hzero
  haveI : IsIso f := isIso_of_mono_of_epi f
  have hle : F.chain j.succ ≤ F.chain j.castSucc :=
    Subobject.le_of_comm (inv f) (by simp [f])
  exact (not_le_of_gt (F.chain_strictMono j.castSucc_lt_succ)) hle

/-- **A weak-semistable object is its own HN filtration.**  One factor, the
object itself, so both extrema are its slope.  This is what places a
weak-semistable rank-zero object — slope `⊤` — in the torsion class at every
finite cutoff. -/
def ofSemistable {E : A} (hE : W.IsSemistable E) : AbelianWeakHNFiltration W E where
  n := 1
  nonempty := Nat.one_pos
  chain := fun i => if i = 0 then ⊥ else ⊤
  chain_strictMono := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.lt_def] at hij
    have hi0 : i = 0 := by lia
    have hj1 : j = 1 := by lia
    subst hi0
    subst hj1
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one,
      one_ne_zero, gt_iff_lt]
    exact lt_of_le_of_ne bot_le
      (Ne.symm (StabilityFunction.subobject_top_ne_bot_of_not_isZero hE.1))
  chain_bot := by simp
  chain_top := by simp
  μ := fun _ => W.slope E
  μ_anti := fun a b hab => by exfalso; exact absurd hab (by lia)
  factor_slope := by
    intro ⟨j, hj⟩
    have hj0 : j = 0 := by lia
    subst hj0
    change W.slope (cokernel (Subobject.ofLE ⊥ ⊤ _)) = W.slope E
    exact W.slope_eq_of_iso (StabilityFunction.subobjectCokernelBotIso
      (⊤ : Subobject E) bot_le ≪≫ asIso (⊤ : Subobject E).arrow)
  factor_semistable := by
    intro ⟨j, hj⟩
    have hj0 : j = 0 := by lia
    subst hj0
    change W.IsSemistable (cokernel (Subobject.ofLE ⊥ ⊤ _))
    exact W.isSemistable_of_iso (StabilityFunction.subobjectCokernelBotIso
      (⊤ : Subobject E) bot_le ≪≫ asIso (⊤ : Subobject E).arrow).symm hE

@[simp]
theorem ofSemistable_μPlus {E : A} (hE : W.IsSemistable E) :
    (ofSemistable hE).μPlus = W.slope E := rfl

@[simp]
theorem ofSemistable_μMinus {E : A} (hE : W.IsSemistable E) :
    (ofSemistable hE).μMinus = W.slope E := rfl

end AbelianWeakHNFiltration

namespace WeakStabilityFunctionOn

/-- A weak stability function has the HN property when every nonzero object
admits a slope-indexed weak HN filtration. -/
def HasHNProperty (W : WeakStabilityFunctionOn (abelianDatum A)) : Prop :=
  ∀ E : A, ¬IsZero E → Nonempty (AbelianWeakHNFiltration W E)

variable (W : WeakStabilityFunctionOn (abelianDatum A))

/-- Slope equality after propositionally rewriting both subobjects in a
successive quotient. -/
theorem slope_cokernel_ofLE_congr {E : A} {A₁ A₂ B₁ B₂ : Subobject E}
    (hA : A₁ = A₂) (hB : B₁ = B₂) {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂} :
    W.slope (cokernel (Subobject.ofLE A₁ B₁ h₁)) =
      W.slope (cokernel (Subobject.ofLE A₂ B₂ h₂)) := by
  subst A₂
  subst B₂
  rfl

/-- Weak semistability is preserved after propositionally rewriting both
subobjects in a successive quotient. -/
theorem isSemistable_cokernel_ofLE_congr {E : A} {A₁ A₂ B₁ B₂ : Subobject E}
    (hA : A₁ = A₂) (hB : B₁ = B₂) {h₁ : A₁ ≤ B₁} {h₂ : A₂ ≤ B₂}
    (hs : W.IsSemistable (cokernel (Subobject.ofLE A₂ B₂ h₂))) :
    W.IsSemistable (cokernel (Subobject.ofLE A₁ B₁ h₁)) := by
  subst A₂
  subst B₂
  exact hs

/-- Successive quotients keep their slope when a subobject chain is mapped
along a monomorphism. -/
theorem slope_cokernel_mapMono_eq {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    W.slope (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) =
      W.slope (cokernel (Subobject.ofLE S T h)) :=
  W.slope_eq_of_iso (StabilityFunction.Subobject.cokernelMapMonoIso f h)

/-- Successive quotients keep their weak semistability when a subobject chain
is mapped along a monomorphism. -/
theorem isSemistable_cokernel_mapMono_iff {X Y : A} (f : X ⟶ Y) [Mono f]
    {S T : Subobject X} (h : S ≤ T) :
    W.IsSemistable (cokernel (Subobject.ofLE ((Subobject.map f).obj S)
      ((Subobject.map f).obj T) ((Subobject.map f).monotone h))) ↔
      W.IsSemistable (cokernel (Subobject.ofLE S T h)) :=
  ⟨W.isSemistable_of_iso (StabilityFunction.Subobject.cokernelMapMonoIso f h),
   W.isSemistable_of_iso (StabilityFunction.Subobject.cokernelMapMonoIso f h).symm⟩

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
