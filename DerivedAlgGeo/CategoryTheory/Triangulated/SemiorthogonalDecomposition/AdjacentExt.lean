/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Blocks
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Adjacent Ext profiles and shift rigidity

Inside a longer exceptional block in the non-generic Enriques argument,
adjacent line bundles have derived Hom `k ⊕ k[-1]`: their shifted Hom spaces
are one-dimensional in degrees zero and one and vanish elsewhere.  Comparing
this profile through a fully faithful linear functor forces two adjacent
objects to carry the same shift.

This is the formal core of the `t = 0` calculation in the proof of
arXiv:2104.13610v2, Theorem 3.3.  The geometric computation establishing the
profile remains in the Enriques layer; the rigidity argument is pure linear
triangulated category theory.
-/

open CategoryTheory

universe w v v' u u' t t'

namespace CategoryTheory.Triangulated

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasShift C ℤ]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
  [HasShift D ℤ]

/-- The shifted-Hom profile `k ⊕ k[-1]` of two adjacent members of an
exceptional block. -/
structure AdjacentExtProfile (E F : C) : Prop where
  /-- The degree-zero Hom space is one-dimensional. -/
  zero_one : Module.finrank k (E ⟶ F⟦(0 : ℤ)⟧) = 1
  /-- The degree-one Hom space is one-dimensional. -/
  one_one : Module.finrank k (E ⟶ F⟦(1 : ℤ)⟧) = 1
  /-- All other shifted Hom spaces vanish. -/
  other_zero : ∀ i : ℤ, i ≠ 0 → i ≠ 1 →
    Module.finrank k (E ⟶ F⟦i⟧) = 0

namespace AdjacentExtProfile

variable {E F : C} {E' F' : D}
variable (A : AdjacentExtProfile (k := k) E F)
  (B : AdjacentExtProfile (k := k) E' F')

include A B in
/-- The arithmetic heart of adjacent-shift rigidity.  If the dimensions of
the source shifted Homs agree with those of the target after translating by
`t - s`, then the two shifts are equal. -/
theorem shifts_eq_of_finrank_eq (s t : ℤ)
    (hfinrank : ∀ i : ℤ,
      Module.finrank k (E ⟶ F⟦i⟧) =
        Module.finrank k (E' ⟶ F'⟦t + i - s⟧)) :
    s = t := by
  have hzero : Module.finrank k (E' ⟶ F'⟦t - s⟧) = 1 := by
    have h := (hfinrank 0).symm.trans A.zero_one
    rw [show t + 0 - s = t - s by omega] at h
    exact h
  have hone : Module.finrank k (E' ⟶ F'⟦t + 1 - s⟧) = 1 := by
    rw [← hfinrank 1]
    simpa using A.one_one
  have hfirst : t - s = 0 ∨ t - s = 1 := by
    by_contra h
    push Not at h
    have := AdjacentExtProfile.other_zero B (t - s) h.1 h.2
    omega
  have hsecond : t + 1 - s = 0 ∨ t + 1 - s = 1 := by
    by_contra h
    push Not at h
    have := AdjacentExtProfile.other_zero B (t + 1 - s) h.1 h.2
    omega
  omega

private noncomputable def homLinearEquivOfFullyFaithful
    (G : C ⥤ D) [G.Additive] [G.Linear k] (hG : G.FullyFaithful)
    (X Y : C) : (X ⟶ Y) ≃ₗ[k] (G.obj X ⟶ G.obj Y) where
  toFun := G.map
  map_add' _ _ := G.map_add
  map_smul' := by intro r f; exact G.map_smul r f
  invFun := hG.preimage
  left_inv := hG.preimage_map
  right_inv := hG.map_preimage

private noncomputable def homShiftLinearEquiv
    (G : C ⥤ D) [G.Additive] [G.Linear k] [G.CommShift ℤ]
    (hG : G.FullyFaithful) (X Y : C) (i : ℤ) :
    (X ⟶ Y⟦i⟧) ≃ₗ[k] (G.obj X ⟶ (G.obj Y)⟦i⟧) :=
  (homLinearEquivOfFullyFaithful G hG X (Y⟦i⟧)).trans
    (Linear.homCongr k (Iso.refl _) ((G.commShiftIso i).app Y))

private noncomputable def shiftedPairHomLinearEquiv
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Linear k]
    (G : C ⥤ D) [G.Additive] [G.Linear k] [G.CommShift ℤ]
    (hG : G.FullyFaithful) (s t i : ℤ)
    (eE : G.obj E ≅ E'⟦s⟧) (eF : G.obj F ≅ F'⟦t⟧) :
    (E ⟶ F⟦i⟧) ≃ₗ[k] (E' ⟶ F'⟦t + i - s⟧) := by
  let eTarget : (G.obj F)⟦i⟧ ≅ (F'⟦t⟧)⟦i⟧ :=
    (shiftFunctor D i).mapIso eF
  let ePair : (G.obj E ⟶ (G.obj F)⟦i⟧) ≃ₗ[k]
      (E'⟦s⟧ ⟶ (F'⟦t⟧)⟦i⟧) :=
    Linear.homCongr k eE eTarget
  let shiftBack := shiftFunctor D (-s)
  let eShift : (E'⟦s⟧ ⟶ (F'⟦t⟧)⟦i⟧) ≃ₗ[k]
      ((E'⟦s⟧)⟦-s⟧ ⟶ ((F'⟦t⟧)⟦i⟧)⟦-s⟧) :=
    homLinearEquivOfFullyFaithful shiftBack
      (shiftEquiv D (-s)).fullyFaithfulFunctor _ _
  let sourceIso : (E'⟦s⟧)⟦-s⟧ ≅ E' :=
    (shiftFunctorCompIsoId D s (-s) (by omega)).app E'
  let targetIso : ((F'⟦t⟧)⟦i⟧)⟦-s⟧ ≅ F'⟦t + i - s⟧ :=
    (shiftFunctor D (-s)).mapIso
        (((shiftFunctorAdd' D t i (t + i) rfl).app F').symm) ≪≫
      (((shiftFunctorAdd' D (t + i) (-s) (t + i - s)
        (by omega)).app F').symm)
  exact (homShiftLinearEquiv G hG E F i).trans <|
    ePair.trans <| eShift.trans <| Linear.homCongr k sourceIso targetIso

include A B in
/-- **Adjacent objects have one common shift.**

If a fully faithful linear shift-compatible functor maps an adjacent source
pair to an adjacent target pair with shifts `s` and `t`, then `s = t`. -/
theorem shifts_eq [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Linear k]
    (G : C ⥤ D) [G.Additive] [G.Linear k] [G.CommShift ℤ]
    (hG : G.FullyFaithful) (s t : ℤ)
    (eE : G.obj E ≅ E'⟦s⟧) (eF : G.obj F ≅ F'⟦t⟧) :
    s = t :=
  AdjacentExtProfile.shifts_eq_of_finrank_eq A B s t fun i ↦
    (shiftedPairHomLinearEquiv (E := E) (F := F) (E' := E') (F' := F')
      G hG s t i eE eF).finrank_eq

end AdjacentExtProfile

namespace OrthogonalExceptionalBlocks

variable {ι : Type t}
variable [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
variable (B : OrthogonalExceptionalBlocks k C ι)

/-- Adjacent Ext profiles for every consecutive pair in every exceptional
block. -/
structure AdjacentExtData : Prop where
  /-- Every consecutive pair has profile `k ⊕ k[-1]`. -/
  profile : ∀ (i : ι) (j : ℕ) (hj : j + 1 < B.length i),
    AdjacentExtProfile (k := k)
      ((B.collection i).obj ⟨j, by omega⟩)
      ((B.collection i).obj ⟨j + 1, hj⟩)

end OrthogonalExceptionalBlocks

/-! ## Length comparison from prefix-by-prefix extension -/

/-- A one-sided prefix-by-prefix matching of block members.  The index
equality records the output of iterating the one-step extension in order: the
`j`-th source member is matched to the `j`-th target member. -/
structure PrefixBlockEmbeddingData
    {I : Type t} {J : Type t'}
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (B_C : OrthogonalExceptionalBlocks k C I)
    (B_D : OrthogonalExceptionalBlocks k D J) (e : I ≃ J) where
  /-- The target position reached by each source extension step. -/
  targetIndex : ∀ i, Fin (B_C.length i) → Fin (B_D.length (e i))
  /-- Extension proceeds in the same order inside the two blocks. -/
  targetIndex_val : ∀ i j, (targetIndex i j).1 = j.1

namespace PrefixBlockEmbeddingData

variable {I : Type t} {J : Type t'}
variable [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
variable [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
variable {B_C : OrthogonalExceptionalBlocks k C I}
  {B_D : OrthogonalExceptionalBlocks k D J} {e : I ≃ J}
variable (A : PrefixBlockEmbeddingData B_C B_D e)

/-- The ordered member map is an embedding. -/
def embedding (i : I) : Fin (B_C.length i) ↪ Fin (B_D.length (e i)) where
  toFun := A.targetIndex i
  inj' := by
    intro j j' h
    apply Fin.ext
    rw [← A.targetIndex_val i j, ← A.targetIndex_val i j', h]

include A in
/-- A one-sided prefix extension proves the corresponding block-length
inequality. -/
theorem length_le (i : I) : B_C.length i ≤ B_D.length (e i) := by
  simpa using Fintype.card_le_of_injective (A.targetIndex i)
    (A.embedding i).injective

end PrefixBlockEmbeddingData

/-- Prefix extension in both directions forces exact equality of
corresponding block lengths. -/
structure BidirectionalPrefixBlockEmbeddingData
    {I : Type t} {J : Type t'}
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (B_C : OrthogonalExceptionalBlocks k C I)
    (B_D : OrthogonalExceptionalBlocks k D J) (e : I ≃ J) where
  /-- Forward prefix extension. -/
  forward : PrefixBlockEmbeddingData B_C B_D e
  /-- Prefix extension after reversing the equivalence. -/
  backward : PrefixBlockEmbeddingData B_D B_C e.symm

namespace BidirectionalPrefixBlockEmbeddingData

variable {I : Type t} {J : Type t'}
variable [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
variable [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
variable {B_C : OrthogonalExceptionalBlocks k C I}
  {B_D : OrthogonalExceptionalBlocks k D J} {e : I ≃ J}
variable (A : BidirectionalPrefixBlockEmbeddingData B_C B_D e)

include A in
/-- Corresponding blocks have equal length.  This is a theorem from the two
finite prefix extensions, rather than a field supplied by the caller. -/
theorem length_eq (i : I) : B_C.length i = B_D.length (e i) := by
  apply Nat.le_antisymm (A.forward.length_le i)
  simpa using A.backward.length_le (e i)

/-- The forward prefix position is the canonical cast along `length_eq`. -/
theorem targetIndex_eq_cast (i : I) (j : Fin (B_C.length i)) :
    A.forward.targetIndex i j = Fin.cast
      (BidirectionalPrefixBlockEmbeddingData.length_eq A i) j := by
  apply Fin.ext
  exact A.forward.targetIndex_val i j

end BidirectionalPrefixBlockEmbeddingData

/-! ## Common shifts along a matched block -/

/-- Memberwise image data after a finite extension has matched blocks of
equal length.  The shift is initially allowed to depend on the member; the
adjacent-Ext theorem below proves that it is constant on each block. -/
structure MemberwiseBlockShiftData
    {I : Type t} {J : Type t'}
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (B_C : OrthogonalExceptionalBlocks k C I)
    (B_D : OrthogonalExceptionalBlocks k D J) (e : I ≃ J)
    (length_eq : ∀ i, B_C.length i = B_D.length (e i))
    (G : C ⥤ D) where
  /-- The shift initially attached to each individual member. -/
  shift : ∀ i, Fin (B_C.length i) → ℤ
  /-- The image of each member is the same-position target member with its
  initially assigned shift. -/
  objectIso : ∀ i j,
    G.obj ((B_C.collection i).obj j) ≅
      ((B_D.collection (e i)).obj (Fin.cast (length_eq i) j))⟦shift i j⟧

namespace MemberwiseBlockShiftData

variable {I : Type t} {J : Type t'}
variable [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
variable [Limits.HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear k] [Pretriangulated D]
variable {B_C : OrthogonalExceptionalBlocks k C I}
  {B_D : OrthogonalExceptionalBlocks k D J} {e : I ≃ J}
  {length_eq : ∀ i, B_C.length i = B_D.length (e i)}
  {G : C ⥤ D} [G.Additive] [G.Linear k] [G.CommShift ℤ]
variable (M : MemberwiseBlockShiftData B_C B_D e length_eq G)
  (A_C : B_C.AdjacentExtData) (A_D : B_D.AdjacentExtData)

include M A_C A_D in
/-- **Every member of a matched block has the shift of its first member.** -/
theorem shift_eq_first (hG : G.FullyFaithful) (i : I) :
    ∀ j : Fin (B_C.length i), M.shift i j = M.shift i (B_C.firstIndex i)
  | ⟨0, _⟩ => rfl
  | ⟨j + 1, hj⟩ => by
      let sourcePrev : Fin (B_C.length i) := ⟨j, by omega⟩
      let sourceNext : Fin (B_C.length i) := ⟨j + 1, hj⟩
      let targetPrev : Fin (B_D.length (e i)) := ⟨j, by
        rw [← length_eq i]
        omega⟩
      let targetNext : Fin (B_D.length (e i)) := ⟨j + 1, by
        rw [← length_eq i]
        exact hj⟩
      have hprevIndex : Fin.cast (length_eq i) sourcePrev = targetPrev :=
        Fin.ext rfl
      have hnextIndex : Fin.cast (length_eq i) sourceNext = targetNext :=
        Fin.ext rfl
      have ePrev :
          G.obj ((B_C.collection i).obj sourcePrev) ≅
            ((B_D.collection (e i)).obj targetPrev)⟦M.shift i sourcePrev⟧ := by
        simpa only [hprevIndex] using M.objectIso i sourcePrev
      have eNext :
          G.obj ((B_C.collection i).obj sourceNext) ≅
            ((B_D.collection (e i)).obj targetNext)⟦M.shift i sourceNext⟧ := by
        simpa only [hnextIndex] using M.objectIso i sourceNext
      have hstep : M.shift i sourcePrev = M.shift i sourceNext :=
        (A_C.profile i j hj).shifts_eq
          (A_D.profile (e i) j (by
            rw [← length_eq i]
            exact hj)) G hG _ _ ePrev eNext
      exact hstep.symm.trans (shift_eq_first hG i ⟨j, by omega⟩)

end MemberwiseBlockShiftData

end CategoryTheory.Triangulated
