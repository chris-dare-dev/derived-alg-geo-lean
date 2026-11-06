/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.FiniteSupport
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Mapping telescopes in triangulated categories

This file supplies the first missing categorical ingredient in the Brown-style
construction behind Theorem A.13 of arXiv:2607.28411v1.  For a sequence

`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯`,

its mapping telescope is the cone of `1 - shift` on the countable coproduct of
the `Xₙ`.  The construction is deliberately triangulated rather than derived:
it only uses a countable coproduct and the axiom completing a morphism to a
distinguished triangle.

The compact-source theorems below prove the two sequential-colimit properties
needed when the Brown approximation tower is assembled: every map into the
telescope factors through a finite stage, and equality in the telescope is
witnessed at a finite later stage. They do not assert Brown representability.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.MappingTelescope

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The endomorphism of the countable coproduct induced by the transition
maps of a sequence. -/
noncomputable def shiftMap : (∐ X) ⟶ (∐ X) :=
  Sigma.desc (fun n ↦ f n ≫ Sigma.ι X (n + 1))

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc (attr := simp)]
theorem ι_shiftMap (n : ℕ) :
    Sigma.ι X n ≫ shiftMap X f = f n ≫ Sigma.ι X (n + 1) := by
  simpa only [shiftMap] using
    (Sigma.ι_comp_desc (fun n ↦ f n ≫ Sigma.ι X (n + 1)) n)

/-- The morphism whose cone defines the mapping telescope. -/
noncomputable def map : (∐ X) ⟶ (∐ X) :=
  𝟙 (∐ X) - shiftMap X f

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc]
theorem ι_map (n : ℕ) :
    Sigma.ι X n ≫ map X f =
      Sigma.ι X n - f n ≫ Sigma.ι X (n + 1) := by
  simp [map]

/-- The projection from a coproduct onto one summand, using zero maps on all
other summands. -/
noncomputable def projection (n : ℕ) : (∐ X) ⟶ X n :=
  Sigma.desc fun i => if h : i = n then eqToHom (congrArg X h) else 0

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp]
theorem ι_projection (i n : ℕ) :
    Sigma.ι X i ≫ projection X n =
      if h : i = n then eqToHom (congrArg X h) else 0 := by
  simpa only [projection] using
    (Sigma.ι_comp_desc
      (fun i => if h : i = n then eqToHom (congrArg X h) else 0) i)

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem ι_projection_self (n : ℕ) :
    Sigma.ι X n ≫ projection X n = 𝟙 (X n) := by
  simp

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem shiftMap_projection_zero :
    shiftMap X f ≫ projection X 0 = 0 := by
  apply Sigma.hom_ext
  intro i
  simp

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem shiftMap_projection_succ (n : ℕ) :
    shiftMap X f ≫ projection X (n + 1) = projection X n ≫ f n := by
  apply Sigma.hom_ext
  intro i
  rw [ι_shiftMap_assoc]
  simp only [ι_projection]
  by_cases h : i = n
  · subst i
    rw [← Category.assoc, ι_projection_self, Category.id_comp]
    simp
  · have hs : i + 1 ≠ n + 1 := by omega
    rw [dite_eq_right hs, comp_zero, ← Category.assoc, ι_projection,
      dite_eq_right h, zero_comp]

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem map_projection_zero :
    map X f ≫ projection X 0 = projection X 0 := by
  simp [map, shiftMap_projection_zero]

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem map_projection_succ (n : ℕ) :
    map X f ≫ projection X (n + 1) =
      projection X (n + 1) - projection X n ≫ f n := by
  simp [map, shiftMap_projection_succ]

variable {K : C} (hK : IsCompactObject.{0} K)

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] hK in
theorem comp_projection_eq_zero_of_comp_map_eq_zero
    (a : K ⟶ ∐ X) (ha : a ≫ map X f = 0) :
    ∀ n, a ≫ projection X n = 0 := by
  intro n
  induction n with
  | zero =>
      have h := congrArg (fun q => q ≫ projection X 0) ha
      simpa [Category.assoc, map_projection_zero] using h
  | succ n hn =>
      have h := congrArg (fun q => q ≫ projection X (n + 1)) ha
      have h' : a ≫ projection X (n + 1) -
          (a ≫ projection X n) ≫ f n = 0 := by
        simpa [Category.assoc, map_projection_succ, Preadditive.comp_sub]
          using h
      rw [hn, zero_comp, sub_zero] at h'
      exact h'

include hK

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
theorem eq_zero_of_comp_map_eq_zero (a : K ⟶ ∐ X)
    (ha : a ≫ map X f = 0) : a = 0 := by
  obtain ⟨s, g, hg⟩ := hK.exists_finite_sum X a
  have hprojection := comp_projection_eq_zero_of_comp_map_eq_zero X f a ha
  have hcomponent (i : ℕ) (hi : i ∈ s) : g i = 0 := by
    calc
      g i = (∑ j ∈ s, g j ≫ Sigma.ι X j) ≫ projection X i := by
        rw [Preadditive.sum_comp]
        simp_rw [Category.assoc, ι_projection]
        symm
        refine (Finset.sum_eq_single i ?_ ?_).trans ?_
        · intro j hj hji
          rw [dite_eq_right hji, comp_zero]
        · intro hnot
          exact (hnot hi).elim
        · simp
      _ = a ≫ projection X i := by rw [← hg]
      _ = 0 := hprojection i
  rw [hg]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hcomponent i hi, zero_comp]

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The `1 - shift` map is injective on morphisms from a compact object. -/
theorem hom_map_injective :
    Function.Injective (fun a : K ⟶ ∐ X => a ≫ map X f) := by
  intro a b hab
  rw [← sub_eq_zero]
  apply eq_zero_of_comp_map_eq_zero X f hK
  simpa only [Preadditive.sub_comp] using sub_eq_zero.mpr hab

omit hK

/-- The composite transition map between two stages of the sequence. -/
noncomputable def transition (i j : ℕ) (h : i ≤ j) : X i ⟶ X j :=
  Functor.OfSequence.map f i j h

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproduct X] in
@[simp]
theorem transition_self (i : ℕ) :
    transition X f i i (by rfl) = 𝟙 (X i) :=
  Functor.OfSequence.map_id f i

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproduct X] in
theorem transition_succ (i j : ℕ) (hij : i ≤ j) :
    transition X f i (j + 1) (hij.trans (Nat.le_succ j)) =
      transition X f i j hij ≫ f j := by
  unfold transition
  rw [Functor.OfSequence.map_comp f i j (j + 1) hij (Nat.le_succ j)]
  rw [Functor.OfSequence.map_le_succ]

/-- A mapping telescope for a sequence, presented as a chosen distinguished
cone of `1 - shift`.  Different choices are noncanonically isomorphic; the
Brown construction only uses the distinguished-triangle interface. -/
structure Data where
  /-- The telescope object. -/
  obj : C
  /-- The coproduct-to-telescope morphism. -/
  hom : (∐ X) ⟶ obj
  /-- The connecting morphism. -/
  connecting : obj ⟶ (∐ X)⟦(1 : ℤ)⟧
  /-- The defining triangle is distinguished. -/
  distinguished :
    Triangle.mk (map X f) hom connecting ∈ distTriang C

/-- Every sequence with a countable coproduct admits a mapping telescope. -/
noncomputable def chosen : Data X f := by
  apply Classical.choice
  obtain ⟨Y, g, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle (map X f)
  exact ⟨⟨Y, g, h, hT⟩⟩

namespace Data

variable {X f} (T : Data X f)

/-- Compatible maps out of a sequence factor through its mapping telescope.

This is the `Hom(-, Z)` exactness statement for the distinguished triangle
defining the telescope. -/
theorem exists_desc {Z : C} (g : ∀ n, X n ⟶ Z)
    (hcompat : ∀ n, f n ≫ g (n + 1) = g n) :
    ∃ k : T.obj ⟶ Z, Sigma.desc g = T.hom ≫ k := by
  have hzero : map X f ≫ Sigma.desc g = 0 := by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, ι_map]
    simp only [Preadditive.sub_comp, Sigma.ι_comp_desc,
      Category.assoc, comp_zero]
    rw [hcompat n, sub_self]
  exact Triangle.yoneda_exact₂
    (Triangle.mk (map X f) T.hom T.connecting)
    T.distinguished (Sigma.desc g) hzero

/-- The factorization through a telescope restricts to the original
compatible family on each coproduct summand. -/
theorem exists_desc_comp_ι {Z : C} (g : ∀ n, X n ⟶ Z)
    (hcompat : ∀ n, f n ≫ g (n + 1) = g n) :
    ∃ k : T.obj ⟶ Z, ∀ n, Sigma.ι X n ≫ T.hom ≫ k = g n := by
  obtain ⟨k, hk⟩ := T.exists_desc g hcompat
  refine ⟨k, fun n ↦ ?_⟩
  rw [← hk, Sigma.ι_comp_desc]

/-- The canonical map from a stage into the mapping telescope. -/
noncomputable def inclusion (n : ℕ) : X n ⟶ T.obj :=
  Sigma.ι X n ≫ T.hom

theorem f_comp_inclusion (n : ℕ) :
    f n ≫ T.inclusion (n + 1) = T.inclusion n := by
  have hz := comp_distTriang_mor_zero₁₂
    (Triangle.mk (map X f) T.hom T.connecting) T.distinguished
  change map X f ≫ T.hom = 0 at hz
  have hzero : (Sigma.ι X n ≫ map X f) ≫ T.hom = 0 := by
    rw [Category.assoc, hz, comp_zero]
  rw [ι_map, Preadditive.sub_comp] at hzero
  have hsub : T.inclusion n - f n ≫ T.inclusion (n + 1) = 0 := by
    simpa [inclusion, Category.assoc] using hzero
  exact (sub_eq_zero.mp hsub).symm

theorem transition_comp_inclusion (i j : ℕ) (hij : i ≤ j) :
    transition X f i j hij ≫ T.inclusion j = T.inclusion i := by
  induction j, hij using Nat.le_induction with
  | base =>
      change Functor.OfSequence.map f i i _ ≫ T.inclusion i = _
      rw [Functor.OfSequence.map_id, Category.id_comp]
  | succ j hij ih =>
      change Functor.OfSequence.map f i (j + 1) _ ≫ T.inclusion (j + 1) = _
      change Functor.OfSequence.map f i j _ ≫ T.inclusion j = _ at ih
      rw [Functor.OfSequence.map_comp f i j (j + 1) hij (Nat.le_succ j)]
      rw [Functor.OfSequence.map_le_succ]
      rw [Category.assoc, T.f_comp_inclusion, ih]

include hK

/-- A compact source has zero composite with the connecting morphism of a
mapping telescope. -/
theorem comp_connecting_eq_zero (a : K ⟶ T.obj) :
    a ≫ T.connecting = 0 := by
  let adj : shiftFunctor C (-1 : ℤ) ⊣ shiftFunctor C (1 : ℤ) :=
    (shiftEquiv C (-1 : ℤ)).toAdjunction
  let q : K⟦(-1 : ℤ)⟧ ⟶ ∐ X :=
    (adj.homAddEquiv K (∐ X)).symm (a ≫ T.connecting)
  have hq : q ≫ map X f = 0 := by
    apply (adj.homAddEquiv K (∐ X)).injective
    change (adj.homEquiv K (∐ X)) (q ≫ map X f) = _
    rw [adj.homEquiv_naturality_right]
    simp only [q, Adjunction.homAddEquiv_symm_apply,
      Equiv.apply_symm_apply, map_zero]
    have hz := comp_distTriang_mor_zero₃₁
      (Triangle.mk (map X f) T.hom T.connecting) T.distinguished
    change T.connecting ≫ (map X f)⟦(1 : ℤ)⟧' = 0 at hz
    calc
      (a ≫ T.connecting) ≫ (map X f)⟦(1 : ℤ)⟧' =
          a ≫ (T.connecting ≫ (map X f)⟦(1 : ℤ)⟧') := Category.assoc _ _ _
      _ = a ≫ 0 := by rw [hz]
      _ = 0 := comp_zero
  have hqzero := eq_zero_of_comp_map_eq_zero X f
    (hK.shift (-1 : ℤ)) q hq
  apply (adj.homAddEquiv K (∐ X)).symm.injective
  simpa [q] using hqzero

/-- A map from a compact object into a telescope lifts to the defining
coproduct. -/
theorem exists_lift_coproduct (a : K ⟶ T.obj) :
    ∃ b : K ⟶ ∐ X, a = b ≫ T.hom := by
  exact Triangle.coyoneda_exact₃
    (Triangle.mk (map X f) T.hom T.connecting)
    T.distinguished a (T.comp_connecting_eq_zero hK a)

/-- Every map from a compact object into the telescope factors through one
finite stage of the sequence. -/
theorem exists_factor_stage (a : K ⟶ T.obj) :
    ∃ (n : ℕ) (b : K ⟶ X n), a = b ≫ T.inclusion n := by
  obtain ⟨b, hb⟩ := T.exists_lift_coproduct hK a
  obtain ⟨s, g, hg⟩ := hK.exists_finite_sum X b
  let N : ℕ := s.sup id
  let c : K ⟶ X N := ∑ i ∈ s.attach,
    g i.1 ≫ transition X f i.1 N (Finset.le_sup (f := id) i.2)
  refine ⟨N, c, ?_⟩
  rw [hb, hg, Preadditive.sum_comp]
  simp only [Category.assoc]
  change (∑ i ∈ s, g i ≫ T.inclusion i) = c ≫ T.inclusion N
  rw [← Finset.sum_attach]
  simp only [c, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Category.assoc, T.transition_comp_inclusion]

/-- If a map from a compact object becomes zero in the telescope, then it is
already killed by a finite transition map. -/
theorem exists_transition_comp_eq_zero (n : ℕ) (b : K ⟶ X n)
    (hb : b ≫ T.inclusion n = 0) :
    ∃ (m : ℕ) (hnm : n ≤ m), b ≫ transition X f n m hnm = 0 := by
  have hzero : (b ≫ Sigma.ι X n) ≫ T.hom = 0 := by
    simpa [inclusion, Category.assoc] using hb
  obtain ⟨q₀, hq₀⟩ := Triangle.coyoneda_exact₂
    (Triangle.mk (map X f) T.hom T.connecting)
    T.distinguished (b ≫ Sigma.ι X n) hzero
  let q : K ⟶ ∐ X := q₀
  have hq : b ≫ Sigma.ι X n = q ≫ map X f := hq₀
  have hcoeff : ∀ j : ℕ, q ≫ projection X j =
      if h : n ≤ j then b ≫ transition X f n j h else 0 := by
    intro j
    induction j with
    | zero =>
        have h := congrArg (fun k => k ≫ projection X 0) hq
        by_cases hn : n = 0
        · subst n
          have h0 : q ≫ projection X 0 = b := by
            simpa [Category.assoc, map_projection_zero] using h.symm
          rw [dite_eq_left le_rfl, h0, transition_self, Category.comp_id]
        · have hnle : ¬ n ≤ 0 := by omega
          simpa [Category.assoc, map_projection_zero, hn, hnle] using h.symm
    | succ j ih =>
        have h := congrArg (fun k => k ≫ projection X (j + 1)) hq
        by_cases hnj : n ≤ j
        · have hne : n ≠ j + 1 := by omega
          have hrel : 0 = q ≫ projection X (j + 1) -
              (q ≫ projection X j) ≫ f j := by
            simpa [Category.assoc, map_projection_succ,
              Preadditive.comp_sub, hne] using h
          have hnext : q ≫ projection X (j + 1) =
              (q ≫ projection X j) ≫ f j :=
            sub_eq_zero.mp hrel.symm
          rw [dite_eq_left (hnj.trans (Nat.le_succ j)), hnext, ih,
            dite_eq_left hnj, transition_succ, Category.assoc]
        · by_cases heq : n = j + 1
          · subst n
            have hrel : b = q ≫ projection X (j + 1) -
                (q ≫ projection X j) ≫ f j := by
              simpa [Category.assoc, map_projection_succ,
                Preadditive.comp_sub] using h
            have hprev : q ≫ projection X j = 0 := by
              simpa [hnj] using ih
            have hnext : q ≫ projection X (j + 1) = b := by
              rw [hprev, zero_comp, sub_zero] at hrel
              exact hrel.symm
            rw [dite_eq_left (by omega), hnext, transition_self, Category.comp_id]
          · have hnle : ¬ n ≤ j + 1 := by omega
            have hrel : 0 = q ≫ projection X (j + 1) -
                (q ≫ projection X j) ≫ f j := by
              simpa [Category.assoc, map_projection_succ,
                Preadditive.comp_sub, heq] using h
            have hprev : q ≫ projection X j = 0 := by
              simpa [hnj] using ih
            have hnext : q ≫ projection X (j + 1) = 0 := by
              rw [hprev, zero_comp, sub_zero] at hrel
              exact hrel.symm
            rw [dite_eq_right hnle, hnext]
  obtain ⟨s, g, hqsum⟩ := hK.exists_finite_sum X q
  let m : ℕ := max n (s.sup id) + 1
  have hnm : n ≤ m := by omega
  have hmnot : m ∉ s := by
    intro hm
    have hmle := Finset.le_sup (f := id) hm
    dsimp [m] at hmle
    omega
  have hqproj : q ≫ projection X m = 0 := by
    rw [hqsum, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Category.assoc, ι_projection]
    have hne : i ≠ m := by
      intro him
      exact hmnot (him ▸ hi)
    rw [dite_eq_right hne, comp_zero]
  refine ⟨m, hnm, ?_⟩
  have hm := hcoeff m
  rw [dite_eq_left hnm, hqproj] at hm
  exact hm.symm

/-- Equality after mapping into the telescope is witnessed at a finite later
stage. -/
theorem exists_transition_comp_eq (n : ℕ) (a b : K ⟶ X n)
    (hab : a ≫ T.inclusion n = b ≫ T.inclusion n) :
    ∃ (m : ℕ) (hnm : n ≤ m),
      a ≫ transition X f n m hnm = b ≫ transition X f n m hnm := by
  have hzero : (a - b) ≫ T.inclusion n = 0 := by
    rw [Preadditive.sub_comp, hab, sub_self]
  obtain ⟨m, hnm, hm⟩ :=
    T.exists_transition_comp_eq_zero hK n (a - b) hzero
  refine ⟨m, hnm, ?_⟩
  rw [Preadditive.sub_comp] at hm
  exact sub_eq_zero.mp hm

end Data

end CategoryTheory.Triangulated.MappingTelescope
