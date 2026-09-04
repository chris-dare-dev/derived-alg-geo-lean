/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveAcyclic
import DerivedAlgGeo.Topology.Sheaves.Cech.GlobalComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveFlasque
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.Sheaves.Flasque

/-!
# Cohomology from Cech exactness on a compact basis

This file formalizes the non-circular basis argument of Stacks Project, Tag 01EW.  A compact
collection is required to admit finite subordinate refinements and to be stable under nonempty
finite intersections. If a sheaf has exact positive Cech complexes on every finite cover inside
the collection, then its positive local cohomology vanishes on every member. The whole-space
case recovers positive derived global-cohomology vanishing.

The proof is by dimension shifting.  After embedding the sheaf into an injective sheaf, local
surjectivity and compactness produce a finite basis cover on which a section of the quotient
lifts.  Degree-one Cech exactness corrects those local lifts so that they glue.  Consequently the
quotient inherits the same basis-Cech exactness, and the Ext long exact sequence completes the
induction.  In particular, no cover is assumed to be derived-acyclic in advance.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TopCat

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A compact collection of opens suited to the Cech-to-derived comparison.  The
`finite_refinement` field says directly that every cover of a member admits a finite subordinate
refinement by members.  This formulation includes both a global compact-open basis and the
distinguished-open basis lying below one fixed affine open.  Stability under nonempty finite
intersections keeps every term of a Cech nerve inside the collection. -/
structure CompactOpenBasis (X : TopCat.{u}) where
  carrier : Set (Opens X)
  isCompact : ∀ U, U ∈ carrier → IsCompact (U : Set X)
  finite_refinement : ∀ {V : Opens X}, V ∈ carrier →
    ∀ {I : Type u} (U : I → Opens X), V ≤ ⨆ i, U i →
      ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X) (a : J → I),
        (∀ j, W j ∈ carrier) ∧ (∀ j, W j ≤ U (a j)) ∧ V = ⨆ j, W j
  inf_mem : ∀ U V, U ∈ carrier → V ∈ carrier → U ⊓ V ∈ carrier

namespace CompactOpenBasis

variable {X : TopCat.{u}} (B : CompactOpenBasis X)

/-- Construct a `CompactOpenBasis` from an ordinary topological basis of compact opens which is
stable under nonempty finite intersections. -/
noncomputable def ofIsBasis (carrier : Set (Opens X)) (isBasis : Opens.IsBasis carrier)
    (isCompact : ∀ U, U ∈ carrier → IsCompact (U : Set X))
    (inf_mem : ∀ U V, U ∈ carrier → V ∈ carrier → U ⊓ V ∈ carrier) :
    CompactOpenBasis X where
  carrier := carrier
  isCompact := isCompact
  finite_refinement := by
    intro V hV I U hVU
    let A : Set (Opens X) :=
      { W | W ∈ carrier ∧ W ≤ V ∧ ∃ i, W ≤ U i }
    have hcover : V ≤ sSup A := by
      intro x hxV
      have hxU : x ∈ ⨆ i, U i := hVU hxV
      rw [Opens.mem_iSup] at hxU
      obtain ⟨i, hxi⟩ := hxU
      have hxiV : x ∈ U i ⊓ V := ⟨hxi, hxV⟩
      obtain ⟨Us, hUsB, hEq⟩ := Opens.isBasis_iff_cover.mp isBasis (U i ⊓ V)
      have hxs : x ∈ sSup Us := hEq ▸ hxiV
      rw [Opens.mem_sSup] at hxs
      obtain ⟨W, hWUs, hxW⟩ := hxs
      have hWU : W ≤ U i ⊓ V := (le_sSup hWUs).trans hEq.symm.le
      have hWA : W ∈ A := ⟨hUsB hWUs, hWU.trans inf_le_right, i,
        hWU.trans inf_le_left⟩
      exact (le_sSup hWA) hxW
    obtain ⟨s, hs⟩ := (isCompact V hV).elim_finite_subcover
      (fun W : A ↦ (W.1 : Set X)) (fun W ↦ W.1.2) (by
        intro x hxV
        have hx : x ∈ sSup A := hcover hxV
        rw [Opens.mem_sSup] at hx
        obtain ⟨W, hWA, hxW⟩ := hx
        exact Set.mem_iUnion.2 ⟨⟨W, hWA⟩, hxW⟩)
    let J := s
    let W : J → Opens X := fun j ↦ j.1.1
    let a : J → I := fun j ↦ Classical.choose j.1.2.2.2
    refine ⟨J, inferInstance, W, a, fun j ↦ j.1.2.1,
      fun j ↦ Classical.choose_spec j.1.2.2.2, ?_⟩
    apply le_antisymm
    · intro x hxV
      have hx : x ∈ ⋃ j ∈ s, (j.1 : Set X) := hs hxV
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hj, hxj⟩ := hx
      rw [Opens.mem_iSup]
      exact ⟨⟨j, hj⟩, hxj⟩
    · rw [iSup_le_iff]
      intro j
      exact j.1.2.2.1
  inf_mem := inf_mem

/-- Every compact basis open has a finite cover by basis opens subordinate to a given open
cover. -/
lemma exists_finite_refinement {V : Opens X} (hV : V ∈ B.carrier)
    {I : Type u} (U : I → Opens X) (hVU : V ≤ ⨆ i, U i) :
    ∃ (J : Type u) (_ : Fintype J) (W : J → Opens X) (a : J → I),
      (∀ j, W j ∈ B.carrier) ∧ (∀ j, W j ≤ U (a j)) ∧ V = ⨆ j, W j :=
  B.finite_refinement hV U hVU

/-- A nonempty finite product of members of a compact basis is again a member. -/
lemma fin_pi_mem {n : ℕ} (U : Fin (n + 1) → Opens X)
    (hU : ∀ i, U i ∈ B.carrier) : (∏ᶜ U) ∈ B.carrier := by
  classical
  have hpi : (∏ᶜ U) = Finset.univ.inf U := by
    apply le_antisymm
    · exact Finset.le_inf fun i _ ↦ leOfHom (Pi.π U i)
    · apply leOfHom
      apply Pi.lift
      intro i
      exact homOfLE (Finset.inf_le (Finset.mem_univ i))
  have hfin : ∀ (s : Finset (Fin (n + 1))), s.Nonempty → s.inf U ∈ B.carrier := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => exact (Finset.not_nonempty_empty hs).elim
    | @insert a s ha ih =>
        by_cases hs' : s.Nonempty
        · rw [Finset.inf_insert]
          exact B.inf_mem _ _ (hU a) (ih hs')
        · rw [Finset.not_nonempty_iff_eq_empty.mp hs']
          simpa using hU a
  exact hpi.symm ▸ hfin Finset.univ Finset.univ_nonempty

end CompactOpenBasis

/-- Positive Cech exactness on all finite covers by members of a compact basis. -/
def IsCechAcyclicOnCompactBasis {X : TopCat.{u}} (B : CompactOpenBasis X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {I : Type u} [Fintype I] (V : Opens X), V ∈ B.carrier →
    (U : I → Opens X) → (∀ i, U i ∈ B.carrier) → V = ⨆ i, U i →
    ∀ (n : ℕ), 0 < n → ((cechComplexFunctor U).obj F.obj).ExactAt n

/-- Injective sheaves are Cech-acyclic on every compact basis. -/
lemma isCechAcyclicOnCompactBasis_of_injective
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] :
    IsCechAcyclicOnCompactBasis B F := by
  intro I _ V hV U hU hcover n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  exact cechComplex_exactAt_succ_of_injective' U F m

private lemma evalOp_map_π
    {X : TopCat.{u}} (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W : Limits.FormalCoproduct (Opens X)} (m : V ⟶ W) (q : V.I) :
    ((Limits.FormalCoproduct.evalOp (Opens X) AddCommGrpCat.{u}).obj F).map m.op ≫
        Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q =
      Limits.Pi.π (fun q ↦ F.obj (op (W.obj q))) (m.f q) ≫
        F.map (m.φ q).op := by
  rw [Limits.FormalCoproduct.evalOp_obj_map]
  change Limits.Pi.lift (fun i ↦
      Limits.Pi.π (fun j ↦ F.obj (op (W.obj j))) (m.f i) ≫
        F.map (m.φ i).op) ≫
      Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q = _
  rw [Limits.Pi.lift_π]

/-- Restriction of a section on `V` to the degree-zero Cech term of a family lying in `V`. -/
private noncomputable def sectionsToCechZero
    {X : TopCat.{u}} {I : Type u} {V : Opens X}
    (U : I → Opens X) (hUV : ∀ i, U i ≤ V)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    G.obj.obj (op V) ⟶ ((cechComplexFunctor U).obj G.obj).X 0 := by
  let W := Limits.FormalCoproduct.mk I U
  change G.obj.obj (op V) ⟶
    ∏ᶜ fun q : (W.cech.obj (op (SimplexCategory.mk 0))).I ↦
      G.obj.obj (op ((W.cech.obj (op (SimplexCategory.mk 0))).obj q))
  exact Limits.Pi.lift fun q ↦ G.obj.map (homOfLE
    ((leOfHom (Limits.Pi.π (U ∘ q) 0)).trans (hUV (q 0)))).op

private lemma sectionsToCechZero_comp_d
    {X : TopCat.{u}} {I : Type u} {V : Opens X}
    (U : I → Opens X) (hUV : ∀ i, U i ≤ V)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    sectionsToCechZero U hUV G ≫ ((cechComplexFunctor U).obj G.obj).d 0 1 = 0 := by
  let W := Limits.FormalCoproduct.mk I U
  let Z := (Limits.FormalCoproduct.cosimplicialObjectFunctor W.cech).obj G.obj
  let T₀ : (W.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((W.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let T₁ : (W.cech.obj (op (SimplexCategory.mk 1))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((W.cech.obj (op (SimplexCategory.mk 1))).obj r))
  change sectionsToCechZero U hUV G ≫
    ((cechComplexFunctor U).obj G.obj).d 0 1 =
      (0 : G.obj.obj (op V) ⟶ ∏ᶜ T₁)
  apply Limits.Pi.hom_ext
  intro q
  rw [zero_comp]
  have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Z.δ i := by
    change AlgebraicTopology.AlternatingCofaceMapComplex.objD Z 0 = _
    rfl
  let m₀ := W.cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let m₁ := W.cech.map (SimplexCategory.δ (1 : Fin 2)).op
  have hZ₀ : Z.δ (0 : Fin 2) ≫ Limits.Pi.π T₁ q =
      Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op :=
    evalOp_map_π G.obj m₀ q
  have hZ₁ : Z.δ (1 : Fin 2) ≫ Limits.Pi.π T₁ q =
      Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op :=
    evalOp_map_π G.obj m₁ q
  have hsections (r : (W.cech.obj (op (SimplexCategory.mk 0))).I) :
      sectionsToCechZero U hUV G ≫ Limits.Pi.π T₀ r =
        G.obj.map (homOfLE
          ((leOfHom (Limits.Pi.π (U ∘ r) 0)).trans (hUV (r 0)))).op := by
    dsimp [sectionsToCechZero, T₀]
    rw [Limits.Pi.lift_π]
  rw [hd, Fin.sum_univ_two]
  rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
    show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
  simp only [one_smul, neg_smul, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]
  erw [hZ₀, hZ₁]
  simp only [← Category.assoc]
  rw [hsections (m₀.f q), hsections (m₁.f q)]
  simp only [← G.obj.map_comp]
  rw [show G.obj.map ((homOfLE _).op ≫ (m₀.φ q).op) =
      G.obj.map ((homOfLE _).op ≫ (m₁.φ q).op) by
    congr 1]
  exact add_neg_cancel _

/-- The family of sections on the chosen opens represented by a degree-zero Cech cochain. -/
private noncomputable def cechZeroFamily
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : ((cechComplexFunctor U).obj G.obj).X 0) :
    ∀ i, G.obj.obj (op (U i)) := by
  let V := Limits.FormalCoproduct.mk I U
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let xV := Limits.Concrete.productEquiv T₀ x
  let r (i : I) : Fin 1 → I := fun _ ↦ i
  let e (i : I) : (∏ᶜ (U ∘ r i)) ≅ U i :=
    Limits.productUniqueIso (U ∘ r i)
  exact fun i ↦ G.obj.map (e i).inv.op (xV (r i))

/-- The degree-zero Cech cochain attached to a family of sections on the chosen opens. -/
private noncomputable def cechZeroOfFamily
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (sf : ∀ i, G.obj.obj (op (U i))) :
    ((cechComplexFunctor U).obj G.obj).X 0 := by
  let V := Limits.FormalCoproduct.mk I U
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  exact (Limits.Concrete.productEquiv T₀).symm fun q : Fin 1 → I ↦
    G.obj.map (Limits.productUniqueIso (U ∘ q)).hom.op (sf (q 0))

private lemma cechZeroFamily_cechZeroOfFamily
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (sf : ∀ i, G.obj.obj (op (U i))) (i : I) :
    cechZeroFamily U G (cechZeroOfFamily U G sf) i = sf i := by
  let r : Fin 1 → I := fun _ ↦ i
  have hr : r 0 = i := rfl
  dsimp [cechZeroFamily, cechZeroOfFamily]
  rw [Equiv.apply_symm_apply]
  erw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp]
  simp

private lemma cechZeroOfFamily_cechZeroFamily
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : ((cechComplexFunctor U).obj G.obj).X 0) :
    cechZeroOfFamily U G (cechZeroFamily U G x) = x := by
  let Q := Fin 1 → I
  let T₀ : Q → AddCommGrpCat.{u} := fun q ↦ G.obj.obj (op (∏ᶜ (U ∘ q)))
  apply (Limits.Concrete.productEquiv T₀).injective
  funext q
  have hq : q = fun _ ↦ q 0 := by
    funext k
    fin_cases k
    rfl
  rw [hq]
  simp only [Limits.Concrete.productEquiv_apply_apply]
  dsimp [cechZeroOfFamily, cechZeroFamily]
  rw [Limits.Concrete.productEquiv_symm_apply_π]
  erw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp]
  rw [show Limits.Pi.π (U ∘ fun _ : Fin 1 ↦ q 0) 0 ≫
      (Limits.productUniqueIso (U ∘ fun _ : Fin 1 ↦ q 0)).inv = 𝟙 _ by
    subsingleton]
  simp
  rfl

private lemma cechZeroOfFamily_map
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (sf : ∀ i, F.obj.obj (op (U i))) :
    ((cechComplexFunctor U).map f.hom).f 0 (cechZeroOfFamily U F sf) =
      cechZeroOfFamily U G (fun i ↦ f.hom.app (op (U i)) (sf i)) := by
  let Q := Fin 1 → I
  let TF : Q → AddCommGrpCat.{u} := fun q ↦ F.obj.obj (op (∏ᶜ (U ∘ q)))
  let TG : Q → AddCommGrpCat.{u} := fun q ↦ G.obj.obj (op (∏ᶜ (U ∘ q)))
  apply (Limits.Concrete.productEquiv TG).injective
  funext q
  simp only [Limits.Concrete.productEquiv_apply_apply]
  dsimp [cechZeroOfFamily, cechComplexFunctor,
    Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor]
  have hπ := CategoryTheory.congr_fun
    (Limits.Pi.map_π (fun q ↦ f.hom.app (op (∏ᶜ (U ∘ q)))) q)
      ((Limits.Concrete.productEquiv TF).symm fun q : Q ↦
        F.obj.map (Limits.productUniqueIso (U ∘ q)).hom.op (sf (q 0)))
  simp only [CategoryTheory.comp_apply] at hπ
  exact hπ.trans (by
    rw [Limits.Concrete.productEquiv_symm_apply_π,
      Limits.Concrete.productEquiv_symm_apply_π]
    exact CategoryTheory.congr_fun
      (f.hom.naturality (Limits.productUniqueIso (U ∘ q)).hom.op) (sf (q 0)))

private lemma cechZeroFamily_map
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : ((cechComplexFunctor U).obj F.obj).X 0) (i : I) :
    cechZeroFamily U G (((cechComplexFunctor U).map f.hom).f 0 x) i =
      f.hom.app (op (U i)) (cechZeroFamily U F x i) := by
  have hx := cechZeroOfFamily_cechZeroFamily U F x
  calc
    _ = cechZeroFamily U G (((cechComplexFunctor U).map f.hom).f 0
        (cechZeroOfFamily U F (cechZeroFamily U F x))) i := by rw [hx]
    _ = _ := by rw [cechZeroOfFamily_map, cechZeroFamily_cechZeroOfFamily]

private lemma cechZeroOfRestrictions_eq_sectionsToCechZero
    {X : TopCat.{u}} {I : Type u} {V : Opens X}
    (U : I → Opens X) (hUV : ∀ i, U i ≤ V)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) (s : G.obj.obj (op V)) :
    cechZeroOfFamily U G
        (fun i ↦ G.obj.map (homOfLE (hUV i)).op s) =
      sectionsToCechZero U hUV G s := by
  let Q := Fin 1 → I
  let T₀ : Q → AddCommGrpCat.{u} := fun q ↦ G.obj.obj (op (∏ᶜ (U ∘ q)))
  apply (Limits.Concrete.productEquiv T₀).injective
  funext q
  simp only [Limits.Concrete.productEquiv_apply_apply]
  dsimp [cechZeroOfFamily, sectionsToCechZero]
  rw [Limits.Concrete.productEquiv_symm_apply_π]
  have hπ := CategoryTheory.congr_fun
    (Limits.Pi.lift_π (fun q : Q ↦ G.obj.map (homOfLE
      ((leOfHom (Limits.Pi.π (U ∘ q) 0)).trans (hUV (q 0)))).op) q) s
  simp only [CategoryTheory.comp_apply] at hπ
  calc
    _ = G.obj.map (homOfLE
        ((leOfHom (Limits.Pi.π (U ∘ q) 0)).trans (hUV (q 0)))).op s := by
      erw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp]
      congr 1
    _ = _ := hπ.symm

private lemma cechZeroFamily_sectionsToCechZero
    {X : TopCat.{u}} {I : Type u} {V : Opens X}
    (U : I → Opens X) (hUV : ∀ i, U i ≤ V)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) (s : G.obj.obj (op V)) (i : I) :
    cechZeroFamily U G (sectionsToCechZero U hUV G s) i =
      G.obj.map (homOfLE (hUV i)).op s := by
  rw [← cechZeroOfRestrictions_eq_sectionsToCechZero U hUV G s,
    cechZeroFamily_cechZeroOfFamily]

/-- The sections represented by a degree-zero Cech cocycle form a compatible family on the
chosen opens. -/
private lemma cechZeroFamily_isCompatible
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : ((cechComplexFunctor U).obj G.obj).X 0)
    (hx : ((cechComplexFunctor U).obj G.obj).d 0 1 x = 0) :
    TopCat.Presheaf.IsCompatible G.obj U (cechZeroFamily U G x) := by
  let V := Limits.FormalCoproduct.mk I U
  let Zc := (Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj G.obj
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let T₁ : (V.cech.obj (op (SimplexCategory.mk 1))).I → AddCommGrpCat.{u} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 1))).obj r))
  let m₀ := V.cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let m₁ := V.cech.map (SimplexCategory.δ (1 : Fin 2)).op
  let xV := Limits.Concrete.productEquiv T₀ x
  have hcocycle (q : (V.cech.obj (op (SimplexCategory.mk 1))).I) :
      (ConcreteCategory.hom (G.obj.map (m₀.φ q).op)) (xV (m₀.f q)) =
        (ConcreteCategory.hom (G.obj.map (m₁.φ q).op)) (xV (m₁.f q)) := by
    have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
        ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Zc.δ i := by
      change AlgebraicTopology.AlternatingCofaceMapComplex.objD Zc 0 = _
      rfl
    have hZ₀ : Zc.δ (0 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op :=
      evalOp_map_π G.obj m₀ q
    have hZ₁ : Zc.δ (1 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op :=
      evalOp_map_π G.obj m₁ q
    have hmor : ((cechComplexFunctor U).obj G.obj).d 0 1 ≫ Limits.Pi.π T₁ q =
        (Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op) -
          (Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op) := by
      rw [hd, Fin.sum_univ_two]
      rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
        show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
      simp only [one_smul, neg_smul, Preadditive.add_comp, Preadditive.neg_comp]
      rw [hZ₀, hZ₁, sub_eq_add_neg]
    have hxq := congrArg
      (fun y ↦ (ConcreteCategory.hom (Limits.Pi.π T₁ q)) y) hx
    rw [map_zero] at hxq
    erw [← ConcreteCategory.comp_apply] at hxq
    erw [hmor] at hxq
    rw [show xV (m₀.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₀.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₀.f q),
      show xV (m₁.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₁.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₁.f q)]
    exact sub_eq_zero.mp hxq
  let r (i : I) : Fin 1 → I := fun _ ↦ i
  let e (i : I) : (∏ᶜ (U ∘ r i)) ≅ U i :=
    Limits.productUniqueIso (U ∘ r i)
  let sf : ∀ i, G.obj.obj (op (U i)) := cechZeroFamily U G x
  change TopCat.Presheaf.IsCompatible G.obj U sf
  intro i j
  let q : Fin 2 → I := fun k ↦ Fin.cases i (fun _ ↦ j) k
  have hδ₀ (k : Fin 1) :
      (SimplexCategory.δ (0 : Fin 2)).toOrderHom k = (1 : Fin 2) := by
    fin_cases k
    rfl
  have hδ₁ (k : Fin 1) :
      (SimplexCategory.δ (1 : Fin 2)).toOrderHom k = (0 : Fin 2) := by
    fin_cases k
    rfl
  have hqδ₀ : q ∘ (⇑(SimplexCategory.δ (0 : Fin 2)).toOrderHom : Fin 1 → Fin 2) =
      r j := by
    funext k
    fin_cases k
    rfl
  have hqδ₁ : q ∘ (⇑(SimplexCategory.δ (1 : Fin 2)).toOrderHom : Fin 1 → Fin 2) =
      r i := by
    funext k
    fin_cases k
    rfl
  have faceComparison (a : I) (p : (∏ᶜ (U ∘ q)) ⟶ U a)
      (qa : Fin 1 → I) (hqa : qa = r a)
      (phi : (∏ᶜ (U ∘ q)) ⟶ ∏ᶜ (U ∘ qa))
      (hphi : ∀ k, HEq (phi ≫ Limits.Pi.π (U ∘ qa) k) p) :
      (G.obj.map (p ≫ (e a).inv).op).hom (xV (r a)) =
        (G.obj.map phi.op).hom (xV qa) := by
    subst qa
    have hphi' : phi = p ≫ (e a).inv := by
      apply Limits.Pi.hom_ext
      intro k
      rw [eq_of_heq (hphi k), Category.assoc]
      dsimp [e]
      rw [Limits.productUniqueIso_inv_π]
      simp [r]
    rw [hphi']
  have projectionHEq {a b : Fin 2} (hab : a = b) :
      HEq (Limits.Pi.π (U ∘ q) a) (Limits.Pi.π (U ∘ q) b) := by
    subst b
    rfl
  have hleft := faceComparison i
    (Limits.Pi.π (U ∘ q) 0)
    (q ∘ (⇑(SimplexCategory.δ (1 : Fin 2)).toOrderHom : Fin 1 → Fin 2)) hqδ₁
    (Limits.Pi.lift (fun k : Fin 1 ↦
      Limits.Pi.π (U ∘ q) ((SimplexCategory.δ (1 : Fin 2)).toOrderHom k)))
    (by
      intro k
      exact (heq_of_eq (Limits.Pi.lift_π (fun k : Fin 1 ↦
        Limits.Pi.π (U ∘ q)
          ((SimplexCategory.δ (1 : Fin 2)).toOrderHom k)) k)).trans
        (projectionHEq (hδ₁ k)))
  have hright := faceComparison j
    (Limits.Pi.π (U ∘ q) 1)
    (q ∘ (⇑(SimplexCategory.δ (0 : Fin 2)).toOrderHom : Fin 1 → Fin 2)) hqδ₀
    (Limits.Pi.lift (fun k : Fin 1 ↦
      Limits.Pi.π (U ∘ q) ((SimplexCategory.δ (0 : Fin 2)).toOrderHom k)))
    (by
      intro k
      exact (heq_of_eq (Limits.Pi.lift_π (fun k : Fin 1 ↦
        Limits.Pi.π (U ∘ q)
          ((SimplexCategory.δ (0 : Fin 2)).toOrderHom k)) k)).trans
        (projectionHEq (hδ₀ k)))
  have hc := (hcocycle q).symm
  dsimp [m₀, m₁, V] at hc
  have hpair :
      G.obj.map (Limits.Pi.π (U ∘ q) 0).op (sf i) =
        G.obj.map (Limits.Pi.π (U ∘ q) 1).op (sf j) := by
    dsimp [sf, cechZeroFamily]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp]
    exact hleft.trans (hc.trans hright.symm)
  let l : U i ⊓ U j ⟶ ∏ᶜ (U ∘ q) :=
    Limits.Pi.lift fun k ↦ Fin.cases (Opens.infLELeft (U i) (U j))
      (fun _ ↦ Opens.infLERight (U i) (U j)) k
  have hpull := congrArg (fun y ↦ G.obj.map l.op y) hpair
  have hpull' :
      G.obj.map ((Limits.Pi.π (U ∘ q) 0).op ≫ l.op) (sf i) =
        G.obj.map ((Limits.Pi.π (U ∘ q) 1).op ≫ l.op) (sf j) := by
    simpa only [G.obj.map_comp, ConcreteCategory.comp_apply] using hpull
  have hl₀ : l ≫ Limits.Pi.π (U ∘ q) 0 = Opens.infLELeft (U i) (U j) := by
    dsimp [l]
    rw [Limits.Pi.lift_π]
    rfl
  have hl₁ : l ≫ Limits.Pi.π (U ∘ q) 1 = Opens.infLERight (U i) (U j) := by
    dsimp [l]
    rw [Limits.Pi.lift_π]
    rfl
  rw [← op_comp, ← op_comp, hl₀, hl₁] at hpull'
  exact hpull'

/-- Applying a short complex of sheaves to one Cech cochain degree. -/
private noncomputable def cechTermShortComplex
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) (n : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (((cechComplexFunctor U).map S.f.hom).f n)
    (((cechComplexFunctor U).map S.g.hom).f n) (by
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
      change ((cechComplexFunctor U).map (S.f ≫ S.g).hom).f n = 0
      rw [S.zero]
      simp)

/-- Cech cochain terms preserve exactness of a short complex of abelian sheaves.  Products of
surjections are handled elementwise, so this works for arbitrary (not necessarily finite) Cech
index types. -/
private lemma cechTermShortComplex_exact
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.Exact) [Mono S.f] (n : ℕ) :
    (cechTermShortComplex U S n).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  let Q := Fin (n + 1) → I
  let T₁ : Q → AddCommGrpCat.{u} := fun q ↦
    S.X₁.obj.obj (op (∏ᶜ (U ∘ q)))
  let T₂ : Q → AddCommGrpCat.{u} := fun q ↦
    S.X₂.obj.obj (op (∏ᶜ (U ∘ q)))
  let T₃ : Q → AddCommGrpCat.{u} := fun q ↦
    S.X₃.obj.obj (op (∏ᶜ (U ∘ q)))
  have hyq (q : Q) :
      S.g.hom.app (op (∏ᶜ (U ∘ q)))
        ((Limits.Concrete.productEquiv T₂) y q) = 0 := by
    have h := congrArg
      (fun z ↦ (Limits.Concrete.productEquiv T₃) z q) hy
    simp only [Limits.Concrete.productEquiv_apply_apply, map_zero] at h
    dsimp [cechTermShortComplex, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor, T₂, T₃] at h
    have hπ := CategoryTheory.congr_fun
      (Limits.Pi.map_π (fun q ↦ S.g.hom.app (op (∏ᶜ (U ∘ q)))) q) y
    simp only [CategoryTheory.comp_apply] at hπ
    rw [Limits.Concrete.productEquiv_apply_apply]
    exact hπ.symm.trans h
  choose z hz using fun q ↦
    TopCat.Sheaf.sections_exact_of_left_exact hS (inferInstance : Mono S.f)
      ((Limits.Concrete.productEquiv T₂) y q) (hyq q)
  refine ⟨(Limits.Concrete.productEquiv T₁).symm z, ?_⟩
  apply (Limits.Concrete.productEquiv T₂).injective
  funext q
  simp only [Limits.Concrete.productEquiv_apply_apply]
  dsimp [cechTermShortComplex, cechComplexFunctor,
    Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor, T₁, T₂]
  have hπ := CategoryTheory.congr_fun
    (Limits.Pi.map_π (fun q ↦ S.f.hom.app (op (∏ᶜ (U ∘ q)))) q)
      ((Limits.Concrete.productEquiv T₁).symm z)
  simp only [CategoryTheory.comp_apply] at hπ
  exact hπ.trans (by
    rw [Limits.Concrete.productEquiv_symm_apply_π]
    simpa only [Limits.Concrete.productEquiv_apply_apply] using hz q)

private lemma exists_finite_basis_lift_cover
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) {V : Opens X} (hV : V ∈ B.carrier)
    (s : S.X₃.obj.obj (op V)) :
    ∃ (I : Type u) (_ : Fintype I) (U : I → Opens X),
      ∃ hUV : ∀ i, U i ≤ V, (∀ i, U i ∈ B.carrier) ∧ V = ⨆ i, U i ∧
      ∃ t : ∀ i, S.X₂.obj.obj (op (U i)),
        ∀ i, S.g.hom.app (op (U i)) (t i) =
          S.X₃.obj.map (homOfLE (hUV i)).op s := by
  have hlocal : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  have hlift := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hlocal
  choose W hWV hpre hxW using fun x : V ↦ hlift V s x.1 x.2
  choose t ht using hpre
  have hcover : V ≤ ⨆ x : V, W x := by
    intro x hxV
    rw [Opens.mem_iSup]
    exact ⟨⟨x, hxV⟩, hxW ⟨x, hxV⟩⟩
  obtain ⟨I, _, U, a, hUB, hUa, hVU⟩ :=
    B.exists_finite_refinement hV W hcover
  have hUV (i : I) : U i ≤ V := (le_iSup U i).trans hVU.symm.le
  let t' : ∀ i, S.X₂.obj.obj (op (U i)) := fun i ↦
    S.X₂.obj.map (homOfLE (hUa i)).op (t (a i))
  refine ⟨I, inferInstance, U, hUV, hUB, hVU, t', fun i ↦ ?_⟩
  dsimp [t']
  rw [← CategoryTheory.comp_apply, S.g.hom.naturality]
  change S.X₃.obj.map (homOfLE (hUa i)).op
      (S.g.hom.app (op (W (a i))) (t (a i))) =
        S.X₃.obj.map (homOfLE (hUV i)).op s
  rw [ht (a i)]
  exact TopCat.Presheaf.restrict_restrict (hUa i) (hWV (a i)) s

/-- On a basis open, degree-one Cech exactness makes the quotient map in a short exact
sequence surjective on sections.  This is the key correction-and-gluing step in Tag 01EW. -/
lemma epi_app_of_isCechAcyclicOnCompactBasis
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hF : IsCechAcyclicOnCompactBasis B S.X₁)
    {V : Opens X} (hV : V ∈ B.carrier) : Epi (S.g.hom.app (op V)) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  haveI := hS.mono_f
  obtain ⟨I, _, U, hUV, hUB, hVU, t, ht⟩ :=
    exists_finite_basis_lift_cover B hS hV s
  let C₁ := (cechComplexFunctor U).obj S.X₁.obj
  let C₂ := (cechComplexFunctor U).obj S.X₂.obj
  let C₃ := (cechComplexFunctor U).obj S.X₃.obj
  let α : C₁ ⟶ C₂ := (cechComplexFunctor U).map S.f.hom
  let β : C₂ ⟶ C₃ := (cechComplexFunctor U).map S.g.hom
  let y : C₂.X 0 := cechZeroOfFamily U S.X₂ t
  have hy : β.f 0 y = sectionsToCechZero U hUV S.X₃ s := by
    change ((cechComplexFunctor U).map S.g.hom).f 0
        (cechZeroOfFamily U S.X₂ t) = _
    rw [cechZeroOfFamily_map]
    rw [← cechZeroOfRestrictions_eq_sectionsToCechZero U hUV S.X₃ s]
    congr 1
    funext i
    exact ht i
  have hdy : β.f 1 (C₂.d 0 1 y) = 0 := by
    calc
      β.f 1 (C₂.d 0 1 y) = C₃.d 0 1 (β.f 0 y) := by
        erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, β.comm]
      _ = C₃.d 0 1 (sectionsToCechZero U hUV S.X₃ s) := by rw [hy]
      _ = 0 := by
        erw [← ConcreteCategory.comp_apply, sectionsToCechZero_comp_d]
        rfl
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff
    (cechTermShortComplex U S 1)).mp (cechTermShortComplex_exact U hS.exact 1)
      (C₂.d 0 1 y) hdy
  change C₁.X 1 at z
  change α.f 1 z = C₂.d 0 1 y at hz
  haveI : Mono (α.f 2) := by
    dsimp [α, C₁, C₂, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor]
    infer_instance
  have hzcycle : C₁.d 1 2 z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (α.f 2)).mp inferInstance
    rw [map_zero]
    calc
      α.f 2 (C₁.d 1 2 z) = C₂.d 1 2 (α.f 1 z) := by
        erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, α.comm]
      _ = C₂.d 1 2 (C₂.d 0 1 y) := by rw [hz]
      _ = 0 := by
        erw [← ConcreteCategory.comp_apply, C₂.d_comp_d]
        rfl
  have hF₁ := hF V hV U hUB hVU 1 (by omega)
  rw [C₁.exactAt_iff' 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at hF₁
  simp only [HomologicalComplex.shortComplexFunctor'_obj_X₁,
    HomologicalComplex.shortComplexFunctor'_obj_X₂,
    HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g] at hF₁
  obtain ⟨w, hw⟩ := hF₁ z hzcycle
  let y' : C₂.X 0 := y - α.f 0 w
  have hy'cycle : C₂.d 0 1 y' = 0 := by
    dsimp [y']
    rw [map_sub, ← ConcreteCategory.comp_apply, α.comm,
      ConcreteCategory.comp_apply, hw, hz, sub_self]
  let sf : ∀ i, S.X₂.obj.obj (op (U i)) := cechZeroFamily U S.X₂ y'
  have hsf : TopCat.Presheaf.IsCompatible S.X₂.obj U sf :=
    cechZeroFamily_isCompatible U S.X₂ y' hy'cycle
  obtain ⟨a, ha, _⟩ := S.X₂.existsUnique_gluing' U V
    (fun i ↦ homOfLE (hUV i)) hVU.le sf hsf
  refine ⟨a, ?_⟩
  apply S.X₃.eq_of_locally_eq' U V (fun i ↦ homOfLE (hUV i)) hVU.le
  intro i
  rw [← CategoryTheory.comp_apply, ← S.g.hom.naturality,
    CategoryTheory.comp_apply, ha i]
  change S.g.hom.app (op (U i)) (cechZeroFamily U S.X₂ y' i) = _
  rw [← cechZeroFamily_map]
  have hβα : β.f 0 (α.f 0 w) = 0 := by
    erw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
      ← Functor.map_comp]
    change ((cechComplexFunctor U).map (S.f ≫ S.g).hom).f 0 w = 0
    rw [S.zero]
    simp
  have hy'map : β.f 0 y' = sectionsToCechZero U hUV S.X₃ s := by
    dsimp [y']
    rw [map_sub, hβα, sub_zero, hy]
  rw [hy'map, cechZeroFamily_sectionsToCechZero]

/-- The degreewise short complex of Cech cochain complexes associated to a short complex of
sheaves. -/
private noncomputable def cechShortComplex
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk
    ((cechComplexFunctor U).map S.f.hom)
    ((cechComplexFunctor U).map S.g.hom) (by
      rw [← Functor.map_comp]
      change (cechComplexFunctor U).map (S.f ≫ S.g).hom = 0
      rw [S.zero]
      simp)

/-- On a finite basis cover, the Cech cochain complexes of a short exact sequence remain short
exact once the left-hand sheaf has the basis-Cech property. -/
private lemma cechShortComplex_shortExact
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    {I : Type u} [Fintype I] (U : I → Opens X) (hUB : ∀ i, U i ∈ B.carrier)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hF : IsCechAcyclicOnCompactBasis B S.X₁) :
    (cechShortComplex U S).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  change (cechTermShortComplex U S n).ShortExact
  haveI := hS.mono_f
  refine ShortComplex.ShortExact.mk'
    (cechTermShortComplex_exact U hS.exact n) ?_ ?_
  · dsimp [cechTermShortComplex, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor]
    infer_instance
  · letI (q : Fin (n + 1) → I) : Epi (S.g.hom.app (op (∏ᶜ (U ∘ q)))) :=
      epi_app_of_isCechAcyclicOnCompactBasis B hS hF
        (B.fin_pi_mem (U ∘ q) (fun k ↦ hUB (q k)))
    dsimp [cechTermShortComplex, cechComplexFunctor,
      Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor]
    infer_instance

/-- The quotient in a short exact sequence inherits positive Cech exactness on the compact
basis when the middle sheaf is injective. -/
lemma isCechAcyclicOnCompactBasis_quotient
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hF : IsCechAcyclicOnCompactBasis B S.X₁) [Injective S.X₂] :
    IsCechAcyclicOnCompactBasis B S.X₃ := by
  intro I _ V hV U hUB hVU n hn
  let T := cechShortComplex U S
  have hT : T.ShortExact := cechShortComplex_shortExact B U hUB hS hF
  have hI : IsCechAcyclicOnCompactBasis B S.X₂ :=
    isCechAcyclicOnCompactBasis_of_injective B S.X₂
  have h₂n : IsZero (T.X₂.homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology T.X₂ n).mp
      (hI V hV U hUB hVU n hn)
  refine hT.exactAt_X₃ n (IsZero.epi h₂n _) ?_
  intro j hnj
  have hj : 0 < j := by
    change n + 1 = j at hnj
    omega
  have h₁j : IsZero (T.X₁.homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology T.X₁ j).mp
      (hF V hV U hUB hVU j hj)
  exact IsZero.mono h₁j _

private noncomputable abbrev derivedH
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type (u + 1) :=
  @Sheaf.H (Opens X) _ (Opens.grothendieckTopology X) F inferInstance hExt n

private noncomputable abbrev derivedH₀Equiv
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    derivedH hExt F 0 ≃+ F.obj.obj (op (⊤ : Opens X)) :=
  @Sheaf.H.equiv₀ (Opens X) _ (Opens.grothendieckTopology X) inferInstance hExt
    F (⊤ : Opens X) Limits.isTerminalTop

private noncomputable abbrev derivedHMap
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    derivedH hExt F n →+ derivedH hExt G n :=
  @Sheaf.H.map (Opens X) _ (Opens.grothendieckTopology X) inferInstance hExt F G f n

private lemma derivedH₀Equiv_naturality
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : derivedH hExt F 0) :
    f.hom.app (op (⊤ : Opens X)) (derivedH₀Equiv hExt F x) =
      derivedH₀Equiv hExt G (derivedHMap hExt f 0 x) :=
  @Sheaf.H.equiv₀_naturality (Opens X) _ (Opens.grothendieckTopology X)
    inferInstance hExt (⊤ : Opens X) Limits.isTerminalTop F G f x

private lemma derivedHMap_apply
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : derivedH hExt F n) :
    derivedHMap hExt f n x =
      @Abelian.Ext.comp.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        _ _ _ n 0 x (Abelian.Ext.mk₀ f) n (add_zero n) :=
  @Sheaf.H.map_apply (Opens X) _ (Opens.grothendieckTopology X)
    inferInstance hExt F G f n x

set_option maxHeartbeats 200000 in
private lemma H_one_subsingleton_of_sections_epi
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ip : InjectivePresentation F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hepi : Epi (ip.shortComplex.g.hom.app (op (⊤ : Opens X)))) :
    Subsingleton (derivedH hExt F 1) := by
  have hS : ip.shortComplex.ShortExact := ip.shortExact_shortComplex
  have hall (x : derivedH hExt F 1) : x = 0 := by
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
      (derivedH₀Equiv hExt ip.shortComplex.X₃ q)
    let b : derivedH hExt ip.shortComplex.X₂ 0 :=
      (derivedH₀Equiv hExt ip.shortComplex.X₂).symm a
    have hb : derivedHMap hExt ip.shortComplex.g 0 b = q := by
      apply (derivedH₀Equiv hExt ip.shortComplex.X₃).injective
      rw [← derivedH₀Equiv_naturality]
      simpa only [b, AddEquiv.apply_symm_apply] using ha
    rw [← hb] at hq
    rw [derivedHMap_apply hExt] at hq
    have hcomp := @ShortComplex.ShortExact.comp_extClass.{u + 1}
      _ _ _ hExt _ hS
    have hbzero := congrArg (fun e ↦
      @Abelian.Ext.comp.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        _ _ _ 0 1 b e 1 (zero_add 1)) hcomp
    simp only [Abelian.Ext.comp_zero.{u + 1}] at hbzero
    have hassoc := @Abelian.Ext.comp_assoc_of_second_deg_zero.{u + 1}
      (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt _ _ _ _ 0 1 1
        b (@Abelian.Ext.mk₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt _ _
          ip.shortComplex.g) hS.extClass rfl
    exact hq.symm.trans (hassoc.trans hbzero)
  exact ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

set_option maxHeartbeats 100000 in
private lemma H_succ_subsingleton_of_shortExact
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (n : ℕ) [Subsingleton (derivedH hExt S.X₃ n)] :
    Subsingleton (derivedH hExt S.X₁ (n + 1)) := by
  have hall (x : derivedH hExt S.X₁ (n + 1)) : x = 0 := by
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    have hq₀ : q = 0 := Subsingleton.elim _ _
    rw [hq₀, Abelian.Ext.zero_comp] at hq
    exact hq.symm
  exact ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

private noncomputable abbrev derivedHPrime
    {X : TopCat.{u}} (hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) (n : ℕ) : Type (u + 1) :=
  @Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _ hExt F n V

private noncomputable abbrev derivedHPrime₀Equiv
    {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens X) :
    derivedHPrime hExt F V 0 ≃+ F.obj.obj (op V) := by
  exact (@Abelian.Ext.addEquiv₀ _ _ _ hExt
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) F).trans
      (freeAbelianYonedaSheafHomAddEquiv V F)

private noncomputable abbrev derivedHPrimeMap
    {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (V : Opens X) (n : ℕ) :
    derivedHPrime hExt F V n →+ derivedHPrime hExt G V n := by
  exact @Abelian.Ext.postcomp _ _ _ hExt F G 0
    (@Abelian.Ext.mk₀ _ _ _ hExt F G f)
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) n n (add_zero n)

private lemma derivedHPrime_addEquiv₀_map
    {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (V : Opens X)
    (x : derivedHPrime hExt F V 0) :
    (@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
      (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) G)
        (derivedHPrimeMap f V 0 x) =
      (@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) F) x ≫ f := by
  apply (@Abelian.Ext.mk₀_bijective _ _ _ hExt
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V :
      TopCat.Sheaf AddCommGrpCat.{u} X) G).injective
  rw [@Abelian.Ext.mk₀_addEquiv₀_apply _ _ _ hExt
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V :
      TopCat.Sheaf AddCommGrpCat.{u} X) G
    (derivedHPrimeMap f V 0 x)]
  rw [← @Abelian.Ext.mk₀_comp_mk₀ _ _ _ hExt
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V :
      TopCat.Sheaf AddCommGrpCat.{u} X) F G
    (Abelian.Ext.addEquiv₀ x) f]
  rw [@Abelian.Ext.mk₀_addEquiv₀_apply _ _ _ hExt
    (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V :
      TopCat.Sheaf AddCommGrpCat.{u} X) F x]
  rfl

private lemma derivedHPrime₀Equiv_naturality
    {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (V : Opens X)
    (x : derivedHPrime hExt F V 0) :
    f.hom.app (op V) (derivedHPrime₀Equiv F V x) =
      derivedHPrime₀Equiv G V (derivedHPrimeMap f V 0 x) := by
  change f.hom.app (op V)
      (freeAbelianYonedaSheafHomAddEquiv V F
        ((@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
          (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) F) x)) =
    freeAbelianYonedaSheafHomAddEquiv V G
      ((@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) G)
          (derivedHPrimeMap f V 0 x))
  calc
    _ = freeAbelianYonedaSheafHomAddEquiv V G
        ((@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
          (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) F) x ≫ f) :=
      (@freeAbelianYonedaSheafHomAddEquiv_comp (Opens X) _
        (Opens.grothendieckTopology X) _ V F G
        ((@Abelian.Ext.addEquiv₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
          (freeAbelianYonedaSheaf (Opens.grothendieckTopology X) V) F) x) f).symm
    _ = _ := congrArg (freeAbelianYonedaSheafHomAddEquiv V G)
      (derivedHPrime_addEquiv₀_map f V x).symm

private lemma derivedHPrimeMap_apply
    {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (V : Opens X) (n : ℕ)
    (x : derivedHPrime hExt F V n) :
    derivedHPrimeMap f V n x =
      @Abelian.Ext.comp.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        _ _ _ n 0 x
          (@Abelian.Ext.mk₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt _ _ f)
          n (add_zero n) := rfl

set_option maxHeartbeats 200000 in
private lemma HPrime_one_subsingleton_of_sections_epi
    {X : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ip : InjectivePresentation F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (V : Opens X) (hepi : Epi (ip.shortComplex.g.hom.app (op V))) :
    Subsingleton (derivedHPrime hExt F V 1) := by
  have hS : ip.shortComplex.ShortExact := ip.shortExact_shortComplex
  have hall (x : derivedHPrime hExt F V 1) : x = 0 := by
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
      (derivedHPrime₀Equiv ip.shortComplex.X₃ V q)
    let b : derivedHPrime hExt ip.shortComplex.X₂ V 0 :=
      (derivedHPrime₀Equiv ip.shortComplex.X₂ V).symm a
    have hb : derivedHPrimeMap ip.shortComplex.g V 0 b = q := by
      apply (derivedHPrime₀Equiv ip.shortComplex.X₃ V).injective
      rw [← derivedHPrime₀Equiv_naturality]
      simpa only [b, AddEquiv.apply_symm_apply] using ha
    rw [← hb] at hq
    rw [derivedHPrimeMap_apply] at hq
    have hcomp := @ShortComplex.ShortExact.comp_extClass.{u + 1}
      _ _ _ hExt _ hS
    have hbzero := congrArg (fun e ↦
      @Abelian.Ext.comp.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt
        _ _ _ 0 1 b e 1 (zero_add 1)) hcomp
    simp only [Abelian.Ext.comp_zero.{u + 1}] at hbzero
    have hassoc := @Abelian.Ext.comp_assoc_of_second_deg_zero.{u + 1}
      (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt _ _ _ _ 0 1 1
        b (@Abelian.Ext.mk₀ (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hExt _ _
          ip.shortComplex.g) hS.extClass rfl
    exact hq.symm.trans (hassoc.trans hbzero)
  exact ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

set_option maxHeartbeats 400000 in
private lemma HPrime_succ_subsingleton_of_shortExact
    {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (V : Opens X) (n : ℕ) [hsub : Subsingleton (derivedHPrime hExt S.X₃ V n)] :
    Subsingleton (derivedHPrime hExt S.X₁ V (n + 1)) := by
  have hall (x : derivedHPrime hExt S.X₁ V (n + 1)) : x = 0 := by
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    have hq₀ : q = 0 := hsub.elim _ _
    rw [hq₀, Abelian.Ext.zero_comp] at hq
    exact hq.symm
  exact ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

set_option maxHeartbeats 400000 in
/-- Cech exactness on finite covers in a compact intersection-stable collection implies
vanishing of positive local cohomology on every member of the collection. -/
theorem HPrime_subsingleton_of_isCechAcyclicOnCompactBasis
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : IsCechAcyclicOnCompactBasis B F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (V : Opens X) (hV : V ∈ B.carrier) (n : ℕ) (hn : 0 < n) :
    Subsingleton (derivedHPrime hExt F V n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  let P : ℕ → Prop := fun k ↦ ∀ (G : TopCat.Sheaf AddCommGrpCat.{u} X),
    IsCechAcyclicOnCompactBasis B G → Subsingleton (derivedHPrime hExt G V (k + 1))
  have hP : ∀ k, P k := by
    intro k
    induction k with
    | zero =>
      intro F hF
      let ip : InjectivePresentation F :=
        Classical.choice (EnoughInjectives.presentation F)
      have hS : ip.shortComplex.ShortExact := ip.shortExact_shortComplex
      exact HPrime_one_subsingleton_of_sections_epi ip V
        (epi_app_of_isCechAcyclicOnCompactBasis B hS hF hV)
    | succ k ih =>
      intro F hF
      let ip : InjectivePresentation F :=
        Classical.choice (EnoughInjectives.presentation F)
      let S := ip.shortComplex
      have hS : S.ShortExact := ip.shortExact_shortComplex
      have hQ : IsCechAcyclicOnCompactBasis B S.X₃ :=
        isCechAcyclicOnCompactBasis_quotient B hS hF
      haveI : Subsingleton (derivedHPrime hExt S.X₃ V (k + 1)) := ih S.X₃ hQ
      exact HPrime_succ_subsingleton_of_shortExact hS V (k + 1)
  exact hP m F hF

set_option maxHeartbeats 100000 in
/-- Cech exactness on finite covers in a compact intersection-stable basis implies vanishing of
positive derived global-section cohomology (Stacks Project, Tag 01EW). -/
theorem H_subsingleton_of_isCechAcyclicOnCompactBasis
    {X : TopCat.{u}} (B : CompactOpenBasis X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : IsCechAcyclicOnCompactBasis B F)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (hTop : (⊤ : Opens X) ∈ B.carrier)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (@Sheaf.H (Opens X) _ (Opens.grothendieckTopology X) F
      inferInstance hExt n) := by
  exact (@subsingleton_HPrime_iff_H (Opens X) _ (Opens.grothendieckTopology X)
    _ hExt ⊤ Limits.isTerminalTop F n).mp
      (HPrime_subsingleton_of_isCechAcyclicOnCompactBasis B F hF ⊤ hTop n hn)

end CategoryTheory.Sheaf
