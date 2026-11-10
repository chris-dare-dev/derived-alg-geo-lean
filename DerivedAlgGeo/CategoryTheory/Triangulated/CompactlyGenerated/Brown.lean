/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Existence
import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Brown approximation towers for compact generators

This file proves the constructive part of Theorem A.13 of
arXiv:2607.28411v1.  For a universe-zero small property `G` of compact objects,
the Brown tower starts with the coproduct of all maps from generators to the
target.  At each successor stage it attaches a coproduct of shifted generators
which kills the kernel on Hom.  Compactness identifies Hom into the mapping
telescope with the sequential direct limit, producing the universal
approximation map required by the aisle constructor.

The universe hypotheses are explicit.  `ObjectProperty.Small.{0} G` says that
the generators form a set, `LocallySmall.{0} C` makes the Hom sets available
as universe-zero indices, and `HasCoproducts.{0} C` supplies exactly the
coproducts used by the construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {G : ObjectProperty C}

/-- A universal approximation map tested only on the chosen generators.

For `U = Coprod(G)`, generator-level Hom control is enough: completing the map
to a triangle first proves that its cone is right orthogonal to `G`, and
coproduct/extension closure then upgrades that orthogonality to all of
`Coprod(G)`. -/
structure GeneratorApproximationMap (G : ObjectProperty C) (A : C) where
  /-- The approximating object. -/
  left : C
  /-- The approximating object lies in `Coprod(G)`. -/
  left_mem : G.coprodClosure.{0} left
  /-- The universal approximation morphism. -/
  hom : left ⟶ A
  /-- Hom into the target is surjective on generators. -/
  hom_surjective (Z : C) (hZ : G Z) :
    Function.Surjective (fun f : Z ⟶ left => f ≫ hom)
  /-- Shifted Hom into the target is injective on generators. -/
  shift_hom_injective (Z : C) (hZ : G Z) :
    Function.Injective
      (fun f : Z ⟶ left⟦(1 : ℤ)⟧ => f ≫ hom⟦(1 : ℤ)⟧')

namespace GeneratorApproximationMap

variable {A : C} (a : GeneratorApproximationMap G A)

/-- The cone of a generator approximation is right orthogonal to the whole
coproduct-and-extension closure of the generators. -/
theorem exists_triangle :
    ∃ (Y : C) (_ : G.coprodClosure.{0}.rightOrthogonal Y)
      (g : A ⟶ Y) (h : Y ⟶ a.left⟦(1 : ℤ)⟧),
        Triangle.mk a.hom g h ∈ distTriang C := by
  obtain ⟨Y, g, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle a.hom
  let T := Triangle.mk a.hom g h
  have hYgen : G.rightOrthogonal Y := by
    intro Z f hZ
    have hfh : f ≫ h = 0 := by
      apply a.shift_hom_injective Z hZ
      change (f ≫ h) ≫ a.hom⟦(1 : ℤ)⟧' =
        (0 : Z ⟶ a.left⟦(1 : ℤ)⟧) ≫ a.hom⟦(1 : ℤ)⟧'
      have hh := comp_distTriang_mor_zero₃₁ T hT
      change h ≫ a.hom⟦(1 : ℤ)⟧' = 0 at hh
      rw [Category.assoc, hh, comp_zero, zero_comp]
    obtain ⟨k, rfl⟩ := Triangle.coyoneda_exact₃ T hT f hfh
    obtain ⟨l, rfl⟩ := a.hom_surjective Z hZ k
    change (l ≫ a.hom) ≫ g = 0
    have hag := comp_distTriang_mor_zero₁₂ T hT
    change a.hom ≫ g = 0 at hag
    rw [Category.assoc, hag, comp_zero]
  have hY : G.coprodClosure.{0}.rightOrthogonal Y := by
    intro Z f hZ
    induction hZ with
    | of_mem Z hZ => exact hYgen f hZ
    | of_iso e _ ih =>
        rw [← cancel_epi e.hom, comp_zero]
        exact ih (e.hom ≫ f)
    | of_coproduct c hc _ ih =>
        apply hc.hom_ext
        intro j
        rw [comp_zero]
        exact ih j (c.ι.app j ≫ f)
    | of_extension T hT _ _ ih₁ ih₃ =>
        have hzero : T.mor₁ ≫ f = 0 := ih₁ (T.mor₁ ≫ f)
        obtain ⟨k, rfl⟩ := Triangle.yoneda_exact₂ T hT f hzero
        rw [ih₃ k, comp_zero]
  exact ⟨Y, hY, g, h, hT⟩

end GeneratorApproximationMap

namespace CompactGeneratorApproximation

/-- Generator-level universal maps are enough to construct the compactly
generated approximation triangles of Theorem A.13. -/
theorem ofGeneratorApproximationMaps
    (hG : G ≤ G.shift (1 : ℤ))
    (happrox : ∀ A : C, Nonempty (GeneratorApproximationMap G A)) :
    CompactGeneratorApproximation.{0} G := by
  refine
    { generator_shift := hG
      exists_triangle := fun A => ?_ }
  obtain ⟨a⟩ := happrox A
  obtain ⟨Y, hY, g, h, hT⟩ := a.exists_triangle
  exact ⟨a.left, Y, a.left_mem, hY, a.hom, g, h, hT⟩

end CompactGeneratorApproximation

namespace CompactGeneratorBrown

variable [ObjectProperty.Small.{0} G] [LocallySmall.{0} C]
  [HasCoproducts.{0} C]

/-- A universe-zero indexing type for the chosen generators. -/
abbrev GeneratorIndex (G : ObjectProperty C)
    [ObjectProperty.Small.{0} G] : Type :=
  Shrink (Subtype G)

/-- The generator represented by a small generator index. -/
def generator (i : GeneratorIndex G) : C :=
  ((equivShrink (Subtype G)).symm i).1

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [LocallySmall.{0} C] [HasCoproducts.{0} C] in
/-- Every small generator index represents an object satisfying `G`. -/
theorem generator_mem (i : GeneratorIndex G) : G (generator (G := G) i) :=
  ((equivShrink (Subtype G)).symm i).2

/-- The universe-zero index of all maps from generators to `A`. -/
abbrev EvaluationIndex (G : ObjectProperty C)
    [ObjectProperty.Small.{0} G] (A : C) : Type :=
  Σ i : GeneratorIndex G, Shrink (generator (G := G) i ⟶ A)

/-- The generator underlying an evaluation summand. -/
abbrev evaluationSource (A : C) (i : EvaluationIndex G A) : C :=
  generator (G := G) i.1

/-- The map to `A` represented by an evaluation summand. -/
def evaluationMap (A : C) (i : EvaluationIndex G A) :
    evaluationSource (G := G) A i ⟶ A :=
  (equivShrink (generator (G := G) i.1 ⟶ A)).symm i.2

/-- The initial Brown approximation: the coproduct of every map from a
generator to the target. -/
def initialObject (A : C) : C :=
  ∐ evaluationSource (G := G) A

/-- The evaluation morphism from the initial Brown approximation. -/
def initialHom (A : C) : initialObject (G := G) A ⟶ A :=
  Sigma.desc (evaluationMap (G := G) A)

/-- The initial Brown object belongs to `Coprod(G)`. -/
theorem initialObject_mem (A : C) :
    G.coprodClosure.{0} (initialObject (G := G) A) := by
  exact .of_coproduct
    (colimit.cocone (Discrete.functor (evaluationSource (G := G) A)))
    (colimit.isColimit _)
    (fun i => G.le_coprodClosure.{0} _ (generator_mem (G := G) i.as.1))

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Every map from a generator to `A` factors through the initial evaluation
morphism. -/
theorem initialHom_surjective (A Z : C) (hZ : G Z) :
    Function.Surjective
      (fun f : Z ⟶ initialObject (G := G) A =>
        f ≫ initialHom (G := G) A) := by
  intro f
  let i : GeneratorIndex G := equivShrink (Subtype G) ⟨Z, hZ⟩
  have hi : generator (G := G) i = Z := by
    simp [i, generator]
  let f' : generator (G := G) i ⟶ A := eqToHom hi ≫ f
  let j : EvaluationIndex G A :=
    ⟨i, equivShrink (generator (G := G) i ⟶ A) f'⟩
  have hj : evaluationSource (G := G) A j = Z := by
    exact hi
  have hmap : eqToHom hj.symm ≫ evaluationMap (G := G) A j = f := by
    dsimp [j, evaluationMap]
    rw [Equiv.symm_apply_apply]
    rw [← Category.assoc, eqToHom_trans]
    simp
  refine
    ⟨eqToHom hj.symm ≫ Sigma.ι (evaluationSource (G := G) A) j, ?_⟩
  change (eqToHom hj.symm ≫ Sigma.ι _ j) ≫ Sigma.desc _ = f
  rw [Category.assoc, Sigma.ι_comp_desc, hmap]

/-- One stage of the Brown approximation tower. -/
structure Stage (G : ObjectProperty C) (A : C) where
  /-- The stage object. -/
  obj : C
  /-- Every stage is built from coproducts and extensions of generators. -/
  mem : G.coprodClosure.{0} obj
  /-- The stage approximation map. -/
  hom : obj ⟶ A

/-- The initial Brown stage. -/
def initialStage (A : C) : Stage G A where
  obj := initialObject (G := G) A
  mem := initialObject_mem (G := G) A
  hom := initialHom (G := G) A

/-- The universe-zero index of the shifted-generator maps in the kernel of a
stage approximation. -/
abbrev KernelIndex {A : C} (s : Stage G A) : Type :=
  Σ i : GeneratorIndex G,
    Shrink { f : (generator (G := G) i)⟦(-1 : ℤ)⟧ ⟶ s.obj //
      f ≫ s.hom = 0 }

/-- The shifted generator underlying a kernel summand. -/
abbrev kernelSource {A : C} (s : Stage G A) (i : KernelIndex s) : C :=
  (generator (G := G) i.1)⟦(-1 : ℤ)⟧

/-- The kernel morphism represented by a kernel summand. -/
def kernelMap {A : C} (s : Stage G A) (i : KernelIndex s) :
    kernelSource s i ⟶ s.obj :=
  ((equivShrink
    { f : (generator (G := G) i.1)⟦(-1 : ℤ)⟧ ⟶ s.obj //
      f ≫ s.hom = 0 }).symm i.2).1

/-- The coproduct of all shifted-generator kernel maps. -/
def kernelObject {A : C} (s : Stage G A) : C :=
  ∐ kernelSource s

/-- The universal kernel map into a Brown stage. -/
def kernelHom {A : C} (s : Stage G A) : kernelObject s ⟶ s.obj :=
  Sigma.desc (kernelMap s)

@[reassoc]
theorem kernelHom_comp_stageHom {A : C} (s : Stage G A) :
    kernelHom s ≫ s.hom = 0 := by
  change Sigma.desc (kernelMap s) ≫ s.hom = 0
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, Sigma.ι_comp_desc]
  rw [comp_zero]
  change ((equivShrink
    { f : (generator (G := G) i.1)⟦(-1 : ℤ)⟧ ⟶ s.obj //
      f ≫ s.hom = 0 }).symm i.2).1 ≫ s.hom = 0
  exact ((equivShrink
    { f : (generator (G := G) i.1)⟦(-1 : ℤ)⟧ ⟶ s.obj //
      f ≫ s.hom = 0 }).symm i.2).2

/-- Shifting the kernel coproduct forward by one puts it in `Coprod(G)`: its
summands become the original generators. -/
theorem kernelObject_shift_mem {A : C} (s : Stage G A) :
    G.coprodClosure.{0} ((kernelObject s)⟦(1 : ℤ)⟧) := by
  let F := Discrete.functor (kernelSource s)
  let c := (shiftFunctor C (1 : ℤ)).mapCocone (colimit.cocone F)
  have hc : IsColimit c :=
    isColimitOfPreserves (shiftFunctor C (1 : ℤ)) (colimit.isColimit F)
  apply ObjectProperty.coprodClosure.of_coproduct c hc
  rintro ⟨i⟩
  refine .of_iso (shiftShiftNeg (generator (G := G) i.1) (-1 : ℤ)).symm ?_
  exact G.le_coprodClosure.{0} _ (generator_mem (G := G) i.1)

/-- The successor data attached to a Brown stage. -/
structure StepData {A : C} (s : Stage G A) where
  /-- The successor stage. -/
  next : Stage G A
  /-- The transition to the successor stage. -/
  transition : s.obj ⟶ next.obj
  /-- The third morphism in the attachment triangle. -/
  connecting : next.obj ⟶ (kernelObject s)⟦(1 : ℤ)⟧
  /-- The attachment is a distinguished triangle. -/
  distinguished :
    Triangle.mk (kernelHom s) transition connecting ∈ distTriang C
  /-- The successor map extends the current approximation map. -/
  transition_hom : transition ≫ next.hom = s.hom
  /-- Every shifted-generator kernel map is killed at the successor. -/
  kills (Z : C) (hZ : G Z) (f : Z⟦(-1 : ℤ)⟧ ⟶ s.obj)
    (hf : f ≫ s.hom = 0) : f ≫ transition = 0

/-- The successor attachment data exist for every Brown stage. -/
theorem stepData_nonempty {A : C} (s : Stage G A) :
    Nonempty (StepData s) := by
  obtain ⟨Y, t, c, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle (kernelHom s)
  let T := Triangle.mk (kernelHom s) t c
  obtain ⟨p, hp⟩ := Triangle.yoneda_exact₂ T hT s.hom
    (kernelHom_comp_stageHom s)
  have hY : G.coprodClosure.{0} Y := by
    exact .of_extension T.rotate (rot_of_distTriang T hT) s.mem
      (kernelObject_shift_mem s)
  let next : Stage G A := ⟨Y, hY, p⟩
  have hkillIndex (i : KernelIndex s) : kernelMap s i ≫ t = 0 := by
    have hzero := comp_distTriang_mor_zero₁₂ T hT
    change Sigma.desc (kernelMap s) ≫ t = 0 at hzero
    calc
      kernelMap s i ≫ t =
          (Sigma.ι (kernelSource s) i ≫ Sigma.desc (kernelMap s)) ≫ t := by
            rw [Sigma.ι_comp_desc]
      _ = Sigma.ι (kernelSource s) i ≫
          (Sigma.desc (kernelMap s) ≫ t) := Category.assoc _ _ _
      _ = Sigma.ι (kernelSource s) i ≫ 0 := by rw [hzero]
      _ = 0 := comp_zero
  refine ⟨
    { next := next
      transition := t
      connecting := c
      distinguished := hT
      transition_hom := hp.symm
      kills := fun Z hZ f hf => ?_ }⟩
  let i : GeneratorIndex G := equivShrink (Subtype G) ⟨Z, hZ⟩
  have hi : generator (G := G) i = Z := by
    simp [i, generator]
  let e : (generator (G := G) i)⟦(-1 : ℤ)⟧ ≅ Z⟦(-1 : ℤ)⟧ :=
    (shiftFunctor C (-1 : ℤ)).mapIso (eqToIso hi)
  let f' : (generator (G := G) i)⟦(-1 : ℤ)⟧ ⟶ s.obj := e.hom ≫ f
  have hf' : f' ≫ s.hom = 0 := by
    simp [f', Category.assoc, hf]
  let j : KernelIndex s :=
    ⟨i, equivShrink
      { q : (generator (G := G) i)⟦(-1 : ℤ)⟧ ⟶ s.obj //
        q ≫ s.hom = 0 } ⟨f', hf'⟩⟩
  have hj : kernelMap s j = f' := by
    simp [kernelMap, j]
  rw [← cancel_epi e.hom, comp_zero]
  have hk := hkillIndex j
  rw [hj] at hk
  change (e.hom ≫ f) ≫ t = 0 at hk
  simpa only [Category.assoc] using hk

/-- Attach all shifted-generator kernel maps to produce the next Brown stage. -/
noncomputable def step {A : C} (s : Stage G A) : StepData s :=
  Classical.choice (stepData_nonempty s)

/-- The recursively constructed Brown stages. -/
noncomputable def tower (A : C) : ℕ → Stage G A
  | 0 => initialStage (G := G) A
  | n + 1 => (step (tower A n)).next

/-- The transition morphisms in the Brown tower. -/
noncomputable def towerTransition (A : C) (n : ℕ) :
    (tower (G := G) A n).obj ⟶ (tower (G := G) A (n + 1)).obj :=
  (step (tower A n)).transition

@[reassoc]
theorem towerTransition_comp_hom (A : C) (n : ℕ) :
    towerTransition (G := G) A n ≫ (tower (G := G) A (n + 1)).hom =
      (tower (G := G) A n).hom :=
  (step (tower A n)).transition_hom

/-- At stage `n + 1`, the tower kills every shifted-generator map in the
kernel of the stage-`n` approximation. -/
theorem towerTransition_kills (A Z : C) (hZ : G Z) (n : ℕ)
    (f : Z⟦(-1 : ℤ)⟧ ⟶ (tower (G := G) A n).obj)
    (hf : f ≫ (tower (G := G) A n).hom = 0) :
    f ≫ towerTransition (G := G) A n = 0 :=
  (step (tower A n)).kills Z hZ f hf

/-- The sequence of objects underlying the Brown tower. -/
abbrev towerObject (A : C) (n : ℕ) : C :=
  (tower (G := G) A n).obj

/-- The chosen mapping telescope of the Brown tower. -/
noncomputable def telescope (A : C) :
    MappingTelescope.Data (towerObject (G := G) A)
      (towerTransition (G := G) A) :=
  MappingTelescope.chosen
    (towerObject (G := G) A) (towerTransition (G := G) A)

/-- The universal morphism from the Brown telescope to the target. -/
noncomputable def limitHom (A : C) : (telescope (G := G) A).obj ⟶ A :=
  Classical.choose ((telescope (G := G) A).exists_desc_comp_ι
    (fun n => (tower (G := G) A n).hom)
    (towerTransition_comp_hom (G := G) A))

@[reassoc]
theorem inclusion_comp_limitHom (A : C) (n : ℕ) :
    (telescope (G := G) A).inclusion n ≫ limitHom (G := G) A =
      (tower (G := G) A n).hom := by
  unfold MappingTelescope.Data.inclusion
  unfold limitHom
  simpa only [Category.assoc] using
    (Classical.choose_spec ((telescope (G := G) A).exists_desc_comp_ι
    (fun n => (tower (G := G) A n).hom)
    (towerTransition_comp_hom (G := G) A)) n)

/-- The Brown telescope belongs to `Coprod(G)`. -/
theorem telescope_mem (hG : G ≤ G.shift (1 : ℤ)) (A : C) :
    G.coprodClosure.{0} (telescope (G := G) A).obj := by
  let X := towerObject (G := G) A
  let f := towerTransition (G := G) A
  let T := telescope (G := G) A
  have hsum : G.coprodClosure.{0} (∐ X) := by
    exact .of_coproduct (colimit.cocone (Discrete.functor X))
      (colimit.isColimit _) (fun i => (tower (G := G) A i.as).mem)
  have hsumShift : G.coprodClosure.{0} ((∐ X)⟦(1 : ℤ)⟧) :=
    ObjectProperty.coprodClosure_le_shift hG _ hsum
  exact .of_extension
    (Triangle.mk (MappingTelescope.map X f) T.hom T.connecting).rotate
    (rot_of_distTriang _ T.distinguished) hsum hsumShift

/-- The Brown telescope map is surjective on Hom from every generator. -/
theorem limitHom_surjective (A Z : C) (hZ : G Z) :
    Function.Surjective
      (fun f : Z ⟶ (telescope (G := G) A).obj =>
        f ≫ limitHom (G := G) A) := by
  intro f
  obtain ⟨b, hb⟩ := initialHom_surjective (G := G) A Z hZ f
  let b0 : Z ⟶ towerObject (G := G) A 0 := b
  have hb0 : b0 ≫ (tower (G := G) A 0).hom = f := by
    exact hb
  refine ⟨b0 ≫ (telescope (G := G) A).inclusion 0, ?_⟩
  calc
    (b0 ≫ (telescope (G := G) A).inclusion 0) ≫
        limitHom (G := G) A =
      b0 ≫ ((telescope (G := G) A).inclusion 0 ≫
        limitHom (G := G) A) := Category.assoc _ _ _
    _ = b0 ≫ (tower (G := G) A 0).hom := by
      rw [inclusion_comp_limitHom]
    _ = f := hb0

/-- The Brown telescope map is injective on shifted Hom from every generator. -/
theorem limitHom_shift_injective
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C))
    (A Z : C) (hZ : G Z) :
    Function.Injective
      (fun f : Z ⟶ (telescope (G := G) A).obj⟦(1 : ℤ)⟧ =>
        f ≫ (limitHom (G := G) A)⟦(1 : ℤ)⟧') := by
  intro a b hab
  change a ≫ (limitHom (G := G) A)⟦(1 : ℤ)⟧' =
    b ≫ (limitHom (G := G) A)⟦(1 : ℤ)⟧' at hab
  rw [← sub_eq_zero]
  let adj : shiftFunctor C (-1 : ℤ) ⊣ shiftFunctor C (1 : ℤ) :=
    (shiftEquiv C (-1 : ℤ)).toAdjunction
  let q : Z⟦(-1 : ℤ)⟧ ⟶ (telescope (G := G) A).obj :=
    (adj.homAddEquiv Z (telescope (G := G) A).obj).symm (a - b)
  have hq : q ≫ limitHom (G := G) A = 0 := by
    apply (adj.homAddEquiv Z A).injective
    change (adj.homEquiv Z A) (q ≫ limitHom (G := G) A) = _
    rw [adj.homEquiv_naturality_right]
    simp only [q, Adjunction.homAddEquiv_symm_apply,
      Equiv.apply_symm_apply, map_zero, Preadditive.sub_comp]
    rw [hab, sub_self]
  obtain ⟨n, c, hc⟩ :=
    (telescope (G := G) A).exists_factor_stage
      ((hcompact Z hZ).shift (-1 : ℤ)) q
  have hkernel : c ≫ (tower (G := G) A n).hom = 0 := by
    calc
      c ≫ (tower (G := G) A n).hom =
          c ≫ ((telescope (G := G) A).inclusion n ≫
            limitHom (G := G) A) := by
              rw [inclusion_comp_limitHom]
      _ = (c ≫ (telescope (G := G) A).inclusion n) ≫
          limitHom (G := G) A := (Category.assoc _ _ _).symm
      _ = q ≫ limitHom (G := G) A := by rw [← hc]
      _ = 0 := hq
  have hkilled : c ≫ towerTransition (G := G) A n = 0 :=
    towerTransition_kills (G := G) A Z hZ n c hkernel
  have hqzero : q = 0 := by
    calc
      q = c ≫ (telescope (G := G) A).inclusion n := hc
      _ = c ≫ (towerTransition (G := G) A n ≫
          (telescope (G := G) A).inclusion (n + 1)) := by
            rw [(telescope (G := G) A).f_comp_inclusion]
      _ = (c ≫ towerTransition (G := G) A n) ≫
          (telescope (G := G) A).inclusion (n + 1) :=
            (Category.assoc _ _ _).symm
      _ = 0 := by rw [hkilled, zero_comp]
  apply (adj.homAddEquiv Z (telescope (G := G) A).obj).symm.injective
  simpa only [q, Equiv.apply_symm_apply, map_zero] using hqzero

/-- The universal generator approximation produced by the Brown tower. -/
noncomputable def generatorApproximationMap
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C))
    (A : C) : GeneratorApproximationMap G A where
  left := (telescope (G := G) A).obj
  left_mem := telescope_mem (G := G) hG A
  hom := limitHom (G := G) A
  hom_surjective := limitHom_surjective (G := G) A
  shift_hom_injective := limitHom_shift_injective (G := G) hcompact A

/-- The constructive Brown-representability output required by Theorem A.13. -/
theorem compactGeneratorApproximation
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C)) :
    CompactGeneratorApproximation.{0} G :=
  CompactGeneratorApproximation.ofGeneratorApproximationMaps hG
    (fun A => ⟨generatorApproximationMap (G := G) hG hcompact A⟩)

/-- The compactly generated t-structure constructed from the Brown tower. -/
noncomputable def tStructure
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C)) :
    TStructure C :=
  (compactGeneratorApproximation (G := G) hG hcompact).tStructure

/-- The Brown t-structure is compactly generated by `G`. -/
theorem tStructure_isCompactlyGeneratedBy
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C)) :
    (tStructure (G := G) hG hcompact).IsCompactlyGeneratedBy.{0} G :=
  (compactGeneratorApproximation (G := G) hG hcompact).isCompactlyGeneratedBy
    hcompact

/-- Formula (A.2), nonpositive half: the Brown aisle is `Coprod(G)`. -/
@[simp]
theorem tStructure_le_zero
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C)) :
    (tStructure (G := G) hG hcompact).le 0 = G.coprodClosure.{0} :=
  (compactGeneratorApproximation (G := G) hG hcompact).tStructure_le_zero

/-- Formula (A.2), degree-one half: the Brown coaisle is the right
orthogonal of `Coprod(G)`. -/
@[simp]
theorem tStructure_ge_one
    (hG : G ≤ G.shift (1 : ℤ))
    (hcompact : G ≤ ObjectProperty.compactObjects.{0} (C := C)) :
    (tStructure (G := G) hG hcompact).ge 1 =
      G.coprodClosure.{0}.rightOrthogonal :=
  (compactGeneratorApproximation (G := G) hG hcompact).tStructure_ge_one

end CompactGeneratorBrown

end CategoryTheory.Triangulated.TStructure
