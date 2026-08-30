/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Metric.Mass.Uniqueness
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.SourceTopology
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Stability

/-!
# Elementary transport of Harder--Narasimhan mass

This file owns the mass bookkeeping that does not mention a distinguished
triangle: the charge-norm bound, behaviour of mass under the shift by `±1`,
invariance under a lifted rotation of the `GL⁺(2, ℝ)` action, and the mass of a
filtration extended by one appended factor.

These are the arithmetic inputs to the triangle comparisons; keeping them apart
from the heart bridge lets them be imported without the heart-equivalence
machinery.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction Matrix
open CategoryTheory.Triangulated
open scoped ENNReal BigOperators ZeroObject

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- The norm of the total charge is at most the sum of the norms of the
Harder--Narasimhan factor charges. -/
theorem norm_charge_le_stabilityMass_toReal
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    ‖σ.charge E‖ ≤ (stabilityMass σ E).toReal := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [σ.charge_postnikovTower_eq_sum F.toPostnikovTower,
    stabilityMass_toReal_eq_sum σ F]
  exact norm_sum_le _ _

omit [IsTriangulated C] in
/-- Shifting an HN filtration by one does not change its mass. -/
theorem HNFiltration.mass_shift_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shift C σ.slicing 1).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [CategoryTheory.Triangulated.HNFiltration.shift]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_shift_one, map_neg, norm_neg]

/-- Shifting an object by one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shift C σ.slicing 1),
    stabilityMass_eq_mass σ F]
  exact CategoryTheory.Triangulated.HNFiltration.mass_shift_one σ F

omit [IsTriangulated C] in
/-- Shifting an HN filtration by minus one does not change its mass. -/
theorem HNFiltration.mass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.shift C σ.slicing (-1)).mass σ = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  simp only [CategoryTheory.Triangulated.HNFiltration.shift]
  change ENNReal.ofReal ‖σ.charge ((F.triangle i).obj₃⟦(-1 : ℤ)⟧)‖ =
    ENNReal.ofReal ‖σ.charge (F.triangle i).obj₃‖
  simp only [PreStabilityCondition.WithClassMap.charge_def,
    classOf_shift_neg_one, map_neg, norm_neg]

/-- Shifting an object by minus one does not change its HN mass. -/
@[simp]
theorem stabilityMass_shift_neg_one
    (σ : StabilityCondition.WithClassMap C v) (E : C) :
    stabilityMass σ (E⟦(-1 : ℤ)⟧) = stabilityMass σ E := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  rw [stabilityMass_eq_mass σ (F.shift C σ.slicing (-1)),
    stabilityMass_eq_mass σ F]
  exact CategoryTheory.Triangulated.HNFiltration.mass_shift_neg_one σ F

/-! ### Invariance under lifted rotations -/

/-- A rotation matrix acts on the complex plane by multiplication by the
unit complex number with the corresponding angle. -/
theorem actC_rotationGLPos (θ : ℝ) (z : ℂ) :
    actC (rotationGLPos θ) z = cexpI (Real.pi * θ) * z := by
  apply cplxCoord.injective
  rw [actC_apply, LinearEquiv.apply_symm_apply, rotationGLPos_mat]
  simp only [cplxCoord_apply]
  ext i
  fin_cases i <;>
    simp [rotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      cexpI_re, cexpI_im, Complex.mul_re, Complex.mul_im] <;> ring

/-- Rotations preserve the complex norm used in each HN mass summand. -/
theorem norm_actC_rotationGLPos (θ : ℝ) (z : ℂ) :
    ‖actC (rotationGLPos θ) z‖ = ‖z‖ := by
  rw [actC_rotationGLPos, norm_mul, norm_cexpI, one_mul]

/-- Relabel an HN filtration after acting on its stability condition by a
lifted rotation.  The tower is unchanged and every phase is translated by
`θ`. -/
def HNFiltration.rotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    HNFiltration C (liftedRotation θ • σ).slicing.P E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  φ := fun i ↦ F.φ i + θ
  hφ := by intro i j hij; linarith [F.hφ hij]
  semistable := by
    intro i
    change σ.slicing.P ((phaseTranslation θ)⁻¹.toOrderIso (F.φ i + θ)) _
    change σ.slicing.P (F.φ i + θ - θ) _
    simpa using F.semistable i

/-- Undo the phase relabelling of an HN filtration for a rotated stability
condition. -/
def HNFiltration.unrotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C (liftedRotation θ • σ).slicing.P E) :
    HNFiltration C σ.slicing.P E where
  n := F.n
  chain := F.chain
  triangle := F.triangle
  triangle_dist := F.triangle_dist
  triangle_obj₁ := F.triangle_obj₁
  triangle_obj₂ := F.triangle_obj₂
  base_isZero := F.base_isZero
  top_iso := F.top_iso
  φ := fun i ↦ F.φ i - θ
  hφ := by intro i j hij; linarith [F.hφ hij]
  semistable := by
    intro i
    have hi := F.semistable i
    change σ.slicing.P ((phaseTranslation θ)⁻¹.toOrderIso (F.φ i)) _ at hi
    change σ.slicing.P (F.φ i - θ) _ at hi
    exact hi

/-- Relabelling an HN filtration by a lifted rotation preserves its finite
mass sum. -/
theorem HNFiltration.mass_rotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C σ.slicing.P E) :
    (F.rotateStability σ (θ := θ)).mass (liftedRotation θ • σ) = F.mass σ := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ‖actC (rotationGLPos θ) (σ.charge (F.factor i))‖ = _
  exact norm_actC_rotationGLPos θ _

/-- Undoing a lifted rotation also preserves the finite HN mass sum. -/
theorem HNFiltration.mass_unrotateStability
    (σ : StabilityCondition.WithClassMap C v) {θ : ℝ} {E : C}
    (F : HNFiltration C (liftedRotation θ • σ).slicing.P E) :
    (F.unrotateStability σ).mass σ = F.mass (liftedRotation θ • σ) := by
  unfold HNFiltration.mass
  apply Finset.sum_congr rfl
  intro i _
  dsimp [HNFiltration.unrotateStability, PostnikovTower.factor]
  change ENNReal.ofReal ‖σ.charge (F.factor i)‖ =
    ENNReal.ofReal ‖actC (rotationGLPos θ) (σ.charge (F.factor i))‖
  rw [norm_actC_rotationGLPos]

/-- Acting on a stability condition by a pure lifted rotation leaves the HN
mass of every object unchanged. -/
@[simp]
theorem stabilityMass_liftedRotation
    (σ : StabilityCondition.WithClassMap C v) (θ : ℝ) (E : C) :
    stabilityMass (liftedRotation θ • σ) E = stabilityMass σ E := by
  apply le_antisymm
  · refine iSup_le fun F ↦ ?_
    rw [← F.mass_unrotateStability σ]
    exact le_iSup (fun G : HNFiltration C σ.slicing.P E ↦ G.mass σ)
      (F.unrotateStability σ)
  · refine iSup_le fun F ↦ ?_
    rw [← F.mass_rotateStability σ (θ := θ)]
    exact le_iSup
      (fun G : HNFiltration C (liftedRotation θ • σ).slicing.P E ↦
        G.mass (liftedRotation θ • σ))
      (F.rotateStability σ)

/-! ### Exact mass splitting across a phase cutoff -/

omit [IsTriangulated C] in
/-- Appending one strictly lower semistable factor to an HN filtration adds
exactly the norm of that factor's charge to the finite mass. -/
theorem HNFiltration.mass_appendFactor
    (σ : StabilityCondition.WithClassMap C v)
    {X E : C} (GX : HNFiltration C σ.slicing.P X)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ X) (eT₂ : T.obj₂ ≅ E)
    (ψ : ℝ) (hψ : σ.slicing.P ψ T.obj₃)
    (hψ_lt : ∀ j : Fin GX.n, ψ < GX.φ j) :
    (GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).mass σ =
      GX.mass σ + ENNReal.ofReal ‖σ.charge T.obj₃‖ := by
  unfold HNFiltration.mass
  change (∑ i : Fin (GX.n + 1),
      ENNReal.ofReal ‖σ.charge
        ((GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt).factor i)‖) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [HNFiltration.appendFactor, PostnikovTower.factor, i.isLt]
  · simp [HNFiltration.appendFactor, PostnikovTower.factor]

/-- Real-valued ambient form of `HNFiltration.mass_appendFactor`. -/
theorem stabilityMass_toReal_appendFactor
    (σ : StabilityCondition.WithClassMap C v)
    {X E : C} (GX : HNFiltration C σ.slicing.P X)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (eT₁ : T.obj₁ ≅ X) (eT₂ : T.obj₂ ≅ E)
    (ψ : ℝ) (hψ : σ.slicing.P ψ T.obj₃)
    (hψ_lt : ∀ j : Fin GX.n, ψ < GX.φ j) :
    (stabilityMass σ E).toReal =
      (stabilityMass σ X).toReal + ‖σ.charge T.obj₃‖ := by
  let G := GX.appendFactor C T hT eT₁ eT₂ ψ hψ hψ_lt
  rw [stabilityMass_eq_mass σ G, stabilityMass_eq_mass σ GX]
  dsimp [G]
  change (CategoryTheory.Triangulated.HNFiltration.mass σ
      (CategoryTheory.Triangulated.HNFiltration.appendFactor
        C GX T hT eT₁ eT₂ ψ hψ hψ_lt)).toReal =
    (CategoryTheory.Triangulated.HNFiltration.mass σ GX).toReal +
      ‖σ.charge T.obj₃‖
  have hm := CategoryTheory.Triangulated.HNFiltration.mass_appendFactor
    σ GX T hT eT₁ eT₂ ψ hψ hψ_lt
  calc
    (CategoryTheory.Triangulated.HNFiltration.mass σ
        (CategoryTheory.Triangulated.HNFiltration.appendFactor
          C GX T hT eT₁ eT₂ ψ hψ hψ_lt)).toReal =
        (CategoryTheory.Triangulated.HNFiltration.mass σ GX +
          ENNReal.ofReal ‖σ.charge T.obj₃‖).toReal :=
      congrArg ENNReal.toReal hm
    _ = (CategoryTheory.Triangulated.HNFiltration.mass σ GX).toReal +
        ‖σ.charge T.obj₃‖ := by
      rw [ENNReal.toReal_add]
      · simp
      · simp [CategoryTheory.Triangulated.HNFiltration.mass,
          CategoryTheory.Triangulated.HNFiltration.mass]
      · exact ENNReal.ofReal_ne_top

end

end CategoryTheory.Triangulated
