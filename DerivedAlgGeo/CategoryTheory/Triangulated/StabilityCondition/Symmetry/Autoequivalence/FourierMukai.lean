/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.Composition
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport

/-!
# Fourier--Mukai autoequivalences acting on stability conditions

The generic `KernelAutoequivalence`, dual-kernel, unit, and convolution theory
lives in `CategoryTheory.Triangulated.FourierMukai.Autoequivalence`. This
specialized consumer adds only transport of Bridgeland stability conditions
and the comparison with the categorical group action.

The declarations extend the canonical `FourierMukai.KernelAutoequivalence`
namespace even though their implementation is physically owned by the
stability-condition subtree.
-/

universe w u u' x t x₁ x₂ x₃ t₁ t₂ t₃

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

noncomputable section

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {𝒲 : Type t} [Category.{x} 𝒲] [HasZeroObject 𝒲] [HasShift 𝒲 ℤ]
  [Preadditive 𝒲] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲]

namespace KernelAutoequivalence

variable (A : KernelAutoequivalence C 𝒲)

section Action

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
  [A.equiv.functor.Additive] [A.equiv.inverse.Additive]
  [A.equiv.functor.CommShift ℤ] [A.equiv.inverse.CommShift ℤ]
  [A.equiv.functor.IsTriangulated] [A.equiv.inverse.IsTriangulated]

/-- The underlying triangulated autoequivalence, with its instances bundled. -/
@[reducible]
def toTriEquiv : GroupAction.TriEquiv C where
  e := A.equiv
  fAdd := inferInstance
  iAdd := inferInstance
  fCS := inferInstance
  iCS := inferInstance
  fTri := inferInstance
  iTri := inferInstance

/-- A kernel autoequivalence transports a stability condition. -/
def actStab (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (K₀.map A.equiv.inverse x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  actStabAut A.equiv v lam hlam σ

@[simp]
theorem actStab_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStab v lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStab_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStab v lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

section OfDual

variable (D : DualKernel A)
  [A.corr.pull.CommShift ℤ] [A.corr.push.CommShift ℤ]
  [A.corr.pull.IsTriangulated] [A.corr.push.IsTriangulated]
  [(A.corr.tensor.obj D.dual).CommShift ℤ]
  [(A.corr.tensor.obj D.dual).IsTriangulated]

/-- Transport with the class-map compatibility stated through the dual kernel. -/
def actStabOfDual (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (A.corr.transformK₀ D.dual x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  A.actStab v lam (fun x => by
    rw [show K₀.map A.equiv.inverse = A.corr.transformK₀ D.dual from
      D.map_inverse_eq_transformK₀]
    exact hlam x) σ

@[simp]
theorem actStabOfDual_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStabOfDual v D lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStabOfDual_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStabOfDual v D lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

/-- A kernel autoequivalence with dual kernel defines an acting group element. -/
def toAutPair (lam : Λ ≃+ Λ)
    (hlam : ∀ x : K₀ C, v (A.corr.transformK₀ D.dual x) = lam (v x)) :
    GroupAction.AutPair v where
  Φ := A.toTriEquiv
  lam := lam
  compat x := by
    show v (K₀.map A.equiv.inverse x) = lam (v x)
    rw [show K₀.map A.equiv.inverse = A.corr.transformK₀ D.dual from
      D.map_inverse_eq_transformK₀]
    exact hlam x

omit [IsTriangulated C] in
@[simp]
theorem toAutPair_lam (lam : Λ ≃+ Λ) (hlam) :
    (A.toAutPair v D lam hlam).lam = lam := rfl

/-- The group element acts by the stability transport from which it was built. -/
theorem toAutPair_act (lam : Λ ≃+ Λ) (hlam) (σ) :
    (A.toAutPair v D lam hlam).act σ =
      A.actStabOfDual v D lam.toAddMonoidHom (fun x => hlam x) σ :=
  rfl

/-- The corresponding quotient action agrees with kernel transport. -/
theorem mk_toAutPair_smul (lam : Λ ≃+ Λ) (hlam) (σ) :
    GroupAction.AutPairQuot.mk (A.toAutPair v D lam hlam) • σ =
      A.actStabOfDual v D lam.toAddMonoidHom (fun x => hlam x) σ :=
  rfl

end OfDual

end Action

end KernelAutoequivalence

section Trans

variable {𝒲₁ : Type t₁} {𝒲₂ : Type t₂} {𝒲₃ : Type t₃}
  [Category.{x₁} 𝒲₁] [HasZeroObject 𝒲₁] [HasShift 𝒲₁ ℤ] [Preadditive 𝒲₁]
  [∀ n : ℤ, (shiftFunctor 𝒲₁ n).Additive] [Pretriangulated 𝒲₁]
  [Category.{x₂} 𝒲₂] [HasZeroObject 𝒲₂] [HasShift 𝒲₂ ℤ] [Preadditive 𝒲₂]
  [∀ n : ℤ, (shiftFunctor 𝒲₂ n).Additive] [Pretriangulated 𝒲₂]
  [Category.{x₃} 𝒲₃] [HasZeroObject 𝒲₃] [HasShift 𝒲₃ ℤ] [Preadditive 𝒲₃]
  [∀ n : ℤ, (shiftFunctor 𝒲₃ n).Additive] [Pretriangulated 𝒲₃]
  {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- Stability transport respects convolution of kernel autoequivalences. -/
theorem KernelAutoequivalence.actStab_trans (A₁ : KernelAutoequivalence C 𝒲₁)
    (A₂ : KernelAutoequivalence C 𝒲₂) (corr₃ : Correspondence C C 𝒲₃)
    (D : ConvolutionData A₁.corr A₂.corr corr₃)
    [A₁.equiv.functor.Additive] [A₁.equiv.inverse.Additive]
    [A₂.equiv.functor.Additive] [A₂.equiv.inverse.Additive]
    [A₁.equiv.functor.CommShift ℤ] [A₁.equiv.inverse.CommShift ℤ]
    [A₂.equiv.functor.CommShift ℤ] [A₂.equiv.inverse.CommShift ℤ]
    [A₁.equiv.functor.IsTriangulated] [A₁.equiv.inverse.IsTriangulated]
    [A₂.equiv.functor.IsTriangulated] [A₂.equiv.inverse.IsTriangulated]
    {lam₁ lam₂ : Λ →+ Λ}
    (h₁ : ∀ x : K₀ C, v (K₀.map A₁.equiv.inverse x) = lam₁ (v x))
    (h₂ : ∀ x : K₀ C, v (K₀.map A₂.equiv.inverse x) = lam₂ (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    A₂.actStab v lam₂ h₂ (A₁.actStab v lam₁ h₁ σ)
      = (A₁.trans A₂ corr₃ D).actStab v (lam₁.comp lam₂)
          (hlam_trans v A₁.equiv A₂.equiv h₁ h₂) σ :=
  actStabAut_trans v A₁.equiv A₂.equiv h₁ h₂ σ

end Trans

end

end CategoryTheory.Triangulated.FourierMukai
