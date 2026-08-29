/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Predicate.Quotient
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Predicate.ZeroChargeLattice
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Basic

/-!
# Genuine and uniform quadratic support for weak stability

This file binds the quadratic support interfaces to the actual classes of
nonzero weak-semistable heart objects.  The packages also store compatibility
between the real-linear charge on the class space and the additive charge of
the weak stability function; without that field a completely unrelated
linear map could satisfy the numerical predicate.

`UniformQuadraticSupportData` is the abstract fixed-category version of the
uniform clause in Definition 18.5 and Lemma 18.6 of arXiv:1902.08184v4.
`QuotientUniformQuadraticSupportData` is the corresponding real-linear core of
Definitions 21.9 and 21.15: zero-charge classes land in the killed subspace,
and a single quadratic form controls all mapped semistable classes on the
quotient.

The geometric boundedness clause (5) of Definition 21.15 is intentionally not
part of these structures.  It requires moduli functors and is outside the
repository's current abstract categorical substrate.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open CategoryTheory.Triangulated.StabilityCondition.Support

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {I V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {v : K₀ C →+ V}

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

namespace WeakStabilityFunction

/-- A genuine quadratic support form for one weak stability function,
together with the required identification of its charge with the chosen
real-linear realization. -/
structure QuadraticSupportData {t : TStructure C}
    (W : WeakStabilityFunction t) (v : K₀ C →+ V)
    (Zlin : V →ₗ[ℝ] ℂ) : Prop where
  /-- The linear charge realizes the weak stability charge on every class. -/
  charge_compatible : ∀ k : K₀ C, Zlin (v k) = W.Z k
  /-- A bundled quadratic form has the required signs on semistable classes
  and the kernel of the linear charge. -/
  quadratic :
    CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty Zlin
      (W.semistableClasses v)

omit [IsTriangulated C] in
/-- Genuine quadratic support implies the existing norm-bound support
predicate for the same semistable locus. -/
theorem QuadraticSupportData.hasSupportProperty {t : TStructure C}
    {W : WeakStabilityFunction t} {Zlin : V →ₗ[ℝ] ℂ}
    (h : W.QuadraticSupportData v Zlin) : W.HasSupportProperty v Zlin :=
  h.quadratic.hasSupportProperty

omit [IsTriangulated C] in
/-- Under genuine support, a zero-charge heart object has zero numerical
class. -/
theorem QuadraticSupportData.class_eq_zero_of_zeroCharge
    {t : TStructure C} {W : WeakStabilityFunction t}
    {Zlin : V →ₗ[ℝ] ℂ} (h : W.QuadraticSupportData v Zlin)
    {E : C} (hE : W.zeroCharge E) : v (K₀.of C E) = 0 :=
  W.class_eq_zero_of_zeroCharge Zlin h.charge_compatible
    h.hasSupportProperty hE

/-- A single quadratic form and a single linear charge controlling an indexed
family of weak stability functions on the same heart.  The quantifier order
forces the form to be uniform. -/
structure UniformQuadraticSupportData {t : TStructure C}
    (W : I → WeakStabilityFunction t) (v : K₀ C →+ V)
    (Zlin : V →ₗ[ℝ] ℂ) : Prop where
  /-- Every fiber charge is the same fixed charge on classes. -/
  charge_compatible : ∀ i (k : K₀ C), Zlin (v k) = (W i).Z k
  /-- One quadratic form controls every fiber semistable locus. -/
  quadratic :
    CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportProperty Zlin
      (fun i => (W i).semistableClasses v)

omit [IsTriangulated C] [FiniteDimensional ℝ V] in
/-- Restrict a uniform weak support package to one index. -/
theorem UniformQuadraticSupportData.fiber {t : TStructure C}
    {W : I → WeakStabilityFunction t} {Zlin : V →ₗ[ℝ] ℂ}
    (h : UniformQuadraticSupportData W v Zlin) (i : I) :
    QuadraticSupportData (W i) v Zlin :=
  ⟨h.charge_compatible i, h.quadratic.fiber i⟩

omit [IsTriangulated C] [FiniteDimensional ℝ V] in
/-- Reindex a uniform weak support package without changing its form. -/
theorem UniformQuadraticSupportData.reindex {J : Type*} {t : TStructure C}
    {W : I → WeakStabilityFunction t} {Zlin : V →ₗ[ℝ] ℂ}
    (h : UniformQuadraticSupportData W v Zlin) (f : J → I) :
    UniformQuadraticSupportData (fun j => W (f j)) v Zlin :=
  ⟨fun j => h.charge_compatible (f j), h.quadratic.reindex f⟩

omit [IsTriangulated C] [FiniteDimensional ℝ V] in
/-- A single weak quadratic support package gives a uniform constant family. -/
theorem QuadraticSupportData.constant {t : TStructure C}
    {W : WeakStabilityFunction t} {Zlin : V →ₗ[ℝ] ℂ}
    (h : W.QuadraticSupportData v Zlin) (I : Type*) :
    UniformQuadraticSupportData (fun _ : I => W) v Zlin :=
  ⟨fun _ => h.charge_compatible, h.quadratic.constant I⟩

/-- Source-facing quotient support for an indexed weak family.

The original semistable classes live in `V`; all zero-charge classes are
required to lie in `V₀`; and the actual quadratic form lives on `V ⧸ V₀`. -/
structure QuotientUniformQuadraticSupportData {t : TStructure C}
    (W : I → WeakStabilityFunction t) (v : K₀ C →+ V)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin) : Prop where
  /-- Every fiber charge is induced by the same charge before quotienting. -/
  charge_compatible : ∀ i (k : K₀ C), Zlin (v k) = (W i).Z k
  /-- Every zero-charge heart class is killed by the quotient. -/
  zero_class_mem : ∀ i (E : C), (W i).zeroCharge E →
    v (K₀.of C E) ∈ V₀
  /-- One genuine quadratic form on the quotient controls all mapped
  semistable classes. -/
  quadratic :
    CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo
      V₀ Zlin hV₀ (fun i => (W i).semistableClasses v)

omit [IsTriangulated C] in
/-- Each fiber of a quotient-uniform package satisfies quadratic support on
its mapped semistable locus. -/
theorem QuotientUniformQuadraticSupportData.fiber {t : TStructure C}
    {W : I → WeakStabilityFunction t} {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ} {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    (h : QuotientUniformQuadraticSupportData W v V₀ Zlin hV₀) (i : I) :
    CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty
      (CategoryTheory.Triangulated.StabilityCondition.Support.quotientCharge V₀ Zlin hV₀)
      (V₀.mkQ '' (W i).semistableClasses v) :=
  h.quadratic.fiber i

omit [IsTriangulated C] in
/-- A zero-charge class is literally zero after applying the quotient map. -/
theorem QuotientUniformQuadraticSupportData.zero_class_eq_zero {t : TStructure C}
    {W : I → WeakStabilityFunction t} {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ} {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    (h : QuotientUniformQuadraticSupportData W v V₀ Zlin hV₀)
    (i : I) {E : C} (hE : (W i).zeroCharge E) :
    V₀.mkQ (v (K₀.of C E)) = 0 :=
  CategoryTheory.Triangulated.StabilityCondition.Support.mkQ_eq_zero_of_mem V₀
    (h.zero_class_mem i E hE)

end WeakStabilityFunction

end

end CategoryTheory.Triangulated.WeakStabilityCondition
