/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ProjectiveSpace
import DerivedAlgGeo.Topology.Category.TopCat.Opens.Limits
import DerivedAlgGeo.Algebra.Category.Grp.Preadditive
import DerivedAlgGeo.Algebra.Category.Grp.Products
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.Differential
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The Čech complex of `O(d)` on polynomial projective space, degreewise

`cechCochainsDegreewiseAddEquiv` identifies degree `n` of Mathlib's Čech complex of `O(d)`,
taken over the variable chart cover, with `polynomialVariableCechCochains` — the explicit
product of homogeneous degree-zero localizations.

## Main definitions

* `polynomialVariableChart` — the variable basic-open cover of polynomial `Proj`;
* `twistPresheaf` — the `AddCommGrpCat`-valued presheaf of `O(d)`, which is what Mathlib's
  Čech complex consumes;
* `cechCochainsDegreewiseAddEquiv` — the degreewise comparison;
* `polynomialVariableCechComplex` — the algebraic Čech complex, with the differential carried
  across that comparison;
* `polynomialVariableCechComplexIso` — Mathlib's Čech complex *is* that algebraic complex.

## Main statements

* `piObj_polynomialVariableChart` — the categorical product of the charts along a Čech index
  is the basic open of the product denominator;
* `cechIndexEquiv_map_face` — the comparison carries a Čech face restriction to the algebraic
  face map;
* `cechCochainsDegreewiseAddEquiv_d` and `polynomialVariableCechComplex_d_apply` — the
  differential is the alternating sum of the algebraic faces.

## Implementation notes

Three shape mismatches separate the two sides, and each is resolved by a different mechanism.

**The outer product.** Degree `n` of the Čech complex is a categorical product `∏ᶜ` in
`AddCommGrpCat`, indexed by `Fin (n + 1) → ι`, while `polynomialVariableCechCochains` is a Pi
type. `AddCommGrpCat.piAddEquivPi` bridges them. That is the whole reason it exists; note the
`AddEquiv` form is needed rather than `piIsoPi`, because the next step is
`AddEquiv.piCongrRight` and `piIsoPi`'s codomain is a bundled object.

**The inner product.** The Čech term evaluates the presheaf on `∏ᶜ (U ∘ x)`, a categorical
product in `Opens`, whereas the algebraic side names the open as a single basic open.
`piObj_polynomialVariableChart` identifies them: the product in `Opens` is the infimum (the
category is a complete lattice), and `basicOpen_polynomialVariableCechDenominator` already says
the infimum of the charts is the basic open of the product. This is an equality of opens, not
merely an isomorphism, so it transports through `eqToIso` rather than a comparison map.

**The coefficients.** `cechTermSectionAddEquiv` lands in the `Type`-valued sheaf, while the
Čech complex needs the `AddCommGrpCat`-valued presheaf. No conversion is required:
`associatedPresheafInAddCommGrp` is defined by bundling exactly that section type, so the two
are definitionally equal and the per-index equivalence is reused unchanged.

Degree `n` of the complex is *definitionally* the product over `Fin (n + 1) → ι` — no `dsimp`
or unfolding lemma is needed to expose it, and `AddCommGrpCat.piAddEquivPi` applies to it
directly.

**The differential.** `cechCochainsDegreewiseAddEquiv` compares one degree at a time;
`polynomialVariableCechComplex` carries the differential across it, so `d ∘ d = 0` and the
comparison isomorphism are both free, and the alternating-sum formula is a theorem about the
complex rather than an obligation inside its construction.

That formula is stated twice. `cechCochainsDegreewiseAddEquiv_d` reads Mathlib's differential
through the comparison, and `polynomialVariableCechComplex_d_apply` phrases the same fact
against the algebraic complex's own `d`. The first is the one to prove things with: the second
puts the equation under the complex's carrier coercion, where `.X n` is semireducible and
`CochainComplex.of.d` hides behind a `dite`, so a cochain has to be typed in the carrier rather
than in the bare `Pi` type for anything to rewrite.

## Tags

Čech complex, projective space, twisting sheaf, homogeneous localization
-/

noncomputable section

open CategoryTheory Limits DirectSum Opposite SetLike TopCat TopologicalSpace

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-- The variable basic-open cover of polynomial `Proj`: the chart where the `i`-th coordinate
is invertible. This is the cover the algebraic Čech terms are indexed by. -/
def polynomialVariableChart :
    ι → Opens (ProjectiveSpectrum.top (polynomialGrading ι k)) :=
  fun i => ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (MvPolynomial.X i)

/-- The `AddCommGrpCat`-valued presheaf of `O(d)` on polynomial `Proj`.

Mathlib's Čech complex is built from a presheaf valued in a preadditive category with products,
so the `Type`-valued sheaf that the section comparisons are stated against cannot be used
directly. Its underlying type is unchanged, which is what lets `cechTermSectionAddEquiv` be
reused here without a conversion step. -/
abbrev twistPresheaf (d : ℕ) :=
  associatedPresheafInAddCommGrp (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)

/-- The categorical product of the charts along a Čech index is the basic open of the product
denominator.

The product in `Opens` is the infimum, because the category is a complete lattice; the rest is
`basicOpen_polynomialVariableCechDenominator`. The conclusion is an equality of opens rather
than an isomorphism, which is what lets the presheaf be transported across it by `eqToIso`. -/
theorem piObj_polynomialVariableChart {n : ℕ} (x : Fin (n + 1) → ι) :
    (∏ᶜ (polynomialVariableChart ι k ∘ x)) =
      ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) := by
  rw [basicOpen_polynomialVariableCechDenominator]
  apply le_antisymm
  · exact le_iInf fun a => leOfHom (Pi.π (polynomialVariableChart ι k ∘ x) a)
  · exact leOfHom (Pi.lift fun a => homOfLE (iInf_le _ a))

/-- One index of the degreewise comparison: the sections of `O(d)` on the categorical product of
charts along `x`, identified with the explicit homogeneous localization at that index.

Two steps: the identification of the open (`piObj_polynomialVariableChart`, transported by
`eqToIso`) and the section comparison (`cechTermSectionAddEquiv`). -/
noncomputable def cechIndexEquiv (d : ℕ) {n : ℕ} (x : Fin (n + 1) → ι) :
    ((twistPresheaf ι k d).obj (op (∏ᶜ (polynomialVariableChart ι k ∘ x))) : AddCommGrpCat) ≃+
      polynomialVariableCechTerm ι k d n x :=
  (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W))
      (piObj_polynomialVariableChart ι k x))).addCommGroupIsoToAddEquiv.trans
    (cechTermSectionAddEquiv ι k d x).symm

/-- Degree `n` of the Čech complex of `O(d)` over the variable charts is the explicit product of
homogeneous degree-zero localizations.

The outer product is `AddCommGrpCat.piAddEquivPi` and each factor is `cechIndexEquiv`.
Degreewise only — the Čech differential is not claimed to correspond here. -/
def cechCochainsDegreewiseAddEquiv (d n : ℕ) :
    (((cechComplexFunctor (polynomialVariableChart ι k)).obj
        (twistPresheaf ι k d)).X n : AddCommGrpCat) ≃+
      polynomialVariableCechCochains ι k d n :=
  (AddCommGrpCat.piAddEquivPi _).trans
    (AddEquiv.piCongrRight fun x => cechIndexEquiv ι k d x)

/-- The degreewise comparison, read one index at a time: project, then compare that index.

Stated against `AddCommGrpCat.piAddEquivPi` rather than `Limits.Pi.π` because the latter needs
its family supplied explicitly to elaborate; `AddCommGrpCat.piIsoPi_hom_eval_apply` converts
between them where a caller actually needs the categorical projection. -/
theorem cechCochainsDegreewiseAddEquiv_apply (d n : ℕ)
    (t : (((cechComplexFunctor (polynomialVariableChart ι k)).obj
      (twistPresheaf ι k d)).X n : AddCommGrpCat)) (x : Fin (n + 1) → ι) :
    cechCochainsDegreewiseAddEquiv ι k d n t x =
      cechIndexEquiv ι k d x (AddCommGrpCat.piAddEquivPi _ t x) :=
  rfl

/-- The inverse comparison, read one index at a time. -/
theorem cechCochainsDegreewiseAddEquiv_symm_apply (d n : ℕ)
    (s : polynomialVariableCechCochains ι k d n) (x : Fin (n + 1) → ι) :
    AddCommGrpCat.piAddEquivPi _
        ((cechCochainsDegreewiseAddEquiv ι k d n).symm s) x =
      (cechIndexEquiv ι k d x).symm (s x) := by
  have h := cechCochainsDegreewiseAddEquiv_apply ι k d n
    ((cechCochainsDegreewiseAddEquiv ι k d n).symm s) x
  rw [AddEquiv.apply_symm_apply] at h
  exact ((AddEquiv.symm_apply_eq _).mpr h).symm

/-- The per-index square: the comparison carries a Čech face restriction to the algebraic face.

The morphism `g` is left arbitrary on purpose. It ranges over `Opens`, where there is at most
one morphism between two objects, so the face inclusion Mathlib's Čech nerve produces is *the*
morphism here and needs no separate identification — `Subsingleton.elim` supplies it. The two
`eqToHom`s identifying the categorical product of charts with the basic open of the denominator
collapse into the same `twistPresheaf.map`, leaving exactly the restriction that
`cechTermSectionAddEquiv_res_face` handles. -/
theorem cechIndexEquiv_map_face (d : ℕ) {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (g : (∏ᶜ (polynomialVariableChart ι k ∘ x)) ⟶
      ∏ᶜ (polynomialVariableChart ι k ∘ (x ∘ j.succAbove)))
    (w : ((twistPresheaf ι k d).obj
      (op (∏ᶜ (polynomialVariableChart ι k ∘ (x ∘ j.succAbove)))) : AddCommGrpCat)) :
    cechIndexEquiv ι k d x
        (ConcreteCategory.hom ((twistPresheaf ι k d).map g.op) w) =
      polynomialVariableCechFace ι k d x j
        (cechIndexEquiv ι k d (x ∘ j.succAbove) w) := by
  have hx := piObj_polynomialVariableChart ι k x
  have hy := piObj_polynomialVariableChart ι k (x ∘ j.succAbove)
  -- The restriction of sections that the algebraic face corresponds to.
  let i : (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k (x ∘ j.succAbove))) :
      (Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))ᵒᵖ) ⟶
      op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)) :=
    eqToHom (congrArg op hy.symm) ≫ g.op ≫ eqToHom (congrArg op hx)
  refine (AddEquiv.symm_apply_eq (cechTermSectionAddEquiv ι k d x)).mpr ?_
  rw [← cechTermSectionAddEquiv_res_face ι k d x j i
    (cechIndexEquiv ι k d (x ∘ j.succAbove) w)]
  have hEy : cechTermSectionAddEquiv ι k d (x ∘ j.succAbove)
      (cechIndexEquiv ι k d (x ∘ j.succAbove) w) =
      ((eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W))
        hy)).addCommGroupIsoToAddEquiv) w :=
    AddEquiv.apply_symm_apply _ _
  rw [hEy]
  -- Both sides are `twistPresheaf.map` of a morphism of opens applied to `w`; the two
  -- morphisms agree because `(Opens X)ᵒᵖ` is thin.
  have hmap : (twistPresheaf ι k d).map g.op ≫
      (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W)) hx)).hom =
      (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W)) hy)).hom ≫
        (twistPresheaf ι k d).map i := by
    have ex : (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W)) hx)).hom =
        (twistPresheaf ι k d).map (eqToHom (congrArg op hx)) := by
      rw [eqToHom_map]; rfl
    have ey : (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W)) hy)).hom =
        (twistPresheaf ι k d).map (eqToHom (congrArg op hy)) := by
      rw [eqToHom_map]; rfl
    rw [ex, ey, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  exact congrArg (fun m => (ConcreteCategory.hom m) w) hmap

/-! ## The explicit algebraic Čech complex

`cechCochainsDegreewiseAddEquiv` compares one degree at a time. Carrying the differential across
it turns that family of comparisons into an isomorphism of cochain complexes, which is what makes
`Hⁱ(Pⁿ, O(d))` the cohomology of a complex written in homogeneous localizations.

The differential is *defined* by transport rather than as an alternating sum. That is deliberate:
`d ∘ d = 0` and the comparison isomorphism are then both free, and the alternating-sum formula
becomes a separate lemma about this complex instead of a proof obligation inside its
construction. -/

/-- Mathlib's Čech complex of `O(d)` over the variable charts. -/
noncomputable abbrev cechComplexOfTwist (d : ℕ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechComplexFunctor (polynomialVariableChart ι k)).obj (twistPresheaf ι k d)

/-- The degreewise comparison, as an isomorphism of bundled abelian groups. -/
noncomputable def cechCochainsIso (d n : ℕ) :
    (cechComplexOfTwist ι k d).X n ≅
      AddCommGrpCat.of (polynomialVariableCechCochains ι k d n) :=
  (cechCochainsDegreewiseAddEquiv ι k d n).toAddCommGrpIso

/-- **The Čech differential in homogeneous localizations.** Reading Mathlib's Čech differential
through the degreewise comparison gives the alternating sum of the algebraic face maps.

This is the computable form of the differential, and it is stated against the comparison rather
than against `polynomialVariableCechComplex`'s own `d` on purpose: the latter puts the equation
under the complex's carrier coercion, where `.X n` is semireducible and neither `rw` nor `show`
reaches the `Pi` type being indexed. `polynomialVariableCechComplex_d_apply` derives that form
from this one, where `CochainComplex.of_d` applies to a morphism instead. -/
theorem cechCochainsDegreewiseAddEquiv_d (d n : ℕ)
    (t : ((cechComplexOfTwist ι k d).X n : AddCommGrpCat)) (x : Fin (n + 2) → ι) :
    cechCochainsDegreewiseAddEquiv ι k d (n + 1)
        (ConcreteCategory.hom ((cechComplexOfTwist ι k d).d n (n + 1)) t) x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j
          (cechCochainsDegreewiseAddEquiv ι k d n t (x ∘ j.succAbove)) := by
  rw [cechCochainsDegreewiseAddEquiv_apply]
  have hproj : AddCommGrpCat.piAddEquivPi _
      (ConcreteCategory.hom ((cechComplexOfTwist ι k d).d n (n + 1)) t) x =
      ConcreteCategory.hom ((cechComplexOfTwist ι k d).d n (n + 1) ≫ Limits.Pi.π _ x) t := by
    rw [ConcreteCategory.comp_apply]
    exact AddCommGrpCat.piIsoPi_hom_eval_apply _ x _
  rw [hproj]
  -- The generic coordinate formula, supplied as an equation so that unification rather than
  -- syntactic matching bridges the `HasProduct` instance and the `cechTermFamily` abbreviation.
  have hd : (cechComplexOfTwist ι k d).d n (n + 1) ≫ Limits.Pi.π _ x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Limits.Pi.π _ (((cechNerve (polynomialVariableChart ι k)).map
            (SimplexCategory.δ j).op).f x) ≫
          (twistPresheaf ι k d).map (((cechNerve (polynomialVariableChart ι k)).map
            (SimplexCategory.δ j).op).φ x).op) :=
    cechComplexFunctor_d_π _ _ x
  rw [hd]
  refine (congrArg (cechIndexEquiv ι k d x)
    (AddCommGrpCat.hom_sum_zsmul_apply Finset.univ
      (fun j : Fin (n + 2) => (-1 : ℤ) ^ (j : ℕ)) _ t)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  refine (congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • cechIndexEquiv ι k d x z)
    (ConcreteCategory.comp_apply _ _ t)).trans ?_
  refine (congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z)
    (cechIndexEquiv_map_face ι k d x j _ _)).trans ?_
  congr 2


/-- The algebraic Čech complex of `O(d)`: in degree `n`, the explicit product of degree-zero
homogeneous localizations, with the differential carried over from Mathlib's Čech complex. -/
noncomputable def polynomialVariableCechComplex (d : ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n => AddCommGrpCat.of (polynomialVariableCechCochains ι k d n))
    (fun n => (cechCochainsIso ι k d n).inv ≫
      (cechComplexOfTwist ι k d).d n (n + 1) ≫ (cechCochainsIso ι k d (n + 1)).hom)
    (fun n => by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc ((cechComplexOfTwist ι k d).d n (n + 1)),
        HomologicalComplex.d_comp_d, Limits.zero_comp, Limits.comp_zero])

/-- The Čech complex of `O(d)` over the variable charts *is* the explicit algebraic complex.

Composed with the Čech-to-derived comparison of
`DerivedAlgGeo.Topology.Sheaves.Cech.GlobalComparison`, this presents every
`Hⁱ(Pⁿ, O(d))` as the cohomology of a complex of homogeneous localizations. -/
noncomputable def polynomialVariableCechComplexIso (d : ℕ) :
    cechComplexOfTwist ι k d ≅ polynomialVariableCechComplex ι k d :=
  HomologicalComplex.Hom.isoOfComponents (fun n => cechCochainsIso ι k d n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp [polynomialVariableCechComplex, CochainComplex.of_d])

/-- The differential of the algebraic Čech complex, in coordinates.

The complex is defined by transport, so this is what makes it computable: `Hⁱ(Pⁿ, O(d))` is the
cohomology of a complex of homogeneous localizations whose differential is the alternating sum
of the explicit face maps.

`s` is taken in the complex's own carrier rather than in
`polynomialVariableCechCochains ι k d n`. The two are definitionally equal, but only the former
lets the differential be rewritten: `CochainComplex.of.d` hides behind a `dite` that only
`CochainComplex.of_d` opens, and with `s` typed as the bare `Pi` type the rewritten term fails
to be type-correct at `instances` transparency. -/
theorem polynomialVariableCechComplex_d_apply (d n : ℕ)
    (s : ((polynomialVariableCechComplex ι k d).X n : AddCommGrpCat))
    (x : Fin (n + 2) → ι) :
    ConcreteCategory.hom ((polynomialVariableCechComplex ι k d).d n (n + 1)) s x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableCechFace ι k d x j (s (x ∘ j.succAbove)) := by
  have hd : (polynomialVariableCechComplex ι k d).d n (n + 1) =
      (cechCochainsIso ι k d n).inv ≫ (cechComplexOfTwist ι k d).d n (n + 1) ≫
        (cechCochainsIso ι k d (n + 1)).hom := by
    simp [polynomialVariableCechComplex, CochainComplex.of_d]
  have happ := congrArg (fun m : (polynomialVariableCechComplex ι k d).X n ⟶
      (polynomialVariableCechComplex ι k d).X (n + 1) => ConcreteCategory.hom m s) hd
  refine (congrArg
    (fun z : polynomialVariableCechCochains ι k d (n + 1) => z x) happ).trans ?_
  show cechCochainsDegreewiseAddEquiv ι k d (n + 1)
      (ConcreteCategory.hom ((cechComplexOfTwist ι k d).d n (n + 1))
        (ConcreteCategory.hom (cechCochainsIso ι k d n).inv s)) x = _
  rw [cechCochainsDegreewiseAddEquiv_d]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact congrArg (fun z : polynomialVariableCechCochains ι k d n => z (x ∘ j.succAbove))
    ((cechCochainsDegreewiseAddEquiv ι k d n).apply_symm_apply s)

/-! ## The same complex for a twist of either sign

Everything above is repeated for `d : ℤ`. Nothing in this layer knows about the sign: the three
shape mismatches recorded in the module docstring — the outer product, the inner product, and the
coefficients — are all statements about the *cover*, and `piObj_polynomialVariableChart` is
therefore reused verbatim rather than restated. The only twist-dependent inputs are the section
comparison `intCechTermSectionAddEquiv` and its face compatibility
`intCechTermSectionAddEquiv_res_face`, and both are already proved with the sign absorbed.

This is the layer `#332`'s dévissage consumes. The nonnegative layer above is not a special case
of it — `natShift` and `intShift` are different graded families, related only by transport — so
it is kept as it stands and `#340`'s vanishing theorem continues to read it. -/

/-- The `AddCommGrpCat`-valued presheaf of `O(d)` for an integer twist. -/
abbrev intTwistPresheaf (d : ℤ) :=
  associatedPresheafInAddCommGrp (polynomialGrading ι k)
    (intShift (polynomialGrading ι k) d)

/-- One index of the degreewise comparison, for an integer twist. -/
noncomputable def intCechIndexEquiv (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) :
    ((intTwistPresheaf ι k d).obj (op (∏ᶜ (polynomialVariableChart ι k ∘ x))) :
        AddCommGrpCat) ≃+
      polynomialVariableIntCechTerm ι k d n x :=
  (eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W))
      (piObj_polynomialVariableChart ι k x))).addCommGroupIsoToAddEquiv.trans
    (intCechTermSectionAddEquiv ι k d x).symm

/-- Degree `n` of the Čech complex of an integer twist `O(d)` over the variable charts is the
explicit product of homogeneous degree-zero localizations. -/
def intCechCochainsDegreewiseAddEquiv (d : ℤ) (n : ℕ) :
    (((cechComplexFunctor (polynomialVariableChart ι k)).obj
        (intTwistPresheaf ι k d)).X n : AddCommGrpCat) ≃+
      polynomialVariableIntCechCochains ι k d n :=
  (AddCommGrpCat.piAddEquivPi _).trans
    (AddEquiv.piCongrRight fun x => intCechIndexEquiv ι k d x)

/-- The degreewise comparison, read one index at a time. -/
theorem intCechCochainsDegreewiseAddEquiv_apply (d : ℤ) (n : ℕ)
    (t : (((cechComplexFunctor (polynomialVariableChart ι k)).obj
      (intTwistPresheaf ι k d)).X n : AddCommGrpCat)) (x : Fin (n + 1) → ι) :
    intCechCochainsDegreewiseAddEquiv ι k d n t x =
      intCechIndexEquiv ι k d x (AddCommGrpCat.piAddEquivPi _ t x) :=
  rfl

/-- The inverse comparison, read one index at a time. -/
theorem intCechCochainsDegreewiseAddEquiv_symm_apply (d : ℤ) (n : ℕ)
    (s : polynomialVariableIntCechCochains ι k d n) (x : Fin (n + 1) → ι) :
    AddCommGrpCat.piAddEquivPi _
        ((intCechCochainsDegreewiseAddEquiv ι k d n).symm s) x =
      (intCechIndexEquiv ι k d x).symm (s x) := by
  have h := intCechCochainsDegreewiseAddEquiv_apply ι k d n
    ((intCechCochainsDegreewiseAddEquiv ι k d n).symm s) x
  rw [AddEquiv.apply_symm_apply] at h
  exact ((AddEquiv.symm_apply_eq _).mpr h).symm

/-- The per-index square for an integer twist: the comparison carries a Čech face restriction to
the algebraic face. As in the nonnegative case, `g` is arbitrary because `Opens` is thin. -/
theorem intCechIndexEquiv_map_face (d : ℤ) {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2))
    (g : (∏ᶜ (polynomialVariableChart ι k ∘ x)) ⟶
      ∏ᶜ (polynomialVariableChart ι k ∘ (x ∘ j.succAbove)))
    (w : ((intTwistPresheaf ι k d).obj
      (op (∏ᶜ (polynomialVariableChart ι k ∘ (x ∘ j.succAbove)))) : AddCommGrpCat)) :
    intCechIndexEquiv ι k d x
        (ConcreteCategory.hom ((intTwistPresheaf ι k d).map g.op) w) =
      polynomialVariableIntCechFace ι k d x j
        (intCechIndexEquiv ι k d (x ∘ j.succAbove) w) := by
  have hx := piObj_polynomialVariableChart ι k x
  have hy := piObj_polynomialVariableChart ι k (x ∘ j.succAbove)
  let i : (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k (x ∘ j.succAbove))) :
      (Opens (ProjectiveSpectrum.top (polynomialGrading ι k)))ᵒᵖ) ⟶
      op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)) :=
    eqToHom (congrArg op hy.symm) ≫ g.op ≫ eqToHom (congrArg op hx)
  refine (AddEquiv.symm_apply_eq (intCechTermSectionAddEquiv ι k d x)).mpr ?_
  rw [← intCechTermSectionAddEquiv_res_face ι k d x j i
    (intCechIndexEquiv ι k d (x ∘ j.succAbove) w)]
  have hEy : intCechTermSectionAddEquiv ι k d (x ∘ j.succAbove)
      (intCechIndexEquiv ι k d (x ∘ j.succAbove) w) =
      ((eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W))
        hy)).addCommGroupIsoToAddEquiv) w :=
    AddEquiv.apply_symm_apply _ _
  rw [hEy]
  have hmap : (intTwistPresheaf ι k d).map g.op ≫
      (eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W)) hx)).hom =
      (eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W)) hy)).hom ≫
        (intTwistPresheaf ι k d).map i := by
    have ex : (eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W)) hx)).hom =
        (intTwistPresheaf ι k d).map (eqToHom (congrArg op hx)) := by
      rw [eqToHom_map]; rfl
    have ey : (eqToIso (congrArg (fun W => (intTwistPresheaf ι k d).obj (op W)) hy)).hom =
        (intTwistPresheaf ι k d).map (eqToHom (congrArg op hy)) := by
      rw [eqToHom_map]; rfl
    rw [ex, ey, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  exact congrArg (fun m => (ConcreteCategory.hom m) w) hmap

/-- Mathlib's Čech complex of an integer twist `O(d)` over the variable charts. -/
noncomputable abbrev intCechComplexOfTwist (d : ℤ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechComplexFunctor (polynomialVariableChart ι k)).obj (intTwistPresheaf ι k d)

/-- The degreewise comparison for an integer twist, as an isomorphism of bundled abelian
groups. -/
noncomputable def intCechCochainsIso (d : ℤ) (n : ℕ) :
    (intCechComplexOfTwist ι k d).X n ≅
      AddCommGrpCat.of (polynomialVariableIntCechCochains ι k d n) :=
  (intCechCochainsDegreewiseAddEquiv ι k d n).toAddCommGrpIso

/-- **The Čech differential of an integer twist in homogeneous localizations.** -/
theorem intCechCochainsDegreewiseAddEquiv_d (d : ℤ) (n : ℕ)
    (t : ((intCechComplexOfTwist ι k d).X n : AddCommGrpCat)) (x : Fin (n + 2) → ι) :
    intCechCochainsDegreewiseAddEquiv ι k d (n + 1)
        (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1)) t) x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableIntCechFace ι k d x j
          (intCechCochainsDegreewiseAddEquiv ι k d n t (x ∘ j.succAbove)) := by
  rw [intCechCochainsDegreewiseAddEquiv_apply]
  have hproj : AddCommGrpCat.piAddEquivPi _
      (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1)) t) x =
      ConcreteCategory.hom
        ((intCechComplexOfTwist ι k d).d n (n + 1) ≫ Limits.Pi.π _ x) t := by
    rw [ConcreteCategory.comp_apply]
    exact AddCommGrpCat.piIsoPi_hom_eval_apply _ x _
  rw [hproj]
  have hd : (intCechComplexOfTwist ι k d).d n (n + 1) ≫ Limits.Pi.π _ x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Limits.Pi.π _ (((cechNerve (polynomialVariableChart ι k)).map
            (SimplexCategory.δ j).op).f x) ≫
          (intTwistPresheaf ι k d).map (((cechNerve (polynomialVariableChart ι k)).map
            (SimplexCategory.δ j).op).φ x).op) :=
    cechComplexFunctor_d_π _ _ x
  rw [hd]
  refine (congrArg (intCechIndexEquiv ι k d x)
    (AddCommGrpCat.hom_sum_zsmul_apply Finset.univ
      (fun j : Fin (n + 2) => (-1 : ℤ) ^ (j : ℕ)) _ t)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  refine (congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • intCechIndexEquiv ι k d x z)
    (ConcreteCategory.comp_apply _ _ t)).trans ?_
  refine (congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z)
    (intCechIndexEquiv_map_face ι k d x j _ _)).trans ?_
  congr 2

/-- The algebraic Čech complex of an integer twist `O(d)`, with the differential carried over
from Mathlib's Čech complex. -/
noncomputable def polynomialVariableIntCechComplex (d : ℤ) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun n => AddCommGrpCat.of (polynomialVariableIntCechCochains ι k d n))
    (fun n => (intCechCochainsIso ι k d n).inv ≫
      (intCechComplexOfTwist ι k d).d n (n + 1) ≫ (intCechCochainsIso ι k d (n + 1)).hom)
    (fun n => by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc ((intCechComplexOfTwist ι k d).d n (n + 1)),
        HomologicalComplex.d_comp_d, Limits.zero_comp, Limits.comp_zero])

/-- The Čech complex of an integer twist `O(d)` over the variable charts *is* the explicit
algebraic complex. -/
noncomputable def polynomialVariableIntCechComplexIso (d : ℤ) :
    intCechComplexOfTwist ι k d ≅ polynomialVariableIntCechComplex ι k d :=
  HomologicalComplex.Hom.isoOfComponents (fun n => intCechCochainsIso ι k d n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp [polynomialVariableIntCechComplex, CochainComplex.of_d])

/-- The differential of the algebraic Čech complex of an integer twist, in coordinates. -/
theorem polynomialVariableIntCechComplex_d_apply (d : ℤ) (n : ℕ)
    (s : ((polynomialVariableIntCechComplex ι k d).X n : AddCommGrpCat))
    (x : Fin (n + 2) → ι) :
    ConcreteCategory.hom ((polynomialVariableIntCechComplex ι k d).d n (n + 1)) s x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        polynomialVariableIntCechFace ι k d x j (s (x ∘ j.succAbove)) := by
  have hd : (polynomialVariableIntCechComplex ι k d).d n (n + 1) =
      (intCechCochainsIso ι k d n).inv ≫ (intCechComplexOfTwist ι k d).d n (n + 1) ≫
        (intCechCochainsIso ι k d (n + 1)).hom := by
    simp [polynomialVariableIntCechComplex, CochainComplex.of_d]
  have happ := congrArg (fun m : (polynomialVariableIntCechComplex ι k d).X n ⟶
      (polynomialVariableIntCechComplex ι k d).X (n + 1) => ConcreteCategory.hom m s) hd
  refine (congrArg
    (fun z : polynomialVariableIntCechCochains ι k d (n + 1) => z x) happ).trans ?_
  show intCechCochainsDegreewiseAddEquiv ι k d (n + 1)
      (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1))
        (ConcreteCategory.hom (intCechCochainsIso ι k d n).inv s)) x = _
  rw [intCechCochainsDegreewiseAddEquiv_d]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact congrArg (fun z : polynomialVariableIntCechCochains ι k d n => z (x ∘ j.succAbove))
    ((intCechCochainsDegreewiseAddEquiv ι k d n).apply_symm_apply s)

end AlgebraicGeometry.Proj
