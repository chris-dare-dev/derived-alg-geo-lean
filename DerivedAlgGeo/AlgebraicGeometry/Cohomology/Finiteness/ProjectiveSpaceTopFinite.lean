/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceCechHomology
import DerivedAlgGeo.Algebra.MvPolynomial.Cech.Finite

/-!
# `Hⁱ(Pⁿ, O(d))` is finite-dimensional in every positive degree

`Cech/Vanishing.lean` kills every degree whose tuples are too short to meet all the variables, by
contracting every Laurent block. The top degree is exactly where that fails, and
`Cech/TopDegree.lean` separates the surviving block instead: every class is carried by the full
block. `Algebra/MvPolynomial/Cech/Finite.lean` shows those full blocks form a
finite-dimensional `k`-space. This file joins the algebraic result to the geometric Čech complex
and discharges the finiteness interface.

## The argument

`intCechBlockCocycles` is the space of full-block cocycles of a degree — a submodule of the
finite-dimensional space of full-block cochains, hence finite-dimensional. `intCechBlockClass`
sends such a cocycle to its cohomology class, and the two halves are:

* `intCechBlockSmul_comp_class` — the class map is `k`-linear. The action on cohomology is the map
  a sheaf endomorphism induces, so this is `homologyπ` naturality once the cycle map is known to
  intertwine the actions, which is `intCechCochainsDegreewiseAddEquiv_smul` from the file below;
* `intCechBlockClass_surjective` — it is onto. `exists_fullBlock_add_coboundary` splits a cocycle
  into its full block and a coboundary; the full block is again a cocycle and lands in
  `cechBlockSpan`, and the coboundary dies in homology by `toCycles_comp_homologyπ`.

`Module.Finite.of_surjective` then gives finiteness on the Čech side, and
`module_finite_linearCoherentH_of_cech` carries it to the group the interface names.

## Two spellings that have to be pinned

`cechCohomologyFunctor` takes its space as an *implicit* argument, and `cechCohomologyModule`
supplies the module instance at whatever spelling its `U` was elaborated with. Writing the chart
family as `polynomialVariableChart ι k` fixes that space to `ProjectiveSpectrum.top _`, while the
finiteness interface asks for `Y`; the two are definitionally equal, so the instance is
inhabited, and *not* reducibly so, so instance search never finds it. `intChart` and
`intTwistModules` are the same objects presented at the variety, and they exist only to make the
one instance search meets be the one that is there. This is the transparency rule of
`.claude/references/instance-transparency.md`, technique 5.

The same effect appears twice more, and is handled the same way: the `AddCommGroup`, `Module` and
`Module.Finite` instances on `intCechBlockCocycles` are named rather than searched for, because it
is a submodule of a product of submodules and search will not assemble that on its own.

## Scope

**Positive degrees only.** `exists_fullBlock_add_coboundary` splits a cocycle in degree `n + 1`,
and the splitting is useful because the remainder is a coboundary — which needs a degree below.
Degree `0` has none, and `H⁰` is not a subquotient but the module of global sections outright; its
finiteness is the finite-dimensionality of a graded piece of the polynomial ring and is a separate
argument. So `Hⁿ(Pⁿ, O(d))` is covered for every `n ≥ 1`, at either sign of `d`, and `P⁰` is not.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace CategoryTheory.Limits

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

theorem intCechCochainsDegreewiseAddEquiv_symm_smul (d : ℤ) (n : ℕ) (r : k)
    (s : polynomialVariableIntCechCochains ι k d n) :
    (intCechCochainsDegreewiseAddEquiv ι k d n).symm (r • s) =
      ConcreteCategory.hom (((cechComplexFunctor (polynomialVariableChart ι k)).map
        (intTwistScalarHom ι k d r)).f n)
        ((intCechCochainsDegreewiseAddEquiv ι k d n).symm s) := by
  apply (intCechCochainsDegreewiseAddEquiv ι k d n).injective
  rw [AddEquiv.apply_symm_apply, intCechCochainsDegreewiseAddEquiv_smul,
    AddEquiv.apply_symm_apply]

set_option maxHeartbeats 400000 in
/-- The abstract cocycle condition, read as the explicit alternating sum. -/
theorem intCech_d_apply_eq_zero_iff (d : ℤ) (n : ℕ)
    (t : ((intCechComplexOfTwist ι k d).X n : AddCommGrpCat)) :
    ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1)) t = 0 ↔
      ∀ x : Fin (n + 2) → ι,
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          cechFace ι k (intShift (polynomialGrading ι k) d) x j
            (intCechCochainsDegreewiseAddEquiv ι k d n t (x ∘ j.succAbove)) = 0 := by
  constructor
  · intro h x
    refine Eq.trans (intCechCochainsDegreewiseAddEquiv_d ι k d n t x).symm ?_
    rw [h, map_zero]
    rfl
  · intro h
    apply (intCechCochainsDegreewiseAddEquiv ι k d (n + 1)).injective
    rw [map_zero]
    funext x
    exact (intCechCochainsDegreewiseAddEquiv_d ι k d n t x).trans (h x)

/-- The full blocks of a Čech degree, included into all cochains.

No finiteness of `ι` is needed: `cechBlockSpan` is defined without it, and only its finite
generation is not. -/
noncomputable def intCechBlockIncl (d : ℤ) (n : ℕ) :
    (∀ x : Fin (n + 1) → ι,
        ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) →ₗ[k]
      polynomialVariableIntCechCochains ι k d n where
  toFun s := fun x => (s x : polynomialVariableIntCechTerm ι k d n x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in
/-- The Čech differential, read on full-block cochains through the degreewise comparison.

`k`-linearity is not assumed of the explicit differential: it is `intCechCochainsDegreewiseAddEquiv`
linearity on both sides of the chain-map square that the scalar endomorphism satisfies. -/
noncomputable def intCechBlockD (d : ℤ) (n : ℕ) :
    (∀ x : Fin (n + 1) → ι,
        ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) →ₗ[k]
      polynomialVariableIntCechCochains ι k d (n + 1) where
  toFun b := intCechCochainsDegreewiseAddEquiv ι k d (n + 1)
    (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1))
      ((intCechCochainsDegreewiseAddEquiv ι k d n).symm (intCechBlockIncl ι k d n b)))
  map_add' a b := by rw [map_add, map_add, map_add, map_add]
  map_smul' r b := by
    show intCechCochainsDegreewiseAddEquiv ι k d (n + 1)
        (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1))
          ((intCechCochainsDegreewiseAddEquiv ι k d n).symm
            (intCechBlockIncl ι k d n (r • b)))) = _
    rw [map_smul, intCechCochainsDegreewiseAddEquiv_symm_smul]
    have hcomm := congrArg (fun m : ((intCechComplexOfTwist ι k d).X n ⟶
        (intCechComplexOfTwist ι k d).X (n + 1)) => ConcreteCategory.hom m
        ((intCechCochainsDegreewiseAddEquiv ι k d n).symm (intCechBlockIncl ι k d n b)))
      (((cechComplexFunctor (polynomialVariableChart ι k)).map
        (intTwistScalarHom ι k d r)).comm n (n + 1))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hcomm
    rw [hcomm, intCechCochainsDegreewiseAddEquiv_smul]
    rfl

/-- The full-block cocycles of a Čech degree. -/
noncomputable def intCechBlockCocycles (d : ℤ) (n : ℕ) :
    Submodule k (∀ x : Fin (n + 1) → ι,
      ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) :=
  LinearMap.ker (intCechBlockD ι k d n)

noncomputable instance addCommGroupIntCechBlockCocycles (d : ℤ) (n : ℕ) :
    AddCommGroup ↥(intCechBlockCocycles ι k d n) :=
  Submodule.addCommGroup (M := ∀ x : Fin (n + 1) → ι,
    ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) _

noncomputable instance moduleIntCechBlockCocycles (d : ℤ) (n : ℕ) :
    Module k ↥(intCechBlockCocycles ι k d n) :=
  Submodule.module (M := ∀ x : Fin (n + 1) → ι,
    ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) _

instance module_finite_intCechBlockCocycles [Fintype ι] (d : ℤ) (n : ℕ) :
    Module.Finite k ↥(intCechBlockCocycles ι k d n) :=
  FiniteDimensional.finiteDimensional_submodule (K := k) (V := ∀ x : Fin (n + 1) → ι,
    ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d x)) _

/-- A full-block cocycle, as a map of abelian groups into the Čech cochains.

Built as a composite of maps that already exist, so `map_add` and `map_zero` come for free. -/
noncomputable def intCechBlockCocycleHom (d : ℤ) (n : ℕ) :
    AddCommGrpCat.of ↥(intCechBlockCocycles ι k d n) ⟶ (intCechComplexOfTwist ι k d).X n :=
  AddCommGrpCat.ofHom
    (((intCechCochainsDegreewiseAddEquiv ι k d n).symm.toAddMonoidHom.comp
        (intCechBlockIncl ι k d n).toAddMonoidHom).comp
      (intCechBlockCocycles ι k d n).subtype.toAddMonoidHom)

theorem intCechBlockCocycleHom_apply (d : ℤ) (n : ℕ)
    (b : ↥(intCechBlockCocycles ι k d n)) :
    ConcreteCategory.hom (intCechBlockCocycleHom ι k d n) b =
      (intCechCochainsDegreewiseAddEquiv ι k d n).symm
        (intCechBlockIncl ι k d n b.1) := rfl

set_option maxHeartbeats 400000 in
theorem intCechBlockCocycleHom_comp_d (d : ℤ) (n : ℕ) :
    intCechBlockCocycleHom ι k d n ≫ (intCechComplexOfTwist ι k d).d n (n + 1) = 0 := by
  ext b
  show ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1))
      ((intCechCochainsDegreewiseAddEquiv ι k d n).symm
        (intCechBlockIncl ι k d n b.1)) = 0
  refine (intCechCochainsDegreewiseAddEquiv ι k d (n + 1)).injective ?_
  exact (b.2 : intCechBlockD ι k d n b.1 = 0).trans (map_zero _).symm

set_option maxHeartbeats 400000 in
/-- The cycle a full-block cocycle determines. -/
noncomputable def intCechBlockCycle (d : ℤ) (n : ℕ) :
    AddCommGrpCat.of ↥(intCechBlockCocycles ι k d n) ⟶
      (intCechComplexOfTwist ι k d).cycles n :=
  (intCechComplexOfTwist ι k d).liftCycles (intCechBlockCocycleHom ι k d n) (n + 1)
    (CochainComplex.next ℕ n) (intCechBlockCocycleHom_comp_d ι k d n)

set_option maxHeartbeats 400000 in
theorem intCechBlockCycle_i (d : ℤ) (n : ℕ) :
    intCechBlockCycle ι k d n ≫ (intCechComplexOfTwist ι k d).iCycles n =
      intCechBlockCocycleHom ι k d n :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

set_option maxHeartbeats 400000 in
/-- The class of a full-block cocycle in Čech cohomology. -/
noncomputable def intCechBlockClass (d : ℤ) (n : ℕ) :
    AddCommGrpCat.of ↥(intCechBlockCocycles ι k d n) ⟶
      (intCechComplexOfTwist ι k d).homology n :=
  intCechBlockCycle ι k d n ≫ (intCechComplexOfTwist ι k d).homologyπ n

/-- Scalar multiplication on the full-block cocycles, as a map of abelian groups. -/
noncomputable def intCechBlockSmul (d : ℤ) (n : ℕ) (r : k) :
    AddCommGrpCat.of ↥(intCechBlockCocycles ι k d n) ⟶
      AddCommGrpCat.of ↥(intCechBlockCocycles ι k d n) :=
  AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom _ r)

set_option maxHeartbeats 1000000 in
theorem intCechBlockSmul_comp_cocycleHom (d : ℤ) (n : ℕ) (r : k) :
    intCechBlockSmul ι k d n r ≫ intCechBlockCocycleHom ι k d n =
      intCechBlockCocycleHom ι k d n ≫
        ((cechComplexFunctor (polynomialVariableChart ι k)).map
          (intTwistScalarHom ι k d r)).f n := by
  ext b
  show (intCechCochainsDegreewiseAddEquiv ι k d n).symm
      (intCechBlockIncl ι k d n (r • b.1)) = _
  rw [map_smul, intCechCochainsDegreewiseAddEquiv_symm_smul]
  rfl

/-- The cycle a full-block cocycle determines intertwines the two scalar actions.

set_option maxHeartbeats 1000000 in
Reduced to `iCycles` by monomorphism, where it is `intCechBlockSmul_comp_cocycleHom`. -/
theorem intCechBlockSmul_comp_cycle (d : ℤ) (n : ℕ) (r : k) :
    intCechBlockSmul ι k d n r ≫ intCechBlockCycle ι k d n =
      intCechBlockCycle ι k d n ≫
        HomologicalComplex.cyclesMap ((cechComplexFunctor (polynomialVariableChart ι k)).map
          (intTwistScalarHom ι k d r)) n := by
  rw [← cancel_mono ((intCechComplexOfTwist ι k d).iCycles n), Category.assoc, Category.assoc,
    intCechBlockCycle_i, HomologicalComplex.cyclesMap_i, ← Category.assoc, intCechBlockCycle_i]
  exact intCechBlockSmul_comp_cocycleHom ι k d n r

/-- **The class map is `k`-linear.**

set_option maxHeartbeats 1000000 in
The action on cohomology is the map the sheaf endomorphism induces, so this is `homologyπ`
naturality once the cycle map is known to intertwine the actions. -/
theorem intCechBlockSmul_comp_class (d : ℤ) (n : ℕ) (r : k) :
    intCechBlockSmul ι k d n r ≫ intCechBlockClass ι k d n =
      intCechBlockClass ι k d n ≫ HomologicalComplex.homologyMap
        ((cechComplexFunctor (polynomialVariableChart ι k)).map
          (intTwistScalarHom ι k d r)) n := by
  rw [intCechBlockClass, ← Category.assoc, intCechBlockSmul_comp_cycle, Category.assoc,
    Category.assoc, HomologicalComplex.homologyπ_naturality]

set_option maxHeartbeats 4000000 in
/-- **Every class is the class of a full-block cocycle.**

`exists_fullBlock_add_coboundary` splits a cocycle into its full block and a coboundary; the full
block is again a cocycle and lies in `cechBlockSpan`, and the coboundary dies in homology. -/
theorem intCechBlockClass_surjective [Fintype ι] (d : ℤ) (n : ℕ) :
    Function.Surjective
      (ConcreteCategory.hom (intCechBlockClass ι k d (n + 1))) := by
  classical
  intro h
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective
    ((intCechComplexOfTwist ι k d).homologyπ (n + 1))).mp inferInstance h
  set w := ConcreteCategory.hom ((intCechComplexOfTwist ι k d).iCycles (n + 1)) z with hw
  have hdw : ConcreteCategory.hom
      ((intCechComplexOfTwist ι k d).d (n + 1) (n + 1 + 1)) w = 0 := by
    rw [hw, ← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  set s := intCechCochainsDegreewiseAddEquiv ι k d (n + 1) w with hs_def
  have hs := (intCech_d_apply_eq_zero_iff ι k d (n + 1) w).mp hdw
  obtain ⟨p, hp⟩ := exists_fullBlock_add_coboundary ι k d s hs
  set b : ∀ y : Fin (n + 1 + 1) → ι,
      ↥(cechBlockSpan ι k (intShift (polynomialGrading ι k) d) d y) := fun y =>
    ⟨intCechFullBlock ι k d s y,
      cechBlockProj_mem_cechBlockSpan ι k _
        (isPolynomialTwist_intShift (R := k) d) y (s y)⟩ with hb_def
  have hincl : intCechBlockIncl ι k d (n + 1) b = intCechFullBlock ι k d s := rfl
  have hbmem : b ∈ intCechBlockCocycles ι k d (n + 1) := by
    show intCechBlockD ι k d (n + 1) b = 0
    refine Eq.trans (congrArg (intCechCochainsDegreewiseAddEquiv ι k d (n + 1 + 1))
      ((intCech_d_apply_eq_zero_iff ι k d (n + 1) _).mpr ?_)) (map_zero _)
    intro x
    rw [(intCechCochainsDegreewiseAddEquiv ι k d (n + 1)).apply_symm_apply, hincl]
    exact intCechFullBlock_cocycle ι k d s hs x
  refine ⟨⟨b, hbmem⟩, ?_⟩
  set q := (intCechCochainsDegreewiseAddEquiv ι k d n).symm p with hq_def
  have hdq : intCechCochainsDegreewiseAddEquiv ι k d (n + 1)
      (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1)) q) =
      s - intCechFullBlock ι k d s := by
    funext x
    rw [intCechCochainsDegreewiseAddEquiv_d, hq_def,
      (intCechCochainsDegreewiseAddEquiv ι k d n).apply_symm_apply]
    have hx := hp x
    show _ = s x - intCechFullBlock ι k d s x
    rw [hx]
    abel
  have hcyc_i : ConcreteCategory.hom ((intCechComplexOfTwist ι k d).iCycles (n + 1))
      (ConcreteCategory.hom (intCechBlockCycle ι k d (n + 1)) ⟨b, hbmem⟩) =
      ConcreteCategory.hom (intCechBlockCocycleHom ι k d (n + 1)) ⟨b, hbmem⟩ :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      (congrArg (fun m : AddCommGrpCat.of ↥(intCechBlockCocycles ι k d (n + 1)) ⟶
          (intCechComplexOfTwist ι k d).X (n + 1) => ConcreteCategory.hom m ⟨b, hbmem⟩)
        (intCechBlockCycle_i ι k d (n + 1)))
  have htoC_i : ConcreteCategory.hom ((intCechComplexOfTwist ι k d).iCycles (n + 1))
      (ConcreteCategory.hom ((intCechComplexOfTwist ι k d).toCycles n (n + 1)) q) =
      ConcreteCategory.hom ((intCechComplexOfTwist ι k d).d n (n + 1)) q :=
    (ConcreteCategory.comp_apply _ _ q).symm.trans
      (congrArg (fun m : (intCechComplexOfTwist ι k d).X n ⟶
          (intCechComplexOfTwist ι k d).X (n + 1) => ConcreteCategory.hom m q)
        (HomologicalComplex.toCycles_i _ _ _))
  have hsplit : z - ConcreteCategory.hom (intCechBlockCycle ι k d (n + 1)) ⟨b, hbmem⟩ =
      ConcreteCategory.hom ((intCechComplexOfTwist ι k d).toCycles n (n + 1)) q := by
    refine (AddCommGrpCat.mono_iff_injective
      ((intCechComplexOfTwist ι k d).iCycles (n + 1))).mp inferInstance ?_
    rw [map_sub, hcyc_i, htoC_i]
    refine (intCechCochainsDegreewiseAddEquiv ι k d (n + 1)).injective ?_
    rw [map_sub, hdq]
    refine congrArg₂ (· - ·) hs_def.symm ?_
    exact ((intCechCochainsDegreewiseAddEquiv ι k d (n + 1)).apply_symm_apply _).trans hincl
  have hbound : ConcreteCategory.hom ((intCechComplexOfTwist ι k d).homologyπ (n + 1))
      (z - ConcreteCategory.hom (intCechBlockCycle ι k d (n + 1)) ⟨b, hbmem⟩) = 0 := by
    rw [hsplit]
    refine Eq.trans (ConcreteCategory.comp_apply _ _ q).symm ?_
    exact congrArg (fun m : (intCechComplexOfTwist ι k d).X n ⟶
        (intCechComplexOfTwist ι k d).homology (n + 1) => ConcreteCategory.hom m q)
      (HomologicalComplex.toCycles_comp_homologyπ _ _ _)
  rw [map_sub, sub_eq_zero] at hbound
  rw [← hz]
  exact (ConcreteCategory.comp_apply _ _ _).trans hbound.symm

/-- The twist `O(d)` as a sheaf of modules on projective space *as a variety*.

The type ascription is the point: `associatedSheaf` lands in `(Proj 𝒜).Modules`, and the finiteness
interface asks for `Y.Modules`. Those are the same term,
but only the second spelling lets `cechCohomologyModule`'s instance be found. -/
noncomputable abbrev intTwistModules (d : ℤ) :
    (Proj (polynomialGrading ι k)).Modules :=
  associatedSheaf (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)

/-- The variable charts, typed as opens of the *variety*.

Same ascription trick as `intTwistModules`: `cechCohomologyFunctor` takes its space as an implicit
argument, so the chart family has to be presented at `Y` for the module instance
`cechCohomologyModule` supplies to be the one instance search meets. -/
noncomputable abbrev intChart : ι → Opens (Proj (polynomialGrading ι k)) :=
  polynomialVariableChart ι k

set_option maxHeartbeats 1000000 in
/-- **The class map, as a `k`-linear map into Čech cohomology.** -/
noncomputable def intCechBlockClassLinear (d : ℤ) (n : ℕ) :
    letI := Cohomology.cechCohomologyModule k (Proj (polynomialGrading ι k))
      (intTwistModules ι k d) (intChart ι k) (n + 1)
    ↥(intCechBlockCocycles ι k d (n + 1)) →ₗ[k]
      ((Cohomology.cechCohomologyFunctor (intChart ι k) (n + 1)).obj
        ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf
          (Proj (polynomialGrading ι k))).obj (intTwistModules ι k d))) :=
  letI := Cohomology.cechCohomologyModule k (Proj (polynomialGrading ι k))
    (intTwistModules ι k d) (intChart ι k) (n + 1)
  { toFun := fun b => ConcreteCategory.hom (intCechBlockClass ι k d (n + 1)) b
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r b => by
      have hb := congrArg
        (fun m : AddCommGrpCat.of ↥(intCechBlockCocycles ι k d (n + 1)) ⟶
            (intCechComplexOfTwist ι k d).homology (n + 1) => ConcreteCategory.hom m b)
        (intCechBlockSmul_comp_class ι k d (n + 1) r)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hb
      exact hb }

set_option maxHeartbeats 1000000 in
/-- **`Hⁿ⁺¹` of an integer twist is finite-dimensional, on the Čech side.** -/
theorem module_finite_cechCohomology_intTwist [Fintype ι] (d : ℤ) (n : ℕ) :
    letI := Cohomology.cechCohomologyModule k (Proj (polynomialGrading ι k))
      (intTwistModules ι k d) (intChart ι k) (n + 1)
    Module.Finite k
      ((Cohomology.cechCohomologyFunctor (intChart ι k) (n + 1)).obj
        ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf
          (Proj (polynomialGrading ι k))).obj (intTwistModules ι k d))) :=
  letI := Cohomology.cechCohomologyModule k (Proj (polynomialGrading ι k))
    (intTwistModules ι k d) (intChart ι k) (n + 1)
  Module.Finite.of_surjective (intCechBlockClassLinear ι k d n)
    (intCechBlockClass_surjective ι k d n)

/-- **`Hⁿ⁺¹(Pⁿ, O(d))` is a finite-dimensional `k`-vector space.**

The interface group is `linearCoherentH`, and the finite spanning set lives on the Čech side;
`module_finite_linearCoherentH_of_cech` carries it across, and it is the `k`-linearity of the
comparison that makes the transfer legitimate.

set_option maxHeartbeats 1000000 in
The injective resolution is chosen rather than supplied: the site of opens is small, so
`canonicalInjectiveResolution` produces one. The `HasExt` witness is instantiated at
`HasExt.standard _`, which is the reconciliation `module_finite_linearCoherentH_of_cech`'s
docstring describes. -/
theorem module_finite_linearCoherentH_projectiveSpaceTwist [Fintype ι] (d : ℤ) (n : ℕ) :
    Module.Finite k ((Cohomology.linearCoherentH k (Proj (polynomialGrading ι k)) (n + 1)).obj
      (projectiveSpaceTwist ι k d)) :=
  Cohomology.module_finite_linearCoherentH_of_cech (Proj (polynomialGrading ι k))
    (projectiveSpaceTwist ι k d) (intChart ι k)
    (CategoryTheory.Sheaf.canonicalInjectiveResolution _)
    (polynomialVariableIntShift_isCechAcyclicCover ι k d (hExt := HasExt.standard _))
    (n + 1)
    (module_finite_cechCohomology_intTwist ι k d n)

end AlgebraicGeometry.Proj
