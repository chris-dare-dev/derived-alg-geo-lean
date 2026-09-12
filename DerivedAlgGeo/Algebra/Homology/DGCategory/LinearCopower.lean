/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.H0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Linear

/-!
# Scalar-linear copowers in a dg category

For a `k`-linear dg category, `DGLinear.homComplex k X Y` repackages the existing
abelian-group-valued Hom-complex as a complex in `ModuleCat k`.  It changes no
underlying graded group or differential; `DGLinear` supplies exactly the
linearity needed for the repackaging.

`IsLinearCopowerOf k K X Z` then says that `Z` represents degree-`p`
*`k`-linear* cochains from `K` to `DGLinear.homComplex k X W`, for every degree and
target.  The universal family is an actual morphism of cochain complexes, and
the existence wrappers follow Mathlib's `HasLimit` pattern.

This is intentionally not a refinement of the additive `IsCopowerOf` API.
The latter is bijective onto all additive cochains; forgetting a linear
universal property would only give bijectivity onto the linear ones, so no such
projection is mathematically available for a general scalar extension.  The
two interfaces coincide only after additional comparison input (for example,
over the integers), which is not asserted here.

This file stops before constructing scalar-linear evaluation data or deriving
an Euler-class formula.  Those require functorial assembly and, later,
homotopy invariance and a finite cohomology presentation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable (k : Type w) [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- The degree-`p` linear cochain induced by a degree-`p` morphism out of a
linear copower: apply the universal chain map, then compose. -/
def linearCopowerCochain {K : CochainComplex (ModuleCat.{v} k) ℤ} {X Z : C}
    (univ : K ⟶ DGLinear.homComplex k X Z) {W : C} (p : ℤ) :
    (DGLinear.homComplex k Z W).X p →ₗ[k]
      CochainComplex.HomComplex.Cochain K (DGLinear.homComplex k X W) p where
  toFun g := CochainComplex.HomComplex.Cochain.mk (fun i j h => ModuleCat.ofHom
    { toFun := fun x => dgComp i p j h (univ.f i x) g
      map_add' := fun x y => by
        rw [map_add, map_add, AddMonoidHom.add_apply]
      map_smul' := fun c x => by
        rw [map_smul, DGLinear.comp_smul_left]
        rfl })
  map_add' g g' := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change dgComp i p j hij (univ.f i x) (g + g') =
      dgComp i p j hij (univ.f i x) g +
        dgComp i p j hij (univ.f i x) g'
    rw [map_add]
  map_smul' c g := by
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change dgComp i p j hij (univ.f i x) (c • g) =
      c • dgComp i p j hij (univ.f i x) g
    rw [DGLinear.comp_smul_right]

@[simp]
lemma linearCopowerCochain_apply
    {K : CochainComplex (ModuleCat.{v} k) ℤ} {X Z : C}
    (univ : K ⟶ DGLinear.homComplex k X Z) {W : C} (p : ℤ)
    (g : (dgHom Z W).X p) (i j : ℤ) (h : i + p = j) (x : K.X i) :
    ((linearCopowerCochain k univ p g).v i j h).hom x =
      dgComp i p j h (univ.f i x) g :=
  rfl

/-- **`Z` is the `k`-linear tensoring of `X` by the complex `K`.**

The universal family is a chain map `K ⟶ DGLinear.homComplex k X Z`.  Composition
with it identifies degree-`p` morphisms out of `Z` with degree-`p` linear
cochains out of `K`, for every degree and target. -/
structure IsLinearCopowerOf
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X Z : C) where
  /-- The universal linear chain map. -/
  univ : K ⟶ DGLinear.homComplex k X Z
  /-- Composition with the universal chain map is bijective onto linear
  cochains, in every degree and from every target. -/
  bijective (W : C) (p : ℤ) :
    Function.Bijective (linearCopowerCochain (W := W) k univ p)

namespace IsLinearCopowerOf

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {K : CochainComplex (ModuleCat.{v} k) ℤ} {X Z Z' : C}

/-- The universal family commutes with the differentials. -/
lemma univ_d (t : IsLinearCopowerOf k K X Z) (i j : ℤ) (x : K.X i) :
    t.univ.f j ((K.d i j).hom x) =
      ((dgHom X Z).d i j).hom (t.univ.f i x) := by
  exact (ConcreteCategory.congr_hom (t.univ.comm i j) x).symm

/-- The representing bijection as a linear equivalence. -/
noncomputable def cochainLinearEquiv (t : IsLinearCopowerOf k K X Z)
    (W : C) (p : ℤ) :
    (dgHom Z W).X p ≃ₗ[k]
      CochainComplex.HomComplex.Cochain
        K (DGLinear.homComplex k X W) p :=
  LinearEquiv.ofBijective (linearCopowerCochain (W := W) k t.univ p)
    (t.bijective W p)

/-- A morphism out of a linear copower is determined by the cochain it
induces. -/
lemma lift_unique (t : IsLinearCopowerOf k K X Z) {W : C} {p : ℤ}
    {g g' : (dgHom Z W).X p}
    (h : ∀ (i j : ℤ) (hij : i + p = j) (x : K.X i),
      dgComp i p j hij (t.univ.f i x) g =
        dgComp i p j hij (t.univ.f i x) g') :
    g = g' := by
  refine (t.bijective W p).injective ?_
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  exact LinearMap.ext fun x => h i j hij x

/-- Every linear cochain out of `K` is induced by a morphism out of the linear
copower. -/
noncomputable def lift (t : IsLinearCopowerOf k K X Z) {W : C} (p : ℤ)
    (c : CochainComplex.HomComplex.Cochain
      K (DGLinear.homComplex k X W) p) :
    (dgHom Z W).X p :=
  (t.cochainLinearEquiv W p).symm c

@[simp]
lemma lift_zero (t : IsLinearCopowerOf k K X Z) {W : C} (p : ℤ) :
    t.lift (W := W) p 0 = 0 :=
  (t.cochainLinearEquiv W p).symm.map_zero

@[simp]
lemma lift_add (t : IsLinearCopowerOf k K X Z) {W : C} (p : ℤ)
    (c c' : CochainComplex.HomComplex.Cochain
      K (DGLinear.homComplex k X W) p) :
    t.lift p (c + c') = t.lift p c + t.lift p c' :=
  (t.cochainLinearEquiv W p).symm.map_add c c'

@[simp]
lemma lift_smul (t : IsLinearCopowerOf k K X Z) {W : C} (p : ℤ)
    (a : k) (c : CochainComplex.HomComplex.Cochain
      K (DGLinear.homComplex k X W) p) :
    t.lift p (a • c) = a • t.lift p c :=
  (t.cochainLinearEquiv W p).symm.map_smul a c

@[simp]
lemma univ_comp_lift (t : IsLinearCopowerOf k K X Z) {W : C} (p : ℤ)
    (c : CochainComplex.HomComplex.Cochain
      K (DGLinear.homComplex k X W) p)
    (i j : ℤ) (hij : i + p = j) (x : K.X i) :
    dgComp i p j hij (t.univ.f i x) (t.lift p c) =
      (c.v i j hij).hom x := by
  have h := (t.cochainLinearEquiv W p).apply_symm_apply c
  exact congrArg (fun z => (z.v i j hij).hom x) h

/-- The canonical comparison between two linear copowers of the same data. -/
noncomputable def compare
    (t : IsLinearCopowerOf k K X Z) (t' : IsLinearCopowerOf k K X Z') :
    (dgHom Z Z').X 0 :=
  t.lift 0 (CochainComplex.HomComplex.Cochain.ofHom t'.univ)

@[simp]
lemma univ_comp_compare
    (t : IsLinearCopowerOf k K X Z) (t' : IsLinearCopowerOf k K X Z')
    (i : ℤ) (x : K.X i) :
    dgComp i 0 i (by omega) (t.univ.f i x) (t.compare t') =
      t'.univ.f i x :=
  by
    change dgComp i 0 i (by omega) (t.univ.f i x)
        (t.lift 0 (CochainComplex.HomComplex.Cochain.ofHom t'.univ)) =
      (t'.univ.f i).hom x
    exact t.univ_comp_lift 0
      (CochainComplex.HomComplex.Cochain.ofHom t'.univ) i i (by omega) x

/-- The canonical comparison is closed, hence is a morphism in `Z⁰ C`. -/
lemma compare_mem_cocycles
    (t : IsLinearCopowerOf k K X Z) (t' : IsLinearCopowerOf k K X Z') :
    t.compare t' ∈ cocycles Z Z' := by
  rw [mem_cocycles_iff]
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i + 1 := by omega
  cases hji
  have hleib := dgComp_leibniz (C := C) i 0 i (i + 1) (by omega) (by omega)
    (t.univ.f i x) (t.compare t')
  rw [t.univ_comp_compare t', ← t'.univ_d i (i + 1),
    ← t.univ_d i (i + 1), t.univ_comp_compare t'] at hleib
  simp only [Int.negOnePow_zero, one_smul, _root_.map_zero] at hleib ⊢
  exact add_right_cancel (hleib.symm.trans (zero_add _).symm)

/-- The two canonical comparisons compose to the identity. -/
lemma compare_comp_compare
    (t : IsLinearCopowerOf k K X Z) (t' : IsLinearCopowerOf k K X Z') :
    dgComp 0 0 0 (by omega) (t.compare t') (t'.compare t) = dgId Z := by
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [← dgComp_assoc i 0 0 i 0 i (by omega) (by omega) (by omega),
    t.univ_comp_compare t', t'.univ_comp_compare t, dgComp_id]

/-- Canonical linear-copower comparisons compose strictly. -/
lemma compare_trans {Z'' : C}
    (t : IsLinearCopowerOf k K X Z) (t' : IsLinearCopowerOf k K X Z')
    (t'' : IsLinearCopowerOf k K X Z'') :
    dgComp 0 0 0 (by omega) (t.compare t') (t'.compare t'') =
      t.compare t'' := by
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [← dgComp_assoc i 0 0 i 0 i (by omega) (by omega) (by omega),
    t.univ_comp_compare t', t'.univ_comp_compare t'',
    t.univ_comp_compare t'']

/-- Comparing a linear copower with itself is the identity. -/
@[simp]
lemma compare_self (t : IsLinearCopowerOf k K X Z) :
    t.compare t = dgId Z := by
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [t.univ_comp_compare t, dgComp_id]

end IsLinearCopowerOf

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]

/-- A linear copower object together with its universal-property witness. -/
structure LinearCopowerData
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C) where
  /-- The chosen linear copower object. -/
  obj : C
  /-- The universal property witnessed by the chosen object. -/
  isLinearCopower : IsLinearCopowerOf k K X obj

/-- Mere existence of a linear copower of `X` by `K`. -/
class HasLinearCopower
    (k : Type w) [CommRing k]
    {C : Type u} [DGCategory.{v} C]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
    [DGLinear k C]
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C) : Prop where
  exists_linearCopower : Nonempty (LinearCopowerData K X)

/-- A witnessed linear copower supplies the corresponding existence
instance. -/
theorem HasLinearCopower.of_isLinearCopower
    {K : CochainComplex (ModuleCat.{v} k) ℤ} {X Z : C}
    (t : IsLinearCopowerOf k K X Z) : HasLinearCopower k K X :=
  ⟨⟨⟨Z, t⟩⟩⟩

/-- A noncomputably selected linear copower and its witness. -/
noncomputable def linearCopowerData
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C)
    [HasLinearCopower k K X] : LinearCopowerData K X :=
  Classical.choice HasLinearCopower.exists_linearCopower

/-- The linear copower object selected from `HasLinearCopower k K X`. -/
noncomputable def linearCopowerObj
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C)
    [HasLinearCopower k K X] : C :=
  (linearCopowerData K X).obj

/-- The witness for the selected `linearCopowerObj k K X`. -/
noncomputable def linearCopowerIsLinearCopower
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C)
    [HasLinearCopower k K X] :
    IsLinearCopowerOf k K X (linearCopowerObj K X) :=
  (linearCopowerData K X).isLinearCopower

/-- Existence of all `k`-linear copowers in a `k`-linear dg category. -/
class HasLinearCopowers
    (k : Type w) [CommRing k]
    (C : Type u) [DGCategory.{v} C]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
    [DGLinear k C] : Prop where
  has_linearCopower
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C) :
    HasLinearCopower k K X := by infer_instance

/-- All linear copowers give each individual linear copower. -/
instance (priority := 100) hasLinearCopowerOfHasLinearCopowers
    [HasLinearCopowers k C]
    (K : CochainComplex (ModuleCat.{v} k) ℤ) (X : C) :
    HasLinearCopower k K X :=
  HasLinearCopowers.has_linearCopower K X

end CategoryTheory
