/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.BoundedHomotopyCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# A concrete `HomFiniteBounded` category (#543)

`EulerForm.lean` introduced `HomFiniteBounded` as supplied data and its own
docstring recorded that no concrete `k`-linear pretriangulated category
existed in this repository for it to be proved about. This file removes that
caveat: the **bounded homotopy category** `Kᵇ(C)` of any Hom-finite `k`-linear
additive category `C` satisfies it, and `Kᵇ(FGModuleCat k)` — bounded
complexes of finite-dimensional vector spaces up to homotopy — is the named
concrete witness.

## Why the homotopy category and not the derived category

For `Dᵇ` the finiteness of Hom-spaces is a theorem *about the localization*.
For `Kᵇ` every statement is elementary: a chain map out of a complex supported
in a finite window is determined by finitely many components, each in a
Hom-finite Hom-space, and homotopy classes are a quotient of that. So `Kᵇ` is
where the witness is built, and it stands on its own as an honest `k`-linear
pretriangulated category.

The route to `Dᵇ` does **not** need the semisimplicity argument
(`Dᵇ(k‑vect) ≃ ℤ`-graded vector spaces) that an earlier reading of #543 took to
be the only option. Over a field every bounded complex is K-projective, and
`CochainComplex.IsKProjective.Qh_map_bijective` then says Hom in `Dᵇ` *is* Hom
in `Kᵇ`. The `Derived` section below carries that out: `boundedQh` is fully
faithful, its essential image is a triangulated subcategory of
`D(FGModuleCat k)` and so `k`-linear pretriangulated, and
`HomFiniteBounded.of_essSurj` moves the `Kᵇ` instance across.

So `HomFiniteBounded` now has a model on a genuine derived category, and no
equivalence `Dᵇ(k-vect) ≃ ℤ`-graded vector spaces is constructed anywhere.

## What this file proves and what it does not

* `CochainComplex.module_finite_hom`: a chain-map space out of a strictly
  bounded complex is a finite `k`-module when `C` is Hom-finite. No bound on
  the target is needed.
* `subsingleton_hom_of_le_lt_ge` / `..of_ge_lt_le`: chain maps between
  complexes with disjoint support windows vanish.
* `instHomFiniteBoundedBounded`: `Kᵇ(C)` satisfies `HomFiniteBounded k` for
  Hom-finite `k`-linear `C`; `homFiniteBounded_fgModuleCat` instantiates it
  at `C := FGModuleCat k`.
* `FGModuleCat.instProjective`: every finite-dimensional vector space is a
  projective object. Mathlib has this for `ModuleCat` but not for
  `FGModuleCat`, and instance search does not find it unaided — it is an
  upstream candidate.
* `isKProjective_of_isStrictlyLE`: a bounded-above complex of
  finite-dimensional vector spaces is K-projective, with no hypothesis beyond
  the bound.
* `homFiniteBounded_boundedDerived`: `HomFiniteBounded k` on the essential
  image of `boundedQh` — a full subcategory of `DerivedCategory (FGModuleCat k)`,
  `k`-linear pretriangulated. This is the honest `Dᵇ` witness #543 asked for.
* **Not** proved: that this essential image is all of the bounded derived
  category — it is defined as an image, and no t-structure characterisation of
  it is given. Nor any comparison of `chiHom` with an Euler characteristic of
  homology, nor `IsRiemannRoch` for anything.
  The obligation #513 named is discharged in the satisfiability sense only:
  the class has a genuine model, so the Euler-form chain is not vacuous.
-/

universe w v u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.Triangulated

variable (k : Type w) [DivisionRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

namespace HomFiniteWitness

open HomologicalComplex

/-- Restriction of a chain map to its components in a finite window,
as a linear map. -/
def homRestrict (K L : CochainComplex C ℤ) (s : Finset ℤ) :
    (K ⟶ L) →ₗ[k] Π i : s, (K.X i ⟶ L.X i) where
  toFun f i := f.f i
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

/-- A chain-map space out of a strictly bounded complex is a finite
`k`-module when the base category is Hom-finite. The target complex needs no
bound. -/
lemma module_finite_hom [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    (K L : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    Module.Finite k (K ⟶ L) := by
  refine FiniteDimensional.of_injective (homRestrict k K L (Finset.Icc a b))
    (fun f g h ↦ ?_)
  ext i
  by_cases hi : i ∈ Finset.Icc a b
  · exact congrFun h ⟨i, hi⟩
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact (K.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
    · exact (K.isZero_of_isStrictlyLE b i hi).eq_of_src _ _

/-- Chain maps from a complex bounded above into one bounded strictly below
it vanish. -/
lemma subsingleton_hom_of_le_lt_ge (K L : CochainComplex C ℤ) (b c : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyGE c] (h : b < c) :
    Subsingleton (K ⟶ L) := by
  constructor
  intro f g
  ext i
  by_cases hi : c ≤ i
  · exact (K.isZero_of_isStrictlyLE b i (by omega)).eq_of_src _ _
  · exact (L.isZero_of_isStrictlyGE c i (by omega)).eq_of_tgt _ _

/-- Chain maps from a complex bounded below into one bounded strictly above
it vanish. -/
lemma subsingleton_hom_of_ge_lt_le (K L : CochainComplex C ℤ) (a d : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyLE d] (h : d < a) :
    Subsingleton (K ⟶ L) := by
  constructor
  intro f g
  ext i
  by_cases hi : a ≤ i
  · exact (L.isZero_of_isStrictlyLE d i (by omega)).eq_of_tgt _ _
  · exact (K.isZero_of_isStrictlyGE a i (by omega)).eq_of_src _ _

variable [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The hom-space `X ⟶ Y⟦i⟧` in `Kᵇ(C)`, identified `k`-linearly with a
hom-space between quotient images of honest complexes, along the two
inclusion/quotient `CommShift` isomorphisms and the defining equalities of
the boundedness property. Both instance fields below factor through this. -/
noncomputable def boundedHomEquiv (X Y : HomotopyCategory.Bounded C) (i : ℤ)
    {KX KY : CochainComplex C ℤ}
    (hX : (HomotopyCategory.quotient C (.up ℤ)).obj KX = X.obj)
    (hY : (HomotopyCategory.quotient C (.up ℤ)).obj KY = Y.obj) :
    (X ⟶ Y⟦i⟧) ≃ₗ[k]
      ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
  (InducedCategory.homLinearEquiv (R := k)).trans
    (Linear.homCongr k (eqToIso hX).symm
      ((((HomotopyCategory.bounded C).ι.commShiftIso i).app Y) ≪≫
        (shiftFunctor (HomotopyCategory C (.up ℤ)) i).mapIso (eqToIso hY).symm ≪≫
          (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso i).app KY).symm))

end HomFiniteWitness

open HomFiniteWitness in
/-- **`Kᵇ` of a Hom-finite linear category is `HomFiniteBounded`.** Every
hom-space is a quotient of a chain-map space out of a bounded complex, and
disjoint support windows kill all chain maps once the shift is large. -/
instance instHomFiniteBoundedBounded
    [∀ X Y : C, Module.Finite k (X ⟶ Y)] :
    HomFiniteBounded k (HomotopyCategory.Bounded C) where
  finite X Y i := by
    obtain ⟨KX, hKX, hX⟩ := (HomotopyCategory.bounded_iff_exists X.obj).1 X.property
    obtain ⟨KY, hKY, hY⟩ := (HomotopyCategory.bounded_iff_exists Y.obj).1 Y.property
    obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hKX
    have : Module.Finite k (KX ⟶ KY⟦i⟧) := module_finite_hom k KX (KY⟦i⟧) a b
    have : Module.Finite k
        ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
      Module.Finite.of_surjective
        ((HomotopyCategory.quotient C (.up ℤ)).mapLinearMap (R := k))
        (HomotopyCategory.quotient C (.up ℤ)).map_surjective
    exact Module.Finite.equiv (boundedHomEquiv k X Y i hX hY).symm
  support_finite X Y := by
    obtain ⟨KX, hKX, hX⟩ := (HomotopyCategory.bounded_iff_exists X.obj).1 X.property
    obtain ⟨KY, hKY, hY⟩ := (HomotopyCategory.bounded_iff_exists Y.obj).1 Y.property
    obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hKX
    obtain ⟨⟨c, _⟩, ⟨d, _⟩⟩ := hKY
    refine Set.Finite.subset (Set.finite_Icc (c - b) (d - a)) (fun i hi ↦ ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hout
    apply hi
    simp only [Set.mem_Icc, not_and_or, not_le] at hout
    have : (KY⟦i⟧).IsStrictlyGE (c - i) := KY.isStrictlyGE_shift c i (c - i) (by omega)
    have : (KY⟦i⟧).IsStrictlyLE (d - i) := KY.isStrictlyLE_shift d i (d - i) (by omega)
    have hsub : Subsingleton (KX ⟶ KY⟦i⟧) := by
      rcases hout with hout | hout
      · exact subsingleton_hom_of_le_lt_ge KX (KY⟦i⟧) b (c - i) (by omega)
      · exact subsingleton_hom_of_ge_lt_le KX (KY⟦i⟧) a (d - i) (by omega)
    have : Subsingleton
        ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
      (HomotopyCategory.quotient C (.up ℤ)).map_surjective.subsingleton
    have : Subsingleton (X ⟶ Y⟦i⟧) :=
      (boundedHomEquiv k X Y i hX hY).toEquiv.subsingleton
    simp [Module.finrank_zero_of_subsingleton]

section FGModuleCat

variable (k : Type u) [Field k]

instance fgModuleCat_hom_finite (V W : FGModuleCat k) : Module.Finite k (V ⟶ W) :=
  Module.Finite.equiv
    ((ModuleCat.homLinearEquiv (M := V.obj) (N := W.obj) (S := k)).symm.trans
      (InducedCategory.homLinearEquiv (R := k)).symm)

/-- **The named concrete witness for #543**: bounded complexes of
finite-dimensional `k`-vector spaces up to homotopy form a `k`-linear
pretriangulated category with finite-dimensional Hom-spaces and finite
Ext-amplitude. The Euler-form chain of `EulerForm.lean` is therefore not
vacuous: `HomFiniteBounded` has a model. -/
theorem homFiniteBounded_fgModuleCat :
    HomFiniteBounded k (HomotopyCategory.Bounded (FGModuleCat k)) :=
  inferInstance

/-- **Every finite-dimensional vector space is a projective object.**

Over a field every module is free, hence `Module.Projective`, and
`ModuleCat.projective_of_categoryTheory_projective` turns that into
categorical projectivity in `ModuleCat k`. The step this instance adds is
descending it along `forget₂`, which is full, faithful and epimorphism-
preserving, so `Functor.projective_of_map_projective` applies.

Instance search does **not** find this chain on its own — it times out at the
default heartbeat budget — which is why the instance is written down rather
than left implicit. Mathlib has no `Projective` result anywhere under
`Algebra/Category/FGModuleCat/`; this is an upstream candidate. -/
instance _root_.FGModuleCat.instProjective (V : FGModuleCat.{u} k) :
    Projective V :=
  (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).projective_of_map_projective
    (inferInstanceAs (Projective ((forget₂ _ _).obj V)))

/-- **A bounded-above complex of finite-dimensional vector spaces is
K-projective.**

`CochainComplex.isKProjective_of_projective` asks for a bound above and
degreewise projectivity; over a field the second hypothesis is free by
`FGModuleCat.instProjective`, so only the bound survives.

This is the input to `CochainComplex.IsKProjective.Qh_map_bijective`, which is
what would carry `instHomFiniteBoundedBounded` across to a derived category.
That transport is not performed here. -/
theorem isKProjective_of_isStrictlyLE (K : CochainComplex (FGModuleCat.{u} k) ℤ)
    (d : ℤ) [K.IsStrictlyLE d] : K.IsKProjective :=
  CochainComplex.isKProjective_of_projective K d

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Every object of `Kᵇ(FGModuleCat k)` is K-projective. Boundedness supplies
the bound above; `FGModuleCat.instProjective` supplies the rest. -/
instance isKProjective_bounded (X : HomotopyCategory.Bounded (FGModuleCat.{u} k)) :
    CochainComplex.IsKProjective X.obj.as := by
  have h : CochainComplex.bounded (FGModuleCat.{u} k) X.obj.as := by
    rw [← HomotopyCategory.bounded_quotient_obj_iff]
    exact X.property
  obtain ⟨-, d, hd⟩ := h
  exact isKProjective_of_isStrictlyLE k X.obj.as d

/-- **`Kᵇ(FGModuleCat k) ⥤ D(FGModuleCat k)`.**

An `abbrev` deliberately: as a `def` the composite is opaque to instance search,
and every structural instance below — `CommShift`, `IsTriangulated`, `Additive`,
`Linear` — is found by unfolding it. -/
noncomputable abbrev boundedQh :
    HomotopyCategory.Bounded (FGModuleCat.{u} k) ⥤ DerivedCategory (FGModuleCat.{u} k) :=
  HomotopyCategory.Bounded.ι (FGModuleCat.{u} k) ⋙ DerivedCategory.Qh

/-- Full, because a K-projective source makes `Qh` bijective on Hom. -/
instance boundedQh_full : (boundedQh k).Full := by
  constructor
  intro X Y f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective X.obj.as Y.obj).2 f
  exact ⟨ObjectProperty.homMk g, hg⟩

/-- Faithful, by the injective half of the same bijection. -/
instance boundedQh_faithful : (boundedQh k).Faithful := by
  constructor
  intro X Y f g h
  apply ObjectProperty.hom_ext
  apply (CochainComplex.IsKProjective.Qh_map_bijective X.obj.as Y.obj).1
  exact h

/-- **The bounded derived locus**: the essential image of `boundedQh`, as a full
subcategory of `D(FGModuleCat k)`.

It is `k`-linear pretriangulated for free. Mathlib's
`ObjectProperty.essImage.IsTriangulated` makes the essential image of a full
triangulated functor a triangulated subcategory, and
`ObjectProperty.instPretriangulatedFullSubcategory` equips the full subcategory
of a triangulated subcategory. Nothing here has to build a t-structure. -/
noncomputable abbrev boundedLift :
    HomotopyCategory.Bounded (FGModuleCat.{u} k) ⥤ (boundedQh k).essImage.FullSubcategory :=
  (boundedQh k).essImage.lift (boundedQh k) (fun X => (boundedQh k).obj_mem_essImage X)

noncomputable instance boundedLift_linear : Functor.Linear k (boundedLift k) where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    exact (boundedQh k).map_smul r f

noncomputable instance boundedLift_essSurj : (boundedLift k).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := Y.property
    exact ⟨X, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **The `Dᵇ` witness for #543.**

`HomFiniteBounded` holds on a full subcategory of a genuine **derived**
category, not merely on a homotopy category. The route is the one
`HomFiniteWitness`'s docstring describes: bounded complexes of
finite-dimensional vector spaces are K-projective, so `Qh` is fully faithful on
them, and `HomFiniteBounded.of_essSurj` carries the `Kᵇ` instance across.

Semisimplicity is not used, and no equivalence `Dᵇ(k-vect) ≃ ℤ`-graded vector
spaces is constructed or needed. -/
noncomputable instance homFiniteBounded_boundedDerived :
    HomFiniteBounded k (boundedQh k).essImage.FullSubcategory :=
  HomFiniteBounded.of_essSurj (boundedLift k) (Functor.FullyFaithful.ofFullyFaithful _)

end Derived

end FGModuleCat

end CategoryTheory.Triangulated
