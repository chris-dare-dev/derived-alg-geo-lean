/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-!
# Tensoring a dg object by a complex

The evaluation functor `RHom(E,-) ⊗ E` needs an object `K ⊗ X` for a complex
`K` and an object `X`, and the repository has no tensor product to build it
with: at the pinned Mathlib revision `HomologicalComplex.HasTensor` does not
synthesize for the `ℤ`-indexed shape, which is the whole reason `DGCategory`
encodes composition as a family of biadditive maps rather than a chain map out
of a tensor product (ADR-0010, ADR-0011).

So the tensoring is stated the way `IsShiftBy` states the shift: by its
universal property, as data plus a bijectivity condition, with no construction
of the object.  `IsCopowerOf K X Z` says `Z` *is* `K ⊗ X`, in the only sense
that matters — degree-`p` morphisms out of `Z` are degree-`p` cochains out of
`K` into the Hom-complex of `X`.

## Why cochains are spelled out

A degree-`p` cochain `K ⟶ dgHom X W` is an additive map `K i ⟶ (dgHom X W) j`
for every `i + p = j`.  Mathlib's `CochainComplex.HomComplex.Cochain` packages
exactly that, but naming it here would drag in the `Triplet` encoding and the
`δ` API for no gain: the two conditions below are stated directly on the
families, in the same vocabulary as the rest of this directory.

## What the bijectivity is for

Everything.  `IsShiftBy` gets its inverse, its uniqueness and its transport
from one bijectivity assumption, and the same three follow here:
`IsCopowerOf.lift` inverts the bijection, `lift_unique` says a morphism out of
a copower is determined by the cochain it induces, and `compare` makes any two
copowers of the same data canonically isomorphic.

## The evaluation functor

`EvaluationData E` is a choice of copower of `E` by `dgHom E X` for every `X`,
in the same shape as `ConeData`: objectwise data, assembled into a dg functor.
Its functor is `RHom(E,-) ⊗ E` and its `evaluation` is the transformation to
the identity, whose component at `X` is the morphism corresponding to the
*identity* cochain of `dgHom E X`.

Every one of the functor's four laws is `lift_unique` applied to the cochain
each side induces; only `map_d` needs anything beyond associativity, and there
it is the Leibniz rule twice, once in `C` and once in the Hom-complex.

## What this does not give

Existence.  Nothing here builds a copower, so nothing here produces an
`EvaluationData`; a category with enough copowers has to supply one, exactly
as `IsPretriangulated` supplies cone and shift choices.  And nothing relates
this functor to a spherical object: that comparison needs `Perf(k)` as a dg
category, which the repository does not have.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- The degree-`p` cochain that a degree-`p` morphism out of a copower induces:
apply the universal family, then compose. -/
def copowerCochain {K : CochainComplex AddCommGrpCat.{v} ℤ} {X Z : C}
    (univ : ∀ i : ℤ, K.X i →+ (dgHom X Z).X i) {W : C} (p : ℤ)
    (g : (dgHom Z W).X p) (i j : ℤ) (h : i + p = j) :
    K.X i →+ (dgHom X W).X j :=
  AddMonoidHom.mk' (fun x => dgComp i p j h (univ i x) g)
    (fun x y => by rw [map_add, map_add, AddMonoidHom.add_apply])

@[simp]
lemma copowerCochain_apply {K : CochainComplex AddCommGrpCat.{v} ℤ} {X Z : C}
    (univ : ∀ i : ℤ, K.X i →+ (dgHom X Z).X i) {W : C} (p : ℤ)
    (g : (dgHom Z W).X p) (i j : ℤ) (h : i + p = j) (x : K.X i) :
    copowerCochain univ p g i j h x = dgComp i p j h (univ i x) g :=
  rfl

/-- **`Z` is the tensoring of `X` by the complex `K`.**

The data is a chain map `K ⟶ dgHom X Z`, and the condition is that composing
with it identifies degree-`p` morphisms out of `Z` with degree-`p` cochains out
of `K`, for every degree and every target.  This is `IsShiftBy`'s pattern: the
object is not built, only characterised. -/
structure IsCopowerOf (K : CochainComplex AddCommGrpCat.{v} ℤ) (X Z : C) where
  /-- The universal family, degree by degree. -/
  univ (i : ℤ) : K.X i →+ (dgHom X Z).X i
  /-- It is a chain map. -/
  univ_d (i j : ℤ) (x : K.X i) :
    univ j ((K.d i j).hom x) = ((dgHom X Z).d i j).hom (univ i x)
  /-- Composing with it is bijective onto cochains, in every degree and from
  every target. -/
  bijective (W : C) (p : ℤ) :
    Function.Bijective (fun g : (dgHom Z W).X p => copowerCochain univ p g)

namespace IsCopowerOf

variable {K : CochainComplex AddCommGrpCat.{v} ℤ} {X Z Z' : C}

/-- **A morphism out of a copower is determined by the cochain it induces.** -/
lemma lift_unique (t : IsCopowerOf K X Z) {W : C} {p : ℤ}
    {g g' : (dgHom Z W).X p}
    (h : ∀ (i j : ℤ) (hij : i + p = j) (x : K.X i),
      dgComp i p j hij (t.univ i x) g = dgComp i p j hij (t.univ i x) g') :
    g = g' := by
  refine (t.bijective W p).injective ?_
  funext i j hij
  exact AddMonoidHom.ext fun x => h i j hij x

/-- **Every cochain out of `K` is induced by a morphism out of the copower.** -/
noncomputable def lift (t : IsCopowerOf K X Z) {W : C} (p : ℤ)
    (c : ∀ i j : ℤ, i + p = j → (K.X i →+ (dgHom X W).X j)) :
    (dgHom Z W).X p :=
  ((t.bijective W p).surjective c).choose

@[simp]
lemma univ_comp_lift (t : IsCopowerOf K X Z) {W : C} (p : ℤ)
    (c : ∀ i j : ℤ, i + p = j → (K.X i →+ (dgHom X W).X j))
    (i j : ℤ) (hij : i + p = j) (x : K.X i) :
    dgComp i p j hij (t.univ i x) (t.lift p c) = c i j hij x := by
  have h := ((t.bijective W p).surjective c).choose_spec
  exact congrArg (fun z => z i j hij x) h

/-- The comparison between two copowers of the same data: the lift of the other
one's universal family.

The index is normalised with `cases` rather than `subst`: the cochain is indexed
by `i + 0 = j`, and `j` is the variable that has to go. -/
noncomputable def compare (t : IsCopowerOf K X Z) (t' : IsCopowerOf K X Z') :
    (dgHom Z Z').X 0 :=
  t.lift 0 (fun i j hij => by
    have hji : j = i := by omega
    cases hji
    exact t'.univ i)

@[simp]
lemma univ_comp_compare (t : IsCopowerOf K X Z) (t' : IsCopowerOf K X Z')
    (i : ℤ) (x : K.X i) :
    dgComp i 0 i (by omega) (t.univ i x) (t.compare t') = t'.univ i x :=
  t.univ_comp_lift 0 _ i i (by omega) x

/-- **Any two copowers of the same data are canonically isomorphic.**  The two
comparisons compose to the identity, so the object `IsCopowerOf` characterises
is unique up to a canonical degree-zero isomorphism. -/
lemma compare_comp_compare (t : IsCopowerOf K X Z) (t' : IsCopowerOf K X Z') :
    dgComp 0 0 0 (by omega) (t.compare t') (t'.compare t) = dgId Z := by
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [← dgComp_assoc i 0 0 i 0 i (by omega) (by omega) (by omega),
    t.univ_comp_compare t', t'.univ_comp_compare t, dgComp_id]

/-- Comparing a copower with itself is the identity. -/
@[simp]
lemma compare_self (t : IsCopowerOf K X Z) : t.compare t = dgId Z := by
  refine t.lift_unique (fun i j hij x => ?_)
  have hji : j = i := by omega
  cases hji
  rw [t.univ_comp_compare t, dgComp_id]

end IsCopowerOf

/-- **A choice of `RHom(E,X) ⊗ E` for every `X`.**

The same shape as `HomogeneousNatTrans.ConeData`: objectwise data that the
next declarations assemble into a dg functor. -/
structure EvaluationData (E : C) where
  /-- The chosen object `RHom(E,X) ⊗ E`. -/
  obj : C → C
  /-- It is the copower of `E` by the Hom-complex out of `E`. -/
  isCopower (X : C) : IsCopowerOf (dgHom E X) E (obj X)

namespace EvaluationData

variable {E : C} (V : EvaluationData E)

/-- The action on a homogeneous morphism: postcompose inside the Hom-complex,
then lift. -/
noncomputable def map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    (dgHom (V.obj X) (V.obj Y)).X p :=
  (V.isCopower X).lift p (fun i j hij =>
    AddMonoidHom.mk' (fun k => (V.isCopower Y).univ j (dgComp i p j hij k f))
      (fun k k' => by rw [map_add, AddMonoidHom.add_apply, map_add]))

@[simp]
lemma univ_comp_map (V : EvaluationData E) {X Y : C} (p : ℤ)
    (f : (dgHom X Y).X p) (i j : ℤ) (hij : i + p = j) (k : (dgHom E X).X i) :
    dgComp i p j hij ((V.isCopower X).univ i k) (V.map p f) =
      (V.isCopower Y).univ j (dgComp i p j hij k f) :=
  (V.isCopower X).univ_comp_lift p _ i j hij k

@[simp]
lemma map_zero {X Y : C} (p : ℤ) : V.map (X := X) (Y := Y) p 0 = 0 := by
  refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
  rw [univ_comp_map, _root_.map_zero, _root_.map_zero, _root_.map_zero]

lemma map_add {X Y : C} (p : ℤ) (f f' : (dgHom X Y).X p) :
    V.map p (f + f') = V.map p f + V.map p f' := by
  refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
  simp only [univ_comp_map, _root_.map_add]

/-- **The evaluation functor `RHom(E,-) ⊗ E`.** -/
noncomputable def functor : DGFunctor C C where
  obj := V.obj
  map {X Y} p := AddMonoidHom.mk' (V.map p) (V.map_add p)
  map_d {X Y} p q f := by
    by_cases hpq : p + 1 = q
    · subst hpq
      refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
      -- Inside the structure the action is wrapped in `AddMonoidHom.mk'`, so
      -- the computation rule does not match until the goal is restated.
      show dgComp i (p + 1) j hij ((V.isCopower X).univ i k)
          (V.map (p + 1) (((dgHom X Y).d p (p + 1)).hom f)) =
        dgComp i (p + 1) j hij ((V.isCopower X).univ i k)
          (((dgHom (V.obj X) (V.obj Y)).d p (p + 1)).hom (V.map p f))
      rw [univ_comp_map]
      -- Leibniz in `C` for `univ k` against `map p f`, then Leibniz in the
      -- Hom-complex out of `E` for `k` against `f`.  The two correction terms
      -- are the same after `univ` is moved across, and cancel.
      have hleib := dgComp_leibniz (C := C) i p (i + p) j (by omega) (by omega)
        ((V.isCopower X).univ i k) (V.map p f)
      rw [univ_comp_map (i := i) (j := i + p) (hij := by omega),
        ← (V.isCopower Y).univ_d (i + p) j,
        ← (V.isCopower X).univ_d i (i + 1),
        univ_comp_map (i := i + 1) (j := j) (hij := by omega),
        dgComp_leibniz (C := C) i p (i + p) j (by omega) (by omega) k f,
        _root_.map_add] at hleib
      simp only [Units.smul_def, map_zsmul] at hleib
      exact add_right_cancel hleib
    · have hshape : ¬(ComplexShape.up ℤ).Rel p q := by
        simpa [ComplexShape.up, ComplexShape.up'] using hpq
      rw [(dgHom X Y).shape p q hshape,
        (dgHom (V.obj X) (V.obj Y)).shape p q hshape]
      show V.map q 0 = _
      rw [V.map_zero]
      simp
  map_id X := by
    refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
    have hji : j = i := by omega
    cases hji
    show dgComp i 0 i hij ((V.isCopower X).univ i k) (V.map 0 (dgId X)) =
      dgComp i 0 i hij ((V.isCopower X).univ i k) (dgId (V.obj X))
    rw [univ_comp_map, dgComp_id, dgComp_id]
  map_comp {X Y Z} p q r h f g := by
    refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
    show dgComp i r j hij ((V.isCopower X).univ i k) (V.map r (dgComp p q r h f g)) =
      dgComp i r j hij ((V.isCopower X).univ i k)
        (dgComp p q r h (V.map p f) (V.map q g))
    rw [← dgComp_assoc i p q (i + p) r j rfl h (by omega)
        ((V.isCopower X).univ i k) (V.map p f) (V.map q g),
      univ_comp_map (i := i) (j := i + p) (hij := rfl),
      univ_comp_map (i := i + p) (j := j) (hij := by omega),
      univ_comp_map (i := i) (j := j) (hij := hij),
      ← dgComp_assoc i p q (i + p) r j rfl h (by omega) k f g]

@[simp]
lemma functor_obj (X : C) : V.functor.obj X = V.obj X := rfl

/-- Not `@[simp]`: `functor_obj` rewrites inside this statement's own type, so
the left-hand side is not in simp normal form and `simpNF` rejects it.  The
same reason keeps `DGFunctor.shiftedFunctor_map` off the simp set. -/
lemma functor_map {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    V.functor.map p f = V.map p f := rfl

/-- The evaluation morphism at `X`: the morphism `RHom(E,X) ⊗ E ⟶ X` induced
by the *identity* cochain of `dgHom E X`.  That is exactly what "evaluate"
means.

The index is normalised with `cases` rather than `subst`, for the reason given
at `IsCopowerOf.compare`. -/
noncomputable def evalHom (X : C) : (dgHom (V.obj X) X).X 0 :=
  (V.isCopower X).lift 0 (fun i j hij => by
    have hji : j = i := by omega
    cases hji
    exact AddMonoidHom.id _)

@[simp]
lemma univ_comp_evalHom (X : C) (i : ℤ) (k : (dgHom E X).X i) :
    dgComp i 0 i (by omega) ((V.isCopower X).univ i k) (V.evalHom X) = k :=
  (V.isCopower X).univ_comp_lift 0 _ i i (by omega) k

/-- **The evaluation transformation `RHom(E,-) ⊗ E ⟶ id`.**

It is homogeneous of degree zero, so its Koszul sign is trivial and naturality
is the plain square: both sides are the cochain `k ↦ k · f`. -/
noncomputable def evaluation :
    DGFunctor.HomogeneousNatTrans V.functor (DGFunctor.id C) 0 :=
  ⟨V.evalHom, by
    intro X Y p r hpr hrp f
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    have hrp' : r = p := by omega
    cases hrp'
    refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
    have hji : j = i + p := by omega
    cases hji
    show dgComp i p (i + p) hij ((V.isCopower X).univ i k)
        (dgComp p 0 p hpr (V.map p f) (V.evalHom Y)) =
      dgComp i p (i + p) hij ((V.isCopower X).univ i k)
        (dgComp 0 p p hrp (V.evalHom X) f)
    rw [← dgComp_assoc i p 0 (i + p) p (i + p) rfl hpr (by omega)
        ((V.isCopower X).univ i k) (V.map p f) (V.evalHom Y),
      univ_comp_map (i := i) (j := i + p) (hij := rfl),
      univ_comp_evalHom,
      ← dgComp_assoc i 0 p i p (i + p) (by omega) hrp (by omega)
        ((V.isCopower X).univ i k) (V.evalHom X) f,
      univ_comp_evalHom]⟩

/-- **The evaluation transformation is closed.**

Componentwise this is the Leibniz rule against the identity cochain: the
universal family is a chain map, so differentiating `univ i k · eval` produces
the same term twice, once from each factor, and the factor that carries
`d eval` is what is left.

Closedness is what lets `evaluation` have a cone, which is the twist. -/
lemma evaluation_isClosed :
    DGFunctor.HomogeneousNatTrans.IsClosed V.evaluation := by
  ext X
  show ((dgHom (V.obj X) X).d 0 1).hom (V.evalHom X) = 0
  refine (V.isCopower X).lift_unique (fun i j hij k => ?_)
  have hji : j = i + 1 := by omega
  cases hji
  have hleib := dgComp_leibniz (C := C) i 0 i (i + 1) (by omega) (by omega)
    ((V.isCopower X).univ i k) (V.evalHom X)
  rw [V.univ_comp_evalHom, ← (V.isCopower X).univ_d i (i + 1),
    V.univ_comp_evalHom] at hleib
  simp only [Int.negOnePow_zero, one_smul, _root_.map_zero] at hleib ⊢
  exact add_right_cancel (hleib.symm.trans (zero_add _).symm)

end EvaluationData

end CategoryTheory
