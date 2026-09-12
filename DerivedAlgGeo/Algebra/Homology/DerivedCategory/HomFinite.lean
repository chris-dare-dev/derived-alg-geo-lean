/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Hom-finiteness of a bounded derived category from Ext-finiteness

This file isolates the exact heart-level input needed to prove
`HomFiniteBounded k (DerivedCategory.Bounded A)`.  The input says that the
derived Ext spaces between degree-zero single objects are finite-dimensional
and have finite support.  A two-variable bounded induction then propagates
those facts across distinguished triangles.

For an abelian category, `ExtFiniteBounded.of_ext` reduces this input to the
usual nonnegative groups `Abelian.Ext X Y n`: negative shifted Homs vanish by
the canonical t-structure, while `Abelian.Ext.homLinearEquiv` handles
nonnegative degrees.

## Geometric boundary

For `A = Coh X`, neither Serre finiteness of coherent cohomology nor
`CoherentExtComparison X` alone proves the hypotheses of `of_ext`.  A smooth
projective application still has to prove that every coherent-sheaf Ext group
is finite-dimensional and that these groups vanish in sufficiently high
degree (for a K3 surface, regularity should give the sharp amplitude).  This
file makes that remaining obligation explicit; it does not install a
geometric instance or assume a bounded resolution.
-/

universe w v u t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Module.Finite

variable {k : Type t} [DivisionRing k]
variable {U : Type u} {V : Type v} {W : Type w}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module k U] [Module k V] [Module k W]

/-- If `U ⟶ V ⟶ W` is exact and the outer vector spaces are
finite-dimensional, then so is the middle vector space. -/
theorem of_exact_middle (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (h : Function.Exact f g) [Module.Finite k U] [Module.Finite k W] :
    Module.Finite k V := by
  let q : (V ⧸ LinearMap.range f) →ₗ[k] W :=
    (LinearMap.range f).liftQ g (fun x hx ↦ (h x).mpr hx)
  have hq : Function.Injective q := LinearMap.injective_range_liftQ_of_exact h
  letI : Module.Finite k (V ⧸ LinearMap.range f) :=
    FiniteDimensional.of_injective q hq
  exact Module.Finite.of_submodule_quotient (LinearMap.range f)

end Module.Finite

namespace DerivedCategory

variable {k : Type t} [DivisionRing k]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear k A]
variable [HasDerivedCategory.{w} A]

attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

/-- Heart-level properness: derived Ext spaces between degree-zero single
objects are finite-dimensional and only finitely many shifts contribute.

The uniform `ℤ`-grading is the form consumed by triangulated dévissage.
Use `ExtFiniteBounded.of_ext` to construct it from the usual nonnegative
`Abelian.Ext` groups. -/
class ExtFiniteBounded : Prop where
  /-- Every shifted Ext space between heart objects is finite-dimensional. -/
  finite : ∀ (X Y : A) (i : ℤ), Module.Finite k
    (ShiftedHom ((singleFunctor A 0).obj X) ((singleFunctor A 0).obj Y) i)
  /-- Only finitely many shifted Ext spaces between a fixed pair contribute. -/
  support_finite : ∀ X Y : A,
    (Function.support fun i : ℤ ↦
      (Module.finrank k
        (ShiftedHom ((singleFunctor A 0).obj X) ((singleFunctor A 0).obj Y) i) : ℤ)).Finite

attribute [instance] ExtFiniteBounded.finite

namespace ExtFiniteBounded

/-- Construct heart-level properness from finite-dimensional ordinary Ext
groups with finite support.  Negative shifted Homs vanish formally from the
canonical t-structure. -/
theorem of_ext
    (hfinite : ∀ (X Y : A) (n : ℕ), Module.Finite k (Abelian.Ext.{w} X Y n))
    (hsupport : ∀ X Y : A,
      (Function.support fun n : ℕ ↦
        (Module.finrank k (Abelian.Ext.{w} X Y n) : ℤ)).Finite) :
    ExtFiniteBounded (k := k) (A := A) where
  finite X Y i := by
    by_cases hi : 0 ≤ i
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      letI := hfinite X Y n
      exact Module.Finite.equiv
        (Abelian.Ext.homLinearEquiv (R := k) (X := X) (Y := Y) (n := n))
    · have hi' : i < 0 := by omega
      have hle : TStructure.t.IsLE ((singleFunctor A 0).obj X) 0 := inferInstance
      have hge : TStructure.t.IsGE (((singleFunctor A 0).obj Y)⟦i⟧) (-i) :=
        TStructure.t.isGE_shift _ 0 i (-i) (by omega)
      haveI : Subsingleton
          (ShiftedHom ((singleFunctor A 0).obj X) ((singleFunctor A 0).obj Y) i) :=
        ⟨fun f g ↦ by
          rw [TStructure.t.zero_of_isLE_of_isGE f 0 (-i) (by omega) hle hge,
            TStructure.t.zero_of_isLE_of_isGE g 0 (-i) (by omega) hle hge]⟩
      exact Module.Finite.of_surjective (0 : k →ₗ[k] _)
        (fun x ↦ ⟨0, Subsingleton.elim _ x⟩)
  support_finite X Y := by
    refine ((hsupport X Y).image fun n : ℕ ↦ (n : ℤ)).subset ?_
    intro i hi
    by_cases hneg : i < 0
    · have hle : TStructure.t.IsLE ((singleFunctor A 0).obj X) 0 := inferInstance
      have hge : TStructure.t.IsGE (((singleFunctor A 0).obj Y)⟦i⟧) (-i) :=
        TStructure.t.isGE_shift _ 0 i (-i) (by omega)
      haveI : Subsingleton
          (ShiftedHom ((singleFunctor A 0).obj X) ((singleFunctor A 0).obj Y) i) :=
        ⟨fun f g ↦ by
          rw [TStructure.t.zero_of_isLE_of_isGE f 0 (-i) (by omega) hle hge,
            TStructure.t.zero_of_isLE_of_isGE g 0 (-i) (by omega) hle hge]⟩
      have hz : Module.finrank k
          (ShiftedHom ((singleFunctor A 0).obj X) ((singleFunctor A 0).obj Y) i) = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [Function.mem_support] at hi
      exact (hi (by exact_mod_cast hz)).elim
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      refine ⟨n, ?_, rfl⟩
      rw [Function.mem_support] at hi ⊢
      intro hn
      apply hi
      have hn' : Module.finrank k (Abelian.Ext.{w} X Y n) = 0 := by
        exact_mod_cast hn
      have he := (Abelian.Ext.homLinearEquiv
        (R := k) (X := X) (Y := Y) (n := n)).finrank_eq
      exact_mod_cast he.symm.trans hn'

end ExtFiniteBounded

/-- The pairwise version of `HomFiniteBounded`, used while dévissing one
variable at a time. -/
structure HomFiniteBoundedPair (X Y : DerivedCategory A) : Prop where
  finite : ∀ i : ℤ, Module.Finite k (X ⟶ Y⟦i⟧)
  support_finite :
    (Function.support fun i : ℤ ↦ (Module.finrank k (X ⟶ Y⟦i⟧) : ℤ)).Finite

namespace HomFiniteBoundedPair

variable {X Y X' Y' : DerivedCategory A}

/-- Simultaneously shifting both objects translates the Ext degree. -/
private noncomputable def shiftLinearEquiv (s t i : ℤ) :
    (X⟦s⟧ ⟶ (Y⟦t⟧)⟦i⟧) ≃ₗ[k] (X ⟶ Y⟦t + i - s⟧) := by
  let shiftBack := shiftFunctor (DerivedCategory A) (-s)
  let eShift : (X⟦s⟧ ⟶ (Y⟦t⟧)⟦i⟧) ≃ₗ[k]
      ((X⟦s⟧)⟦-s⟧ ⟶ ((Y⟦t⟧)⟦i⟧)⟦-s⟧) :=
    homLinearEquivOfFullyFaithful shiftBack
      (shiftEquiv (DerivedCategory A) (-s)).fullyFaithfulFunctor _ _
  let sourceIso : (X⟦s⟧)⟦-s⟧ ≅ X :=
    (shiftFunctorCompIsoId (DerivedCategory A) s (-s) (by omega)).app X
  let targetIso : ((Y⟦t⟧)⟦i⟧)⟦-s⟧ ≅ Y⟦t + i - s⟧ :=
    (shiftFunctor (DerivedCategory A) (-s)).mapIso
        (((shiftFunctorAdd' (DerivedCategory A) t i (t + i) rfl).app Y).symm) ≪≫
      (((shiftFunctorAdd' (DerivedCategory A) (t + i) (-s) (t + i - s)
        (by omega)).app Y).symm)
  exact eShift.trans (Linear.homCongr k sourceIso targetIso)

/-- `HomFiniteBoundedPair` is invariant under isomorphism in both variables. -/
theorem of_iso (h : HomFiniteBoundedPair (k := k) X Y)
    (eX : X ≅ X') (eY : Y ≅ Y') : HomFiniteBoundedPair (k := k) X' Y' where
  finite i := by
    letI := h.finite i
    exact Module.Finite.equiv
      (Linear.homCongr k eX ((shiftFunctor (DerivedCategory A) i).mapIso eY))
  support_finite := by
    have heq : (fun i : ℤ ↦ (Module.finrank k (X' ⟶ Y'⟦i⟧) : ℤ)) =
        fun i : ℤ ↦ (Module.finrank k (X ⟶ Y⟦i⟧) : ℤ) := by
      funext i
      exact_mod_cast
        (Linear.homCongr k eX ((shiftFunctor (DerivedCategory A) i).mapIso eY)).finrank_eq.symm
    rw [heq]
    exact h.support_finite

/-- `HomFiniteBoundedPair` is invariant under independent shifts of its two
objects. -/
theorem shift (h : HomFiniteBoundedPair (k := k) X Y) (s t : ℤ) :
    HomFiniteBoundedPair (k := k) (X⟦s⟧) (Y⟦t⟧) where
  finite i := by
    letI := h.finite (t + i - s)
    exact Module.Finite.equiv
      (shiftLinearEquiv (k := k) (X := X) (Y := Y) s t i).symm
  support_finite := by
    refine (h.support_finite.image fun j : ℤ ↦ j - t + s).subset ?_
    intro i hi
    refine ⟨t + i - s, ?_, by ring⟩
    rw [Function.mem_support] at hi ⊢
    intro hz
    apply hi
    have he := (shiftLinearEquiv (k := k) (X := X) (Y := Y) s t i).finrank_eq
    have hz' : Module.finrank k (X ⟶ Y⟦t + i - s⟧) = 0 := by
      exact_mod_cast hz
    exact_mod_cast he.trans hz'

end HomFiniteBoundedPair

section Exact

variable {I : Type*}
variable {U V W : I → Type*}
variable [∀ i, AddCommGroup (U i)] [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
variable [∀ i, Module k (U i)] [∀ i, Module k (V i)] [∀ i, Module k (W i)]

/-- Pointwise exactness places the finrank support of the middle family inside
the union of the two outer supports. -/
private theorem support_finite_of_exact
    (f : ∀ i, U i →ₗ[k] V i) (g : ∀ i, V i →ₗ[k] W i)
    (hexact : ∀ i, Function.Exact (f i) (g i))
    [∀ i, Module.Finite k (U i)] [∀ i, Module.Finite k (W i)]
    (hU : (Function.support fun i ↦ (Module.finrank k (U i) : ℤ)).Finite)
    (hW : (Function.support fun i ↦ (Module.finrank k (W i) : ℤ)).Finite) :
    (Function.support fun i ↦ (Module.finrank k (V i) : ℤ)).Finite := by
  refine (hU.union hW).subset ?_
  intro i hi
  by_contra hi'
  have hiU : i ∉ Function.support (fun i ↦ (Module.finrank k (U i) : ℤ)) :=
    fun h ↦ hi' (Set.mem_union_left _ h)
  have hiW : i ∉ Function.support (fun i ↦ (Module.finrank k (W i) : ℤ)) :=
    fun h ↦ hi' (Set.mem_union_right _ h)
  rw [Function.mem_support, not_ne_iff] at hiU hiW
  have hiU' : Module.finrank k (U i) = 0 := by exact_mod_cast hiU
  have hiW' : Module.finrank k (W i) = 0 := by exact_mod_cast hiW
  have hUzero : ∀ x : U i, x = 0 := finrank_zero_iff_forall_zero.mp hiU'
  have hWzero : ∀ x : W i, x = 0 := finrank_zero_iff_forall_zero.mp hiW'
  have zero_of (x : V i) : x = 0 := by
    obtain ⟨z, hz⟩ := (hexact i x).mp (hWzero ((g i) x))
    rw [← hz, hUzero z, map_zero]
  haveI : Subsingleton (V i) := ⟨fun x y ↦ (zero_of x).trans (zero_of y).symm⟩
  have hz : Module.finrank k (V i) = 0 := Module.finrank_zero_of_subsingleton
  rw [Function.mem_support] at hi
  exact hi (by exact_mod_cast hz)

end Exact

namespace HomFiniteBoundedPair

variable {X : DerivedCategory A}

private noncomputable def postcomp {Y Z : DerivedCategory A} (f : Y ⟶ Z) :
    (X ⟶ Y) →ₗ[k] (X ⟶ Z) :=
  { toFun := fun a ↦ a ≫ f
    map_add' := by simp
    map_smul' := by simp }

private theorem postcomp_exact (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang _) :
    Function.Exact (postcomp (k := k) (X := X) T.mor₁)
      (postcomp (k := k) (X := X) T.mor₂) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T hT x hx
    exact ⟨y, by simpa [postcomp] using hy.symm⟩
  · rintro ⟨y, rfl⟩
    change (y ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

private noncomputable def precomp {X Y Z : DerivedCategory A} (f : X ⟶ Y) :
    (Y ⟶ Z) →ₗ[k] (X ⟶ Z) :=
  { toFun := fun a ↦ f ≫ a
    map_add' := by simp
    map_smul' := by simp }

private theorem precomp_exact (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang _) (Y : DerivedCategory A) :
    Function.Exact (precomp (k := k) (Z := Y) T.mor₂)
      (precomp (k := k) (Z := Y) T.mor₁) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x hx
    exact ⟨y, by simpa [precomp] using hy.symm⟩
  · rintro ⟨y, rfl⟩
    change T.mor₁ ≫ T.mor₂ ≫ y = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

/-- Pairwise Hom-finiteness is closed under the middle object of a
distinguished triangle in the second variable. -/
theorem obj₂_right (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : HomFiniteBoundedPair (k := k) X T.obj₁)
    (h₃ : HomFiniteBoundedPair (k := k) X T.obj₃) :
    HomFiniteBoundedPair (k := k) X T.obj₂ where
  finite i := by
    let S := (shiftFunctor (Triangle (DerivedCategory A)) i).obj T
    have hS : S ∈ distTriang _ := Triangle.shift_distinguished T hT i
    letI : Module.Finite k (X ⟶ S.obj₁) := by
      change Module.Finite k (X ⟶ T.obj₁⟦i⟧)
      exact h₁.finite i
    letI : Module.Finite k (X ⟶ S.obj₃) := by
      change Module.Finite k (X ⟶ T.obj₃⟦i⟧)
      exact h₃.finite i
    exact Module.Finite.of_exact_middle
      (postcomp (k := k) (X := X) S.mor₁)
      (postcomp (k := k) (X := X) S.mor₂)
      (postcomp_exact (k := k) (X := X) S hS)
  support_finite := by
    letI (i : ℤ) : Module.Finite k
        (X ⟶ ((shiftFunctor (Triangle (DerivedCategory A)) i).obj T).obj₁) := by
      change Module.Finite k (X ⟶ T.obj₁⟦i⟧)
      exact h₁.finite i
    letI (i : ℤ) : Module.Finite k
        (X ⟶ ((shiftFunctor (Triangle (DerivedCategory A)) i).obj T).obj₃) := by
      change Module.Finite k (X ⟶ T.obj₃⟦i⟧)
      exact h₃.finite i
    exact support_finite_of_exact
      (fun i ↦ postcomp (k := k) (X := X)
        ((shiftFunctor (Triangle (DerivedCategory A)) i).obj T).mor₁)
      (fun i ↦ postcomp (k := k) (X := X)
        ((shiftFunctor (Triangle (DerivedCategory A)) i).obj T).mor₂)
      (fun i ↦ postcomp_exact (k := k) (X := X)
        ((shiftFunctor (Triangle (DerivedCategory A)) i).obj T)
        (Triangle.shift_distinguished T hT i))
      h₁.support_finite h₃.support_finite

variable {Y : DerivedCategory A}

/-- Pairwise Hom-finiteness is closed under the middle object of a
distinguished triangle in the first variable. -/
theorem obj₂_left (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : HomFiniteBoundedPair (k := k) T.obj₁ Y)
    (h₃ : HomFiniteBoundedPair (k := k) T.obj₃ Y) :
    HomFiniteBoundedPair (k := k) T.obj₂ Y where
  finite i := by
    letI := h₃.finite i
    letI := h₁.finite i
    exact Module.Finite.of_exact_middle
      (precomp (k := k) (Z := Y⟦i⟧) T.mor₂)
      (precomp (k := k) (Z := Y⟦i⟧) T.mor₁)
      (precomp_exact (k := k) T hT (Y⟦i⟧))
  support_finite := by
    letI (i : ℤ) := h₃.finite i
    letI (i : ℤ) := h₁.finite i
    exact support_finite_of_exact
      (fun i ↦ precomp (k := k) (Z := Y⟦i⟧) T.mor₂)
      (fun i ↦ precomp (k := k) (Z := Y⟦i⟧) T.mor₁)
      (fun i ↦ precomp_exact (k := k) T hT (Y⟦i⟧))
      h₃.support_finite h₁.support_finite

end HomFiniteBoundedPair

variable [ExtFiniteBounded (k := k) (A := A)]

/-- Heart-level Ext-finiteness propagates to a bounded object in the first
variable and a degree-zero heart object in the second. -/
private theorem homFiniteBoundedPair_bounded_single {E : DerivedCategory A}
    (hE : TStructure.t.bounded E) (Y : A) :
    HomFiniteBoundedPair (k := k) E ((singleFunctor A 0).obj Y) := by
  refine bounded_induction (⊤ : ObjectProperty A)
    (fun E ↦ ∀ Y : A, HomFiniteBoundedPair (k := k) E ((singleFunctor A 0).obj Y))
    ?_ ?_ ?_ hE (fun _ ↦ trivial) Y
  · intro E E' e h Y
    exact (h Y).of_iso e (Iso.refl _)
  · intro n X _ Y
    let e : ((singleFunctor A 0).obj X)⟦-n⟧ ≅ (singleFunctor A n).obj X :=
      ((singleFunctors A).shiftIso (-n) n 0 (by omega)).app X
    exact ((⟨ExtFiniteBounded.finite X Y,
      ExtFiniteBounded.support_finite X Y⟩ :
        HomFiniteBoundedPair (k := k) ((singleFunctor A 0).obj X)
          ((singleFunctor A 0).obj Y)).shift (-n) 0).of_iso e
      ((shiftFunctorZero (DerivedCategory A) ℤ).app ((singleFunctor A 0).obj Y))
  · intro T hT h₁ h₃ Y
    exact HomFiniteBoundedPair.obj₂_left T hT (h₁ Y) (h₃ Y)

/-- Heart-level Ext-finiteness propagates to every pair of bounded derived
objects. -/
theorem homFiniteBoundedPair_of_bounded {E E' : DerivedCategory A}
    (hE : TStructure.t.bounded E) (hE' : TStructure.t.bounded E') :
    HomFiniteBoundedPair (k := k) E E' := by
  refine bounded_induction (⊤ : ObjectProperty A)
    (fun E' ↦ HomFiniteBoundedPair (k := k) E E') ?_ ?_ ?_ hE'
      (fun _ ↦ trivial)
  · intro W W' e h
    exact h.of_iso (Iso.refl _) e
  · intro n Y _
    let e : ((singleFunctor A 0).obj Y)⟦-n⟧ ≅ (singleFunctor A n).obj Y :=
      ((singleFunctors A).shiftIso (-n) n 0 (by omega)).app Y
    exact (homFiniteBoundedPair_bounded_single (k := k) hE Y).shift 0 (-n) |>.of_iso
      ((shiftFunctorZero (DerivedCategory A) ℤ).app E) e
  · intro T hT h₁ h₃
    exact HomFiniteBoundedPair.obj₂_right T hT h₁ h₃

/-- **Bounded derived Hom-finiteness from heart Ext-finiteness.**

This is a named theorem rather than a global instance so geometric callers
must choose and expose the heart-level input explicitly. -/
theorem homFiniteBounded_boundedDerived :
    HomFiniteBounded k (DerivedCategory.Bounded A) where
  finite E E' i := by
    have h := homFiniteBoundedPair_of_bounded (k := k) E.property E'.property
    letI : Module.Finite k
        ((DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A).obj E ⟶
          ((DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A).obj E')⟦i⟧) :=
      h.finite i
    exact Module.Finite.equiv
      (homShiftLinearEquiv
        (DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A)
        (ObjectProperty.fullyFaithfulι _) E E' i).symm
  support_finite E E' := by
    have h := homFiniteBoundedPair_of_bounded (k := k) E.property E'.property
    have heq : (fun i : ℤ ↦ (Module.finrank k (E ⟶ E'⟦i⟧) : ℤ)) =
        fun i : ℤ ↦
          (Module.finrank k
            ((DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A).obj E ⟶
              ((DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A).obj E')⟦i⟧) : ℤ) := by
      funext i
      exact_mod_cast
        (finrank_hom_shift_map
          (DerivedCategory.Bounded.ι : DerivedCategory.Bounded A ⥤ DerivedCategory A)
          (ObjectProperty.fullyFaithfulι _) E E' i).symm
    rw [heq]
    exact h.support_finite

end DerivedCategory
