/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Bounded induction on objects with cohomology in a subcategory

Let `A` be an abelian category and `P : ObjectProperty A` a class of objects
closed under isomorphism and containing zero. The canonical truncation
triangles of `DerivedCategory A` do not leave `cohomologyIn P`: the
cohomology of a truncation is either a cohomology object of the original
complex or zero. This file proves that, and derives from it the induction
principle a dévissage runs on.

## Main results

* `DerivedCategory.cohomologyIn_truncLT`, `DerivedCategory.cohomologyIn_truncGE`:
  the canonical truncations of an object with cohomology in `P` have cohomology
  in `P`.
* `DerivedCategory.bounded_induction`: a property of objects of the derived
  category that holds for every single object with cohomology in `P`, is
  closed under isomorphism, and is closed under the middle term of a
  distinguished triangle, holds for every bounded object with cohomology in
  `P`. The induction is on the cohomological amplitude, and the step is the
  truncation triangle `τ_{< a + 1} E ⟶ E ⟶ τ_{≥ a + 1} E`.

Taking `P = ⊤` gives the absolute statement: a triangulated-closed,
isomorphism-closed property containing every single object holds on
`DerivedCategory.Bounded A`.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- The cohomology of `τ_{< n} E` in degree `i` is that of `E` for `i < n` and zero
otherwise, so it lies in `P` whenever the cohomology of `E` does. -/
lemma cohomologyIn_truncLT {E : DerivedCategory A} (hE : cohomologyIn P E) (n : ℤ) :
    cohomologyIn P ((TStructure.t.truncLT n).obj E) := by
  intro i
  set T := (TStructure.t.triangleLTGE n).obj E with hT_def
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished n E
  by_cases hi : i < n
  · -- `Hⁱ(τ_{< n} E) ⟶ Hⁱ E` is an isomorphism.
    have h₃ : IsZero ((homologyFunctor A i).obj T.obj₃) :=
      isZero_of_isGE T.obj₃ n i hi
    have h₃' : IsZero ((homologyFunctor A (i - 1)).obj T.obj₃) :=
      isZero_of_isGE T.obj₃ n (i - 1) (by omega)
    have hmono : Mono ((homologyFunctor A i).map T.mor₁) :=
      (HomologySequence.exact₁ T hT (i - 1) i (by omega)).mono_g (h₃'.eq_of_src _ _)
    have hepi : Epi ((homologyFunctor A i).map T.mor₁) :=
      (HomologySequence.exact₂ T hT i).epi_f (h₃.eq_of_tgt _ _)
    have hiso : IsIso ((homologyFunctor A i).map T.mor₁) := isIso_of_mono_of_epi _
    exact P.prop_of_iso (@asIso _ _ _ _ _ hiso).symm (hE i)
  · exact P.prop_of_isZero (isZero_of_isLE T.obj₁ (n - 1) i (by omega))

/-- The cohomology of `τ_{≥ n} E` in degree `i` is that of `E` for `n ≤ i` and zero
otherwise, so it lies in `P` whenever the cohomology of `E` does. -/
lemma cohomologyIn_truncGE {E : DerivedCategory A} (hE : cohomologyIn P E) (n : ℤ) :
    cohomologyIn P ((TStructure.t.truncGE n).obj E) := by
  intro i
  set T := (TStructure.t.triangleLTGE n).obj E with hT_def
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished n E
  by_cases hi : i < n
  · exact P.prop_of_isZero (isZero_of_isGE T.obj₃ n i hi)
  · -- `Hⁱ E ⟶ Hⁱ(τ_{≥ n} E)` is an isomorphism.
    have h₁ : IsZero ((homologyFunctor A i).obj T.obj₁) :=
      isZero_of_isLE T.obj₁ (n - 1) i (by omega)
    have h₁' : IsZero ((homologyFunctor A (i + 1)).obj T.obj₁) :=
      isZero_of_isLE T.obj₁ (n - 1) (i + 1) (by omega)
    have hmono : Mono ((homologyFunctor A i).map T.mor₂) :=
      (HomologySequence.exact₂ T hT i).mono_g (h₁.eq_of_src _ _)
    have hepi : Epi ((homologyFunctor A i).map T.mor₂) :=
      (HomologySequence.exact₃ T hT i (i + 1) rfl).epi_f (h₁'.eq_of_tgt _ _)
    have hiso : IsIso ((homologyFunctor A i).map T.mor₂) := isIso_of_mono_of_epi _
    exact P.prop_of_iso (@asIso _ _ _ _ _ hiso) (hE i)

omit [P.ContainsZero] in
/-- The single object `(singleFunctor A n).obj Y` has cohomology in `P` exactly
when `Y` does; only the forward direction is needed downstream. -/
lemma prop_of_cohomologyIn_singleFunctor_obj {n : ℤ} {Y : A}
    (h : cohomologyIn P ((singleFunctor A n).obj Y)) : P Y :=
  P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A n).app Y) (h n)

/-- **Bounded induction.** Let `Q` be a property of objects of the derived
category which is closed under isomorphism, holds for every single object
`(singleFunctor A n).obj Y` with `P Y`, and holds for the middle term of a
distinguished triangle whenever it holds for the outer two. Then `Q` holds for
every bounded object whose cohomology lies in `P`.

The induction is on the amplitude `N` with `E` concentrated in `[a, a + N]`;
the step splits `E` by the truncation triangle at `a + 1`, whose first term is
concentrated in degree `a` and whose third term has amplitude `N - 1`. -/
theorem bounded_induction (Q : ObjectProperty (DerivedCategory A))
    (hiso : ∀ {E E' : DerivedCategory A}, (E ≅ E') → Q E → Q E')
    (hsingle : ∀ (n : ℤ) (Y : A), P Y → Q ((singleFunctor A n).obj Y))
    (hcone : ∀ (T : Triangle (DerivedCategory A)), T ∈ distTriang _ →
      Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    {E : DerivedCategory A} (hE : TStructure.t.bounded E) (hP : cohomologyIn P E) : Q E := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hE
  suffices key : ∀ (N : ℕ) (E : DerivedCategory A) (a : ℤ), E.IsGE a → E.IsLE (a + N) →
      cohomologyIn P E → Q E by
    refine key (b - a).toNat E a ha ?_ hP
    exact TStructure.t.isLE_of_le E b _ (by omega)
  intro N
  induction N with
  | zero =>
    intro E a ha hb hP
    have : E.IsLE a := by simpa using hb
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE E a
    refine hiso e.symm (hsingle a Y ?_)
    exact prop_of_cohomologyIn_singleFunctor_obj P
      (fun i ↦ P.prop_of_iso ((homologyFunctor A i).mapIso e) (hP i))
  | succ N ih =>
    intro E a ha hb hP
    refine hcone _ (TStructure.t.triangleLTGE_distinguished (a + 1) E) ?_ ?_
    · refine ih ((TStructure.t.truncLT (a + 1)).obj E) a inferInstance ?_
        (cohomologyIn_truncLT P hP (a + 1))
      exact TStructure.t.isLE_of_le _ a _ (by omega)
    · refine ih ((TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance ?_
        (cohomologyIn_truncGE P hP (a + 1))
      have : ((TStructure.t.truncGE (a + 1)).obj E).IsLE (a + (N + 1 : ℕ)) := inferInstance
      exact TStructure.t.isLE_of_le _ (a + (N + 1 : ℕ)) _ (by push_cast; omega)

end DerivedCategory
