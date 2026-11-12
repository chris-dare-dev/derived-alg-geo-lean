/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Basic

/-!
# `C^dg`: cochain complexes as a dg category

For a preadditive category `A`, the cochain complexes over `A` form a dg
category whose Hom-complexes are Mathlib's `CochainComplex.HomComplex`.

## Main definitions

* `CategoryTheory.Cdg` — a type synonym for `CochainComplex A ℤ`, so the dg
  structure does not attach itself to the cochain complexes globally;
  `CategoryTheory.Cdg.of` is the underlying cochain complex.
* `CategoryTheory.Cdg.struct` — the `DGCategoryStruct` on `Cdg A`, with
  Hom-complexes `CochainComplex.HomComplex` and composition `Cochain.comp`.

## Main results

* The `DGCategory` instance on `CategoryTheory.Cdg A`: every axiom is a Mathlib
  lemma about `Cochain`.
* `CategoryTheory.Cdg.dgHom_eq`, `CategoryTheory.Cdg.dgId_eq` and
  `CategoryTheory.Cdg.dgComp_eq` — the computation rules unfolding the
  instance.

## Implementation notes

Every field and every axiom is Mathlib's, not this repository's:

| `DGCategoryStruct` | supplied by |
|---|---|
| `dgHom` | `CochainComplex.HomComplex` |
| `dgId` | `Cochain.ofHom (𝟙 K)` |
| `dgComp` | `Cochain.comp` |
| `dgComp_assoc` | `Cochain.comp_assoc` |
| `dgId_comp`, `dgComp_id` | `Cochain.id_comp`, `Cochain.comp_id` |
| `dgId_cocycle` | `δ_ofHom` |
| `dgComp_leibniz` | `δ_comp` |

That the last row is a single lemma application rather than a sign argument is
why `DGCategory` has `AddCommGrpCat`-valued Hom-complexes and uses Mathlib's
sign convention for the Leibniz rule. A `ModuleCat k`-valued `dgHom` would not
typecheck against `HomComplex` at all, and the mirror Leibniz rule
`(δf) · g + (-1)^p · f · (δg)` typechecks but is false here.

## References

Mathlib's `CochainComplex.HomComplex`, `CochainComplex.HomComplex.Cochain.comp`
and `CochainComplex.HomComplex.δ_comp`.

## Tags

dg category, cochain complex, Hom complex, Leibniz rule
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CochainComplex.HomComplex

variable (A : Type u) [Category.{v} A] [Preadditive A]

/-- Cochain complexes over `A`, carrying their dg structure. A type synonym, so
the instance does not attach itself to `CochainComplex A ℤ` globally. -/
def Cdg : Type max u v := CochainComplex A ℤ

namespace Cdg

/-- The underlying cochain complex. -/
def of (K : Cdg A) : CochainComplex A ℤ := K

variable {A}

instance struct : DGCategoryStruct.{v} (Cdg A) where
  dgHom K L := CochainComplex.HomComplex (of A K) (of A L)
  dgId K := Cochain.ofHom (𝟙 (of A K))
  dgComp p q r h :=
    AddMonoidHom.mk' (fun z₁ =>
        AddMonoidHom.mk' (fun z₂ => z₁.comp z₂ h) (fun z₂ z₂' => z₁.comp_add z₂ z₂' h))
      (fun z₁ z₁' => by ext z₂; exact Cochain.add_comp z₁ z₁' z₂ h)

/-! The three computation rules that unfold this instance. Each is `rfl`; they
exist so `simp` can get from a `DGCategoryStruct` goal to a `Cochain` one, which
is where every Mathlib lemma is stated. -/

@[simp]
lemma dgHom_eq (K L : Cdg A) :
    DGCategoryStruct.dgHom K L = CochainComplex.HomComplex (of A K) (of A L) := rfl

@[simp]
lemma dgId_eq (K : Cdg A) :
    DGCategoryStruct.dgId K = Cochain.ofHom (𝟙 (of A K)) := rfl

-- Not `@[simp]`: the left-hand side simplifies further, so it can never be in
-- simp-normal form and the `simpNF` linter rejects it. It is used by name.
lemma dgComp_eq {K L M : Cdg A} (p q r : ℤ) (h : p + q = r)
    (f : (DGCategoryStruct.dgHom K L).X p) (g : (DGCategoryStruct.dgHom L M).X q) :
    DGCategoryStruct.dgComp p q r h f g = Cochain.comp f g h := rfl

/-- `C^dg A` is a dg category. Every axiom is a Mathlib lemma applied. -/
instance : DGCategory.{v} (Cdg A) where
  dgComp_assoc p q r pq qr pqr hpq hqr hpqr f g h :=
    Cochain.comp_assoc f g h hpq hqr (by omega)
  dgId_comp p f := Cochain.id_comp f
  dgComp_id p f := Cochain.comp_id f
  dgId_cocycle K := by
    simp only [dgHom_eq, dgId_eq]
    exact δ_ofHom _
  dgComp_leibniz p q r r' h hr f g := by
    simp only [dgHom_eq]
    exact δ_comp f g h (p + 1) (q + 1) r' hr rfl rfl

end Cdg

end CategoryTheory
