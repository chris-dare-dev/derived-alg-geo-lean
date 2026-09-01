/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The Čech differential in coordinates

Mathlib defines the Čech complex of a presheaf as `alternatingCofaceMapComplex` applied to the
cosimplicial object attached to the Čech nerve of a formal coproduct. That definition is compact
but says nothing directly about components: it never names the index of a cochain, nor the
restriction that carries a face into it.

This file supplies that reading. `cechComplexFunctor_delta_π` computes one coface at one index,
and `cechComplexFunctor_d_π` assembles the alternating sum. Both are statements about Mathlib's
construction, so they live in Mathlib's namespace.

## Main statements

* `cechComplexFunctor_delta_π` — the `j`-th coface, projected at `x`, is the projection at the
  face `x ∘ j.succAbove` followed by the presheaf on the face inclusion;
* `cechComplexFunctor_d_π` — the differential, projected at `x`, is the alternating sum of those;
* `cechComplexFunctor_map_f_π` — the map induced by a morphism of presheaves, projected at `x`, is
  the projection at `x` followed by that morphism on the intersection.

## Implementation notes

The projections are stated in the shape Mathlib's construction produces, indexed by
`ToType (mk n) → ι` with the object written through the Čech nerve rather than as `∏ᶜ (U ∘ x)`.
A caller-friendly restatement belongs downstream, together with the identification of the
intersection.

Both proofs finish with `exact` rather than `rw`. The two sides differ in the `HasProduct`
instance argument that `Pi.π` carries, which `rw` will not see through but definitional
unification will. Rewriting with `Pi.lift_π` fails here for that reason alone.

`Fin.succAbove` needs no reindexing lemma: `SimplexCategory.δ j` has
`toOrderHom = Fin.succAbove j`, so this is the shape the Čech nerve already produces via
`FormalCoproduct.mapPower`.
-/

universe w v' v u' u

open CategoryTheory.Limits AlgebraicTopology Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
variable [HasProducts.{w} A] [HasFiniteProducts C] [Preadditive A]
variable {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The Čech nerve of the family `U`, as a simplicial formal coproduct. -/
noncomputable abbrev cechNerve : SimplicialObject (Limits.FormalCoproduct C) :=
  (Limits.FormalCoproduct.mk _ U).cech

/-- The Čech cosimplicial object of a presheaf against the nerve of `U`. -/
noncomputable abbrev cechCosimplicial : CosimplicialObject A :=
  (Limits.FormalCoproduct.cosimplicialObjectFunctor (cechNerve U)).obj P

/-- Degree-`n` Čech cochains, in the shape Mathlib's construction produces. -/
noncomputable abbrev cechTermFamily (n : ℕ) :
    (ToType (SimplexCategory.mk n) → ι) → A :=
  fun x => P.obj (op (((cechNerve U).obj (op (SimplexCategory.mk n))).obj x))

omit [Preadditive A] in
/-- The `j`-th coface, projected at the index `x`, is the projection at the face index
`(cech.map (δ j).op).f x = x ∘ j.succAbove` followed by the presheaf on the face inclusion.

Preadditivity plays no part here — only the alternating sum in `cechComplexFunctor_d_π` needs
it. -/
theorem cechComplexFunctor_delta_π {n : ℕ} (j : Fin (n + 2))
    (x : ToType (SimplexCategory.mk (n + 1)) → ι) :
    (cechCosimplicial U P).δ j ≫ Pi.π (cechTermFamily U P (n + 1)) x =
      Pi.π (cechTermFamily U P n) (((cechNerve U).map (SimplexCategory.δ j).op).f x) ≫
        P.map (((cechNerve U).map (SimplexCategory.δ j).op).φ x).op := by
  rw [CosimplicialObject.δ, Limits.FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Limits.Pi.lift_π _ _

/-- The map a morphism of presheaves induces on Čech cochains, projected at the index `x`, is the
projection at `x` followed by the morphism on that intersection.

`evalOp` sends a morphism to `Pi.map` componentwise, so once the two sides are recognised as a
`Pi.map` and its projection this is `Pi.map_π`. The recognition is `rfl` rather than a rewrite:
`cechComplexFunctor` reaches `evalOp` through two functor compositions, and only definitional
unfolding crosses them.

Unlike `cechComplexFunctor_delta_π` this cannot omit `Preadditive A`: it names
`cechComplexFunctor` itself, whose target `CochainComplex A ℕ` needs the zero morphisms. -/
theorem cechComplexFunctor_map_f_π {F G : Cᵒᵖ ⥤ A} (φ : F ⟶ G) (n : ℕ)
    (x : ToType (SimplexCategory.mk n) → ι) :
    ((cechComplexFunctor U).map φ).f n ≫ Pi.π (cechTermFamily U G n) x =
      Pi.π (cechTermFamily U F n) x ≫
        φ.app (op (((cechNerve U).obj (op (SimplexCategory.mk n))).obj x)) := by
  have h : ((cechComplexFunctor U).map φ).f n =
      Limits.Pi.map (fun i : ToType (SimplexCategory.mk n) → ι =>
        φ.app (op (((cechNerve U).obj (op (SimplexCategory.mk n))).obj i))) := rfl
  rw [h]
  exact Limits.Pi.map_π _ _

/-- The Čech differential, projected at the index `x`, is the alternating sum of the face
restrictions. This is the formula a concrete computation of `Hⁱ` consumes. -/
theorem cechComplexFunctor_d_π {n : ℕ} (x : ToType (SimplexCategory.mk (n + 1)) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ Pi.π (cechTermFamily U P (n + 1)) x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Pi.π (cechTermFamily U P n) (((cechNerve U).map (SimplexCategory.δ j).op).f x) ≫
          P.map (((cechNerve U).map (SimplexCategory.δ j).op).φ x).op) := by
  have hd : ((cechComplexFunctor U).obj P).d n (n + 1) =
      AlternatingCofaceMapComplex.objD (cechCosimplicial U P) n := by
    show ((Limits.FormalCoproduct.cochainComplexFunctor (cechNerve U)).obj P).d n (n + 1) = _
    rw [Limits.FormalCoproduct.cochainComplexFunctor_obj_d, CochainComplex.of_d]
  rw [hd, AlternatingCofaceMapComplex.objD]
  refine (Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (Preadditive.zsmul_comp _ _ _).trans ?_
  exact congrArg (fun m => (-1 : ℤ) ^ (j : ℕ) • m) (cechComplexFunctor_delta_π U P j x)

end CategoryTheory
