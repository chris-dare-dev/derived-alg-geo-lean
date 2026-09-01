/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# The alternating coface complex is the opposite of an alternating face complex

Mathlib develops extra degeneracies, and the homotopy equivalence they induce, on the
**simplicial** side: `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` is stated
against `alternatingFaceMapComplex` and lands in `ChainComplex`. Čech cohomology, in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, is built from
`alternatingCofaceMapComplex` and is **cosimplicial**. Nothing upstream connects the two, so
no Čech vanishing argument can reach the machinery that would prove it.

This file supplies the connection: for a cosimplicial object `Y` in a preadditive category,

```lean
((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op
```

Both sides are `Y.obj ⦋n⦌` in degree `n` — that much is `rfl` — and both differentials are
`∑ i, (-1) ^ i • δ i`. What is not `rfl` is that `HomologicalComplex.op` distributes over the
sum and the `zsmul`; that is the content, such as it is, and `op_sum` and `op_zsmul` supply
it.

## Why this is the useful direction

The alternative is to define an extra *co*degeneracy structure on augmented cosimplicial
objects and redo the homotopy from scratch, roughly duplicating
`Mathlib/AlgebraicTopology/ExtraDegeneracy.lean`. With this isomorphism that is unnecessary:
a cosimplicial object in `A` is a simplicial object in `Aᵒᵖ`, the upstream extra-degeneracy
theory applies there verbatim, and the isomorphism carries its conclusion back. In
particular `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` — the Čech object of a
family has an extra degeneracy once the terminal object maps into one of its members — is
already upstream and can be used as it stands.

## The payoff

`exactAt_succ_of_extraDegeneracy` is what #13 consumes: an extra degeneracy on an augmented
simplicial object in `Aᵒᵖ` whose underlying object is `Y.op` forces the alternating coface
complex of `Y` to be exact in every positive degree. The chain is
`ExtraDegeneracy.homotopyEquiv` (upstream) → quasi-isomorphism → `exactAt_iff_of_quasiIsoAt`
→ `ChainComplex.exactAt_succ_single_obj`, carried across `opIso`.

`exactAt_succ_of_extraDegeneracy_map` adds the contravariant transport. `ExtraDegeneracy.map`
takes a covariant functor, while Čech cohomology applies `FormalCoproduct.evalOp` of a
presheaf, which is contravariant on the site; `Functor.rightOp` turns one into the other, and
this lemma is the composite in the form the caller wants.

## Not done here

An augmentation `ε` for `alternatingCofaceMapComplex`, dual to `AlternatingFaceMapComplex.ε`,
was expected to be needed and **is not**. The augmentation is handled on the simplicial side
by `homotopyEquiv`, and the coface complex only ever appears unaugmented, so adding one would
be dead weight. Recorded because the issue asked for it.

`DerivedAlgGeo/AlgebraicGeometry/Cohomology/Cech/Affine.lean` now supplies the remaining affine
argument: it identifies
the restriction maps degreewise as localizations and descends exactness from a finite
distinguished-open cover whose defining elements span the unit ideal.

The `Abelian A` hypothesis is stronger than the argument needs — `Preadditive`, a zero object
and homology would do — but the two `HasZeroMorphisms Aᵒᵖ` instances (`Preadditive`'s and
`Limits.hasZeroMorphismsOpposite`) are only definitionally equal, and `rw` sees through
neither. Assuming `Abelian` makes instance search pick one consistently. Every intended
caller is abelian.

## References

* `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean` — the simplicial theory this reaches
* `Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean` — the Čech object's
  extra degeneracy, already upstream
-/

universe v u

open CategoryTheory Opposite Simplicial

namespace AlgebraicTopology

namespace AlternatingCofaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The alternating coface map complex of a cosimplicial object `Y` in `A`, made opposite, is
the alternating face map complex of `Y` viewed as a simplicial object in `Aᵒᵖ`.

Degreewise both sides are `Y.obj ⦋n⦌`, and both differentials are `∑ i, (-1) ^ i • δ i`; the
proof is that `op` distributes over that sum. -/
noncomputable def opIso (Y : CosimplicialObject A) :
    ((alternatingCofaceMapComplex A).obj Y).op ≅ (alternatingFaceMapComplex Aᵒᵖ).obj Y.op :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : j + 1 = i)
    simp only [Iso.refl_hom, HomologicalComplex.op_d]
    simp [AlternatingFaceMapComplex.objD, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj,
      AlternatingCofaceMapComplex.objD, SimplicialObject.δ, CosimplicialObject.δ,
      CochainComplex.of_d, op_sum, op_zsmul]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

@[simp]
lemma opIso_hom_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).hom.f n = 𝟙 _ :=
  rfl

@[simp]
lemma opIso_inv_f (Y : CosimplicialObject A) (n : ℕ) :
    (opIso Y).inv.f n = 𝟙 _ :=
  rfl

end AlternatingCofaceMapComplex

section Exactness

open SimplicialObject.Augmented

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Positive-degree exactness from an extra degeneracy.** If the opposite of a cosimplicial
object `Y` in `A` underlies an augmented simplicial object in `Aᵒᵖ` carrying an extra
degeneracy, then the alternating coface complex of `Y` is exact in every positive degree.

The augmentation is not visible in the conclusion, which is the point: it lives on the
simplicial side, where `ExtraDegeneracy.homotopyEquiv` already handles it. -/
lemma exactAt_succ_of_extraDegeneracy {Y : CosimplicialObject A}
    {X : SimplicialObject.Augmented Aᵒᵖ} (e : drop.obj X ≅ Y.op)
    (ed : ExtraDegeneracy X) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj Y).ExactAt (n + 1) := by
  have H : ((alternatingFaceMapComplex Aᵒᵖ).obj Y.op).ExactAt (n + 1) := by
    rw [← exactAt_iff_of_quasiIsoAt ((alternatingFaceMapComplex Aᵒᵖ).map e.hom) (n + 1)]
    show (AlternatingFaceMapComplex.obj (drop.obj X)).ExactAt (n + 1)
    rw [exactAt_iff_of_quasiIsoAt ed.homotopyEquiv.hom]
    exact ChainComplex.exactAt_succ_single_obj _ _
  exact (HomologicalComplex.exactAt_op_iff _).mp
    ((exactAt_iff_of_quasiIsoAt (AlternatingCofaceMapComplex.opIso Y).hom (n + 1)).mpr H)

/-- The same, with the **contravariant** transport folded in.

`ExtraDegeneracy.map` applies a covariant functor. Čech cohomology applies
`FormalCoproduct.evalOp` of a presheaf, which is contravariant on the site; `Functor.rightOp`
converts one to the other. This is the form a Čech vanishing argument calls. -/
lemma exactAt_succ_of_extraDegeneracy_map {D : Type*} [Category D]
    {X : SimplicialObject.Augmented D} (ed : ExtraDegeneracy X) (G : Dᵒᵖ ⥤ A)
    {Y : CosimplicialObject A}
    (e : drop.obj (((whiskering _ _).obj G.rightOp).obj X) ≅ Y.op) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj Y).ExactAt (n + 1) :=
  exactAt_succ_of_extraDegeneracy e (ed.map G.rightOp) n

end Exactness

end AlgebraicTopology
