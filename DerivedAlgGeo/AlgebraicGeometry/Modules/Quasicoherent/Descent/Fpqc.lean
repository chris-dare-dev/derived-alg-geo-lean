/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import DerivedAlgGeo.Algebra.Category.ModuleCat.Descent.FaithfullyFlat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.StrongTrans
import DerivedAlgGeo.AlgebraicGeometry.Sites.StackQuasiCompact
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataPrime
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack

/-!
# Quasi-coherent sheaves form an fpqc stack

Quasi-coherent module sheaves have effective descent along every faithfully flat morphism of
affine schemes, and `qcohPseudofunctor` is a stack for the fpqc topology, hence for the fppf
and étale topologies.

## Main results

* `AlgebraicGeometry.Scheme.qcohPseudofunctor_isStackFor_Spec_map`: effective descent along
  `Spec.map φ` for a faithfully flat ring map `φ`, the case of Stacks 023S to which its proof
  reduces.
* `AlgebraicGeometry.Scheme.qcohPseudofunctor_isStack_fpqcTopology`: quasi-coherent sheaves
  form a stack for the fpqc topology (Stacks 023T).
* `AlgebraicGeometry.Scheme.qcohPseudofunctor_isStack_fppfTopology`,
  `AlgebraicGeometry.Scheme.qcohPseudofunctor_isStack_etaleTopology`: the coarser topologies.

## Implementation notes

The proof is Vistoli's. Descent along a faithfully flat map of affine schemes is module descent
(`CommRingCat.isStackFor_moduleCat_of_faithfullyFlat`) transported in two steps: along the
strong transformation `tildeStrongTrans`, whose components are equivalences
(`Pseudofunctor.isStackFor_iff_of_isEquivalence`), and then along the functor `Scheme.Spec`,
which preserves pullbacks because it is a right adjoint
(`Pseudofunctor.isStackFor_singleton_comp_toPseudofunctor_iff`). The fpqc criterion
`isStack_fpqcTopology_iff` combines this with the Zariski stack property
`qcohPseudofunctor_isStack_zariskiTopology`; a flat surjective morphism `Spec.map φ` comes from
a faithfully flat `φ` by `flat_and_surjective_SpecMap_iff`.

## References

* [Stacks, Tag 023S](https://stacks.math.columbia.edu/tag/023S): Descent, Lemma 35.5.1, and its
  proof.
* [Stacks, Tag 023T](https://stacks.math.columbia.edu/tag/023T): Descent, Proposition 35.5.2.
* A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*,
  arXiv:math/0412512v4, Theorem 4.23.

## Tags

quasi-coherent sheaf, descent, faithfully flat, fpqc, fppf, étale, stack
-/

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

/-- **Descent along a faithfully flat map of affine schemes.** If `φ : A ⟶ B` is a faithfully
flat map of commutative rings, quasi-coherent module sheaves have effective descent along
`Spec.map φ : Spec B ⟶ Spec A`. Stacks, Tag 023S states this for a standard fpqc covering of an
affine scheme, and its proof reduces to this case of a single morphism.

The proof composes three transports: module descent along `φ`
(`CommRingCat.isStackFor_moduleCat_of_faithfullyFlat`), the strong transformation
`tildeStrongTrans` with equivalence components (`Pseudofunctor.isStackFor_iff_of_isEquivalence`),
and reindexing along the pullback-preserving functor `Scheme.Spec`
(`Pseudofunctor.isStackFor_singleton_comp_toPseudofunctor_iff`).

Faithful flatness cannot be weakened to flatness: for `φ : ℤ ⟶ ℚ`, the quasi-coherent sheaf
associated with `ℤ/2` pulls back to zero along `Spec ℚ ⟶ Spec ℤ`, as does the zero sheaf. -/
theorem qcohPseudofunctor_isStackFor_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.FaithfullyFlat) :
    qcohPseudofunctor.IsStackFor (Presieve.singleton (Spec.map φ)) :=
  (Pseudofunctor.isStackFor_singleton_comp_toPseudofunctor_iff Scheme.Spec qcohPseudofunctor
    φ.op).1 ((Pseudofunctor.isStackFor_iff_of_isEquivalence tildeStrongTrans _).1
      (CommRingCat.isStackFor_moduleCat_of_faithfullyFlat φ hφ))

/-- **Quasi-coherent sheaves form an fpqc stack** (Stacks, Tag 023T; Vistoli, Theorem 4.23).
Descent data of quasi-coherent module sheaves along an fpqc covering are effective, and
morphisms of quasi-coherent sheaves glue. -/
instance qcohPseudofunctor_isStack_fpqcTopology : qcohPseudofunctor.{u}.IsStack fpqcTopology :=
  (isStack_fpqcTopology_iff _).2 ⟨inferInstance, fun _ _ f hf hs ↦
    qcohPseudofunctor_isStackFor_Spec_map f ((flat_and_surjective_SpecMap_iff f).1 ⟨hf, hs⟩)⟩

/-- Quasi-coherent sheaves form a stack for the fppf topology. -/
instance qcohPseudofunctor_isStack_fppfTopology : qcohPseudofunctor.{u}.IsStack fppfTopology :=
  .of_le fppfTopology_le_fpqcTopology

/-- Quasi-coherent sheaves form a stack for the étale topology. -/
instance qcohPseudofunctor_isStack_etaleTopology : qcohPseudofunctor.{u}.IsStack etaleTopology :=
  .of_le etaleTopology_le_fpqcTopology

end AlgebraicGeometry.Scheme
