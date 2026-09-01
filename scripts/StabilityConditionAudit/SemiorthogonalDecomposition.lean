/-
Semiorthogonal-decomposition slice of the StabilityCondition audit.  The source is generic
triangulated category theory; this audit owns it alongside the other generic triangulated roots.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition

#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.component
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.semiorthogonal
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.mk.inj
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.total
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.component_le_total
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.hom_eq_zero
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.HasTriangulatedComponents
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.IsFull
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.IsStronglyFull
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.IsStronglyFull.isFull
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.map
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.map_component
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.reindex
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.reindex_component
#print axioms CategoryTheory.Limits.productHasZeroMorphisms
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.single
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.single_component
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.single_total
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.single_isStronglyFull
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.single_isFull
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.productComponent
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.productComponent_zero
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.productComponent_one
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.product
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.product_component

-- Orientation: the one place the direction convention is pinned. ofReverse
-- reindexes a classically-ordered family along OrderDual; ofReverseFin lands
-- the finite case back on Fin n through the root's own reindex.
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.ofReverse
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.ofReverse_component
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.ofReverse_hom_eq_zero
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.ofReverseFin
#print axioms CategoryTheory.Triangulated.SemiorthogonalSequence.ofReverseFin_component

-- Exceptional objects: no self-maps into a nonzero shift, endomorphism ring
-- the base field via algebraMap bijectivity. Every clause has consuming
-- theorems; the honest inhabitant is the D^b(field) example (exc-e5 / #936).
#print axioms CategoryTheory.Triangulated.IsExceptional
#print axioms CategoryTheory.Triangulated.IsExceptional.hom_shift_eq_zero
#print axioms CategoryTheory.Triangulated.IsExceptional.algebraMap_bijective
#print axioms CategoryTheory.algebraMap_end_apply
#print axioms CategoryTheory.Triangulated.IsExceptional.end_eq_smul_id
#print axioms CategoryTheory.Triangulated.IsExceptional.not_isZero
#print axioms CategoryTheory.Triangulated.IsExceptional.end_eq_zero_or_eq_one_of_mul_self
#print axioms CategoryTheory.Triangulated.IsExceptional.not_nonempty_iso_shift
#print axioms CategoryTheory.Triangulated.IsExceptional.hom_shift_shift_eq_zero
#print axioms CategoryTheory.Triangulated.IsExceptional.shift
#print axioms CategoryTheory.Triangulated.IsExceptional.of_equivalence

-- Exceptional collections: the classical-direction structure, its envelope
-- components, the semiorthogonality theorem via double envelope peeling, and
-- the two upstream-candidate retract-stability instances for the orthogonals.
#print axioms CategoryTheory.ObjectProperty.rightOrthogonal_isStableUnderRetracts
#print axioms CategoryTheory.ObjectProperty.leftOrthogonal_isStableUnderRetracts
#print axioms CategoryTheory.Triangulated.ExceptionalCollection
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.obj
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.exceptional
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.hom_shift_eq_zero
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.mk.inj
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.IsStrong
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.component
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.obj_mem_component
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.component_nonempty
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.hom_shift_shift_eq_zero
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.semiorthogonal_component
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.toSemiorthogonalSequence
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.toSemiorthogonalSequence_component
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.IsFull
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.IsStronglyFull
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.IsStronglyFull.isFull
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.hasTriangulatedComponents
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.ofExceptional
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.reindex
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.reindex_toSemiorthogonalSequence
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.toSemiorthogonalSequenceFin
#print axioms CategoryTheory.Triangulated.ExceptionalCollection.toSemiorthogonalSequenceFin_component
