/-
Fppf and étale stack-descent slice of the AlgebraicGeometry audit, split out so
concurrent branches append to different files (#480). See the umbrella file for
the contract.

Every record below is about topology comparisons on the site of schemes, or
about descent for stacks REPRESENTED by a scheme. Nothing here records an
algebraic stack, an algebraic-space diagonal, or an atlas of the
universally-gluable relative-perfect moduli stack.
-/
import DerivedAlgGeo.AlgebraicGeometry.Sites
import DerivedAlgGeo.AlgebraicGeometry.Stacks
open AlgebraicGeometry

/-! ## Comparing the big Zariski, étale, fppf and fpqc sites -/

#print axioms AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage
#print axioms AlgebraicGeometry.Scheme.etaleTopology_le_fppfTopology
#print axioms AlgebraicGeometry.Scheme.etaleTopology_le_fpqcTopology
#print axioms AlgebraicGeometry.Scheme.zariskiTopology_le_fppfTopology
#print axioms AlgebraicGeometry.Scheme.subcanonical_etaleTopology

/-! ## Covering families from Mathlib covers -/

#print axioms AlgebraicGeometry.Scheme.Cover.toStackCover
#print axioms AlgebraicGeometry.Scheme.Cover.toStackCover_index
#print axioms AlgebraicGeometry.Scheme.Cover.toStackCover_obj
#print axioms AlgebraicGeometry.Scheme.Cover.toStackCover_hom
#print axioms AlgebraicGeometry.Scheme.fppfCover
#print axioms AlgebraicGeometry.Scheme.fppfCoverOfSmoothSurjective
#print axioms AlgebraicGeometry.Scheme.etaleCover
#print axioms AlgebraicGeometry.zariskiCoverToFppf
#print axioms AlgebraicGeometry.zariskiCoverToEtale

/-! ## Representable stacks at the fppf and étale levels -/

#print axioms AlgebraicGeometry.representableFppfStack
#print axioms AlgebraicGeometry.representableEtaleStack
#print axioms AlgebraicGeometry.representableFppfStack_presheaf
#print axioms AlgebraicGeometry.representableEtaleStack_presheaf
#print axioms AlgebraicGeometry.representableEtaleStack_eq_ofLE
#print axioms AlgebraicGeometry.representableZariskiStack_eq_ofLE
#print axioms AlgebraicGeometry.representableFppfObject
#print axioms AlgebraicGeometry.representableFppfObject_eq

/-! ## Effective fppf and étale descent -/

#print axioms AlgebraicGeometry.representableFppfCechDescentEquivalence
#print axioms AlgebraicGeometry.representableEtaleCechDescentEquivalence
#print axioms AlgebraicGeometry.representableFppfDescentAlong
#print axioms AlgebraicGeometry.representableFppfDescentAlongSmoothSurjective
#print axioms AlgebraicGeometry.representableEtaleDescentAlong
#print axioms AlgebraicGeometry.representableFppfFullyFaithfulToCechDescent
#print axioms AlgebraicGeometry.representableFppfEssSurjToCechDescent
