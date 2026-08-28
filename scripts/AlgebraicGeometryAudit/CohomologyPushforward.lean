/-
Cohomology-pushforward slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.Topology.Sheaves.CohomologyPushforward

/-! ## Cohomology along a closed embedding (#572 step 3, instantiated)

The abstract comparison of `CategoryTheory/SheafCohomologyPushforward.lean`, discharged at a map
of spaces. The only non-instance input is exactness of `f_*`.
-/

#print axioms DerivedAlgGeo.Topology.isTerminalTopOpens
#print axioms DerivedAlgGeo.Topology.terminal_opens_eq_top
#print axioms DerivedAlgGeo.Topology.cohomologyPushforwardAddEquiv
