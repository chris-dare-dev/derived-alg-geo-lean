/-
Cohomology-pushforward slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.CategoryTheory.TopologicalSheafCohomologyPushforward

/-! ## Cohomology is unchanged by an exact pushforward (#572 step 3, slice 3)

`Hⁿ(K, F) ≃+ Hⁿ(J, G_* F)`. The assembly of `ConstantSheafPullback.lean` (slice 1) and
`ExtAdjunction.lean` (slice 2); the body is one `.trans`.
-/

#print axioms CategoryTheory.sheafCohomologyPushforwardAddEquiv
#print axioms CategoryTheory.sheafH_eq_ext
#print axioms CategoryTheory.sheafHPushforwardAddEquiv

/-! ## Topological instantiation at a closed embedding -/

#print axioms DerivedAlgGeo.Topology.isTerminalTopOpens
#print axioms DerivedAlgGeo.Topology.terminal_opens_eq_top
#print axioms DerivedAlgGeo.Topology.cohomologyPushforwardAddEquiv
#print axioms DerivedAlgGeo.Topology.schemeCohomologyPushforwardAddEquiv
