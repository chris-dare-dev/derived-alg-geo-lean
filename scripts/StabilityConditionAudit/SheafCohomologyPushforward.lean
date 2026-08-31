/-
Cohomology-pushforward slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CohomologyPushforward

/-! ## Cohomology is unchanged by an exact pushforward (#572 step 3, slice 3)

`Hⁿ(K, F) ≃+ Hⁿ(J, G_* F)`. The assembly of `ConstantPullback.lean` (slice 1) and
`ExtAdjunction.lean` (slice 2); the body is one `.trans`.
-/

#print axioms CategoryTheory.sheafCohomologyPushforwardAddEquiv
#print axioms CategoryTheory.sheafH_eq_ext
#print axioms CategoryTheory.sheafHPushforwardAddEquiv
