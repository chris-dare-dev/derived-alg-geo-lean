/-
Pushforward-stalks slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.Topology.Sheaves.PushforwardStalks

/-! ## Stalks of a pushforward off a closed range (#572 step 3)

The half of the stalkwise picture Mathlib does not have. The other half, on the range itself, is
`stalkPushforward_iso_of_isInducing` and needs only `IsInducing`.
-/

#print axioms DerivedAlgGeo.Topology.offRange
#print axioms DerivedAlgGeo.Topology.preimage_eq_bot_of_le
#print axioms DerivedAlgGeo.Topology.subsingleton_of_isTerminal
#print axioms DerivedAlgGeo.Topology.subsingleton_stalk_pushforward
#print axioms DerivedAlgGeo.Topology.stalkPushforward_naturality
#print axioms DerivedAlgGeo.Topology.surjective_stalk_map_pushforward
#print axioms DerivedAlgGeo.Topology.isLocallySurjective_pushforward
