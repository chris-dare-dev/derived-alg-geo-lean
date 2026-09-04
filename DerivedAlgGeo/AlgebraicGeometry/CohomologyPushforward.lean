/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.CohomologyPushforward
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Cohomology and pushforward along a closed immersion

This algebraic-geometry leaf specializes the space-level comparison from
`Topology/Sheaves/CohomologyPushforward.lean` to the underlying map of a closed
immersion of schemes. Keeping the specialization here prevents the generic CategoryTheory layer
from importing algebraic geometry.
-/

universe u

open CategoryTheory TopologicalSpace TopCat
open DerivedAlgGeo.Topology

namespace DerivedAlgGeo.AlgebraicGeometry

set_option maxHeartbeats 1000000 in
/-- **`#572` step 3 at a closed immersion of schemes.**

`Hⁿ(X, F) ≃+ Hⁿ(Y, ι_* F)`. A closed immersion is a closed embedding on underlying spaces
(`IsClosedImmersion.isClosedEmbedding`), which supplies both hypotheses of the topological
statement directly.

This is an isomorphism for each abelian sheaf `F`; naturality in `F`, a universe-parametric
`HasExt`, and the passage from coherent sheaves to abelian sheaves remain separate work. -/
noncomputable def schemeCohomologyPushforwardAddEquiv
    {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsClosedImmersion g]
    (F : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H (((Opens.map g.base).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).obj F) n :=
  cohomologyPushforwardAddEquiv g.base
    (_root_.AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding g).isInducing
    (_root_.AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding g).isClosed_range F n

end DerivedAlgGeo.AlgebraicGeometry
