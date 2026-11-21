import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.LocallyFree
import DerivedAlgGeo.AlgebraicGeometry.Modules.Descent.Zariski

/-!
# Descent of scheme-module sheaves

Gluing of module sheaves on schemes along covers: the stack property of `X ↦ X.Modules`, with
pullback, for a Grothendieck topology on the category of schemes.

## Main definitions

* `Descent/Zariski.lean`: the pseudofunctor `AlgebraicGeometry.Scheme.modulesPseudofunctor`
  and the module sheaf glued from a descent datum along open immersions.
* `Descent/LocallyFree.lean`: local freeness of a fixed rank as a local property of objects of
  `modulesPseudofunctor`.

## Main results

* `AlgebraicGeometry.Scheme.modulesPseudofunctor_isStack`: module sheaves form a stack for the
  big Zariski topology.
* `AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_of_cover`: local freeness of rank `r`
  descends along jointly surjective families of open immersions.

## Implementation notes

This umbrella re-exports its children. The quasi-coherent substack lives with quasi-coherence,
in `Modules/Quasicoherent/Descent.lean`.

## References

* [Stacks, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK): glueing sheaves.

## Tags

module sheaf, descent, stack
-/
