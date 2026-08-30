/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Slicing

/-!
# Historical names for restating immutable reviews

The canonical declarations live in the Bridgeland strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
The aliases below are deliberately outside the `DerivedAlgGeo` library and are
imported only by the restatement executable. They let the exact, immutable
statement payloads in `attest/review.yaml` elaborate without exposing the
retired namespace to library consumers or the declaration emitter.

Do not import this module from library code, add aliases, or use these names in
new review payloads. Review-to-declaration joins survive renames by statement
digest; this bridge exists only because the stored pretty-printed statements
must still resolve the names that the reviewer originally read.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde
  (since := "2026-08-30")]
alias GLTilde :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde

namespace GLTilde

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde.group
  (since := "2026-08-30")]
alias group :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde.group

end GLTilde

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot
  (since := "2026-08-30")]
alias AutPairQuot :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot

namespace AutPairQuot

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.group
  (since := "2026-08-30")]
alias group :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.group

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.mulAction
  (since := "2026-08-30")]
alias mulAction :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.mulAction

end AutPairQuot

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.gltildeSlicingMulAction
  (since := "2026-08-30")]
alias gltildeSlicingMulAction :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.gltildeSlicingMulAction

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
