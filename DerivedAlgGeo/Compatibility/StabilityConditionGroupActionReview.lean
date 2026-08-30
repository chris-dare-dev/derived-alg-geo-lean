/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Slicing

/-!
# Human-review compatibility for the GroupAction namespace cutover

The canonical declarations live in the Bridgeland strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
The aliases below exist only so the immutable, human-authored statement payloads
in `attest/review.yaml` continue to elaborate after that namespace cutover.

Do not add consumers or further aliases here. Once the named reviewer has
reconfirmed the two affected entries against the canonical declarations, this
module and its umbrella import should be removed.
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
