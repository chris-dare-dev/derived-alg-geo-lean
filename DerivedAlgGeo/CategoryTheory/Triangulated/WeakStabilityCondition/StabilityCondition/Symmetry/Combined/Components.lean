/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.JointContinuous
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Transport of connected components by symmetries

A group acting continuously, element by element, on a topological space also
acts on its connected-component set.  This file packages that general fact and
then applies it to the three symmetry groups already acting on the Bridgeland
stability space:

* `GLTilde`;
* `AutPairQuot v`;
* `GLTilde × AutPairQuot v`.

The resulting action is not merely a permutation of component labels.  Each
group element restricts to a homeomorphism from one component subtype to the
component subtype carrying the translated label.  The stabilizer of a label
therefore acts on the corresponding component itself.
-/

open CategoryTheory.Triangulated
open Set

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

noncomputable section

universe u v

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

/-- The action induced on connected-component labels by a continuous group
action. -/
def componentSmul (g : G) (cc : ConnectedComponents X) : ConnectedComponents X :=
  (continuous_const_smul g).connectedComponentsMap cc

@[simp]
theorem componentSmul_mk (g : G) (x : X) :
    componentSmul g (ConnectedComponents.mk x) = ConnectedComponents.mk (g • x) :=
  rfl

/-- Functoriality of connected components turns the original group action into
an action on component labels.

**`scoped`.** Stated at full generality, in a domain-specific namespace, for a
class pairing (`MulAction`/`ConnectedComponents`) that Mathlib does not equip at
this pin. If it is ever upstreamed, an unscoped copy here becomes a second
instance for the same class and type. -/
scoped instance componentMulAction : MulAction G (ConnectedComponents X) where
  smul := componentSmul
  one_smul cc := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe cc
    exact congrArg ConnectedComponents.mk (one_smul G x)
  mul_smul g h cc := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe cc
    exact congrArg ConnectedComponents.mk (mul_smul g h x)

/-- A symmetry maps the connected component of `x` exactly onto the connected
component of `g • x`.  Continuity gives one inclusion; applying the inverse
symmetry gives the other. -/
theorem image_connectedComponent_smul (g : G) (x : X) :
    (fun y : X ↦ g • y) '' connectedComponent x = connectedComponent (g • x) := by
  apply Set.Subset.antisymm
  · exact (continuous_const_smul g).image_connectedComponent_subset x
  · intro y hy
    refine ⟨g⁻¹ • y, ?_, ?_⟩
    · have hpre : g⁻¹ • y ∈ connectedComponent (g⁻¹ • (g • x)) :=
        (continuous_const_smul g⁻¹).mapsTo_connectedComponent (g • x) hy
      simpa using hpre
    · simp

/-- Restriction of a symmetry to a homeomorphism between the corresponding
connected-component subtypes. -/
def componentHomeomorph (g : G) (cc : ConnectedComponents X) :
    {x : X // ConnectedComponents.mk x = cc} ≃ₜ
      {x : X // ConnectedComponents.mk x = componentSmul g cc} :=
  (Homeomorph.smul g).subtype fun x ↦ by
    change ConnectedComponents.mk x = cc ↔
      componentSmul g (ConnectedComponents.mk x) = componentSmul g cc
    constructor
    · exact fun h ↦ congrArg (componentSmul g) h
    · intro h
      change g • ConnectedComponents.mk x = g • cc at h
      exact smul_left_cancel g h

@[simp]
theorem componentHomeomorph_apply_coe (g : G) (cc : ConnectedComponents X)
    (x : {x : X // ConnectedComponents.mk x = cc}) :
    (componentHomeomorph g cc x : X) = g • (x : X) :=
  rfl

/-- The subgroup preserving a chosen connected component. -/
abbrev componentStabilizer (cc : ConnectedComponents X) : Subgroup G :=
  MulAction.stabilizer G cc

theorem mem_componentStabilizer_iff {cc : ConnectedComponents X} {g : G} :
    g ∈ componentStabilizer (G := G) cc ↔ g • cc = cc :=
  MulAction.mem_stabilizer_iff

/-- The component stabilizer acts on the corresponding component subtype.

`scoped` for the same reason as `componentMulAction` above. -/
scoped instance componentStabilizerMulAction (cc : ConnectedComponents X) :
    MulAction (componentStabilizer (G := G) cc)
      {x : X // ConnectedComponents.mk x = cc} where
  smul g x := ⟨g.1 • x.1, by
    rw [← componentSmul_mk, x.2]
    exact g.2⟩
  one_smul x := by
    apply Subtype.ext
    exact one_smul G x.1
  mul_smul g h x := by
    apply Subtype.ext
    exact mul_smul g.1 h.1 x.1

end

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
