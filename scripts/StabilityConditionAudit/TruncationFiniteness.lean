import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.TruncationFiniteness

/-! Axiom audit and direct-import client for component-level truncation finiteness. -/

#print axioms CategoryTheory.Functor.truncLE_mem_of_component_lift

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

-- The target locus is only `B`, not every object of `D`.
example (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (t : TStructure C) (t' : TStructure D) [F.IsTExact t t']
    (A P : ObjectProperty C) (B Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms]
    (hLift : ∀ Y : D, B Y → ∃ X : C, A X ∧ Nonempty (F.obj X ≅ Y))
    (hSource : ∀ X : C, A X → ∀ n : ℤ, P ((t.truncLE n).obj X))
    (hPres : ∀ X : C, P X → Q (F.obj X))
    (Y : D) (hY : B Y) (n : ℤ) :
    Q ((t'.truncLE n).obj Y) :=
  F.truncLE_mem_of_component_lift t t' A P B Q hLift hSource hPres Y hY n
