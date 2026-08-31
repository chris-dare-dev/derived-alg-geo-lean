/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids.Morphism

/-!
# Representable big-Zariski stacks

The generic construction of a discrete stack from a sheaf and the generic
notion of a representable stack morphism are owned by
`CategoryTheory/Sites/StackInGroupoids`.  This geometric consumer applies
that API to the subcanonical big-Zariski site of schemes.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite

noncomputable section

universe u

/-- The big-Zariski stack represented by a scheme `X`. -/
def representableZariskiStack (X : Scheme.{u}) :
    StackInGroupoids Scheme.{u} Scheme.zariskiTopology :=
  stackInGroupoidsOfSheaf Scheme.zariskiTopology (yoneda.obj X)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.zariskiTopology.{u}) (yoneda.obj X))

/-- The stack represented by `X` has effective Čech descent for every big
Zariski covering family. -/
def representableZariskiCechDescentEquivalence
    (X S : Scheme.{u})
    (U : StackInGroupoids.Cover (J := Scheme.zariskiTopology) S) :=
  (representableZariskiStack X).cechDescentEquivalence U

/-- A morphism `T ⟶ X`, regarded as an object of the stack represented by
`X` over `T`. -/
def representableZariskiObject {X T : Scheme.{u}} (f : T ⟶ X) :
    (representableZariskiStack X).presheaf.obj (.mk (op T)) :=
  Discrete.mk f

/-- The representable stack remembers its scheme morphisms faithfully. -/
theorem representableZariskiObject_injective {X T : Scheme.{u}} :
    Function.Injective (representableZariskiObject (X := X) (T := T)) := by
  intro f g h
  exact congrArg Discrete.as h

end


end AlgebraicGeometry
