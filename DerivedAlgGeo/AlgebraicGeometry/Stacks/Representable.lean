/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

/-!
# Representable stacks on the big scheme sites

The generic construction of a discrete stack from a sheaf and the generic
notion of a representable stack morphism are owned by
`CategoryTheory/Sites/Descent/StackInGroupoids`.  This geometric consumer applies
that API to the subcanonical big-Zariski, fppf and étale sites of schemes.
The slice-site example below uses Mathlib’s subcanonical-over instance.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite

noncomputable section

universe u

/-- The big-Zariski stack represented by a scheme `X`. -/
abbrev representableZariskiStack (X : Scheme.{u}) :
    StackInGroupoids Scheme.{u} Scheme.zariskiTopology :=
  StackInGroupoids.representable Scheme.zariskiTopology X

/-- The big-fppf stack represented by a scheme `X`. Its subcanonicity follows
from fpqc descent for representable presheaves. -/
abbrev representableFppfStack (X : Scheme.{u}) :
    StackInGroupoids Scheme.{u} Scheme.fppfTopology :=
  StackInGroupoids.representable Scheme.fppfTopology X

/-- The big-étale stack represented by a scheme `X`. -/
abbrev representableEtaleStack (X : Scheme.{u}) :
    StackInGroupoids Scheme.{u} Scheme.etaleTopology :=
  StackInGroupoids.representable Scheme.etaleTopology X

-- Representability on a slice site needs no scheme-specific stack constructor.
example (S : Scheme.{u}) (T : Over S) :
    StackInGroupoids (Over S) (Scheme.fppfTopology.over S) :=
  StackInGroupoids.representable (Scheme.fppfTopology.over S) T

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
