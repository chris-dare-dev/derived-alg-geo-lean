/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.Divisors.CartierLineBundle

/-!
# Cartier divisors as coherent derived objects

This file transports the canonical `CartierDivisor.lineBundleData` bridge
into `Coh X`, `D(Coh X)`, and `Dᵇ(Coh X)`. The canonical objects are aliases
of the generic `LineBundleData` adapters, so there is no second choice of
representative. Comparison isomorphisms identify them with an associated
sheaf packaged using any independently supplied coherence proof; this is the
form needed by existing short-exact-sequence APIs.
-/

universe u

open CategoryTheory
open AlgebraicGeometry.DerivedCategory

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- The associated sheaf of a Cartier divisor, canonically packaged as a
coherent sheaf. -/
noncomputable def coh (D : CartierDivisor X) : Coh X :=
  (lineBundleData D).coh

@[simp]
theorem coh_obj (D : CartierDivisor X) :
    (coh D).obj = associatedSheaf D :=
  rfl

/-- Compare the canonical coherent object with the same associated sheaf
packaged using an independently supplied proof of coherence. -/
noncomputable def cohIso (D : CartierDivisor X)
    (h : Scheme.coherent X (associatedSheaf D)) :
    coh D ≅ (⟨associatedSheaf D, h⟩ : Coh X) :=
  ObjectProperty.isoMk (P := Scheme.coherent X) (Iso.refl _)

variable [IsLocallyNoetherian X]

/-- The associated line bundle placed canonically in degree zero of
`D(Coh X)`. -/
noncomputable def derivedObject (D : CartierDivisor X) :
    SchemeCoherentDerivedCategory X :=
  (lineBundleData D).derivedObject

@[simp]
theorem derivedObject_eq_single (D : CartierDivisor X) :
    derivedObject D =
      (DerivedCategory.singleFunctor (Coh X) 0).obj (coh D) :=
  rfl

/-- A Cartier divisor's degree-zero derived object is perfect because its
associated sheaf is a line bundle. -/
theorem derivedObject_perfect (D : CartierDivisor X) :
    schemePerfect X (derivedObject D) :=
  (lineBundleData D).derivedObject_perfect

/-- A Cartier divisor's degree-zero derived object is bounded for the
canonical t-structure. -/
theorem derivedObject_bounded (D : CartierDivisor X) :
    (DerivedCategory.TStructure.t (C := Coh X)).bounded (derivedObject D) :=
  (lineBundleData D).derivedObject_bounded

/-- Compare the canonical derived object with the degree-zero object formed
from an independently supplied coherence proof. -/
noncomputable def derivedObjectIso (D : CartierDivisor X)
    (h : Scheme.coherent X (associatedSheaf D)) :
    derivedObject D ≅
      (DerivedCategory.singleFunctor (Coh X) 0).obj
        (⟨associatedSheaf D, h⟩ : Coh X) :=
  (DerivedCategory.singleFunctor (Coh X) 0).mapIso (cohIso D h)

/-- The canonical Cartier-divisor object of `Dᵇ(Coh X)`. Its underlying
derived object is exactly `derivedObject D`. -/
noncomputable def boundedDerivedObject (D : CartierDivisor X) :
    SchemeBoundedCoherentDerivedCategory X :=
  (lineBundleData D).boundedDerivedObject

@[simp]
theorem boundedDerivedObject_obj (D : CartierDivisor X) :
    (boundedDerivedObject D).obj = derivedObject D :=
  rfl

/-- The bounded degree-zero object formed from an independently supplied
coherence proof. This is the comparison target used by short exact sequences
whose endpoints predate the canonical Cartier-divisor adapter. -/
noncomputable def boundedDerivedObjectOfCoherence (D : CartierDivisor X)
    (h : Scheme.coherent X (associatedSheaf D)) :
    SchemeBoundedCoherentDerivedCategory X :=
  ⟨(DerivedCategory.singleFunctor (Coh X) 0).obj
      (⟨associatedSheaf D, h⟩ : Coh X),
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩

@[simp]
theorem boundedDerivedObjectOfCoherence_obj (D : CartierDivisor X)
    (h : Scheme.coherent X (associatedSheaf D)) :
    (boundedDerivedObjectOfCoherence D h).obj =
      (DerivedCategory.singleFunctor (Coh X) 0).obj
        (⟨associatedSheaf D, h⟩ : Coh X) :=
  rfl

/-- The canonical bounded object agrees, up to the fully faithful
full-subcategory lift, with every proof-packaged degree-zero representative. -/
noncomputable def boundedDerivedObjectIso (D : CartierDivisor X)
    (h : Scheme.coherent X (associatedSheaf D)) :
    boundedDerivedObject D ≅ boundedDerivedObjectOfCoherence D h :=
  ObjectProperty.isoMk
    (P := (DerivedCategory.TStructure.t (C := Coh X)).bounded)
    (derivedObjectIso D h)

end

end AlgebraicGeometry.Scheme.CartierDivisor
