/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import DerivedAlgGeo.Algebra.Homology.Homotopy.HomologyModel

/-!
# Formality of complexes of vector spaces

This file constructs the zero-differential homology model of a cochain complex
of vector spaces and a noncanonical homotopy equivalence to that model.

The construction is deliberately coefficient-side and unbounded.  It uses
choice to split each space of cycles into boundaries and representatives and
to choose preimages of boundaries under the preceding differential.  No
naturality in the complex is claimed.  Finite support and finite-dimensionality
play no role here; packaging a finite cohomology presentation is a downstream
consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory Category Limits

namespace CochainComplex

variable {k : Type u} [DivisionRing k]

/-- Avoid the low-priority projective/free instance loop when choosing
splittings: over a division ring, choose a basis explicitly. -/
private noncomputable instance moduleCatProjective
    (M : ModuleCat.{v} k) : Projective M := by
  letI : Module.Free k M := Module.Free.of_divisionRing k M
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis k M)

namespace ModuleCatFormality

variable (K : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ)

/-- A chosen section of the homology quotient.  Every vector space is
projective, so the epimorphism from cycles splits. -/
private noncomputable def homologySection :
    K.homology i ⟶ K.cycles i :=
  Projective.factorThru (𝟙 (K.homology i)) (K.homologyπ i)

@[reassoc (attr := simp)]
private lemma homologySection_comp_homologyπ :
    homologySection K i ≫ K.homologyπ i = 𝟙 (K.homology i) :=
  Projective.factorThru_comp (𝟙 (K.homology i)) (K.homologyπ i)

/-- Projection of cycles to their boundary part, using the chosen homology
section. -/
private noncomputable def boundaryPart : K.cycles i ⟶ K.cycles i :=
  𝟙 (K.cycles i) - K.homologyπ i ≫ homologySection K i

@[reassoc]
private lemma boundaryPart_comp_homologyπ :
    boundaryPart K i ≫ K.homologyπ i = 0 := by
  rw [boundaryPart, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    homologySection_comp_homologyπ, Category.comp_id, sub_self]

/-- The short complex presenting homology as the cokernel of incoming
boundaries. -/
private noncomputable abbrev boundarySequence :
    ShortComplex (ModuleCat.{v} k) :=
  ShortComplex.mk (K.toCycles ((ComplexShape.up ℤ).prev i) i)
    (K.homologyπ i) (K.toCycles_comp_homologyπ _ _)

private lemma boundarySequence_exact : (boundarySequence K i).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (K.homologyIsCokernel ((ComplexShape.up ℤ).prev i) i rfl)

/-- Incoming boundaries, regarded as a surjection onto the kernel of the
homology quotient. -/
private noncomputable def toBoundaryKernel :
    K.X ((ComplexShape.up ℤ).prev i) ⟶ kernel (K.homologyπ i) :=
  kernel.lift (K.homologyπ i)
    (K.toCycles ((ComplexShape.up ℤ).prev i) i)
    (K.toCycles_comp_homologyπ _ _)

private noncomputable instance toBoundaryKernel_epi :
    Epi (toBoundaryKernel K i) :=
  (boundarySequence_exact K i).epi_kernelLift

/-- The boundary projection factored through the kernel of the homology
quotient. -/
private noncomputable def boundaryPartKernel :
    K.cycles i ⟶ kernel (K.homologyπ i) :=
  kernel.lift (K.homologyπ i) (boundaryPart K i)
    (boundaryPart_comp_homologyπ K i)

/-- A chosen preimage in the preceding chain group of the boundary part of a
cycle. -/
private noncomputable def boundaryPreimage :
    K.cycles i ⟶ K.X ((ComplexShape.up ℤ).prev i) :=
  Projective.factorThru (boundaryPartKernel K i) (toBoundaryKernel K i)

@[reassoc]
private lemma boundaryPreimage_comp_toCycles :
    boundaryPreimage K i ≫
      K.toCycles ((ComplexShape.up ℤ).prev i) i = boundaryPart K i := by
  rw [← kernel.lift_ι (K.homologyπ i)
    (K.toCycles ((ComplexShape.up ℤ).prev i) i)
    (K.toCycles_comp_homologyπ _ _), ← Category.assoc]
  change boundaryPreimage K i ≫ toBoundaryKernel K i ≫
    kernel.ι (K.homologyπ i) = boundaryPart K i
  rw [boundaryPreimage, ← Category.assoc, Projective.factorThru_comp,
    boundaryPartKernel, kernel.lift_ι]

@[reassoc]
private lemma toCycles_comp_boundaryPart (j : ℤ) :
    K.toCycles j i ≫ boundaryPart K i = K.toCycles j i := by
  simp only [boundaryPart, Preadditive.comp_sub, Category.comp_id,
    K.toCycles_comp_homologyπ_assoc, zero_comp, sub_zero]

/-- Projection onto a chosen complement of the cycles: take the outgoing
boundary, choose a preimage one degree earlier, and identify that degree with
the source degree. -/
private noncomputable def outgoingPart : K.X i ⟶ K.X i :=
  K.toCycles i ((ComplexShape.up ℤ).next i) ≫
    boundaryPreimage K ((ComplexShape.up ℤ).next i) ≫
    (K.XIsoOfEq (by simp)).hom

@[reassoc]
private lemma outgoingPart_comp_d :
    outgoingPart K i ≫ K.d i ((ComplexShape.up ℤ).next i) =
      K.d i ((ComplexShape.up ℤ).next i) := by
  unfold outgoingPart
  rw [Category.assoc, Category.assoc, K.XIsoOfEq_hom_comp_d]
  simp only [← K.toCycles_i, boundaryPreimage_comp_toCycles_assoc]
  rw [← Category.assoc, toCycles_comp_boundaryPart]

/-- A chosen projection from the chain group to its cycles. -/
private noncomputable def cyclesProjection : K.X i ⟶ K.cycles i :=
  K.liftCycles (𝟙 (K.X i) - outgoingPart K i)
    ((ComplexShape.up ℤ).next i) rfl (by
      rw [Preadditive.sub_comp, Category.id_comp, outgoingPart_comp_d, sub_self])

@[reassoc]
private lemma cyclesProjection_comp_iCycles :
    cyclesProjection K i ≫ K.iCycles i = 𝟙 (K.X i) - outgoingPart K i :=
  K.liftCycles_i _ _ _ _

@[reassoc]
private lemma iCycles_comp_toCycles_next :
    K.iCycles i ≫ K.toCycles i ((ComplexShape.up ℤ).next i) = 0 := by
  apply (cancel_mono (K.iCycles ((ComplexShape.up ℤ).next i))).1
  simp

@[reassoc]
private lemma iCycles_comp_outgoingPart :
    K.iCycles i ≫ outgoingPart K i = 0 := by
  simp only [outgoingPart, iCycles_comp_toCycles_next_assoc, zero_comp]

@[reassoc (attr := simp)]
private lemma iCycles_comp_cyclesProjection :
    K.iCycles i ≫ cyclesProjection K i = 𝟙 (K.cycles i) := by
  rw [← cancel_mono (K.iCycles i), Category.assoc,
    cyclesProjection_comp_iCycles, Category.id_comp, Preadditive.comp_sub,
    Category.comp_id, iCycles_comp_outgoingPart, sub_zero]

/-- The chosen projection from a complex to its zero-differential homology
model. -/
private noncomputable def toHomologyModel : K ⟶ homologyModel K where
  f i := cyclesProjection K i ≫ K.homologyπ i
  comm' i j hij := by
    rw [homologyModel_d, comp_zero]
    change (0 : K.X i ⟶ K.homology j) =
      K.d i j ≫ cyclesProjection K j ≫ K.homologyπ j
    obtain rfl := (ComplexShape.up ℤ).next_eq' hij
    rw [← K.toCycles_i, Category.assoc,
      iCycles_comp_cyclesProjection_assoc, K.toCycles_comp_homologyπ]

/-- The chosen inclusion of homology representatives into the complex. -/
private noncomputable def fromHomologyModel : homologyModel K ⟶ K where
  f i := homologySection K i ≫ K.iCycles i
  comm' i j _ := by
    simp only [homologyModel_d, zero_comp, Category.assoc,
      K.iCycles_d, comp_zero]

private lemma fromHomologyModel_comp_toHomologyModel :
    fromHomologyModel K ≫ toHomologyModel K = 𝟙 (homologyModel K) := by
  apply HomologicalComplex.hom_ext
  intro i
  change homologySection K i ≫ K.iCycles i ≫ cyclesProjection K i ≫
    K.homologyπ i = 𝟙 (K.homology i)
  simp only [iCycles_comp_cyclesProjection_assoc,
    homologySection_comp_homologyπ]

@[reassoc]
private lemma d_comp_cyclesProjection :
    K.d i ((ComplexShape.up ℤ).next i) ≫
      cyclesProjection K ((ComplexShape.up ℤ).next i) =
        K.toCycles i ((ComplexShape.up ℤ).next i) := by
  rw [← K.toCycles_i, Category.assoc,
    iCycles_comp_cyclesProjection, Category.comp_id]

/-- The degree-minus-one family underlying the contracting homotopy. -/
private noncomputable def contractingHom (i j : ℤ) : K.X i ⟶ K.X j :=
  if hij : (ComplexShape.up ℤ).Rel j i then
    -(cyclesProjection K i ≫ boundaryPreimage K i ≫
      (K.XIsoOfEq ((ComplexShape.up ℤ).prev_eq' hij)).hom)
  else 0

private lemma dNext_contractingHom :
    dNext i (contractingHom K) = -outgoingPart K i := by
  have hi : (ComplexShape.up ℤ).Rel i
      ((ComplexShape.up ℤ).next i) := by simp
  rw [dNext_eq _ hi, contractingHom, dif_pos hi,
    Preadditive.comp_neg]
  simp only [d_comp_cyclesProjection_assoc, outgoingPart]

private lemma prevD_contractingHom :
    prevD i (contractingHom K) =
      -(cyclesProjection K i ≫ boundaryPart K i ≫ K.iCycles i) := by
  have hi : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev i) i := by
    change (ComplexShape.up ℤ).prev i + 1 = i
    rw [CochainComplex.prev]
    omega
  rw [prevD_eq _ hi, contractingHom, dif_pos hi,
    Preadditive.neg_comp]
  simp only [Category.assoc]
  rw [K.XIsoOfEq_hom_comp_d, ← K.toCycles_i]
  simp only [boundaryPreimage_comp_toCycles_assoc]

private lemma toHomologyModel_comp_fromHomologyModel_f :
    (toHomologyModel K ≫ fromHomologyModel K).f i =
      -outgoingPart K i +
        -(cyclesProjection K i ≫ boundaryPart K i ≫ K.iCycles i) +
          𝟙 (K.X i) := by
  change cyclesProjection K i ≫ K.homologyπ i ≫ homologySection K i ≫
    K.iCycles i = -outgoingPart K i +
      -(cyclesProjection K i ≫ boundaryPart K i ≫ K.iCycles i) +
        𝟙 (K.X i)
  simp only [boundaryPart, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.assoc, Category.id_comp, cyclesProjection_comp_iCycles]
  abel

/-- The chosen projection followed by the inclusion of homology
representatives is homotopic to the identity. -/
private noncomputable def homotopyToFrom :
    Homotopy (toHomologyModel K ≫ fromHomologyModel K) (𝟙 K) where
  hom := contractingHom K
  zero i j hij := by
    rw [contractingHom, dif_neg hij]
  comm i := by
    rw [dNext_contractingHom, prevD_contractingHom]
    exact toHomologyModel_comp_fromHomologyModel_f K i

end ModuleCatFormality

/-- Every unbounded cochain complex of vector spaces is noncanonically
homotopy equivalent to its zero-differential homology model.

This construction is not natural in `K`: it records choices of homology
representatives and boundary preimages. -/
noncomputable def homotopyEquivHomologyModel
    (K : CochainComplex (ModuleCat.{v} k) ℤ) :
    HomotopyEquiv K (homologyModel K) where
  hom := ModuleCatFormality.toHomologyModel K
  inv := ModuleCatFormality.fromHomologyModel K
  homotopyHomInvId := ModuleCatFormality.homotopyToFrom K
  homotopyInvHomId := Homotopy.ofEq
    (ModuleCatFormality.fromHomologyModel_comp_toHomologyModel K)

end CochainComplex
