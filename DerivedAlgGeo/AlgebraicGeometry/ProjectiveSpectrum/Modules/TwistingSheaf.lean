/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Shift
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.AssociatedSheaf

/-!
# Twists and twisting sheaves on `Proj`

For the sign convention fixed in `Shift`, this file defines

* `sheafNatTwist 𝓜 d` from the exact natural shift;
* `sheafTwist 𝓜 d` from the zero-extended integer shift; and
* `twistingSheaf 𝒜 d`, notation-free `𝒪(d)`, by applying the construction to the graded ring
  as a module over itself.

The normalization at zero is an actual isomorphism of sheaves of modules.  Natural shifts also
carry a strict composition comparison.  Mixed integer iteration is not asserted at the graded
module level because truncating negative degrees makes that statement false; its sheaf-level
comparison belongs with the later quasi-coherence/basic-open equivalence.
-/

noncomputable section

open CategoryTheory TopologicalSpace

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-- The associated sheaf of the natural shift `M(d)`, for `d : ℕ`. -/
def sheafNatTwist (d : ℕ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  associatedSheaf 𝒜 (natShift 𝓜 d)

/-- The associated sheaf of the integer shift `M(d)`, with negative degrees zero-extended. -/
def sheafTwist (d : ℤ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  associatedSheaf 𝒜 (intShift 𝓜 d)

/-- The zero integer twist is canonically isomorphic to the original associated sheaf. -/
def sheafTwistZeroIso : sheafTwist 𝒜 𝓜 0 ≅ associatedSheaf 𝒜 𝓜 :=
  associatedIsoOfPiecewiseIff (𝓜 := intShift 𝓜 0) 𝒜 𝓜
    (fun i m => mem_intShift_zero_iff 𝓜 i m)

/-- Natural shift by zero is canonically the original associated sheaf. -/
def sheafNatTwistZeroIso : sheafNatTwist 𝒜 𝓜 0 ≅ associatedSheaf 𝒜 𝓜 :=
  associatedIsoOfPiecewiseIff (𝓜 := natShift 𝓜 0) 𝒜 𝓜 fun i m => by
    change m ∈ 𝓜 (i + 0) ↔ m ∈ 𝓜 i
    simp

/-- Natural shifts compose according to addition of their indices. -/
def sheafNatTwistAddIso (d e : ℕ) :
    sheafNatTwist 𝒜 (natShift 𝓜 d) e ≅ sheafNatTwist 𝒜 𝓜 (d + e) :=
  associatedIsoOfPiecewiseIff
    (𝓜 := natShift (natShift 𝓜 d) e) 𝒜 (natShift 𝓜 (d + e))
      (fun i m => mem_natShift_add_iff 𝓜 d e i m)

section Ring

/-- The twisting sheaf `𝒪(d)` on `Proj 𝒜`, using the convention `A(d)ₙ = Aₙ₊d`. -/
def twistingSheaf (d : ℤ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  sheafTwist 𝒜 𝒜 d

/-- The normalization `𝒪(0) ≅ Ã`; the identification of `Ã` with the structure sheaf is kept
as the next affine/quasi-coherence comparison rather than hidden in this definition. -/
def twistingSheafZeroIso : twistingSheaf 𝒜 0 ≅ associatedSheaf 𝒜 𝒜 :=
  sheafTwistZeroIso 𝒜 𝒜

/-- A nonnegative integer twist agrees with the corresponding strict natural twist. -/
def twistingSheafOfNatIso (d : ℕ) :
    twistingSheaf 𝒜 (d : ℤ) ≅ sheafNatTwist 𝒜 𝒜 d :=
  associatedIsoOfPiecewiseIff (𝓜 := intShift 𝒜 (d : ℤ)) 𝒜 (natShift 𝒜 d)
    (fun i a => mem_intShift_ofNat_iff 𝒜 d i a)

end Ring

end AlgebraicGeometry.Proj
