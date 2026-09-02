/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Phase
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.LocallyFinite
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap

/-!
# Equivariance of preimage transfer

Preimage transfer commutes with compatible autoequivalences.  Compatibility is
the natural isomorphism one obtains by passing an equivariant geometric
functor through the inverse representatives used by `Slicing.mapEquiv`.

`Slicing.PreimageData.mapEquiv` shows that the lifting witness itself
transports along compatible autoequivalences, so the twisted preimage slicing
exists whenever the untwisted one does.  Together with
`Slicing.preimage_mapEquiv` this is Lemma 3.5(1) and Lemma 3.9(1) of
arXiv:2607.28411v1 in full, and Lemma 3.2 of arXiv:2601.22994:
`f^♯(𝒫 ⊗ L) = f^♯𝒫 ⊗ f^*L` *and* the left-hand side is a slicing.

The final theorems spell this out for representatives of `AutPairQuot`.  The
class-lattice components do not enter the slicing equality, but they do enter
the stability-level statement: `AutPair.preimage` transports the compatible
lattice datum along the functor, and `AutPair.preimage_act` is the
charge-carrying form of the equality.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

universe v₁ u₁ v₂ u₂ u₃ u₄

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (s : Slicing D) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
  [F.IsTriangulated] (h : s.PreimageData F)

/-- Preimage transfer commutes with compatible triangulated
autoequivalences.  The compatibility is stated for inverse functors because
`Slicing.mapEquiv` defines membership by applying the inverse representative. -/
theorem Slicing.preimage_mapEquiv (PhiC : C ≌ C) (PhiD : D ≌ D)
    [PhiC.functor.Additive] [PhiC.inverse.Additive]
    [PhiC.functor.CommShift ℤ] [PhiC.inverse.CommShift ℤ]
    [PhiC.functor.IsTriangulated] [PhiC.inverse.IsTriangulated]
    [PhiD.functor.Additive] [PhiD.inverse.Additive]
    [PhiD.functor.CommShift ℤ] [PhiD.inverse.CommShift ℤ]
    [PhiD.functor.IsTriangulated] [PhiD.inverse.IsTriangulated]
    (alpha : F ⋙ PhiD.inverse ≅ PhiC.inverse ⋙ F)
    (hmap : (s.mapEquiv PhiD).PreimageData F) :
    (s.mapEquiv PhiD).preimage F hmap =
      (s.preimage F h).mapEquiv PhiC := by
  apply Slicing.ext
  funext phi E
  apply propext
  constructor
  · intro hE
    change s.P phi ((F ⋙ PhiD.inverse).obj E) at hE
    change s.P phi ((PhiC.inverse ⋙ F).obj E)
    exact ObjectProperty.prop_of_iso _ (alpha.app E) hE
  · intro hE
    change s.P phi ((PhiC.inverse ⋙ F).obj E) at hE
    change s.P phi ((F ⋙ PhiD.inverse).obj E)
    exact ObjectProperty.prop_of_iso _ (alpha.app E).symm hE

section Twist

variable {s F}

omit [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] in
/-- The lifting witness transports along compatible autoequivalences: the
twisted preimage collection is a slicing whenever the untwisted one is.  This
is the existence half of Lemma 3.5(1) and Lemma 3.9(1) of arXiv:2607.28411v1,
which `Slicing.preimage_mapEquiv` had to assume.

Hom-vanishing is pulled back through the faithful inverse `PhiC.inverse`, and
an HN filtration for the twisted collection is obtained by filtering
`PhiC.inverse.obj E` for the untwisted one, pushing through `PhiC.functor`,
and landing on `E` by the counit, exactly as in `Slicing.mapEquiv` itself. -/
theorem Slicing.PreimageData.mapEquiv (h : s.PreimageData F) (PhiC : C ≌ C) (PhiD : D ≌ D)
    [PhiC.functor.Additive] [PhiC.functor.CommShift ℤ] [PhiC.functor.IsTriangulated]
    [PhiD.functor.Additive] [PhiD.inverse.Additive]
    [PhiD.functor.CommShift ℤ] [PhiD.inverse.CommShift ℤ]
    [PhiD.functor.IsTriangulated] [PhiD.inverse.IsTriangulated]
    (alpha : F ⋙ PhiD.inverse ≅ PhiC.inverse ⋙ F) :
    (s.mapEquiv PhiD).PreimageData F where
  hom_vanishing phi₁ phi₂ A B hphi hA hB g := by
    have hA' : s.P phi₁ (F.obj (PhiC.inverse.obj A)) :=
      ObjectProperty.prop_of_iso _ (alpha.app A) hA
    have hB' : s.P phi₂ (F.obj (PhiC.inverse.obj B)) :=
      ObjectProperty.prop_of_iso _ (alpha.app B) hB
    have hzero := h.hom_vanishing phi₁ phi₂ _ _ hphi hA' hB' (PhiC.inverse.map g)
    exact PhiC.inverse.map_injective (by simpa using hzero)
  hn_exists E := by
    obtain ⟨Fil⟩ := h.hn_exists (PhiC.inverse.obj E)
    exact ⟨CategoryTheory.Triangulated.HNFiltration.ofIso C
      (HNFiltration.mapF (P' := (s.mapEquiv PhiD).preimagePhase F) Fil PhiC.functor
        (fun phi X hX => ObjectProperty.prop_of_iso (s.P phi)
          (F.mapIso (PhiC.unitIso.app X) ≪≫ (alpha.app (PhiC.functor.obj X)).symm) hX))
      (PhiC.counitIso.app E)⟩

/-- `Slicing.preimage_mapEquiv` with the transported witness: the twisted
preimage slicing is the twist of the preimage slicing, and it exists.  This is
the complete statement of Lemma 3.5(1) and Lemma 3.9(1) of arXiv:2607.28411v1
and of Lemma 3.2 of arXiv:2601.22994 at the level of slicings. -/
theorem Slicing.PreimageData.preimage_mapEquiv (h : s.PreimageData F)
    (PhiC : C ≌ C) (PhiD : D ≌ D)
    [PhiC.functor.Additive] [PhiC.inverse.Additive]
    [PhiC.functor.CommShift ℤ] [PhiC.inverse.CommShift ℤ]
    [PhiC.functor.IsTriangulated] [PhiC.inverse.IsTriangulated]
    [PhiD.functor.Additive] [PhiD.inverse.Additive]
    [PhiD.functor.CommShift ℤ] [PhiD.inverse.CommShift ℤ]
    [PhiD.functor.IsTriangulated] [PhiD.inverse.IsTriangulated]
    (alpha : F ⋙ PhiD.inverse ≅ PhiC.inverse ⋙ F) :
    (s.mapEquiv PhiD).preimage F (h.mapEquiv PhiC PhiD alpha) =
      (s.preimage F h).mapEquiv PhiC :=
  s.preimage_mapEquiv F h PhiC PhiD alpha _

end Twist

variable [IsTriangulated C] [IsTriangulated D]
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

end CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
variable {LambdaC : Type u₃} [AddCommGroup LambdaC]
variable {LambdaD : Type u₄} [AddCommGroup LambdaD]

omit [IsTriangulated C] [IsTriangulated D] in
/-- Representative-level `AutPairQuot` compatibility for preimage transfer.

This theorem is intentionally about representatives `aC` and `aD`: quotient
descent additionally requires the geometric transfer data to be independent
of representatives, which is a property of the eventual family functors. -/
@[nolint unusedArguments]
theorem AutPair.preimage_representatives
    (s : Slicing D) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (h : s.PreimageData F)
    (vC : K₀ C →+ LambdaC) (vD : K₀ D →+ LambdaD)
    (aC : AutPair vC) (aD : AutPair vD)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ aC.Φ.e.inverse ⋙ F)
    (hmap : (s.mapEquiv aD.Φ.e).PreimageData F) :
    (s.mapEquiv aD.Φ.e).preimage F hmap =
      (s.preimage F h).mapEquiv aC.Φ.e :=
  CategoryTheory.Triangulated.Slicing.preimage_mapEquiv
    s F h aC.Φ.e aD.Φ.e alpha hmap

variable {vD : K₀ D →+ LambdaD}

omit [IsTriangulated C] [IsTriangulated D] in
/-- The compatible lattice datum of a target pair transports to the
transferred class map `v ∘ K₀(F)`: the same `lam` works, because the
intertwining isomorphism identifies `K₀(F) ∘ K₀(PhiC⁻¹)` with
`K₀(PhiD⁻¹) ∘ K₀(F)`.  This is what lets an autoequivalence of the source
act on transferred stability conditions with charges, not only on their
slicings. -/
def AutPair.preimage (aD : AutPair vD) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (PhiC : TriEquiv C)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ PhiC.e.inverse ⋙ F) :
    AutPair (vD.comp (K₀.map F)) where
  Φ := PhiC
  lam := aD.lam
  compat x := by
    have hcomp : (K₀.map F).comp (K₀.map PhiC.e.inverse) =
        (K₀.map aD.Φ.e.inverse).comp (K₀.map F) := by
      rw [← K₀.map_comp, ← K₀.map_comp, K₀.map_congr alpha]
    have hx := DFunLike.congr_fun hcomp x
    simp only [AddMonoidHom.comp_apply] at hx
    change vD (K₀.map F (K₀.map PhiC.e.inverse x)) = aD.lam (vD (K₀.map F x))
    rw [hx, aD.compat]

omit [IsTriangulated C] [IsTriangulated D] in
/-- The transported pair acts on the source through the chosen twist.
Definitional; recorded for `simp`. -/
@[simp]
theorem AutPair.preimage_Φ (aD : AutPair vD) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (PhiC : TriEquiv C)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ PhiC.e.inverse ⋙ F) :
    (aD.preimage F PhiC alpha).Φ = PhiC := rfl

omit [IsTriangulated C] [IsTriangulated D] in
/-- The transported pair keeps the lattice automorphism of the original.
Definitional; recorded for `simp`. -/
@[simp]
theorem AutPair.preimage_lam (aD : AutPair vD) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (PhiC : TriEquiv C)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ PhiC.e.inverse ⋙ F) :
    (aD.preimage F PhiC alpha).lam = aD.lam := rfl

/-- **Transfer commutes with the autoequivalence action on stability
conditions.**  Acting by `aD` and then transferring along `F` is the same as
transferring and then acting by the transported pair.  The slicing half is
`Slicing.PreimageData.preimage_mapEquiv`; the charge half is definitional,
since both sides carry `Z ∘ lam`.  This is Lemma 3.2 of arXiv:2601.22994 with
its central charges: `(f_♯σ) ⊗ L = f_♯(σ ⊗ f^*L)`. -/
theorem AutPair.preimage_act (aD : AutPair vD)
    (σ : StabilityCondition.WithClassMap D vD) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : σ.slicing.PreimageData F)
    (PhiC : TriEquiv C) (alpha : F ⋙ aD.Φ.e.inverse ≅ PhiC.e.inverse ⋙ F) :
    (aD.act σ).preimage F (h.mapEquiv PhiC.e aD.Φ.e alpha) =
      (aD.preimage F PhiC alpha).act (σ.preimage F h) := by
  refine StabilityCondition.WithClassMap.ext (C := C) ?_ ?_
  · exact h.preimage_mapEquiv PhiC.e aD.Φ.e alpha
  · ext x
    rfl

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
