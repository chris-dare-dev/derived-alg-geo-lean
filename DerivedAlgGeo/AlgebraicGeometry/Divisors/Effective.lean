/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.AssociatedSheaf
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Exactness
import DerivedAlgGeo.AlgebraicGeometry.Modules.LocallySurjective
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Effective Cartier divisors

An effective Cartier divisor on an integral scheme is presented by a Cartier divisor, a closed
subscheme, and an identification of `O_X(-D)` with the ideal sheaf of that subscheme. This file
constructs the fundamental sequence

`0 → O_X(-D) → O_X → i_* O_D → 0`,

proves its exactness in `X.Modules`, and lifts it to `Coh X` under explicit coherence
hypotheses. Exact tensoring by an invertible sheaf is supplied by the neutral `Modules.Tensor`
layer; this gives the normalized twisted sequence

`0 → O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D → 0`.

The closed subscheme comes from Mathlib's `Scheme.IdealSheafData.subscheme`. Surjectivity of
the quotient map is checked locally on the affine-open basis, where Mathlib supplies the
corresponding surjectivity theorem.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

/-- The quotient from the structure sheaf to the pushed-forward structure sheaf of the closed
subscheme defined by an ideal sheaf. -/
noncomputable def quotientMap (I : X.IdealSheafData) :
    Modules.Hom (SheafOfModules.unit X.ringCatSheaf)
      ((Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- The structure-sheaf quotient defining a closed subscheme is an epimorphism.

The affine opens are a basis, so every point of an open `U` sits in an affine `V ≤ U`, and
`subschemeι_app_surjective` produces a preimage there. That is exactly the pointwise hypothesis
of `Modules.epi_of_pointwise_preimages`, which runs the local-surjectivity chain. -/
noncomputable instance quotientMap_epi (I : X.IdealSheafData) :
    Epi (C := X.Modules) I.quotientMap := by
  refine Modules.epi_of_pointwise_preimages _ ?_
  intro U t x hxU
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  obtain ⟨s, hs⟩ := I.subschemeι_app_surjective ⟨V, hV⟩ (t |_ V)
  exact ⟨V, hVU, hxV, s, hs⟩

end IdealSheafData

variable [IsIntegral X]

/-- An effective Cartier divisor is a Cartier divisor whose inverse associated sheaf is the
ideal sheaf of a closed subscheme. -/
structure EffectiveCartierDivisor where
  divisor : CartierDivisor X
  idealSheaf : X.IdealSheafData
  idealIso : CartierDivisor.associatedSheaf (-divisor) ≅
    kernel (C := X.Modules) idealSheaf.quotientMap

namespace EffectiveCartierDivisor

/-- The pushed-forward structure sheaf of the divisor's closed subscheme. -/
noncomputable def structureSheaf (D : EffectiveCartierDivisor (X := X)) : X.Modules :=
  (Modules.pushforward D.idealSheaf.subschemeι).obj
    (SheafOfModules.unit D.idealSheaf.subscheme.ringCatSheaf)

/-- The quotient `O_X → i_* O_D`. -/
noncomputable def quotient (D : EffectiveCartierDivisor (X := X)) :
    Modules.Hom (SheafOfModules.unit X.ringCatSheaf) D.structureSheaf :=
  D.idealSheaf.quotientMap

noncomputable instance quotient_epi (D : EffectiveCartierDivisor (X := X)) :
    Epi (C := X.Modules) D.quotient := by
  dsimp only [quotient]
  exact D.idealSheaf.quotientMap_epi

/-- The canonical inclusion `O_X(-D) → O_X`. -/
noncomputable def idealInclusion (D : EffectiveCartierDivisor (X := X)) :
    Modules.Hom (CartierDivisor.associatedSheaf (-D.divisor))
      (SheafOfModules.unit X.ringCatSheaf) :=
  D.idealIso.hom ≫ kernel.ι (C := X.Modules) D.quotient

/-- The fundamental complex `O_X(-D) → O_X → i_* O_D`. -/
noncomputable def fundamentalSequence (D : EffectiveCartierDivisor (X := X)) :
    ShortComplex X.Modules :=
  ShortComplex.mk D.idealInclusion D.quotient (by
    change (D.idealIso.hom ≫ kernel.ι (C := X.Modules) D.quotient) ≫
      D.quotient = 0
    calc
      _ = D.idealIso.hom ≫
          (kernel.ι (C := X.Modules) D.quotient ≫ D.quotient) :=
        Category.assoc _ _ _
      _ = D.idealIso.hom ≫ 0 := congrArg (D.idealIso.hom ≫ ·)
        (kernel.condition (C := X.Modules) D.quotient)
      _ = 0 := comp_zero)

private noncomputable def kernelSequence (D : EffectiveCartierDivisor (X := X)) :
    ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (C := X.Modules) D.quotient) D.quotient (kernel.condition _)

private noncomputable def fundamentalSequenceIsoKernel
    (D : EffectiveCartierDivisor (X := X)) :
    D.fundamentalSequence ≅ D.kernelSequence :=
  ShortComplex.isoMk D.idealIso (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)

/-- The fundamental sequence of an effective Cartier divisor is short exact. -/
theorem fundamentalSequence_shortExact (D : EffectiveCartierDivisor (X := X)) :
    D.fundamentalSequence.ShortExact := by
  apply ShortComplex.shortExact_of_iso D.fundamentalSequenceIsoKernel.symm
  change (ShortComplex.mk (kernel.ι (C := X.Modules) D.quotient) D.quotient
    (kernel.condition (C := X.Modules) D.quotient)).ShortExact
  exact { exact := ShortComplex.exact_kernel (C := X.Modules) D.quotient }

/-- The divisor structure sheaf is the cokernel of `O_X(-D) → O_X`. -/
noncomputable def cokernelIsoStructureSheaf (D : EffectiveCartierDivisor (X := X)) :
    cokernel (C := X.Modules) D.idealInclusion ≅ D.structureSheaf :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (C := X.Modules) D.idealInclusion)
    D.fundamentalSequence_shortExact.gIsCokernel

/-- The structure sheaf of the divisor, twisted by `O_X(E)`. -/
noncomputable def twistedStructureSheaf (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) : X.Modules :=
  Modules.tensorObj (CartierDivisor.associatedSheaf E) D.structureSheaf

/-- Tensor form of the fundamental sequence twisted by `O_X(E)`. -/
noncomputable def tensorTwistSequence (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) : ShortComplex X.Modules :=
  D.fundamentalSequence.map
    (Modules.tensorLeftFunctor (CartierDivisor.associatedSheaf E))

/-- The source of the tensor-twisted sequence is `O_X(E - D)`. -/
noncomputable def twistSourceIso (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) :
    (D.tensorTwistSequence E).X₁ ≅
      CartierDivisor.associatedSheaf (E - D.divisor) :=
  CartierDivisor.associatedTensorAddIso E (-D.divisor) ≪≫
    eqToIso (by simp [sub_eq_add_neg])

/-- The middle of the tensor-twisted sequence is `O_X(E)`. -/
noncomputable def twistMiddleIso (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) :
    (D.tensorTwistSequence E).X₂ ≅ CartierDivisor.associatedSheaf E :=
  Modules.tensorUnitRightIso (CartierDivisor.associatedSheaf E)

/-- The inclusion `O_X(E - D) → O_X(E)`. -/
noncomputable def twistedIdealInclusion (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) :
    CartierDivisor.associatedSheaf (E - D.divisor) ⟶
      CartierDivisor.associatedSheaf E :=
  (D.twistSourceIso E).inv ≫ (D.tensorTwistSequence E).f ≫
    (D.twistMiddleIso E).hom

/-- The quotient `O_X(E) → O_X(E) ⊗ i_* O_D`. -/
noncomputable def twistedQuotient (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) :
    CartierDivisor.associatedSheaf E ⟶ D.twistedStructureSheaf E :=
  (D.twistMiddleIso E).inv ≫ (D.tensorTwistSequence E).g

/-- The normalized twisted fundamental sequence
`O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D`. -/
noncomputable def twistSequence (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) : ShortComplex X.Modules :=
  ShortComplex.mk (D.twistedIdealInclusion E) (D.twistedQuotient E) (by
    change ((D.twistSourceIso E).inv ≫ (D.tensorTwistSequence E).f ≫
      (D.twistMiddleIso E).hom) ≫
      ((D.twistMiddleIso E).inv ≫ (D.tensorTwistSequence E).g) = 0
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [(D.tensorTwistSequence E).zero, comp_zero])

private noncomputable def tensorTwistSequenceIsoTwistSequence
    (D : EffectiveCartierDivisor (X := X)) (E : CartierDivisor X) :
    D.tensorTwistSequence E ≅ D.twistSequence E :=
  ShortComplex.isoMk (D.twistSourceIso E) (D.twistMiddleIso E) (Iso.refl _)
    (by simp [twistSequence, twistedIdealInclusion])
    (by
      dsimp [twistSequence, twistedQuotient]
      rw [Iso.hom_inv_id_assoc]
      change (D.tensorTwistSequence E).g =
        (D.tensorTwistSequence E).g ≫ 𝟙 _
      exact (Category.comp_id (D.tensorTwistSequence E).g).symm)

/-- Twisting the fundamental sequence by any Cartier divisor remains short exact. -/
theorem twistSequence_shortExact (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) : (D.twistSequence E).ShortExact := by
  apply ShortComplex.shortExact_of_iso (D.tensorTwistSequenceIsoTwistSequence E)
  exact Modules.shortExact_map_tensorLeft_of_invertible
    (CartierDivisor.associatedSheaf E) D.fundamentalSequence
      D.fundamentalSequence_shortExact

/-- The final term of the twisted sequence is the cokernel of its inclusion. -/
noncomputable def twistCokernelIso (D : EffectiveCartierDivisor (X := X))
    (E : CartierDivisor X) :
    cokernel (C := X.Modules) (D.twistedIdealInclusion E) ≅
      D.twistedStructureSheaf E :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (C := X.Modules) (D.twistedIdealInclusion E))
    (D.twistSequence_shortExact E).gIsCokernel

/-- The divisor structure sheaf is coherent when `O_X(-D)` and `O_X` are coherent. -/
theorem structureSheaf_isCoherent (D : EffectiveCartierDivisor (X := X))
    [IsLocallyNoetherian X]
    (hIdeal : Scheme.coherent X (CartierDivisor.associatedSheaf (-D.divisor)))
    (hUnit : Scheme.coherent X (SheafOfModules.unit X.ringCatSheaf)) :
    Scheme.coherent X D.structureSheaf :=
  (Scheme.coherent X).prop_of_iso D.cokernelIsoStructureSheaf
    ((Scheme.coherent X).prop_cokernel D.idealInclusion hIdeal hUnit)

/-- The coherent-sheaf form of the fundamental sequence. -/
noncomputable def cohFundamentalSequence (D : EffectiveCartierDivisor (X := X))
    [IsLocallyNoetherian X]
    (hIdeal : Scheme.coherent X (CartierDivisor.associatedSheaf (-D.divisor)))
    (hUnit : Scheme.coherent X (SheafOfModules.unit X.ringCatSheaf)) :
    ShortComplex (Coh X) :=
  ShortComplex.mk
    (⟨D.idealInclusion⟩ :
      (⟨CartierDivisor.associatedSheaf (-D.divisor), hIdeal⟩ : Coh X) ⟶
        (⟨SheafOfModules.unit X.ringCatSheaf, hUnit⟩ : Coh X))
    (⟨D.quotient⟩ :
      (⟨SheafOfModules.unit X.ringCatSheaf, hUnit⟩ : Coh X) ⟶
        (⟨D.structureSheaf, D.structureSheaf_isCoherent hIdeal hUnit⟩ : Coh X))
    (by
      apply ObjectProperty.hom_ext
      exact D.fundamentalSequence.zero)

/-- The coherent fundamental sequence is short exact. -/
theorem cohFundamentalSequence_shortExact
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (hIdeal : Scheme.coherent X (CartierDivisor.associatedSheaf (-D.divisor)))
    (hUnit : Scheme.coherent X (SheafOfModules.unit X.ringCatSheaf)) :
    (D.cohFundamentalSequence hIdeal hUnit).ShortExact := by
  letI : (Coh.ι X).Faithful := by
    change (Scheme.coherent X).ι.Faithful
    infer_instance
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (Coh.ι X)
  let e : D.fundamentalSequence ≅
      (D.cohFundamentalSequence hIdeal hUnit).map (Coh.ι X) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rfl) (by rfl)
  exact ShortComplex.shortExact_of_iso e D.fundamentalSequence_shortExact

/-- The twisted divisor sheaf is coherent when the two line-bundle terms are coherent. -/
theorem twistedStructureSheaf_isCoherent
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    Scheme.coherent X (D.twistedStructureSheaf E) :=
  (Scheme.coherent X).prop_of_iso (D.twistCokernelIso E)
    ((Scheme.coherent X).prop_cokernel (D.twistedIdealInclusion E)
      hSource hMiddle)

/-- The coherent-sheaf form of the twisted fundamental sequence. -/
noncomputable def cohTwistSequence
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    ShortComplex (Coh X) :=
  ShortComplex.mk
    (⟨D.twistedIdealInclusion E⟩ :
      (⟨CartierDivisor.associatedSheaf (E - D.divisor), hSource⟩ : Coh X) ⟶
        (⟨CartierDivisor.associatedSheaf E, hMiddle⟩ : Coh X))
    (⟨D.twistedQuotient E⟩ :
      (⟨CartierDivisor.associatedSheaf E, hMiddle⟩ : Coh X) ⟶
        (⟨D.twistedStructureSheaf E,
          D.twistedStructureSheaf_isCoherent E hSource hMiddle⟩ : Coh X))
    (by
      apply ObjectProperty.hom_ext
      exact (D.twistSequence E).zero)

/-- The coherent twisted fundamental sequence is short exact. -/
theorem cohTwistSequence_shortExact
    (D : EffectiveCartierDivisor (X := X)) [IsLocallyNoetherian X]
    (E : CartierDivisor X)
    (hSource : Scheme.coherent X
      (CartierDivisor.associatedSheaf (E - D.divisor)))
    (hMiddle : Scheme.coherent X (CartierDivisor.associatedSheaf E)) :
    (D.cohTwistSequence E hSource hMiddle).ShortExact := by
  letI : (Coh.ι X).Faithful := by
    change (Scheme.coherent X).ι.Faithful
    infer_instance
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (Coh.ι X)
  change (D.twistSequence E).ShortExact
  exact D.twistSequence_shortExact E

end EffectiveCartierDivisor

end AlgebraicGeometry.Scheme
