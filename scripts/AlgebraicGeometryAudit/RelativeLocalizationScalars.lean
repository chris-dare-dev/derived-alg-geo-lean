import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-! Axiom records and an ordinary relative-scheme client for denominator scalars. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory

#print axioms AlgebraicGeometry.DerivedCategory.Dqc.boundedCoherentLinearOfAffineMap
#print axioms AlgebraicGeometry.DerivedCategory.Dqc.boundedCoherentLinearOfAffineMap_smul
#print axioms AlgebraicGeometry.DerivedCategory.Dqc.isIso_smul_id_of_isLocalization
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.affineAlgebraBaseChange
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.boundedFunctor_isIso_smul_denominator

noncomputable section

universe u

-- No affineness hypothesis is imposed on X or its base change.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : Families.SchemeBaseChange (Spec (CommRingCat.of R)))
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap X
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent)
    (s : M)
    (E : Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
        (X ⨯ Families.SchemeBaseChange.affineAlgebraBaseChange
          (R := R) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
        (Families.SchemeBaseChange.baseChangeSnd X
          (Families.SchemeBaseChange.affineAlgebraBaseChange
            (R := R) (A := A))).left
    IsIso ((s : R) • 𝟙 ((pull.boundedFunctor hBounded).obj E)) := by
  exact Families.SchemeBaseChange.boundedFunctor_isIso_smul_denominator
    M X pull hBounded s E

private noncomputable abbrev projectiveLineBaseChange
    (k : Type u) [Field k] :
    Families.SchemeBaseChange (Spec (CommRingCat.of k)) :=
  Over.mk (projectiveSpaceToSpec (ULift.{u} (Fin 2)) k)

-- A concrete non-affine-facing caller: X is the projective line over k.
example {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (M : Submonoid k) [IsLocalization M A]
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap (projectiveLineBaseChange k)
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := k) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent)
    (s : M)
    (E : Dqc.SchemeBoundedCoherentDqcCategory
      (projectiveLineBaseChange k ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of k))).left) :
    letI : Linear k (Dqc.SchemeBoundedCoherentDqcCategory
        (projectiveLineBaseChange k ⨯
          Families.SchemeBaseChange.affineAlgebraBaseChange
            (R := k) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap k A)
        (Families.SchemeBaseChange.baseChangeSnd (projectiveLineBaseChange k)
          (Families.SchemeBaseChange.affineAlgebraBaseChange
            (R := k) (A := A))).left
    IsIso ((s : k) • 𝟙 ((pull.boundedFunctor hBounded).obj E)) := by
  exact Families.SchemeBaseChange.boundedFunctor_isIso_smul_denominator
    M (projectiveLineBaseChange k) pull hBounded s E

end
