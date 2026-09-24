import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-! Axiom record and ordinary clients for relative bounded-coherent pullback linearity. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.boundedFunctor_linearOfLocalization
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.boundedFunctor_additiveOfLocalization

noncomputable section

universe u

-- A caller installs the two explicit affine-base actions, then uses `map_smul`.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : Families.SchemeBaseChange (Spec (CommRingCat.of R)))
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap X
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent)
    {E F : Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left}
    (r : R) (g : E ⟶ F) :
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (RingHom.id R)
        (Families.SchemeBaseChange.baseChangeSnd X
          (Families.SchemeBaseChange.identityBaseChange
            (Spec (CommRingCat.of R)))).left
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
        (Families.SchemeBaseChange.baseChangeSnd X
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A))).left
    (pull.boundedFunctor hBounded).map (r • g) =
      r • (pull.boundedFunctor hBounded).map g := by
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :=
    Dqc.boundedCoherentLinearOfAffineMap (RingHom.id R)
      (Families.SchemeBaseChange.baseChangeSnd X
        (Families.SchemeBaseChange.identityBaseChange
          (Spec (CommRingCat.of R)))).left
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)).left) :=
    Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
      (Families.SchemeBaseChange.baseChangeSnd X
        (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A))).left
  letI : Functor.Linear R (pull.boundedFunctor hBounded) :=
    Families.SchemeBaseChange.boundedFunctor_linearOfLocalization M X pull hBounded
  exact (pull.boundedFunctor hBounded).map_smul r g

-- Additivity is a separately proved input: together with linearity it gives
-- the actual Hom-map linear morphism, with no Hom-localization assumption.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    (X : Families.SchemeBaseChange (Spec (CommRingCat.of R)))
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap X
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent)
    (E F : Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (RingHom.id R)
        (Families.SchemeBaseChange.baseChangeSnd X
          (Families.SchemeBaseChange.identityBaseChange
            (Spec (CommRingCat.of R)))).left
    letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
        (Families.SchemeBaseChange.baseChangeSnd X
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A))).left
    (E ⟶ F) →ₗ[R]
      ((pull.boundedFunctor hBounded).obj E ⟶
        (pull.boundedFunctor hBounded).obj F) := by
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of R))).left) :=
    Dqc.boundedCoherentLinearOfAffineMap (RingHom.id R)
      (Families.SchemeBaseChange.baseChangeSnd X
        (Families.SchemeBaseChange.identityBaseChange
          (Spec (CommRingCat.of R)))).left
  letI : Linear R (Dqc.SchemeBoundedCoherentDqcCategory
      (X ⨯ Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A)).left) :=
    Dqc.boundedCoherentLinearOfAffineMap (algebraMap R A)
      (Families.SchemeBaseChange.baseChangeSnd X
        (Families.SchemeBaseChange.affineAlgebraBaseChange (R := R) (A := A))).left
  letI : (pull.boundedFunctor hBounded).Additive :=
    Families.SchemeBaseChange.boundedFunctor_additiveOfLocalization M X pull hBounded
  letI : (pull.boundedFunctor hBounded).Linear R :=
    Families.SchemeBaseChange.boundedFunctor_linearOfLocalization M X pull hBounded
  exact (pull.boundedFunctor hBounded).mapLinearMap R

private noncomputable abbrev projectiveLineBaseChange
    (k : Type u) [Field k] :
    Families.SchemeBaseChange (Spec (CommRingCat.of k)) :=
  Over.mk (projectiveSpaceToSpec (ULift.{u} (Fin 2)) k)

-- The additivity prerequisite applies with a non-affine total space as well.
example {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (M : Submonoid k) [IsLocalization M A]
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap (projectiveLineBaseChange k)
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := k) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent) :
    (pull.boundedFunctor hBounded).Additive :=
  Families.SchemeBaseChange.boundedFunctor_additiveOfLocalization
    M (projectiveLineBaseChange k) pull hBounded

-- The base scheme can be a projective line, not merely an affine scheme.
example {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (M : Submonoid k) [IsLocalization M A]
    (pull : Families.SchemeBaseChange.DqcLeftDerivedPullback
      (Families.SchemeBaseChange.baseChangeMap (projectiveLineBaseChange k)
        (Families.SchemeBaseChange.toIdentityBaseChange
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := k) (A := A)))))
    (hBounded : pull.PreservesBoundedCoherent) :
    letI : Linear k (Dqc.SchemeBoundedCoherentDqcCategory
      (projectiveLineBaseChange k ⨯ Families.SchemeBaseChange.identityBaseChange
        (Spec (CommRingCat.of k))).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (RingHom.id k)
        (Families.SchemeBaseChange.baseChangeSnd (projectiveLineBaseChange k)
          (Families.SchemeBaseChange.identityBaseChange (Spec (CommRingCat.of k)))).left
    letI : Linear k (Dqc.SchemeBoundedCoherentDqcCategory
      (projectiveLineBaseChange k ⨯
        Families.SchemeBaseChange.affineAlgebraBaseChange (R := k) (A := A)).left) :=
      Dqc.boundedCoherentLinearOfAffineMap (algebraMap k A)
        (Families.SchemeBaseChange.baseChangeSnd (projectiveLineBaseChange k)
          (Families.SchemeBaseChange.affineAlgebraBaseChange (R := k) (A := A))).left
    Functor.Linear k (pull.boundedFunctor hBounded) := by
  exact Families.SchemeBaseChange.boundedFunctor_linearOfLocalization
    M (projectiveLineBaseChange k) pull hBounded

end
