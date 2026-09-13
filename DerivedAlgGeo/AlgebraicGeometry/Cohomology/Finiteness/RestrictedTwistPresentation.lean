/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Projective
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward.Finite
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-!
# Restricted-twist presentations on a projective variety

Let `ι : X ↪ Pⁿ` be a projective presentation. Serre's theorem gives a finite sum of negative
twists surjecting onto `ι_* F`. Coherent pullback is right exact, so pulling that map back remains
an epimorphism. Composing with the adjunction counit `ι^* ι_* F ⟶ F` produces the desired
restricted-twist quotient as soon as that counit is known to be epi.

Pushforward along the closed immersion is faithful because its underlying continuous map is
inducing. The general adjunction theorem therefore makes the counit epic, which discharges that
premise without assuming the stronger standard isomorphism `ι^* ι_* F ≅ F`. The kernel of the
resulting quotient is formed afresh in `Coh X`, so no exactness of closed-immersion pullback is
asserted or used.

## Main results

* `ProjectivePresentation.restrictedTwist` is the pullback of the ambient projective twist;
* `ProjectivePresentation.restrictedTwist_isInvertible` proves its underlying module sheaf is
  intrinsically invertible;
* `ProjectivePresentation.exists_shortExact_coproduct_restrictedTwist_of_counit_epi` records the
  exact categorical reduction through the counit;
* `ProjectivePresentation.exists_shortExact_coproduct_restrictedTwist` gives the unconditional
  coherent restricted-twist presentation.
-/

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePresentation

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))]

/-- The restriction to `X` of the degree-`d` twisting sheaf from the chosen ambient projective
space. This definition requires no exactness or monoidal structure on pullback. -/
noncomputable def restrictedTwist
    (P : AlgebraicGeometry.ProjectivePresentation k X) (d : ℤ) : Coh X := by
  letI := Fintype.ofFinite P.index
  exact (Coh.pullback P.embedding).obj (Proj.projectiveSpaceTwist P.index k d)

/-- The underlying module sheaf of every restricted twist is invertible. Pullback preserves
rank-one local trivializations, so this needs no monoidal structure on the pullback functor. -/
theorem restrictedTwist_isInvertible
    (P : AlgebraicGeometry.ProjectivePresentation k X) (d : ℤ) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from (Coh.ι X).obj (P.restrictedTwist d)) := by
  letI := Fintype.ofFinite P.index
  change SheafOfModules.IsInvertible.{u, u, u}
    (show SheafOfModules X.ringCatSheaf from
      (Scheme.Modules.pullback P.embedding).obj
        ((Coh.ι _).obj (Proj.projectiveSpaceTwist P.index k d)))
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules (Proj (polynomialGrading P.index k)).ringCatSheaf from
        (Coh.ι _).obj (Proj.projectiveSpaceTwist P.index k d)) :=
    Proj.twistingSheaf_isInvertible (polynomialGrading P.index k)
      (fun i ↦ ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
      (polynomialVariable_adjoin_eq_top P.index k)
  infer_instance

variable [IsVariety k X]

/-- **A coherent sheaf is a quotient of finitely many restricted negative twists, provided the
closed-immersion pullback/pushforward counit is epi at that sheaf.**

This is the exact reduction supplied by the current APIs. The premise is expected to follow from
the standard theorem `ι^* ι_* F ≅ F` for a closed immersion; no such theorem is available at the
current Mathlib pin. -/
theorem exists_shortExact_coproduct_restrictedTwist_of_counit_epi
    (P : AlgebraicGeometry.ProjectivePresentation k X) [Nontrivial P.index] (F : Coh X)
    (hcounit : Epi
      ((Scheme.Modules.pullbackPushforwardAdjunction P.embedding).counit.app
        ((Coh.ι X).obj F))) :
    ∃ (S : ShortComplex (Coh X)) (_ : S.ShortExact) (_ : S.X₃ ≅ F)
      (N : ℕ) (_ : 1 ≤ N) (I : Type u) (_ : Finite I),
      S.X₂ = ∐ (fun _ : I ↦ P.restrictedTwist (-(N : ℤ))) := by
  classical
  letI := Fintype.ofFinite P.index
  let Y : Scheme.{u} := Proj (polynomialGrading P.index k)
  haveI : IsProper (Y ↘ Spec (CommRingCat.of k)) :=
    Proj.isProper_projectiveSpaceToSpec P.index k
  haveI : IsNoetherian Y := Variety.isNoetherian_of_isProper (k := k)
  haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := P.isProper_structureMorphism
  haveI : IsNoetherian X := Variety.isNoetherian_of_isProper (k := k)
  let PF : Coh Y := (Coh.pushforward P.embedding).obj F
  obtain ⟨T, hT, eT, N, hN, I, hI, hmiddle⟩ :=
    Proj.exists_shortExact_coproduct_twist P.index k PF
  letI := Fintype.ofFinite I
  haveI : Epi T.g := hT.epi_g
  let q : T.X₂ ⟶ PF := T.g ≫ eT.hom
  haveI : Epi q := epi_comp _ _
  let G : Coh X := ∐ (fun _ : I ↦ P.restrictedTwist (-(N : ℤ)))
  let eG : (Coh.pullback P.embedding).obj T.X₂ ≅ G :=
    (Coh.pullback P.embedding).mapIso (eqToIso hmiddle) ≪≫
      PreservesCoproduct.iso (Coh.pullback P.embedding)
        (fun _ : I ↦ Proj.projectiveSpaceTwist P.index k (-(N : ℤ)))
  haveI : Epi ((Coh.pullback P.embedding).map q) :=
    (Coh.pullback P.embedding).map_epi q
  let c : (Coh.pullback P.embedding).obj PF ⟶ F :=
    (Coh.ι X).preimage
      ((Scheme.Modules.pullbackPushforwardAdjunction P.embedding).counit.app
        ((Coh.ι X).obj F))
  haveI : Epi ((Coh.ι X).map c) := by
    rw [Functor.map_preimage]
    exact hcounit
  haveI : Epi c := (Coh.ι X).epi_of_epi_map inferInstance
  let qX : G ⟶ F := eG.inv ≫ (Coh.pullback P.embedding).map q ≫ c
  haveI : Epi qX := epi_comp _ _
  refine ⟨ShortComplex.mk (kernel.ι qX) qX (kernel.condition qX), ?_, Iso.refl F,
    N, hN, I, hI, rfl⟩
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel qX)
      mono_f := inferInstance
      epi_g := inferInstance }

/-- **Every coherent sheaf on a projective variety is a quotient of finitely many restricted
negative twists.**

The closed-immersion pullback/pushforward counit is epic because module-sheaf pushforward along
an inducing map is faithful. This conclusion does not require pullback to be exact, nor does it
claim the stronger counit isomorphism. -/
theorem exists_shortExact_coproduct_restrictedTwist
    (P : AlgebraicGeometry.ProjectivePresentation k X) [Nontrivial P.index] (F : Coh X) :
    ∃ (S : ShortComplex (Coh X)) (_ : S.ShortExact) (_ : S.X₃ ≅ F)
      (N : ℕ) (_ : 1 ≤ N) (I : Type u) (_ : Finite I),
      S.X₂ = ∐ (fun _ : I ↦ P.restrictedTwist (-(N : ℤ))) :=
  P.exists_shortExact_coproduct_restrictedTwist_of_counit_epi F inferInstance

end AlgebraicGeometry.ProjectivePresentation
