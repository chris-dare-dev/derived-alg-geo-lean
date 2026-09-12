/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChange
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift

/-!
# Pullback between K-flat base-change categories

A morphism `f : T ⟶ U` over `S` induces `X ×_S T ⟶ X ×_S U`. This file constructs
its derived pullback from the K-flat resolution already carried by the target base-change data and
then restricts that functor to `(Dqc)_U ⟶ (Dqc)_T` and `D_U ⟶ D_T`.

The only component-level hypothesis is preservation of `(Dqc)`. Once the derived pullback also
preserves bounded coherent cohomology, preservation of `D_U` follows formally because `D_U` was
constructed as the inverse image of `(Dqc)_U` in that intrinsic bounded-coherent locus.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S}

/-- The morphism `X ×_S T ⟶ X ×_S U` induced by `f : T ⟶ U`. -/
abbrev baseChangeMap (X : SchemeBaseChange S) {T U : SchemeBaseChange S} (f : T ⟶ U) :
    X ⨯ T ⟶ X ⨯ U :=
  Limits.prod.map (𝟙 X) f

/-- The square formed by `X ×_S f` and the second projections is a
pullback square in the category of schemes over `S`. -/
theorem baseChangeMap_isPullback (X : SchemeBaseChange S)
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    IsPullback (baseChangeSnd X T) (baseChangeMap X f) f
      (baseChangeSnd X U) := by
  apply IsPullback.mk'
  · simp only [baseChangeSnd, baseChangeMap, Limits.prod.map_snd]
  · intro Z φ φ' hfst hsnd
    apply Limits.prod.hom_ext
    · have h := congrArg (fun k ↦ k ≫ Limits.prod.fst) hsnd
      simpa only [Category.assoc, baseChangeMap, Limits.prod.map_fst,
        Category.comp_id] using h
    · exact hfst
  · intro Z a b h
    refine ⟨Limits.prod.lift (b ≫ Limits.prod.fst) a, ?_, ?_⟩
    · exact Limits.prod.lift_snd _ _
    · apply Limits.prod.hom_ext
      · simp only [Category.assoc, baseChangeMap, Limits.prod.map_fst,
          Category.comp_id, Limits.prod.lift_fst]
      · simp only [baseChangeMap]
        rw [Category.assoc, Limits.prod.map_snd, ← Category.assoc,
          Limits.prod.lift_snd]
        exact h

/-- Open immersions are preserved by the product base change `X ×_S -`. -/
theorem isOpenImmersion_baseChangeMap (X : SchemeBaseChange S)
    {T U : SchemeBaseChange S} (f : T ⟶ U) [IsOpenImmersion f.left] :
    IsOpenImmersion (baseChangeMap X f).left := by
  exact (@IsOpenImmersion).of_isPullback
    ((Over.forget S).map_isPullback (baseChangeMap_isPullback X f))
    (by change IsOpenImmersion f.left; infer_instance)

instance (priority := 900) isOpenImmersionBaseChangeMap
    (X : SchemeBaseChange S) {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : IsOpenImmersion (baseChangeMap X f).left :=
  isOpenImmersion_baseChangeMap X f

/-- Quasi-compact morphisms are preserved by the product base change
`X ×_S -`. -/
theorem quasiCompact_baseChangeMap (X : SchemeBaseChange S)
    {T U : SchemeBaseChange S} (f : T ⟶ U) [QuasiCompact f.left] :
    QuasiCompact (baseChangeMap X f).left := by
  exact MorphismProperty.of_isPullback (P := @QuasiCompact)
    ((Over.forget S).map_isPullback (baseChangeMap_isPullback X f))
    (by change QuasiCompact f.left; infer_instance)

instance (priority := 900) quasiCompactBaseChangeMap
    (X : SchemeBaseChange S) {T U : SchemeBaseChange S} (f : T ⟶ U)
    [QuasiCompact f.left] : QuasiCompact (baseChangeMap X f).left :=
  quasiCompact_baseChangeMap X f

/-- Affine morphisms are preserved by the product base change
`X ×_S -`.  In particular, the induced morphism remains affine when the
original morphism is an affine localization. -/
theorem isAffineHom_baseChangeMap (X : SchemeBaseChange S)
    {T U : SchemeBaseChange S} (f : T ⟶ U) [IsAffineHom f.left] :
    IsAffineHom (baseChangeMap X f).left := by
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    ((Over.forget S).map_isPullback (baseChangeMap_isPullback X f))
    (by change IsAffineHom f.left; infer_instance)

instance (priority := 900) isAffineHomBaseChangeMap
    (X : SchemeBaseChange S) {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsAffineHom f.left] : IsAffineHom (baseChangeMap X f).left :=
  isAffineHom_baseChangeMap X f

namespace DqcLeftDerivedPullback

variable {V W : SchemeBaseChange S} {f : V ⟶ W}

/-- A `Dqc` derived pullback preserves the intrinsic bounded-coherent locus. -/
def PreservesBoundedCoherent (pull : DqcLeftDerivedPullback f) : Prop :=
  ∀ E : Dqc.SchemeBoundedCoherentDqcCategory W.left,
    Dqc.schemeBoundedCoherentCohomology V.left (pull.functor.obj E.obj)

/-- Restrict a `Dqc` derived pullback to intrinsic bounded-coherent complexes. -/
noncomputable def boundedFunctor (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent) :
    Dqc.SchemeBoundedCoherentDqcCategory W.left ⥤
      Dqc.SchemeBoundedCoherentDqcCategory V.left :=
  (Dqc.schemeBoundedCoherentCohomology V.left).lift
    (Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor) h

/-- Forgetting bounded-coherent witnesses recovers the `Dqc` pullback. -/
noncomputable def boundedFunctorCompInclusion (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent) :
    pull.boundedFunctor h ⋙ Dqc.SchemeBoundedCoherentDqcCategory.ι V.left ≅
      Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor :=
  (Dqc.schemeBoundedCoherentCohomology V.left).liftCompιIso
    (Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor) h

@[simp]
theorem boundedFunctor_obj_obj (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent)
    (E : Dqc.SchemeBoundedCoherentDqcCategory W.left) :
    ((pull.boundedFunctor h).obj E).obj = pull.functor.obj E.obj :=
  rfl

end DqcLeftDerivedPullback

namespace KFlatBaseChangeData

variable {f : T ⟶ U}

/-- Construct pullback along `X ×_S T ⟶ X ×_S U` from the K-flat resolution on
`X ×_S U` carried by the target base-change data. -/
def pullbackAlong (D : KFlatBaseChangeData X U) (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic D.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      D.tensorResolution (baseChangeMap X f)) :
    DqcLeftDerivedPullback (baseChangeMap X f) :=
  kFlatDqcLeftDerivedPullback D.tensorResolution (baseChangeMap X f)
    hAcyclic hQuasicoherent

/-- For an open immersion of bases, the honest ambient left-derived functor
underlying the K-flat pullback is essentially surjective.  Open immersions are
stable under the product base change `X ×_S -`, and the preceding geometric
construction applies to that induced open immersion. -/
noncomputable instance pullbackAlong_ambient_essSurj_of_isOpenImmersion
    (D : KFlatBaseChangeData X U) (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic D.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      D.tensorResolution (baseChangeMap X f)) [IsOpenImmersion f.left] :
    (D.pullbackAlong f hAcyclic hQuasicoherent).ambient.functor.EssSurj := by
  letI : IsOpenImmersion (baseChangeMap X f).left := by infer_instance
  dsimp [pullbackAlong, kFlatDqcLeftDerivedPullback]
  exact LeftDerivedPullback.essSurj_of_isOpenImmersion _

/-- The exact component-level statement that pullback along `f` preserves the constructed
quasicoherent base-change component. -/
def PullbackPreservesQuasicoherentComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f)) : Prop :=
  DU.quasicoherentComponent P ≤
    (DT.quasicoherentComponent P).inverseImage pull.functor

/-- Pullback between the constructed quasicoherent base-change categories. -/
noncomputable def quasicoherentPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (h : PullbackPreservesQuasicoherentComponent DT DU P pull) :
    DU.QuasicoherentCategory P ⥤ DT.QuasicoherentCategory P :=
  ObjectProperty.liftOfLE pull.functor h

/-- Forgetting component witnesses recovers the ambient `Dqc` pullback. -/
noncomputable def quasicoherentPullbackCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (h : PullbackPreservesQuasicoherentComponent DT DU P pull) :
    quasicoherentPullback DT DU P pull h ⋙ (DT.quasicoherentComponent P).ι ≅
      (DU.quasicoherentComponent P).ι ⋙ pull.functor :=
  (DT.quasicoherentComponent P).liftCompιIso
    ((DU.quasicoherentComponent P).ι ⋙ pull.functor)
    (fun E ↦ h E.obj E.property)

/-- Preservation of the bounded component follows from preservation of `(Dqc)` together with
preservation of bounded coherent cohomology by the same derived pullback. -/
theorem pullback_preservesBoundedComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    DU.boundedComponent P ≤
      (DT.boundedComponent P).inverseImage (pull.boundedFunctor hBounded) := by
  intro E hE
  exact hDqc E.obj hE

/-- Pullback between the constructed bounded base-change categories. -/
noncomputable def boundedPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    DU.BoundedCategory P ⥤ DT.BoundedCategory P :=
  ObjectProperty.liftOfLE (pull.boundedFunctor hBounded)
    (pullback_preservesBoundedComponent DT DU P pull hDqc hBounded)

/-- Forgetting component witnesses recovers pullback on the intrinsic bounded-coherent loci. -/
noncomputable def boundedPullbackCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    boundedPullback DT DU P pull hDqc hBounded ⋙ (DT.boundedComponent P).ι ≅
      (DU.boundedComponent P).ι ⋙ pull.boundedFunctor hBounded :=
  (DT.boundedComponent P).liftCompιIso
    ((DU.boundedComponent P).ι ⋙ pull.boundedFunctor hBounded)
    (fun E ↦ pullback_preservesBoundedComponent DT DU P pull hDqc hBounded
      E.obj E.property)

/-- The fully K-flat form of pullback on `(Dqc)`: both the ambient derived functor and its
restriction to the constructed component are obtained from the resolutions. -/
noncomputable def kFlatQuasicoherentPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic DU.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      DU.tensorResolution (baseChangeMap X f))
    (hComponent : PullbackPreservesQuasicoherentComponent DT DU P
      (DU.pullbackAlong f hAcyclic hQuasicoherent)) :
    DU.QuasicoherentCategory P ⥤ DT.QuasicoherentCategory P :=
  quasicoherentPullback DT DU P (DU.pullbackAlong f hAcyclic hQuasicoherent) hComponent

/-- The fully K-flat form of pullback on `D`: the bounded restriction is constructed from the
same K-flat derived pullback used on `(Dqc)`. -/
noncomputable def kFlatBoundedPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic DU.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      DU.tensorResolution (baseChangeMap X f))
    (hComponent : PullbackPreservesQuasicoherentComponent DT DU P
      (DU.pullbackAlong f hAcyclic hQuasicoherent))
    (hBounded : (DU.pullbackAlong f hAcyclic hQuasicoherent).PreservesBoundedCoherent) :
    DU.BoundedCategory P ⥤ DT.BoundedCategory P :=
  boundedPullback DT DU P (DU.pullbackAlong f hAcyclic hQuasicoherent)
    hComponent hBounded

/-- Pullback on `(Dqc)` when membership in the source component is detected after ambient
pullback. This is the form in which essential surjectivity descends from the ambient category. -/
noncomputable def quasicoherentPullbackOfDetection
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDetect : ∀ E : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left,
      DU.quasicoherentComponent P E ↔
        DT.quasicoherentComponent P (pull.functor.obj E)) :
    DU.QuasicoherentCategory P ⥤ DT.QuasicoherentCategory P :=
  ObjectProperty.preimageLift pull.functor hDetect

/-- Lemma 3.18's essential-surjectivity argument for the quasicoherent component: ambient
essential surjectivity and detection of component membership imply essential surjectivity of the
restricted pullback. -/
noncomputable instance quasicoherentPullbackOfDetection_essSurj
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDetect : ∀ E : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left,
      DU.quasicoherentComponent P E ↔
        DT.quasicoherentComponent P (pull.functor.obj E))
    [pull.functor.EssSurj] :
    (quasicoherentPullbackOfDetection DT DU P pull hDetect).EssSurj := by
  dsimp [quasicoherentPullbackOfDetection]
  exact ObjectProperty.instEssSurjPreimageLift hDetect

/-- Pullback on `D` when bounded-component membership is detected after ambient bounded
pullback. -/
noncomputable def boundedPullbackOfDetection
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hBounded : pull.PreservesBoundedCoherent)
    (hDetect : ∀ E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left,
      DU.boundedComponent P E ↔
        DT.boundedComponent P ((pull.boundedFunctor hBounded).obj E)) :
    DU.BoundedCategory P ⥤ DT.BoundedCategory P :=
  ObjectProperty.preimageLift (pull.boundedFunctor hBounded) hDetect

/-- Lemma 3.18's essential-surjectivity argument for the bounded component. -/
noncomputable instance boundedPullbackOfDetection_essSurj
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hBounded : pull.PreservesBoundedCoherent)
    (hDetect : ∀ E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left,
      DU.boundedComponent P E ↔
        DT.boundedComponent P ((pull.boundedFunctor hBounded).obj E))
    [(pull.boundedFunctor hBounded).EssSurj] :
    (boundedPullbackOfDetection DT DU P pull hBounded hDetect).EssSurj := by
  dsimp [boundedPullbackOfDetection]
  exact ObjectProperty.instEssSurjPreimageLift hDetect

end KFlatBaseChangeData

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
