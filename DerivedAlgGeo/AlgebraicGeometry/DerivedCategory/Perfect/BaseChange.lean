/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatBaseChangeCounit
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Perfect.Relative
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.RestrictionComp

/-!
# Relative perfection is stable under derived base change of a flat family

Let `q : Y ⟶ T` be flat, `h : T' ⟶ T` any morphism and `h' : Y ×_T T' ⟶ Y` the projection. A
relative-perfect object of `Dqc(Y)` has a relative-perfect left-derived pullback along `h'`, over
`T'`. A chart `(U, P)` of the object at `h' y'` pulls back to the chart `(h'⁻¹ U, h'^* P)` at `y'`.

Relative perfection is `schemeRelativePerfect`, condition (A) of Stacks Remark 36.35.14
(Tag 0DI9). The statement is the condition (A) form of Stacks Lemma 36.35.6 (Tag 0DI5), which
BLMNPS quote as Lemma 8.4. Both state it for Stacks Definition 36.35.1 (Tag 0DI0) and a flat,
locally finitely presented `q`; Remark 36.35.14 states that the two definitions agree there, and
that agreement is not proved here.

## Main definitions

* `AlgebraicGeometry.LocalRelativePerfectChart.baseChange` — the pulled-back chart.

## Main results

* `AlgebraicGeometry.schemeRelativePerfect_baseChange_of_isPullback` — relative perfection is
  stable under every `Dqc` left-derived pullback along the first projection of a pullback
  square of a flat morphism.
* `AlgebraicGeometry.schemeRelativePerfect_baseChange` — the case of the chosen fibre product.

## Implementation notes

Let `(U, P)` be a chart of `E` at `y = f y'`, with `P` in degrees at most `b`, and let `K` be a
complex representing `E`. Write `U' = f⁻¹ U`, `f_U : U' ⟶ U` for the restriction, `R` for the
canonical free-Yoneda K-flat resolution and `τ = K.truncLE N` for a natural number `N ≥ b`.

* Every left-derived pullback along `f` is canonically isomorphic to the K-flat one, which sends
  `K` to `f^* (R K)`. Its restriction to `U'` is `f_U^* (R K)|_U`.
* The complex `K` need not be bounded above, but its restriction to `U` has no cohomology above
  `b`, as `P` represents it. The comparison `R τ ⟶ R K` is the leg at `N` of the colimit of the
  resolved good-truncation tower of `K`
  (`Scheme.Modules.isColimitFreeYonedaSheafCoproductTotalTruncLETowerCocone`). After restriction to
  `U` and pullback along `f_U` the transition maps from `N` on are quasi-isomorphisms between
  bounded-above complexes of modules flat over `T`
  (`Scheme.Modules.quasiIso_pullback_of_isPullback`). Exact filtered colimits commute with
  homology, so the leg itself becomes a quasi-isomorphism.
* On `U`, the complexes `P` and `(R τ)|_U` are bounded above with terms flat over `T` and are
  isomorphic in `D(U)`. Any left-derived pullback along `f_U` computes both by degreewise pullback
  (`LeftDerivedPullback.isIso_counit_of_isFlatOver`), which identifies `f_U^* P` with
  `f_U^* (R τ)|_U`.

Flatness of `q` is used only through the last two steps. Local finite presentation of `q`, which
Stacks Lemma 36.35.6 (Tag 0DI5) assumes, is not used by the argument with condition (A) charts.

## References

* The Stacks Project, Lemma 36.35.6 ([Tag 0DI5](https://stacks.math.columbia.edu/tag/0DI5)).
* The Stacks Project, Remark 36.35.14 ([Tag 0DI9](https://stacks.math.columbia.edu/tag/0DI9)).
* A. Bayer, M. Lahoz, E. Macrì, H. Nuer, A. Perry, P. Stellari, *Stability conditions in families*,
  arXiv:1902.08184, Lemma 8.4.

## Tags

relative perfection, base change, derived pullback, flat family
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {S : Scheme.{u}} {X X' : SchemeBaseChange S} {f : X' ⟶ X} {T T' : Scheme.{u}}
  {q : X.left ⟶ T} {q' : X'.left ⟶ T'} {h : T' ⟶ T}

/-- The restriction of a pullback square of schemes to the preimage of an open subscheme of its
upper right corner is a pullback square. -/
private theorem isPullback_restrict (H : IsPullback f.left q' q h) (U : X.left.Opens) :
    IsPullback (f.left ∣_ U) ((f.left ⁻¹ᵁ U).ι ≫ q') (U.ι ≫ q) h :=
  (isPullback_morphismRestrict f.left U).paste_vert H

/-- The restriction `f⁻¹ U ⟶ U` of `f`, as a morphism of scheme base changes over `T`. -/
private abbrev restrictOver (f : X' ⟶ X) (q : X.left ⟶ T) (U : X.left.Opens) :
    (Over.mk ((f.left ∣_ U) ≫ (relativeOpenBaseChange q U).hom) : SchemeBaseChange T) ⟶
      relativeOpenBaseChange q U :=
  Over.homMk (f.left ∣_ U)

/-- Degreewise pullback of cochain complexes of module sheaves along a morphism of schemes. -/
private abbrev pullCx {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    CochainComplex Y.Modules ℤ ⥤ CochainComplex Z.Modules ℤ :=
  (Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical free-Yoneda K-flat resolution of complexes of module sheaves. -/
private abbrev resol (Y : Scheme.{u}) :
    CochainComplex Y.Modules ℤ ⥤ CochainComplex Y.Modules ℤ :=
  Scheme.Modules.freeYonedaSheafCoproductTotalComplexFunctor Y

/-- The augmentation of the free-Yoneda resolution, a quasi-isomorphism at every complex. -/
private abbrev aug (Y : Scheme.{u}) : resol Y ⟶ 𝟭 (CochainComplex Y.Modules ℤ) :=
  Scheme.Modules.freeYonedaSheafCoproductTotalAugmentation Y

/-- Restriction of a module sheaf flat over the identity to an open subscheme is flat over the
open subscheme. -/
private theorem isFlatOver_id_restrict {Y : Scheme.{u}} (U : Y.Opens) {M : Y.Modules}
    (hM : Scheme.Modules.IsFlatOver (𝟙 Y) M) :
    Scheme.Modules.IsFlatOver (𝟙 U.toScheme) ((Scheme.Modules.pullback U.ι).obj M) :=
  hM.of_isPullback (IsPullback.id_vert U.ι)

/-- Restriction to an open subscheme is exact. -/
private theorem preservesFiniteLimits_restrict {Y : Scheme.{u}} (U : Y.Opens) :
    PreservesFiniteLimits (Scheme.Modules.pullback U.ι) :=
  openImmersionModulePullback_preservesFiniteLimits (relativeOpenTo (𝟙 Y) U)

/-- Let `H₁ ⋙ H₂ ⋙ H₃` send a cocone `s` over a sequential diagram `F` to a colimit cocone of
complexes in an abelian category with exact sequential colimits. If it sends every transition map
out of `N` to a quasi-isomorphism, it sends the leg of `s` at `N` to a quasi-isomorphism: homology
commutes with the colimit, and the homology diagram is constant from `N` on. -/
private theorem quasiIso_map_ι_of_isColimit {C₁ C₂ C₃ D : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* D] [Abelian D] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
    {F : ℕ ⥤ C₁} (s : Cocone F) (H₁ : C₁ ⥤ C₂) (H₂ : C₂ ⥤ C₃) (H₃ : C₃ ⥤ CochainComplex D ℤ)
    (hs : IsColimit ((H₁ ⋙ H₂ ⋙ H₃).mapCocone s)) (N : ℕ)
    (hF : ∀ ⦃n : ℕ⦄ (φ : N ⟶ n), QuasiIso (H₃.map (H₂.map (H₁.map (F.map φ))))) :
    QuasiIso (H₃.map (H₂.map (H₁.map (s.ι.app N)))) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hev : ((F ⋙ H₁ ⋙ H₂ ⋙ H₃) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).IsEventuallyConstantFrom N :=
    fun n φ ↦ by
      have : QuasiIso ((F ⋙ H₁ ⋙ H₂ ⋙ H₃).map φ) := hF φ
      exact (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  exact hev.isIso_ι_of_isColimit (isColimitOfPreserves _ hs)

section Chart

variable {E : SchemeQuasicoherentDerivedCategory X.left} {x : X.left}
  (c : LocalRelativePerfectChart q E x) {K : CochainComplex X.left.Modules ℤ}

/-- A representing complex restricted to a chart has no cohomology above the chart. -/
private theorem exactAt_restrict (e₀ : (SchemeDerivedCategory.Q X.left).obj K ≅ E.obj) (i : ℤ)
    (hi : c.upper < i) : ((pullCx c.openSubset.ι).obj K).ExactAt i := by
  let φ := c.represents ≪≫ (derivedPullback (relativeOpenTo q c.openSubset)).mapIso e₀.symm ≪≫
    (derivedPullbackFactors (relativeOpenTo q c.openSubset)).app K
  have := c.strictlyLE
  have h0 := (c.model.exactAt_of_isLE c.upper i hi).isZero_homology
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact h0.of_iso
    (((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso φ.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _)

/-- On a chart, the good truncation above the chart is a quasi-isomorphism. It is written as the
leg of the good-truncation tower. -/
private theorem quasiIso_restrict_leg (e₀ : (SchemeDerivedCategory.Q X.left).obj K ≅ E.obj)
    (n : ℕ) (hn : c.upper ≤ n) :
    QuasiIso ((pullCx c.openSubset.ι).map ((CochainComplex.truncLETowerCocone K).ι.app n)) := by
  have := preservesFiniteLimits_restrict c.openSubset
  have : ((CochainComplex.truncLETower K).obj n).IsStrictlyLE n :=
    inferInstanceAs ((K.truncLE n).IsStrictlyLE n)
  rw [quasiIso_iff]
  intro i
  by_cases hi : i ≤ n
  · have : QuasiIsoAt ((CochainComplex.truncLETowerCocone K).ι.app n) i :=
      K.quasiIsoAt_ιTruncLE n i hi
    infer_instance
  · rw [quasiIsoAt_iff_exactAt _ _
      (((pullCx c.openSubset.ι).obj ((CochainComplex.truncLETower K).obj n)).exactAt_of_isLE n i
        (by omega))]
    exact exactAt_restrict c e₀ i (by omega)

/-- The free-Yoneda resolution of a complex, restricted to a chart, has terms flat over the
base. -/
private theorem isFlatOver_restrict_resolution [Flat q] (U : X.left.Opens)
    (M : CochainComplex X.left.Modules ℤ) (i : ℤ) :
    Scheme.Modules.IsFlatOver (U.ι ≫ q) (((pullCx U.ι).obj ((resol X.left).obj M)).X i) :=
  Scheme.Modules.IsFlatOver.of_isFlatOver_id (isFlatOver_id_restrict U
    (Scheme.Modules.freeYonedaSheafCoproductTotalComplexFunctor_obj_X_isFlatOverId _ M i))

/-- Restricted to a chart, the resolved transition maps of the good-truncation tower above the
chart are quasi-isomorphisms. -/
private theorem quasiIso_restrict_resolution_map
    (e₀ : (SchemeDerivedCategory.Q X.left).obj K ≅ E.obj) {m n : ℕ} (φ : m ⟶ n)
    (hm : c.upper ≤ m) :
    QuasiIso ((pullCx c.openSubset.ι).map
      ((resol X.left).map ((CochainComplex.truncLETower K).map φ))) := by
  have := preservesFiniteLimits_restrict c.openSubset
  have hmn : (m : ℤ) ≤ n := by exact_mod_cast leOfHom φ
  have hι : QuasiIso ((pullCx c.openSubset.ι).map ((CochainComplex.truncLETower K).map φ)) := by
    have h₁ := quasiIso_restrict_leg c e₀ m hm
    have := quasiIso_restrict_leg c e₀ n (hm.trans hmn)
    have hcomp : (pullCx c.openSubset.ι).map ((CochainComplex.truncLETower K).map φ) ≫
        (pullCx c.openSubset.ι).map ((CochainComplex.truncLETowerCocone K).ι.app n) =
          (pullCx c.openSubset.ι).map ((CochainComplex.truncLETowerCocone K).ι.app m) := by
      rw [← Functor.map_comp, (CochainComplex.truncLETowerCocone K).w φ]
    have : QuasiIso ((pullCx c.openSubset.ι).map ((CochainComplex.truncLETower K).map φ) ≫
        (pullCx c.openSubset.ι).map ((CochainComplex.truncLETowerCocone K).ι.app n)) := by
      rw [hcomp]
      exact h₁
    exact quasiIso_of_comp_right
      ((pullCx c.openSubset.ι).map ((CochainComplex.truncLETower K).map φ))
      ((pullCx c.openSubset.ι).map ((CochainComplex.truncLETowerCocone K).ι.app n))
  have hc : ∀ M, QuasiIso ((pullCx c.openSubset.ι).map ((aug X.left).app M)) := fun M ↦ by
    have := Scheme.Modules.quasiIso_freeYonedaSheafCoproductTotalAugmentation X.left M
    infer_instance
  have hcomm : (pullCx c.openSubset.ι).map ((resol X.left).map
        ((CochainComplex.truncLETower K).map φ)) ≫
      (pullCx c.openSubset.ι).map ((aug X.left).app ((CochainComplex.truncLETower K).obj n)) =
      (pullCx c.openSubset.ι).map ((aug X.left).app ((CochainComplex.truncLETower K).obj m)) ≫
        (pullCx c.openSubset.ι).map ((CochainComplex.truncLETower K).map φ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact (aug X.left).naturality ((CochainComplex.truncLETower K).map φ)
  have := hc ((CochainComplex.truncLETower K).obj n)
  have := hc ((CochainComplex.truncLETower K).obj m)
  have : QuasiIso ((pullCx c.openSubset.ι).map ((resol X.left).map
        ((CochainComplex.truncLETower K).map φ)) ≫
      (pullCx c.openSubset.ι).map ((aug X.left).app ((CochainComplex.truncLETower K).obj n))) := by
    rw [hcomm]
    infer_instance
  exact quasiIso_of_comp_right
    ((pullCx c.openSubset.ι).map ((resol X.left).map ((CochainComplex.truncLETower K).map φ)))
    ((pullCx c.openSubset.ι).map ((aug X.left).app ((CochainComplex.truncLETower K).obj n)))

/-- Restricted to a chart and pulled back along the base change, the resolved good truncation
above the chart is a quasi-isomorphism. It is the leg at `N` of the colimit of the resolved
good-truncation tower, whose transition maps from `N` on become quasi-isomorphisms between
bounded-above complexes flat over the base. -/
private theorem quasiIso_baseChange_resolution_leg (H : IsPullback f.left q' q h) [Flat q]
    (e₀ : (SchemeDerivedCategory.Q X.left).obj K ≅ E.obj) (N : ℕ) (hN : c.upper ≤ N) :
    QuasiIso ((pullCx (f.left ∣_ c.openSubset)).map ((pullCx c.openSubset.ι).map
      ((resol X.left).map ((CochainComplex.truncLETowerCocone K).ι.app N)))) := by
  have hcol : IsColimit ((resol X.left ⋙ pullCx c.openSubset.ι ⋙
      pullCx (f.left ∣_ c.openSubset)).mapCocone (CochainComplex.truncLETowerCocone K)) :=
    isColimitOfPreserves (pullCx c.openSubset.ι ⋙ pullCx (f.left ∣_ c.openSubset))
      (Scheme.Modules.isColimitFreeYonedaSheafCoproductTotalTruncLETowerCocone X.left K)
  have : AB5OfSize.{0, 0} (f.left ⁻¹ᵁ c.openSubset).toScheme.Modules :=
    AB5OfSize_of_univLE (f.left ⁻¹ᵁ c.openSubset).toScheme.Modules
  refine quasiIso_map_ι_of_isColimit (CochainComplex.truncLETowerCocone K) (resol X.left)
    (pullCx c.openSubset.ι) (pullCx (f.left ∣_ c.openSubset)) hcol N fun n φ ↦ ?_
  have hle : (N : ℤ) ≤ n := by exact_mod_cast leOfHom φ
  have : ((CochainComplex.truncLETower K).obj N).IsStrictlyLE N :=
    inferInstanceAs ((K.truncLE N).IsStrictlyLE N)
  have : ((CochainComplex.truncLETower K).obj n).IsStrictlyLE n :=
    inferInstanceAs ((K.truncLE n).IsStrictlyLE n)
  have : ((resol X.left).obj ((CochainComplex.truncLETower K).obj N)).IsStrictlyLE N :=
    Scheme.Modules.isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj _ _ _
  have : ((resol X.left).obj ((CochainComplex.truncLETower K).obj n)).IsStrictlyLE n :=
    Scheme.Modules.isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj _ _ _
  exact Scheme.Modules.quasiIso_pullback_of_isPullback (isPullback_restrict H c.openSubset)
    _ N n (quasiIso_restrict_resolution_map c e₀ φ hN)
    (isFlatOver_restrict_resolution c.openSubset _) (isFlatOver_restrict_resolution c.openSubset _)

/-- The isomorphism in the derived category of `f⁻¹ U` exhibiting the pulled-back model of a
chart as the restriction of the derived pullback. -/
private def baseChangeRepresents (H : IsPullback f.left q' q h) [Flat q]
    (P : LeftDerivedPullback f) {E' : SchemeQuasicoherentDerivedCategory X'.left}
    (e : E'.obj ≅ P.functor.obj E.obj) (e₀ : (SchemeDerivedCategory.Q X.left).obj K ≅ E.obj)
    (N : ℕ) (hN : c.upper ≤ N) :
    (SchemeDerivedCategory.Q (f.left ⁻¹ᵁ c.openSubset).toScheme).obj
        ((pullCx (f.left ∣_ c.openSubset)).obj c.model) ≅
      (derivedPullback (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).obj E'.obj := by
  have := preservesFiniteLimits_restrict c.openSubset
  let QX := SchemeDerivedCategory.Q X.left
  let QU := SchemeDerivedCategory.Q c.openSubset.toScheme
  let QU' := SchemeDerivedCategory.Q (f.left ⁻¹ᵁ c.openSubset).toScheme
  let A := arbitraryLeftDerivedPullback f
  let AU := arbitraryLeftDerivedPullback (restrictOver f q c.openSubset)
  let Ψ := (kFlatPullbackAcyclicResolution (freeYonedaSchemeKFlatResolution X.left) f
    (kFlatPullbackAcyclic _ f)).derivedFactors
  let θ := Functor.leftDerivedNatIso A.functor P.functor A.counit P.counit
    (HomologicalComplex.quasiIso _ _) (Iso.refl _)
  have hι : IsIso (QU.map ((pullCx c.openSubset.ι).map
      ((CochainComplex.truncLETowerCocone K).ι.app N))) :=
    Localization.inverts _ (HomologicalComplex.quasiIso _ _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 (quasiIso_restrict_leg c e₀ N hN))
  let φ : QU.obj c.model ≅
      QU.obj ((pullCx c.openSubset.ι).obj ((CochainComplex.truncLETower K).obj N)) :=
    c.represents ≪≫ (derivedPullback (relativeOpenTo q c.openSubset)).mapIso e₀.symm ≪≫
      (derivedPullbackFactors (relativeOpenTo q c.openSubset)).app K ≪≫
      (@asIso _ _ _ _ _ hι).symm
  have haug : IsIso (QU.map ((pullCx c.openSubset.ι).map
      ((aug X.left).app ((CochainComplex.truncLETower K).obj N)))) := by
    have := Scheme.Modules.quasiIso_freeYonedaSheafCoproductTotalAugmentation X.left
      ((CochainComplex.truncLETower K).obj N)
    exact Localization.inverts _ (HomologicalComplex.quasiIso _ _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)
  have : ((CochainComplex.truncLETower K).obj N).IsStrictlyLE N :=
    inferInstanceAs ((K.truncLE N).IsStrictlyLE N)
  have : ((resol X.left).obj ((CochainComplex.truncLETower K).obj N)).IsStrictlyLE N :=
    Scheme.Modules.isStrictlyLE_freeYonedaSheafCoproductTotalComplexFunctor_obj _ _ _
  have hflat : Flat (c.openSubset.ι ≫ q) := inferInstance
  have hAM : IsIso (AU.counit.app c.model) :=
    @LeftDerivedPullback.isIso_counit_of_isFlatOver _ _ _ _ AU _ _ _ _ _
      (isPullback_restrict H c.openSubset) hflat c.model c.upper c.strictlyLE c.flatOverBase
  have hAR : IsIso (AU.counit.app ((pullCx c.openSubset.ι).obj
      ((resol X.left).obj ((CochainComplex.truncLETower K).obj N)))) :=
    @LeftDerivedPullback.isIso_counit_of_isFlatOver _ _ _ _ AU _ _ _ _ _
      (isPullback_restrict H c.openSubset) hflat _ N
      (inferInstance : CochainComplex.IsStrictlyLE
        ((pullCx c.openSubset.ι).obj
          ((resol X.left).obj ((CochainComplex.truncLETower K).obj N))) N)
      (isFlatOver_restrict_resolution c.openSubset ((CochainComplex.truncLETower K).obj N))
  have hLQ : IsIso (QU'.map ((pullCx (f.left ∣_ c.openSubset)).map ((pullCx c.openSubset.ι).map
      ((resol X.left).map ((CochainComplex.truncLETowerCocone K).ι.app N))))) :=
    Localization.inverts _ (HomologicalComplex.quasiIso _ _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (quasiIso_baseChange_resolution_leg c H e₀ N hN))
  let ε : Scheme.Modules.pullback c.openSubset.ι ⋙
      Scheme.Modules.pullback (f.left ∣_ c.openSubset) ≅
      Scheme.Modules.pullback f.left ⋙ Scheme.Modules.pullback (f.left ⁻¹ᵁ c.openSubset).ι :=
    (Scheme.Modules.pullbackComp' (f.left ∣_ c.openSubset) c.openSubset.ι _ rfl).symm ≪≫
      Scheme.Modules.pullbackComp' (f.left ⁻¹ᵁ c.openSubset).ι f.left _
        (morphismRestrict_ι f.left c.openSubset).symm
  exact (@asIso _ _ _ _ _ hAM).symm ≪≫ AU.functor.mapIso φ ≪≫
    AU.functor.mapIso (@asIso _ _ _ _ _ haug).symm ≪≫ @asIso _ _ _ _ _ hAR ≪≫
    @asIso _ _ _ _ _ hLQ ≪≫
    QU'.mapIso ((NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).app ((resol X.left).obj K)) ≪≫
    ((derivedPullbackFactors (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).app
      ((complexPullback f).obj ((resol X.left).obj K))).symm ≪≫
    (derivedPullback (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).mapIso (Ψ.app K).symm ≪≫
    (derivedPullback (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).mapIso (θ.app (QX.obj K)) ≪≫
    (derivedPullback (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).mapIso (P.functor.mapIso e₀) ≪≫
    (derivedPullback (relativeOpenTo q' (f.left ⁻¹ᵁ c.openSubset))).mapIso e.symm

end Chart

/-- **Base change of a relative-perfect chart along a flat family.** Let `f : X' ⟶ X` have
underlying morphism the first projection of a pullback square along a flat `q : X ⟶ T`, and let
`P` be a left-derived pullback along `f`. A chart `(U, M)` of `E` at `f x'` gives the chart
`(f⁻¹ U, f_U^* M)` of the derived pullback of `E` at `x'`, over `T'`, where `f_U : f⁻¹ U ⟶ U`
is the restriction of `f`. -/
def LocalRelativePerfectChart.baseChange (H : IsPullback f.left q' q h) [Flat q]
    (P : LeftDerivedPullback f) {E : SchemeQuasicoherentDerivedCategory X.left}
    {E' : SchemeQuasicoherentDerivedCategory X'.left} (e : E'.obj ≅ P.functor.obj E.obj)
    {x' : X'.left} (c : LocalRelativePerfectChart q E (f.left x')) :
    LocalRelativePerfectChart q' E' x' where
  openSubset := f.left ⁻¹ᵁ c.openSubset
  mem_openSubset := c.mem_openSubset
  lower := c.lower
  upper := c.upper
  lower_le_upper := c.lower_le_upper
  model := (pullCx (f.left ∣_ c.openSubset)).obj c.model
  strictlyGE := by have := c.strictlyGE; infer_instance
  strictlyLE := by have := c.strictlyLE; infer_instance
  flatOverBase i := (c.flatOverBase i).of_isPullback (isPullback_restrict H c.openSubset)
  represents := baseChangeRepresents c H P e
    ((SchemeDerivedCategory.Q X.left).objObjPreimageIso E.obj) c.upper.toNat
    (Int.self_le_toNat c.upper)
  finitePresentation i :=
    Scheme.Modules.isFinitePresentation_pullback _ _ (c.finitePresentation i)

/-- **Relative perfection is stable under derived base change of a flat family**, for any
pullback square. Let `f : X' ⟶ X` have underlying morphism the first projection of a pullback
square `X' = X ×_T T'` along a flat `q : X ⟶ T`, with second projection `q'`. For every `Dqc`
left-derived pullback `P` along `f`, the pullback of an object perfect relative to `q` is perfect
relative to `q'`.

This is the form, for relative perfection defined by condition (A) of Stacks Remark 36.35.14
(Tag 0DI9), of Stacks Lemma 36.35.6 (Tag 0DI5), quoted as BLMNPS Lemma 8.4. Those are stated for
Stacks Definition 36.35.1 (Tag 0DI0) and assume `q` locally of finite presentation, which is not
used here. The agreement of the two definitions is not proved here. The statement holds for every
inhabitant of `DqcLeftDerivedPullback f`.

Flatness of `q` cannot be dropped. Over a field `k`, let `T = Spec k[x]`,
`X = Spec k[x, y] ⧸ (xy)`, which is not flat over `T`, and `T' ⟶ T` the origin. The complex
`𝒪_X ⧸ (y)` in degree `0` is perfect relative to `q`: it is finitely presented and flat over `T`.
Over `A = k[x, y] ⧸ (xy)` it has the periodic resolution `⋯ → A --x--> A --y--> A`, so
`Tor^A_{2j}(A ⧸ (y), A ⧸ (x)) = k` for every `j ≥ 1`. Its derived pullback to the fibre over the
origin has nonzero cohomology in infinitely many degrees, so it has no bounded local model. -/
theorem schemeRelativePerfect_baseChange_of_isPullback (H : IsPullback f.left q' q h) [Flat q]
    (P : DqcLeftDerivedPullback f) {E : SchemeQuasicoherentDerivedCategory X.left}
    (hE : schemeRelativePerfect q E) : schemeRelativePerfect q' (P.functor.obj E) := fun x' ↦
  (hE (f.left x')).map (LocalRelativePerfectChart.baseChange H P.ambient (Iso.refl _))

/-- **Relative perfection is stable under derived base change of a flat family**: the
condition (A) form of Stacks Lemma 36.35.6 (Tag 0DI5) and BLMNPS Lemma 8.4, without local finite
presentation. Let `q : Y ⟶ T` be flat and `h : T' ⟶ T` any morphism. For every `Dqc`
left-derived pullback `P` along the projection `Y ×_T T' ⟶ Y`, the pullback of an object of
`Dqc(Y)` perfect relative to `q` is perfect relative to the projection `Y ×_T T' ⟶ T'`.

Flatness of `q` cannot be dropped; see `schemeRelativePerfect_baseChange_of_isPullback` for the
witness, and for the relation to Stacks Definition 36.35.1 (Tag 0DI0). -/
theorem schemeRelativePerfect_baseChange {Y T T' : Scheme.{u}} (q : Y ⟶ T) (h : T' ⟶ T) [Flat q]
    (P : DqcLeftDerivedPullback (pullbackFstOver q h)) {E : SchemeQuasicoherentDerivedCategory Y}
    (hE : schemeRelativePerfect q E) :
    schemeRelativePerfect (Limits.pullback.snd q h) (P.functor.obj E) :=
  schemeRelativePerfect_baseChange_of_isPullback (IsPullback.of_hasPullback q h) P hE

end

end AlgebraicGeometry
