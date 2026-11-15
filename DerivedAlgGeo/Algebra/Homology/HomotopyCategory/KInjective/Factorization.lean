/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits

/-!
# Functorial injective replacements orthogonal to a family of complexes

Let `C` be a Grothendieck abelian category and `E : ι → CochainComplex C ℤ` a `w`-small
family of complexes. This file constructs a functor `CochainComplex.injectiveReplacement E`
and a natural monomorphism `M ⟶ injectiveReplacement E M` such that the target has
injective terms and every morphism from a member of `E` to it is null-homotopic. When the
members of `E` are acyclic, the comparison is a quasi-isomorphism. This is Stacks,
Lemmas 19.12.4 and 19.12.5 (Tags 079M, 079N), obtained in one step from the small
object argument.

## Main definitions

* `CochainComplex.injectiveReplacement E`: the functor.
* `CochainComplex.injectiveReplacementι E`: the natural comparison from the identity.

## Main results

* `CochainComplex.mono_injectiveReplacementι_app`: the comparison is a monomorphism.
* `CochainComplex.quasiIso_injectiveReplacementι_app`: it is a quasi-isomorphism when
  the members of `E` are acyclic.
* `CochainComplex.injective_injectiveReplacement_X`: the replacement has injective terms.
* `CochainComplex.nonempty_homotopy_zero_injectiveReplacement`: every morphism from a
  member of `E` to the replacement is null-homotopic.

## Implementation notes

The replacement factors `M ⟶ 0` by Mathlib's small object argument with respect to two
families of monomorphisms, following `IsGrothendieckAbelian.generatingMonomorphisms`:

* `E i ⟶ mappingCone (𝟙 (E i))`: a morphism from `E i` extends along it exactly when
  it is null-homotopic;
* for `n : ℤ` and a subobject `A` of the separator, the induced morphism of disks
  `double (𝟙 A) ⟶ double (𝟙 G)` in degrees `n` and `n + 1`. Disks corepresent
  evaluation in degree `n`, so lifting against these is lifting against the generating
  monomorphisms of `C`, which makes each term injective.

Every left lifting morphism is a retract of a transfinite composition of pushouts of
coproducts of these. So it is a monomorphism, and when `E` is acyclic it is a
quasi-isomorphism: monomorphic quasi-isomorphisms are stable under coproducts and
transfinite compositions because colimits are exact, and under pushouts because a pushout
keeps the cokernel.

## References

* [The Stacks project, Tag 079M](https://stacks.math.columbia.edu/tag/079M)
* [The Stacks project, Tag 079N](https://stacks.math.columbia.edu/tag/079N)

## Tags

injective resolution, small object argument, Grothendieck abelian category, quasi-isomorphism
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

open CategoryTheory Limits MorphismProperty ZeroObject

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace InjectiveReplacement

private lemma quasiIso_of_acyclic {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (hX : X.Acyclic)
    (hY : Y.Acyclic) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact ⟨⟨0, ((X.exactAt_iff_isZero_homology n).1 (hX n)).eq_of_src _ _,
    ((Y.exactAt_iff_isZero_homology n).1 (hY n)).eq_of_src _ _⟩⟩

/-- The mapping cone of an identity is acyclic: it is zero in the homotopy category. -/
private lemma acyclic_mappingCone_id (K : CochainComplex C ℤ) :
    (mappingCone (𝟙 K)).Acyclic := by
  have h := Pretriangulated.Triangle.isZero₃_of_isIso₁ _
    (HomotopyCategory.mappingCone_triangleh_distinguished (𝟙 K)) (by
      change IsIso ((HomotopyCategory.quotient C _).map (𝟙 K))
      rw [CategoryTheory.Functor.map_id]
      infer_instance)
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomotopyCategory.homologyFunctor C _ n).map_isZero h).of_iso
    ((HomotopyCategory.homologyFunctorFactors C _ n).app _).symm

/-- The disk on `X` in degrees `n` and `n + 1`: it corepresents `K ↦ (X ⟶ K.X n)`. -/
private noncomputable abbrev disk (n : ℤ) (X : C) : CochainComplex C ℤ :=
  HomologicalComplex.double (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

/-- The degree-`n` term of the disk on `X` is `X`. -/
private noncomputable abbrev diskIso (n : ℤ) (X : C) : (disk n X).X n ≅ X :=
  HomologicalComplex.doubleXIso₀ (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

private lemma isZero_disk_X (n : ℤ) (X : C) (k : ℤ) (h₀ : k ≠ n) (h₁ : k ≠ n + 1) :
    IsZero ((disk n X).X k) :=
  HomologicalComplex.isZero_double_X (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) k
    h₀ h₁

private noncomputable def diskHomEquiv (n : ℤ) (X : C) (K : CochainComplex C ℤ) :
    (disk n X ⟶ K) ≃ (X ⟶ K.X n) :=
  (HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId _ (by lia) X).homEquiv

private lemma diskHomEquiv_apply (n : ℤ) (X : C) {K : CochainComplex C ℤ} (g : disk n X ⟶ K) :
    diskHomEquiv n X K g = (diskIso n X).inv ≫ g.f n :=
  rfl

/-- The morphism of disks induced by a morphism of objects. -/
private noncomputable def diskMap (n : ℤ) {X Y : C} (f : X ⟶ Y) : disk n X ⟶ disk n Y :=
  (diskHomEquiv n X _).symm (f ≫ (diskIso n Y).inv)

private lemma diskMap_f (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (diskMap n f).f n = (diskIso n X).hom ≫ f ≫ (diskIso n Y).inv := by
  have := (diskHomEquiv n X (disk n Y)).apply_symm_apply (f ≫ (diskIso n Y).inv)
  rw [diskHomEquiv_apply] at this
  rw [← this]
  simp [diskMap]

private lemma diskHomEquiv_diskMap_comp (n : ℤ) {X Y : C} (f : X ⟶ Y) {K : CochainComplex C ℤ}
    (l : disk n Y ⟶ K) : diskHomEquiv n X K (diskMap n f ≫ l) = f ≫ diskHomEquiv n Y K l := by
  rw [diskHomEquiv_apply, diskHomEquiv_apply, HomologicalComplex.comp_f, diskMap_f]
  simp

private lemma acyclic_disk (n : ℤ) (X : C) : (disk n X).Acyclic := by
  intro k
  by_cases h₀ : k = n
  · subst k
    rw [(disk n X).exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.exact_iff_mono _
        ((isZero_disk_X n X (n - 1) (by lia) (by lia)).eq_of_src _ _)]
    dsimp
    rw [HomologicalComplex.double_d _ _ (by lia)]
    infer_instance
  by_cases h₁ : k = n + 1
  · subst k
    rw [(disk n X).exactAt_iff' n (n + 1) (n + 1 + 1) (by simp) (by simp),
      ShortComplex.exact_iff_epi _
        ((isZero_disk_X n X (n + 1 + 1) (by lia) (by lia)).eq_of_tgt _ _)]
    dsimp
    rw [HomologicalComplex.double_d _ _ (by lia)]
    infer_instance
  · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_disk_X n X k h₀ h₁)

private lemma isIso_disk_d (n : ℤ) (X : C) : IsIso ((disk n X).d n (n + 1)) := by
  rw [HomologicalComplex.double_d _ _ (by lia)]
  infer_instance

private lemma mono_diskMap (n : ℤ) {X Y : C} (f : X ⟶ Y) [Mono f] : Mono (diskMap n f) := by
  have h₀ : Mono ((diskMap n f).f n) := by
    rw [diskMap_f]
    infer_instance
  refine HomologicalComplex.mono_of_mono_f _ (fun k => ?_)
  by_cases hk₀ : k = n
  · subst k
    exact h₀
  by_cases hk₁ : k = n + 1
  · subst k
    have := isIso_disk_d n X
    have := isIso_disk_d n Y
    have e : (diskMap n f).f (n + 1) =
        inv ((disk n X).d n (n + 1)) ≫ (diskMap n f).f n ≫ (disk n Y).d n (n + 1) := by
      rw [(diskMap n f).comm, IsIso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  · exact ⟨fun g h _ => (isZero_disk_X n X k hk₀ hk₁).eq_of_tgt g h⟩

/-- A monomorphism followed by a pushout: the pushout of a monomorphic
quasi-isomorphism along any morphism is a quasi-isomorphism once it is a monomorphism. -/
private lemma quasiIso_of_isPushout {A A' B B' : CochainComplex C ℤ} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') [Mono f] [QuasiIso f] [Mono f'] :
    QuasiIso f' := by
  let S := ShortComplex.mk f (cokernel.π f) (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hQ : (cokernel f).Acyclic := hS.acyclic_X₃ (by dsimp [S]; infer_instance)
  let π' : B' ⟶ cokernel f := sq.desc 0 (cokernel.π f) (by simp)
  have hπ' : g' ≫ π' = cokernel.π f := sq.inr_desc _ _ _
  have : Epi π' := epi_of_epi_fac hπ'
  let S' := ShortComplex.mk f' π' (sq.inl_desc _ _ _)
  have hS' : S'.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _
        (CokernelCofork.IsColimit.ofπ _ _
          (fun {Z} k hk => cokernel.desc f (g' ≫ k) (by
            rw [← Category.assoc, ← sq.w, Category.assoc, hk, comp_zero]))
          (fun {Z} k hk => by
            apply sq.hom_ext
            · rw [← Category.assoc, show f' ≫ π' = 0 from sq.inl_desc _ _ _, zero_comp]
              exact hk.symm
            · rw [← Category.assoc, hπ', cokernel.π_desc])
          (fun {Z} k hk m hm => by
            rw [← cancel_epi (cokernel.π f), cokernel.π_desc, ← hπ', Category.assoc, hm])) }
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₃ (k : ℤ) : IsZero ((cokernel f).homology k) :=
    ((cokernel f).exactAt_iff_isZero_homology k).1 (hQ k)
  have : Mono (HomologicalComplex.homologyMap f' n) :=
    (hS'.homology_exact₁ (n - 1) n (by simp)).mono_g ((h₃ (n - 1)).eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap f' n) :=
    (hS'.homology_exact₂ n).epi_f ((h₃ n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Monomorphic quasi-isomorphisms. -/
private def monoQuasiIso : MorphismProperty (CochainComplex C ℤ) :=
  fun _ _ f => Mono f ∧ QuasiIso f

private instance : (monoQuasiIso (C := C)).IsStableUnderRetracts where
  of_retract h hg :=
    ⟨(monomorphisms _).of_retract h hg.1, (HomologicalComplex.quasiIso _ _).of_retract h hg.2⟩

private instance : (monoQuasiIso (C := C)).IsStableUnderCobaseChange where
  of_isPushout sq hf := by
    have := hf.1
    have := hf.2
    have : Mono _ := (monomorphisms _).of_isPushout sq hf.1
    exact ⟨this, quasiIso_of_isPushout sq⟩

section Grothendieck

variable [IsGrothendieckAbelian.{w} C]

private instance (J : Type w) : (monoQuasiIso (C := C)).IsStableUnderCoproductsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    refine ⟨MorphismProperty.IsStableUnderColimitsOfShape.condition (W := monomorphisms _)
      X₁ X₂ c₁ c₂ h₁ h₂ f (fun j => (hf j).1) φ hφ, ?_⟩
    have : ∀ j, QuasiIso (f.app j) := fun j => (hf j).2
    have hc : QuasiIso (colim.map f) := HomologicalComplex.quasiIso_colimMap f this
    have e : φ = (h₁.coconePointUniqueUpToIso (colimit.isColimit X₁)).hom ≫ colim.map f ≫
        ((h₂.coconePointUniqueUpToIso (colimit.isColimit X₂)).inv) := by
      refine h₁.hom_ext (fun j => ?_)
      simp [hφ]
    rw [e]
    infer_instance

private instance (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (monoQuasiIso (C := C)).IsStableUnderTransfiniteCompositionOfShape J where
  le := fun _ _ f hf => by
    obtain ⟨h⟩ := hf
    refine ⟨(monomorphisms _).transfiniteCompositionsOfShape_le J _
      (h.ofLE (fun _ _ _ hg => hg.1)).mem, ?_⟩
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : PreservesWellOrderContinuousOfShape J (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) n) :=
      ⟨fun j hj => by
        have := hj.nonempty_Iio.to_subtype
        infer_instance⟩
    have := (isomorphisms _).transfiniteCompositionsOfShape_le J _
      (transfiniteCompositionsOfShape_map_of_preserves J
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) f
        (h.ofLE (fun _ _ g hg => by
          have := hg.2
          exact (quasiIsoAt_iff_isIso_homologyMap g n).1 inferInstance)).mem)
    exact this

private instance : (monoQuasiIso (C := C)).IsStableUnderTransfiniteComposition.{w} where

private instance : (monoQuasiIso (C := C)).IsStableUnderCoproducts.{w} where

variable {ι : Type w} (E : ι → CochainComplex C ℤ)

/-- The domains of the generating morphisms. -/
@[reducible] private noncomputable def dom :
    ι ⊕ (ℤ × Subobject (separator C)) → CochainComplex C ℤ
  | .inl i => E i
  | .inr (n, A) => disk n (A : C)

/-- The codomains of the generating morphisms. -/
@[reducible] private noncomputable def cod :
    ι ⊕ (ℤ × Subobject (separator C)) → CochainComplex C ℤ
  | .inl i => mappingCone (𝟙 (E i))
  | .inr (n, _) => disk n (separator C)

/-- The generating morphisms: `E i ⟶ mappingCone (𝟙 (E i))`, along which morphisms
extend exactly when they are null-homotopic, and the morphisms of disks induced by
subobjects of the separator, along which morphisms extend when the terms are
injective. -/
@[reducible] private noncomputable def gen :
    (d : ι ⊕ (ℤ × Subobject (separator C))) → (dom E d ⟶ cod E d)
  | .inl i => mappingCone.inr (𝟙 (E i))
  | .inr (n, A) => diskMap n A.arrow

/-- The class of generating morphisms. -/
private noncomputable def generating : MorphismProperty (CochainComplex C ℤ) :=
  MorphismProperty.ofHoms (gen E)

private lemma mono_gen (d : ι ⊕ (ℤ × Subobject (separator C))) : Mono (gen E d) := by
  rcases d with i | ⟨n, A⟩
  · refine HomologicalComplex.mono_of_mono_f _ (fun p => ?_)
    have : IsSplitMono ((mappingCone.inr (𝟙 (E i))).f p) :=
      IsSplitMono.mk' ⟨_, mappingCone.inr_f_snd_v (𝟙 (E i)) p⟩
    change Mono ((mappingCone.inr (𝟙 (E i))).f p)
    infer_instance
  · exact mono_diskMap n A.arrow

private instance : IsSmall.{w} (generating E) := by
  dsimp [generating]
  infer_instance

private lemma generating_le_monomorphisms : generating E ≤ monomorphisms _ := by
  rintro _ _ _ ⟨d⟩
  exact mono_gen E d

private lemma generating_le_monoQuasiIso (hE : ∀ i, (E i).Acyclic) :
    generating E ≤ monoQuasiIso := by
  rintro _ _ _ ⟨d⟩
  refine ⟨mono_gen E d, ?_⟩
  rcases d with i | ⟨n, A⟩
  · exact quasiIso_of_acyclic _ (hE i) (acyclic_mappingCone_id _)
  · exact quasiIso_of_acyclic _ (acyclic_disk _ _) (acyclic_disk _ _)

private instance : HasSmallObjectArgument.{w} (generating E) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w}
    (Σ d : ι ⊕ (ℤ × Subobject (separator C)), Subobject (dom E d))
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms _).TransfiniteCompositionOfShape κ.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ ≤ monomorphisms _) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generating_le_monomorphisms E }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨d⟩ := hi
        exact hκ.of_injective (fun S : Subobject (dom E d) =>
          (⟨d, S⟩ : Σ d' : ι ⊕ (ℤ × Subobject (separator C)), Subobject (dom E d')))
          (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.1 h).2) }⟩

private lemma llp_rlp_le_monoQuasiIso (hE : ∀ i, (E i).Acyclic) :
    (generating E).rlp.llp ≤ monoQuasiIso := by
  rw [llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monoQuasiIso (C := C))).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    exact generating_le_monoQuasiIso E hE
  · simp

private lemma llp_rlp_le_monomorphisms : (generating E).rlp.llp ≤ monomorphisms _ := by
  rw [← IsGrothendieckAbelian.llp_rlp_monomorphisms
    (isSeparator_separator (CochainComplex C ℤ))]
  exact antitone_llp (antitone_rlp (generating_le_monomorphisms E))

/-- The functor sending `M` to the arrow `M ⟶ 0`. -/
private noncomputable def toArrowZero : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj M := Arrow.mk (0 : M ⟶ 0)
  map f := Arrow.homMk f (𝟙 _) (by simp)

/-- The functorial factorization given by the small object argument. -/
private noncomputable abbrev factorizationData :=
  functorialFactorizationData (generating E).rlp.llp (generating E).rlp

end Grothendieck

end InjectiveReplacement

open InjectiveReplacement

variable [IsGrothendieckAbelian.{w} C] {ι : Type w} (E : ι → CochainComplex C ℤ)

/-- **Stacks, Lemmas 19.12.4 and 19.12.5 (Tags 079M, 079N).** Given a `w`-small family
`E` of complexes, a functorial replacement `M ⟶ injectiveReplacement E M` of every
complex by one with injective terms to which every morphism from a member of `E` is
null-homotopic. The comparison is a monomorphism (`injectiveReplacementι`), and a
quasi-isomorphism when the members of `E` are acyclic. -/
noncomputable def injectiveReplacement : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  toArrowZero ⋙ (factorizationData E).Z

/-- The comparison `M ⟶ injectiveReplacement E M`. -/
noncomputable def injectiveReplacementι :
    𝟭 (CochainComplex C ℤ) ⟶ injectiveReplacement E where
  app M := (factorizationData E).i.app (toArrowZero.obj M)
  naturality _ _ f := (factorizationData E).i.naturality (toArrowZero.map f)

instance mono_injectiveReplacementι_app (M : CochainComplex C ℤ) :
    Mono ((injectiveReplacementι E).app M) :=
  llp_rlp_le_monomorphisms E _ ((factorizationData E).hi _)

lemma quasiIso_injectiveReplacementι_app (hE : ∀ i, (E i).Acyclic) (M : CochainComplex C ℤ) :
    QuasiIso ((injectiveReplacementι E).app M) :=
  (llp_rlp_le_monoQuasiIso E hE _ ((factorizationData E).hi _)).2

instance injective_injectiveReplacement_X (M : CochainComplex C ℤ) (n : ℤ) :
    Injective (((injectiveReplacement E).obj M).X n) := by
  have hp := (factorizationData E).hp (toArrowZero.obj M)
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp (isSeparator_separator C)]
  rintro _ _ _ ⟨A⟩
  constructor
  intro u v sq
  have hA := hp _ (MorphismProperty.ofHoms.mk (Sum.inr (n, A)))
  have sq' : CommSq ((diskHomEquiv n (A : C) _).symm u) (gen E (Sum.inr (n, A)))
      ((factorizationData E).p.app (toArrowZero.obj M)) 0 :=
    ⟨(isZero_zero _).eq_of_tgt _ _⟩
  obtain ⟨⟨L⟩⟩ := hA.sq_hasLift sq'
  obtain ⟨l, hl⟩ : ∃ l : disk n (separator C) ⟶ (injectiveReplacement E).obj M,
      diskMap n A.arrow ≫ l = (diskHomEquiv n (A : C) _).symm u :=
    ⟨L.l, L.fac_left⟩
  exact ⟨⟨{ l := diskHomEquiv n _ _ l
            fac_left := by rw [← diskHomEquiv_diskMap_comp, hl, Equiv.apply_symm_apply]
            fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩

lemma nonempty_homotopy_zero_injectiveReplacement (M : CochainComplex C ℤ) (i : ι)
    (f : E i ⟶ (injectiveReplacement E).obj M) : Nonempty (Homotopy f 0) := by
  have hp := (factorizationData E).hp (toArrowZero.obj M)
  have hi := hp _ (MorphismProperty.ofHoms.mk (Sum.inl i))
  have sq : CommSq f (gen E (Sum.inl i)) ((factorizationData E).p.app (toArrowZero.obj M)) 0 :=
    ⟨(isZero_zero _).eq_of_tgt _ _⟩
  obtain ⟨⟨L⟩⟩ := hi.sq_hasLift sq
  obtain ⟨l, hl⟩ : ∃ l : mappingCone (𝟙 (E i)) ⟶ (injectiveReplacement E).obj M,
      mappingCone.inr (𝟙 (E i)) ≫ l = f :=
    ⟨L.l, L.fac_left⟩
  refine ⟨(Cochain.equivHomotopy f 0).symm
    ⟨(mappingCone.inl (𝟙 (E i))).comp (Cochain.ofHom l) (add_zero _), ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero, δ_comp_ofHom, mappingCone.δ_inl, ← Cochain.ofHom_comp,
    Category.id_comp, hl]

end CochainComplex
