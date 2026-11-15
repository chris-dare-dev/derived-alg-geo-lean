/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits

/-!
# A criterion for K-injectivity in Grothendieck abelian categories

Let `C` be a Grothendieck abelian category and `E : ι → CochainComplex C ℤ` a family
of acyclic complexes that *detects* acyclic complexes: every nonzero acyclic
complex contains a nonzero subcomplex isomorphic to some `E i`. A complex `I` of
injective objects such that every morphism `E i ⟶ I` is null-homotopic is
K-injective (Stacks, Lemma 19.12.3, Tag 079L).

The family is a parameter. A family of bounded-above acyclic complexes of
bounded size with this detecting property is Stacks, Lemma 19.12.2 (Tag 079K),
and the literal form of 079L follows by specializing to it.

## Main definitions

None: this file proves properties of Mathlib's `CochainComplex.IsKInjective`.

## Main results

* `CochainComplex.exists_cochain_extension_of_homotopy_zero`: across a degreewise
  monomorphism `A ⟶ B` whose cokernel maps to `I` only null-homotopically, a
  null-homotopy of the restriction to `A` of a morphism `B ⟶ I` extends to one
  of the morphism.
* `CochainComplex.hasLiftingProperty_mappingCocone_fst_id`: the same statement as
  a left lifting property against `mappingCocone.fst (𝟙 I)`.
* `CochainComplex.isKInjective_of_injective_of_homotopy_zero`: the criterion of
  Tag 079L, with the orthogonality stated by null-homotopies.
* `CochainComplex.isKInjective_of_injective_of_rightOrthogonal`: the same, with
  the orthogonality stated in the homotopy category.

## Implementation notes

Neither hypothesis can be dropped. Over `ℤ/4`, the complex with every term `ℤ/4`
and every differential multiplication by `2` is acyclic and termwise injective,
as `ℤ/4` is self-injective, but its identity is not null-homotopic; the
orthogonality excludes it. Conversely, null-homotopies are extended degree by
degree, which needs injective terms.

Morphisms to the mapping cocone of `𝟙 I` are morphisms to `I` together with a
null-homotopy, so extending null-homotopies is a lifting property. An acyclic
complex `M` is the top of a transfinite chain of acyclic subcomplexes starting
at `⊥`, each step adding a copy of some `E i`; at limit stages the union is
acyclic because filtered colimits are exact. The left lifting property is stable
under transfinite composition, so `0 ⟶ M` lifts against
`mappingCocone.fst (𝟙 I)`, and every morphism `M ⟶ I` is null-homotopic. The
chain follows the construction of Mathlib's
`IsGrothendieckAbelian.generatingMonomorphisms.functor`, with acyclic subcomplexes
in place of subobjects of a generator; the helper declarations are private.

## References

* [The Stacks project, Tag 079L](https://stacks.math.columbia.edu/tag/079L)
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988)

## Tags

K-injective complex, Grothendieck abelian category, null-homotopy, mapping cocone,
transfinite composition, lifting property
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

open CategoryTheory Limits

namespace CochainComplex

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section Extension

variable {A B Q I : CochainComplex C ℤ} (j : A ⟶ B) [∀ n, Mono (j.f n)]
  {π : B ⟶ Q} {w : j ≫ π = 0} (hQ : IsColimit (CokernelCofork.ofπ π w))
  [∀ n, Injective (I.X n)]

include hQ in
/-- **Null-homotopies extend across a monomorphism with orthogonal cokernel.**

Let `j : A ⟶ B` be a degreewise monomorphism with cokernel `Q`, and let `I` have
injective terms. If every morphism `Q ⟶ I` is null-homotopic, then for every
morphism `b : B ⟶ I`, every null-homotopy `γ` of `j ≫ b` (in the sign convention
`δ γ + j ≫ b = 0` of `mappingCocone.lift`) is the restriction of a
null-homotopy of `b`.

The extension is built degreewise from the injectivity of the terms of `I`; the
error is a morphism `B ⟶ I` vanishing on `A`, hence a morphism `Q ⟶ I`, and a
null-homotopy of it corrects the extension. -/
lemma exists_cochain_extension_of_homotopy_zero
    (hQI : ∀ u : Q ⟶ I, Nonempty (Homotopy u 0))
    (b : B ⟶ I) (γ : Cochain A I (-1))
    (hγ : δ (-1) 0 γ + Cochain.ofHom (j ≫ b) = 0) :
    ∃ β : Cochain B I (-1), δ (-1) 0 β + Cochain.ofHom b = 0 ∧
      (Cochain.ofHom j).comp β (zero_add _) = γ := by
  let β₀ : Cochain B I (-1) :=
    Cochain.mk (fun p q hpq => Injective.factorThru (γ.v p q hpq) (j.f p))
  have hβ₀ : (Cochain.ofHom j).comp β₀ (zero_add _) = γ := by
    ext p q hpq
    simp [β₀, Cochain.zero_cochain_comp_v]
  let g : Cocycle B I 0 := ⟨-Cochain.ofHom b - δ (-1) 0 β₀, by
    rw [Cocycle.mem_iff 0 1 (by simp)]
    simp [δ_neg, δ_sub, δ_δ]⟩
  have hjg : j ≫ g.homOf = 0 := by
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe, Cochain.ofHom_zero]
    have h₁ : (Cochain.ofHom j).comp (δ (-1) 0 β₀) (zero_add 0) = δ (-1) 0 γ := by
      rw [← δ_ofHom_comp, hβ₀]
    have h₂ : (Cochain.ofHom j).comp (Cochain.ofHom b) (zero_add 0) =
        Cochain.ofHom (j ≫ b) := by
      rw [Cochain.ofHom_comp]
    simp only [g, Cochain.comp_sub, Cochain.comp_neg, h₁, h₂]
    rw [← neg_add', add_comm, hγ, neg_zero]
  let u : Q ⟶ I := hQ.desc (CokernelCofork.ofπ _ hjg)
  have hu : π ≫ u = g.homOf := hQ.fac (CokernelCofork.ofπ _ hjg) WalkingParallelPair.one
  obtain ⟨κ, hκ⟩ := Cochain.equivHomotopy _ _ (hQI u).some
  rw [Cochain.ofHom_zero, add_zero] at hκ
  refine ⟨β₀ + (Cochain.ofHom π).comp κ (zero_add _), ?_, ?_⟩
  · have h₃ : (Cochain.ofHom π).comp (δ (-1) 0 κ) (zero_add 0) = g.1 := by
      rw [← hκ, ← Cochain.ofHom_comp, hu, Cocycle.cochain_ofHom_homOf_eq_coe]
    rw [δ_add, δ_ofHom_comp, h₃]
    simp only [g]
    abel
  · rw [Cochain.comp_add, hβ₀, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      ← Cochain.ofHom_comp, w, Cochain.ofHom_zero, Cochain.zero_comp, add_zero]

end Extension

section MappingCocone

variable {K L X : CochainComplex C ℤ} (φ : K ⟶ L)

/-- Cochains to the mapping cocone are determined by their two components. -/
private lemma mappingCocone_cochain_ext {n m : ℤ} (hnm : n + -1 = m)
    {γ γ' : Cochain X (mappingCocone φ) n}
    (h₁ : γ.comp (Cochain.ofHom (mappingCocone.fst φ)) (add_zero n) =
      γ'.comp (Cochain.ofHom (mappingCocone.fst φ)) (add_zero n))
    (h₂ : γ.comp (mappingCocone.snd φ) hnm = γ'.comp (mappingCocone.snd φ) hnm) :
    γ = γ' := by
  ext p q hpq
  have e₁ := Cochain.congr_v h₁ p q hpq
  have e₂ := Cochain.congr_v h₂ p (q + -1) (by lia)
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at e₁
  rw [Cochain.comp_v _ _ hnm p q (q + -1) hpq (by lia),
    Cochain.comp_v _ _ hnm p q (q + -1) hpq (by lia)] at e₂
  rw [← Category.comp_id (γ.v p q hpq), ← Category.comp_id (γ'.v p q hpq),
    ← mappingCocone.id_X φ q (q + -1) rfl]
  simp only [Preadditive.comp_add, reassoc_of% e₁, reassoc_of% e₂]

/-- The coboundary of the second projection of the mapping cocone. -/
private lemma mappingCocone_δ_snd :
    δ (-1) 0 (mappingCocone.snd φ) = -Cochain.ofHom (mappingCocone.fst φ ≫ φ) := by
  have h : Cochain.ofHom (𝟙 (mappingCocone φ)) =
      mappingCocone.liftCochain φ (Cochain.ofHom (mappingCocone.fst φ))
        (mappingCocone.snd φ) (by simp) :=
    mappingCocone_cochain_ext φ (zero_add _) (by simp) (by simp)
  have h' := congrArg (δ 0 1) h
  rw [δ_ofHom, mappingCocone.δ_liftCochain _ _ _ _ 1 (by simp), δ_ofHom,
    Cochain.zero_comp, zero_sub, eq_comm, neg_eq_zero] at h'
  have hrs : (mappingCocone.inr φ).1.comp (mappingCocone.snd φ) (add_neg_cancel 1) =
      Cochain.ofHom (𝟙 L) := by
    ext p
    simp [Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p rfl (by lia)]
  have h'' := congrArg (fun z => z.comp (mappingCocone.snd φ) (add_neg_cancel 1)) h'
  simp only [Cochain.zero_comp] at h''
  rw [Cochain.comp_assoc _ _ _ (zero_add 1) (add_neg_cancel 1) (by simp), hrs,
    Cochain.comp_id] at h''
  rw [← Cochain.ofHom_comp] at h''
  exact eq_neg_of_add_eq_zero_left h''

private lemma δ_ofHom_comp_mappingCocone_snd (l : X ⟶ mappingCocone φ) :
    δ (-1) 0 ((Cochain.ofHom l).comp (mappingCocone.snd φ) (zero_add _)) =
      -Cochain.ofHom (l ≫ mappingCocone.fst φ ≫ φ) := by
  rw [δ_ofHom_comp, mappingCocone_δ_snd, Cochain.comp_neg, ← Cochain.ofHom_comp]

/-- Morphisms to the mapping cocone are determined by their two components. -/
private lemma mappingCocone_hom_ext {f f' : X ⟶ mappingCocone φ}
    (h₁ : f ≫ mappingCocone.fst φ = f' ≫ mappingCocone.fst φ)
    (h₂ : (Cochain.ofHom f).comp (mappingCocone.snd φ) (zero_add _) =
      (Cochain.ofHom f').comp (mappingCocone.snd φ) (zero_add _)) : f = f' :=
  Cochain.ofHom_injective (mappingCocone_cochain_ext φ (zero_add _)
    (by simpa only [← Cochain.ofHom_comp] using congrArg Cochain.ofHom h₁) h₂)

/-- A morphism that factors through the projection `mappingCocone (𝟙 I) ⟶ I` is
null-homotopic. -/
private lemma nonempty_homotopy_zero_of_fac {I : CochainComplex C ℤ} {g : X ⟶ I}
    (l : X ⟶ mappingCocone (𝟙 I)) (hl : l ≫ mappingCocone.fst (𝟙 I) = g) :
    Nonempty (Homotopy g 0) :=
  ⟨(Cochain.equivHomotopy g 0).symm
    ⟨-(Cochain.ofHom l).comp (mappingCocone.snd (𝟙 I)) (zero_add _), by
      rw [δ_neg, δ_ofHom_comp_mappingCocone_snd, Category.comp_id, hl, neg_neg,
        Cochain.ofHom_zero, add_zero]⟩⟩

end MappingCocone

/-- **The extension of null-homotopies as a lifting property.**

Morphisms to `mappingCocone (𝟙 I)` are morphisms to `I` with a null-homotopy, so
`exists_cochain_extension_of_homotopy_zero` says exactly that a monomorphism
whose cokernel maps to `I` only null-homotopically has the left lifting property
against `mappingCocone.fst (𝟙 I)`. -/
lemma hasLiftingProperty_mappingCocone_fst_id {A B Q I : CochainComplex C ℤ}
    (j : A ⟶ B) [Mono j] {π : B ⟶ Q} {w : j ≫ π = 0}
    (hQ : IsColimit (CokernelCofork.ofπ π w)) [∀ n, Injective (I.X n)]
    (hQI : ∀ u : Q ⟶ I, Nonempty (Homotopy u 0)) :
    HasLiftingProperty j (mappingCocone.fst (𝟙 I)) where
  sq_hasLift {t b} sq := by
    obtain ⟨β, hβ, hβj⟩ := exists_cochain_extension_of_homotopy_zero j hQ hQI b
      ((Cochain.ofHom t).comp (mappingCocone.snd (𝟙 I)) (zero_add _)) (by
        rw [δ_ofHom_comp_mappingCocone_snd, Category.comp_id, sq.w, neg_add_cancel])
    have hl : (Cochain.ofHom (mappingCocone.lift (𝟙 I) b β (by simpa using hβ))).comp
        (mappingCocone.snd (𝟙 I)) (zero_add _) = β := by
      ext p q hpq
      simp
    exact ⟨⟨{ l := mappingCocone.lift (𝟙 I) b β (by simpa using hβ)
              fac_left := mappingCocone_hom_ext _ (by simp [sq.w]) (by
                rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, hl, hβj])
              fac_right := by simp }⟩⟩

section Criterion

/-- In a Grothendieck abelian category, a filtered colimit of acyclic complexes is
acyclic. -/
private lemma acyclic_of_isColimit [IsGrothendieckAbelian.{w} C] {J : Type w} [SmallCategory J]
    [IsFiltered J] {F : J ⥤ CochainComplex C ℤ} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ k, (F.obj k).Acyclic) : c.pt.Acyclic := fun n => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  exact (isColimitOfPreserves (HomologicalComplex.homologyFunctor C _ n) hc).hom_ext
    (fun k => (((F.obj k).exactAt_iff_isZero_homology n).1 (hF k n)).eq_of_src _ _)

private lemma acyclic_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := fun n => (hK n).of_iso e

namespace KInjectiveCriterion

variable [IsGrothendieckAbelian.{w} C] {M : CochainComplex C ℤ}
  (φ : Subobject M → Subobject M) (hφ : ∀ A, A ≤ φ A)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The transfinite iteration of `φ` from `⊥`, as a functor to `MonoOver M`. -/
private noncomputable def functorToMonoOver : J ⥤ MonoOver M where
  obj j := MonoOver.mk (transfiniteIterate φ j ⊥).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ hφ (leOfHom f)))

/-- The transfinite iteration of `φ` from `⊥`, as a functor to complexes. -/
private noncomputable abbrev functor : J ⥤ CochainComplex C ℤ :=
  functorToMonoOver φ hφ J ⋙ MonoOver.forget _ ⋙ Over.forget _

private lemma functor_isWellOrderContinuous : (functor φ hφ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver φ hφ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver φ hφ J) c
    dsimp [c, functorToMonoOver]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit φ ⊥ m hm⟩

private lemma exists_ordinal (hφ' : ∀ A ≠ ⊤, A < φ A) (hφtop : φ ⊤ = ⊤) :
    ∃ (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate φ j (⊥ : Subobject M) = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject M)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have hJ : HasCardinalLT (Subobject M) (Cardinal.mk κ.ord.ToType) :=
    lt_of_lt_of_le (Order.lt_succ _) (by simp [κ])
  exact ⟨κ.ord, top_mem_range_transfiniteIterate φ ⊥ hφ' hφtop
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)⟩

end KInjectiveCriterion

variable {ι : Type*} {E : ι → CochainComplex C ℤ}
  {I : CochainComplex C ℤ} [∀ n, Injective (I.X n)]

/-- One step of the filtration: a proper acyclic subcomplex `A` of an acyclic
complex `M` is strictly contained in an acyclic subcomplex `A'` such that the
inclusion `A ⟶ A'` lifts against `mappingCocone.fst (𝟙 I)`. -/
private lemma exists_larger_subobject (hE : ∀ i, (E i).Acyclic)
    (hdetect : ∀ M : CochainComplex C ℤ, M.Acyclic → ¬ IsZero M →
      ∃ (i : ι) (f : E i ⟶ M), Mono f ∧ ¬ IsZero (E i))
    (hI : ∀ (i : ι) (f : E i ⟶ I), Nonempty (Homotopy f 0))
    {M : CochainComplex C ℤ} (hM : M.Acyclic) (A : Subobject M) (hA : A ≠ ⊤)
    (hAc : (A : CochainComplex C ℤ).Acyclic) :
    ∃ (A' : Subobject M) (h : A < A'), (A' : CochainComplex C ℤ).Acyclic ∧
      HasLiftingProperty (Subobject.ofLE A A' h.le) (mappingCocone.fst (𝟙 I)) := by
  let S := ShortComplex.mk A.arrow (cokernel.π A.arrow) (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel A.arrow }
  have hSf : QuasiIso S.f := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ⟨⟨0,
      (((A : CochainComplex C ℤ).exactAt_iff_isZero_homology n).1 (hAc n)).eq_of_src _ _,
      ((M.exactAt_iff_isZero_homology n).1 (hM n)).eq_of_src _ _⟩⟩
  have hQ : (cokernel A.arrow).Acyclic := hS.acyclic_X₃ hSf
  have hQ0 : ¬ IsZero (cokernel A.arrow) := by
    intro hz
    apply hA
    rw [← Subobject.isIso_arrow_iff_eq_top]
    have : Epi A.arrow := hS.exact.epi_f (hz.eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  obtain ⟨i, f, hf, hEi⟩ := hdetect _ hQ hQ0
  let P := pullback (cokernel.π A.arrow) f
  let ι' : (A : CochainComplex C ℤ) ⟶ P := pullback.lift A.arrow 0 (by simp)
  have hι' : Mono ι' := mono_of_mono_fac (pullback.lift_fst _ _ _)
  let T := ShortComplex.mk ι' (pullback.snd _ f) (by simp [ι'])
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (KernelFork.IsLimit.ofι _ _
          (fun {Z} g hg => hS.exact.lift (g ≫ pullback.fst (cokernel.π A.arrow) f) (by
            dsimp [S]
            rw [Category.assoc, pullback.condition, reassoc_of% hg, zero_comp]))
          (fun {Z} g hg => by
            apply pullback.hom_ext
            · simp only [T, ι', Category.assoc, pullback.lift_fst]
              exact hS.exact.lift_f _ _
            · simp only [T, ι', Category.assoc, pullback.lift_snd, comp_zero]
              exact hg.symm)
          (fun {Z} g hg m hm => by
            rw [← cancel_mono A.arrow, hS.exact.lift_f, ← hm]
            simp [T, ι'])) }
  have hAP : ¬ IsIso ι' := by
    intro h
    apply hEi
    have h₁ : pullback.snd (cokernel.π A.arrow) f = 0 := by
      rw [← cancel_epi ι']
      simp [ι']
    exact IsZero.of_epi_eq_zero _ h₁
  have hlt : A < Subobject.mk (pullback.fst (cokernel.π A.arrow) f) := by
    conv_lhs => rw [← Subobject.mk_arrow A]
    exact Subobject.mk_lt_mk_of_comm ι' (pullback.lift_fst _ _ _) hAP
  refine ⟨Subobject.mk (pullback.fst (cokernel.π A.arrow) f), hlt, ?_, ?_⟩
  · exact acyclic_of_iso (Subobject.underlyingIso _).symm (hT.acyclic_X₂ hAc (hE i))
  · have hfac : Subobject.ofLE _ _ hlt.le ≫
        (Subobject.underlyingIso (pullback.fst (cokernel.π A.arrow) f)).hom = ι' := by
      apply pullback.hom_ext
      · simp [ι']
      · rw [← cancel_mono f]
        simp [ι', ← pullback.condition]
    have := hasLiftingProperty_mappingCocone_fst_id ι' hT.gIsCokernel (hI i)
    exact HasLiftingProperty.of_arrow_iso_left
      (Arrow.isoMk (Iso.refl _) (Subobject.underlyingIso _).symm (by simp [← hfac]) :
        Arrow.mk ι' ≅ Arrow.mk (Subobject.ofLE _ _ hlt.le)) _

variable [IsGrothendieckAbelian.{w} C]

/-- **Stacks, Lemma 19.12.3 (Tag 079L).** Let `E` be a family of acyclic complexes
that detects acyclic complexes: every nonzero acyclic complex has a nonzero
subcomplex isomorphic to some `E i`. A complex `I` of injective objects such that
every morphism `E i ⟶ I` is null-homotopic is K-injective.

Termwise injectivity alone is not enough. Over `ℤ/4`, the complex with every term
`ℤ/4` and every differential multiplication by `2` is acyclic and termwise
injective, as `ℤ/4` is self-injective, but its identity is not null-homotopic,
so it is not K-injective.

The proof writes `0 ⟶ M`, for `M` acyclic, as a transfinite composition of
inclusions of acyclic subcomplexes whose successive quotients are copies of
members of `E`. Each step lifts against `mappingCocone.fst (𝟙 I)`
(`hasLiftingProperty_mappingCocone_fst_id`), hence so does the composition, and a
lift of `M ⟶ I` through that projection is a null-homotopy. -/
@[stacks 079L]
theorem isKInjective_of_injective_of_homotopy_zero (hE : ∀ i, (E i).Acyclic)
    (hdetect : ∀ M : CochainComplex C ℤ, M.Acyclic → ¬ IsZero M →
      ∃ (i : ι) (f : E i ⟶ M), Mono f ∧ ¬ IsZero (E i))
    (hI : ∀ (i : ι) (f : E i ⟶ I), Nonempty (Homotopy f 0)) :
    I.IsKInjective where
  nonempty_homotopy_zero {M} g hM := by
    classical
    have H (A : Subobject M) : ∃ A' : Subobject M,
        (A ≠ ⊤ ∧ (A : CochainComplex C ℤ).Acyclic → ∃ (h : A < A'),
          (A' : CochainComplex C ℤ).Acyclic ∧
            HasLiftingProperty (Subobject.ofLE A A' h.le) (mappingCocone.fst (𝟙 I))) ∧
        (¬ (A ≠ ⊤ ∧ (A : CochainComplex C ℤ).Acyclic) → A' = ⊤) := by
      by_cases h : A ≠ ⊤ ∧ (A : CochainComplex C ℤ).Acyclic
      · obtain ⟨A', hA'⟩ := exists_larger_subobject hE hdetect hI hM A h.1 h.2
        exact ⟨A', fun _ => hA', fun h' => absurd h h'⟩
      · exact ⟨⊤, fun h' => absurd h' h, fun _ => rfl⟩
    choose φ hφ_spec hφ_else using H
    have hφ_top : φ ⊤ = ⊤ := hφ_else ⊤ (fun h => h.1 rfl)
    have hφ_lt (A : Subobject M) (hA : A ≠ ⊤) : A < φ A := by
      by_cases hAc : (A : CochainComplex C ℤ).Acyclic
      · exact (hφ_spec A ⟨hA, hAc⟩).1
      · rw [hφ_else A (fun h => hAc h.2)]
        exact lt_top_iff_ne_top.2 hA
    have hφ_le (A : Subobject M) : A ≤ φ A := by
      by_cases hA : A = ⊤
      · subst hA
        rw [hφ_top]
      · exact (hφ_lt A hA).le
    have hstep (A B : Subobject M) (h : A ≤ B) (hB : B = φ A)
        (hAc : (A : CochainComplex C ℤ).Acyclic) :
        HasLiftingProperty (Subobject.ofLE A B h) (mappingCocone.fst (𝟙 I)) := by
      by_cases hA : A = ⊤
      · obtain rfl : B = A := by rw [hB, hA, hφ_top]
        rw [Subobject.ofLE_refl]
        infer_instance
      · subst hB
        exact (hφ_spec A ⟨hA, hAc⟩).2.2
    obtain ⟨o, j, hj⟩ := KInjectiveCriterion.exists_ordinal φ hφ_lt hφ_top
    have : Nonempty o.ToType := ⟨j⟩
    have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
    have := KInjectiveCriterion.functor_isWellOrderContinuous φ hφ_le o.ToType
    have hacyc (k : o.ToType) :
        ((transfiniteIterate φ k (⊥ : Subobject M) : Subobject M) :
          CochainComplex C ℤ).Acyclic := by
      induction k using SuccOrder.limitRecOn with
      | isMin k hk =>
        obtain rfl := hk.eq_bot
        rw [transfiniteIterate_bot]
        exact HomologicalComplex.acyclic_of_isZero _
          ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
      | succ k hk ih =>
        rw [transfiniteIterate_succ _ _ _ hk]
        by_cases htop : transfiniteIterate φ k (⊥ : Subobject M) = ⊤
        · rw [htop, hφ_top]
          have := (Subobject.isIso_arrow_iff_eq_top (⊤ : Subobject M)).2 rfl
          exact acyclic_of_iso (asIso (⊤ : Subobject M).arrow).symm hM
        · exact (hφ_spec _ ⟨htop, ih⟩).2.1
      | isSuccLimit k hk ih =>
        have := hk.nonempty_Iio.to_subtype
        exact acyclic_of_isColimit
          ((KInjectiveCriterion.functor φ hφ_le o.ToType).isColimitOfIsWellOrderContinuous k hk)
          (fun x => ih x.1 x.2)
    let F := (Set.initialSegIic j).monotone.functor ⋙
      KInjectiveCriterion.functor φ hφ_le o.ToType
    have hF (k : Set.Iic j) (hk : ¬ IsMax k) :
        HasLiftingProperty (F.map (homOfLE (Order.le_succ k))) (mappingCocone.fst (𝟙 I)) :=
      hstep _ _ _ (by
        change transfiniteIterate φ (Order.succ k).1 ⊥ = φ (transfiniteIterate φ k.1 ⊥)
        rw [Set.Iic.succ_eq_of_not_isMax hk,
          transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]) (hacyc k.1)
    have hlift := HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (colimitOfDiagramTerminal isTerminalTop F) hF
    have hzero : IsZero (F.obj ⊥) := by
      change IsZero ((transfiniteIterate φ (⊥ : o.ToType) (⊥ : Subobject M) : Subobject M) :
        CochainComplex C ℤ)
      rw [transfiniteIterate_bot]
      exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
    have := (Subobject.isIso_arrow_iff_eq_top _).2 hj
    let sq : CommSq (0 : F.obj ⊥ ⟶ mappingCocone (𝟙 I))
        ((coconeOfDiagramTerminal isTerminalTop F).ι.app ⊥) (mappingCocone.fst (𝟙 I))
        ((transfiniteIterate φ j (⊥ : Subobject M)).arrow ≫ g) := ⟨hzero.eq_of_src _ _⟩
    let l : ((transfiniteIterate φ j (⊥ : Subobject M) : Subobject M) : CochainComplex C ℤ) ⟶
        mappingCocone (𝟙 I) := sq.lift
    have hl : l ≫ mappingCocone.fst (𝟙 I) =
        (transfiniteIterate φ j (⊥ : Subobject M)).arrow ≫ g := sq.fac_right
    exact nonempty_homotopy_zero_of_fac
      (inv (transfiniteIterate φ j (⊥ : Subobject M)).arrow ≫ l)
      (by rw [Category.assoc, hl, IsIso.inv_hom_id_assoc])

/-- **Stacks, Lemma 19.12.3 (Tag 079L)**, with the orthogonality stated in the
homotopy category: a complex of injectives right orthogonal in `K(C)` to a family
of acyclic complexes that detects acyclic complexes is K-injective. -/
theorem isKInjective_of_injective_of_rightOrthogonal (hE : ∀ i, (E i).Acyclic)
    (hdetect : ∀ M : CochainComplex C ℤ, M.Acyclic → ¬ IsZero M →
      ∃ (i : ι) (f : E i ⟶ M), Mono f ∧ ¬ IsZero (E i))
    (hI : ∀ (i : ι) (f : (HomotopyCategory.quotient C (.up ℤ)).obj (E i) ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj I), f = 0) :
    I.IsKInjective :=
  isKInjective_of_injective_of_homotopy_zero hE hdetect (fun i f =>
    ⟨HomotopyCategory.homotopyOfEq _ _ (by
      rw [hI i ((HomotopyCategory.quotient _ _).map f), Functor.map_zero])⟩)

end Criterion

end CochainComplex
