/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExtendScalars
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.Algebra.Homology.Embedding.StupidTruncGE
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Pseudo-coherent complexes of modules

TODO
-/

open CategoryTheory Limits Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u

namespace ModuleCat

/-- Stacks 064Q (1). An object `K` of `D(R)` is `m`-pseudo-coherent if there are a bounded
complex `E` of finite free `R`-modules and a morphism `α : E ⟶ K` such that `Hⁱ(α)` is an
isomorphism for `i > m` and `Hᵐ(α)` is surjective. -/
def mPseudoCoherent (R : Type u) [CommRing R] (m : ℤ) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ ∃ (E : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
    E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
    (∀ i, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
    ∃ α : DerivedCategory.Q.obj E ⟶ K,
      (∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map α)

/-- Stacks 064Q (2), in the equivalent form 064U (2): `K` is pseudo-coherent if it is
`m`-pseudo-coherent for every `m`. -/
def pseudoCoherent (R : Type u) [CommRing R] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun K ↦ ∀ m, mPseudoCoherent R m K

variable {R : Type u} [CommRing R]

set_option quotPrecheck false in
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-! ### Elementary properties -/

/-- Every term of the complex is a finite free module. -/
private def FinFree (E : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)

private lemma finFree_of_isZero {M : ModuleCat.{u} R} (hM : IsZero M) :
    Module.Free R M ∧ Module.Finite R M := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  exact ⟨inferInstance, inferInstance⟩

private lemma finFree_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : Module.Free R M ∧ Module.Finite R M) : Module.Free R N ∧ Module.Finite R N := by
  obtain ⟨_, _⟩ := hM
  exact ⟨Module.Free.of_equiv e.toLinearEquiv, Module.Finite.equiv e.toLinearEquiv⟩

private lemma finite_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N) (hM : Module.Finite R M) :
    Module.Finite R N :=
  Module.Finite.equiv e.toLinearEquiv

private lemma projective_of_finFree {M : ModuleCat.{u} R} (hM : Module.Free R M) :
    Projective M :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis R M)

instance (m : ℤ) : (mPseudoCoherent R m).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩
    refine ⟨E, a, b, ha, hb, hE, α ≫ e.hom, fun i hi ↦ ?_, ?_⟩
    · rw [Functor.map_comp]
      have := hα i hi
      infer_instance
    · rw [Functor.map_comp]
      infer_instance

instance : (pseudoCoherent R).IsClosedUnderIsomorphisms where
  of_iso e hK m := (mPseudoCoherent R m).prop_of_iso e (hK m)

/-- An `m`-pseudo-coherent object is `m'`-pseudo-coherent for `m ≤ m'`. -/
theorem mPseudoCoherent.of_le {m m' : ℤ} (h : m ≤ m') {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : mPseudoCoherent R m K) : mPseudoCoherent R m' K := by
  obtain ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩ := hK
  refine ⟨E, a, b, ha, hb, hE, α, fun i hi ↦ hα i (by omega), ?_⟩
  rcases h.lt_or_eq with h | rfl
  · have := hα m' h
    infer_instance
  · exact hαm

/-- Stacks 064W (1). If `Hⁱ(K) = 0` for `i ≥ m`, then `K` is `m`-pseudo-coherent. -/
theorem mPseudoCoherent_of_isZero {m : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : ∀ i, m ≤ i → IsZero ((H i).obj K)) : mPseudoCoherent R m K := by
  have hX (i : ℤ) : IsZero ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
  have h0 (i : ℤ) : IsZero ((H i).obj (DerivedCategory.Q.obj 0)) :=
    (H i).map_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))
  refine ⟨0, 0, 0, ?_, ?_, fun i ↦ finFree_of_isZero (hX i), 0, fun i hi ↦ ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i _ ↦ hX i
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i _ ↦ hX i
  · exact isIso_of_source_target_iso_zero _ (h0 i).isoZero (hK i hi.le).isoZero
  · exact (hK m le_rfl).epi _

private lemma pseudoCoherent_Q_obj_aux (E : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [E.IsStrictlyGE a] [E.IsStrictlyLE b] (hE : FinFree E) :
    pseudoCoherent R (DerivedCategory.Q.obj E) :=
  fun _ ↦ ⟨E, a, b, inferInstance, inferInstance, hE, 𝟙 _, fun _ _ ↦ by
    rw [CategoryTheory.Functor.map_id]; infer_instance,
      by rw [CategoryTheory.Functor.map_id]; infer_instance⟩

/-- A bounded complex of finite free modules is pseudo-coherent. -/
theorem pseudoCoherent_Q_obj (E : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [E.IsStrictlyGE a] [E.IsStrictlyLE b]
    (hE : ∀ i, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) :
    pseudoCoherent R (DerivedCategory.Q.obj E) :=
  pseudoCoherent_Q_obj_aux E a b hE

/-! ### Transport along isomorphic arrows -/

private lemma arrow_iff {C : Type*} [Category* C] {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e₁ : A ≅ A') (e₂ : B ≅ B') (w : f ≫ e₂.hom = e₁.hom ≫ g) :
    (IsIso f ↔ IsIso g) ∧ (Epi f ↔ Epi g) ∧ (Mono f ↔ Mono g) := by
  let e : Arrow.mk f ≅ Arrow.mk g := Arrow.isoMk e₁ e₂ w.symm
  exact ⟨(MorphismProperty.isomorphisms C).arrow_mk_iso_iff e,
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff e,
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff e⟩

private lemma homologyFunctor_map_Q_map_iff {E F : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : E ⟶ F) (i : ℤ) :
    (IsIso ((H i).map (DerivedCategory.Q.map φ)) ↔
        IsIso (HomologicalComplex.homologyMap φ i)) ∧
      (Epi ((H i).map (DerivedCategory.Q.map φ)) ↔
        Epi (HomologicalComplex.homologyMap φ i)) ∧
      (Mono ((H i).map (DerivedCategory.Q.map φ)) ↔
        Mono (HomologicalComplex.homologyMap φ i)) :=
  arrow_iff ((DerivedCategory.homologyFunctorFactors _ i).app E)
    ((DerivedCategory.homologyFunctorFactors _ i).app F)
    (DerivedCategory.homologyFunctorFactors_hom_naturality φ i)

/-! ### Stupid truncation -/

section StupidTrunc

variable (E : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)

private lemma isIso_stupidTruncGEι_f (j : ℤ) (hj : m ≤ j) :
    IsIso ((HomologicalComplex.stupidTruncGEι E m).f j) := by
  dsimp [HomologicalComplex.stupidTruncGEι]
  rw [dite_eq_left hj]
  infer_instance

private lemma quasiIsoAt_stupidTruncGEι (i : ℤ) (hi : m < i) :
    QuasiIsoAt (HomologicalComplex.stupidTruncGEι E m) i := by
  rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  have h₁ := isIso_stupidTruncGEι_f E m (i - 1) (by omega)
  have h₂ := isIso_stupidTruncGEι_f E m i (by omega)
  have h₃ := isIso_stupidTruncGEι_f E m (i + 1) (by omega)
  have : IsIso ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (i - 1) i (i + 1)).map (HomologicalComplex.stupidTruncGEι E m)) :=
    @ShortComplex.isIso_of_isIso _ _ _ _ _ _ h₁ h₂ h₃
  infer_instance

private lemma epi_homologyMap_stupidTruncGEι :
    Epi (HomologicalComplex.homologyMap (HomologicalComplex.stupidTruncGEι E m) m) := by
  have h₂ := isIso_stupidTruncGEι_f E m m le_rfl
  have h₃ := isIso_stupidTruncGEι_f E m ((ComplexShape.up ℤ).next m) (by simp)
  have : IsIso (HomologicalComplex.cyclesMap (HomologicalComplex.stupidTruncGEι E m) m) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono' _ h₂ (@IsIso.mono_of_iso _ _ _ _ _ h₃)
  have := HomologicalComplex.homologyπ_naturality (HomologicalComplex.stupidTruncGEι E m) m
  have : Epi (HomologicalComplex.homologyπ _ m ≫
      HomologicalComplex.homologyMap (HomologicalComplex.stupidTruncGEι E m) m) := by
    rw [this]
    infer_instance
  exact epi_of_epi (HomologicalComplex.homologyπ _ m) _

end StupidTrunc

/-- An `m`-pseudo-coherent object has a witness concentrated in degrees `≥ m`: replace the complex
by its stupid truncation `σ_{≥ m}`, as in the proof of Stacks 064R. -/
private lemma exists_isStrictlyGE {m : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : mPseudoCoherent R m K) :
    ∃ (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ), E.IsStrictlyGE m ∧ E.IsStrictlyLE b ∧
      FinFree E ∧ ∃ α : DerivedCategory.Q.obj E ⟶ K,
        (∀ i, m < i → IsIso ((H i).map α)) ∧ Epi ((H m).map α) := by
  obtain ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩ := hK
  let ι := HomologicalComplex.stupidTruncGEι E m
  let E' : CochainComplex (ModuleCat.{u} R) ℤ := E.stupidTrunc (ComplexShape.embeddingUpIntGE m)
  have hE' : E'.IsStrictlyGE m :=
    show (E.stupidTrunc _).IsStrictlySupported (ComplexShape.embeddingUpIntGE m) from inferInstance
  refine ⟨E', b, hE', ?_, fun i ↦ ?_, DerivedCategory.Q.map ι ≫ α, fun i hi ↦ ?_, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_cases hmi : m ≤ i
    · have := isIso_stupidTruncGEι_f E m i hmi
      exact (E.isZero_of_isStrictlyLE b i hi).of_iso (asIso (ι.f i))
    · exact E'.isZero_of_isStrictlyGE m i (by omega)
  · by_cases hmi : m ≤ i
    · have := isIso_stupidTruncGEι_f E m i hmi
      exact finFree_of_iso (asIso (ι.f i)).symm (hE i)
    · exact finFree_of_isZero (E'.isZero_of_isStrictlyGE m i (by omega))
  · have := quasiIsoAt_stupidTruncGEι E m i hi
    have := (homologyFunctor_map_Q_map_iff ι i).1.2 inferInstance
    have := hα i hi
    rw [Functor.map_comp]
    infer_instance
  · have := (homologyFunctor_map_Q_map_iff ι m).2.1.2 (epi_homologyMap_stupidTruncGEι E m)
    rw [Functor.map_comp]
    infer_instance

/-! ### Morphisms out of K-projective complexes -/

private lemma Q_map_surjective {P L : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKProjective]
    (g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : P ⟶ L, DerivedCategory.Q.map φ = g := by
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  obtain ⟨g', hg'⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj L)).2 (e.hom.app P ≫ g ≫ e.inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := e.hom.naturality φ
  dsimp at h hg'
  rw [hg', Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  rw [← cancel_epi (e.hom.app P), ← h]

/-- A morphism from a K-projective complex concentrated in degrees `≥ m` to an object with
cohomology concentrated in degrees `< m` vanishes. -/
private lemma hom_eq_zero_of_isStrictlyGE {P : CochainComplex (ModuleCat.{u} R) ℤ}
    [P.IsKProjective] {m : ℤ} [P.IsStrictlyGE m] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : ∀ i, m ≤ i → IsZero ((H i).obj C)) (g : DerivedCategory.Q.obj P ⟶ C) : g = 0 := by
  have : C.IsLE (m - 1) := (DerivedCategory.isLE_iff C (m - 1)).2 fun i hi ↦ hC i (by omega)
  obtain ⟨C', hC', ⟨e⟩⟩ := C.exists_iso_Q_obj_of_isLE (m - 1)
  obtain ⟨ψ, hψ⟩ := Q_map_surjective (g ≫ e.hom)
  have : ψ = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    by_cases hi : i < m
    · exact (P.isZero_of_isStrictlyGE m i hi).eq_of_src _ _
    · exact (C'.isZero_of_isStrictlyLE (m - 1) i (by omega)).eq_of_tgt _ _
  rw [← cancel_mono e.hom, zero_comp, ← hψ, this, Functor.map_zero]

/-- The lifting step in the proof of Stacks 064R (Derived Categories, Lemma 13.19.? ):
a morphism from a K-projective complex in degrees `≥ m` factors through any `β : E ⟶ L` with
`Hⁱ(β)` an isomorphism for `i > m` and surjective for `i = m`, by an actual map of complexes. -/
private lemma exists_lift {P E : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKProjective] {m : ℤ}
    [P.IsStrictlyGE m] {L : DerivedCategory (ModuleCat.{u} R)}
    (β : DerivedCategory.Q.obj E ⟶ L) (hβ : ∀ i, m < i → IsIso ((H i).map β))
    (hβm : Epi ((H m).map β)) (γ : DerivedCategory.Q.obj P ⟶ L) :
    ∃ φ : P ⟶ E, DerivedCategory.Q.map φ ≫ β = γ := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle β
  have hC : ∀ i, m ≤ i → IsZero ((H i).obj C) := by
    intro i hi
    have hepi : Epi ((H i).map β) := by
      rcases hi.lt_or_eq with hi | rfl
      · have := hβ i hi
        infer_instance
      · exact hβm
    have hmono : Mono ((H (i + 1)).map β) := by
      have := hβ (i + 1) (by omega)
      infer_instance
    exact (DerivedCategory.HomologySequence.exact₃ _ hT i (i + 1)).isZero_of_both_zeros
      ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT i).1 hepi)
      ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT i (i + 1)).1 hmono)
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hT γ (hom_eq_zero_of_isStrictlyGE hC _)
  obtain ⟨φ, rfl⟩ := Q_map_surjective a
  exact ⟨φ, ha.symm⟩

/-! ### Mapping cones of finite free complexes -/

private lemma finFree_mappingCone {P E : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ E)
    (hP : FinFree P) (hE : FinFree E) : FinFree (CochainComplex.mappingCone φ) := by
  intro i
  obtain ⟨_, _⟩ := hP (i + 1)
  obtain ⟨_, _⟩ := hE i
  exact finFree_of_iso ((HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd _ _).symm ⟨inferInstance, inferInstance⟩

private lemma isStrictlyGE_mappingCone {P E : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ E)
    (a₁ a₂ : ℤ) [P.IsStrictlyGE a₁] [E.IsStrictlyGE a₂] :
    (CochainComplex.mappingCone φ).IsStrictlyGE (min (a₁ - 1) a₂) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨P.isZero_of_isStrictlyGE a₁ (i + 1) (by omega), E.isZero_of_isStrictlyGE a₂ i (by omega)⟩

private lemma isStrictlyLE_mappingCone {P E : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ E)
    (b₁ b₂ : ℤ) [P.IsStrictlyLE b₁] [E.IsStrictlyLE b₂] :
    (CochainComplex.mappingCone φ).IsStrictlyLE (max (b₁ - 1) b₂) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨P.isZero_of_isStrictlyLE b₁ (i + 1) (by omega), E.isZero_of_isStrictlyLE b₂ i (by omega)⟩

/-! ### Four lemma on the homology sequences of a morphism of triangles -/

section FourLemma

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {T T' : Triangle (DerivedCategory C)} (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _)
  (φ : T ⟶ T') (n : ℤ)

/-- The morphism of six-term homology sequences induced by a morphism of triangles. -/
private noncomputable def homologySequenceMap :
    (DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅ T n (n + 1) rfl ⟶
      (DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅ T' n (n + 1) rfl :=
  ComposableArrows.homMk₅
    ((DerivedCategory.homologyFunctor C n).map φ.hom₁)
    ((DerivedCategory.homologyFunctor C n).map φ.hom₂)
    ((DerivedCategory.homologyFunctor C n).map φ.hom₃)
    ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₁)
    ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₂)
    ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₃)
    (show (DerivedCategory.homologyFunctor C n).map T.mor₁ ≫ _ = _ ≫
        (DerivedCategory.homologyFunctor C n).map T'.mor₁ by
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (show (DerivedCategory.homologyFunctor C n).map T.mor₂ ≫ _ = _ ≫
        (DerivedCategory.homologyFunctor C n).map T'.mor₂ by
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    ((DerivedCategory.homologyFunctor C 0).homologySequenceδ_naturality φ n (n + 1) rfl).symm
    (show (DerivedCategory.homologyFunctor C (n + 1)).map T.mor₁ ≫ _ = _ ≫
        (DerivedCategory.homologyFunctor C (n + 1)).map T'.mor₁ by
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (show (DerivedCategory.homologyFunctor C (n + 1)).map T.mor₂ ≫ _ = _ ≫
        (DerivedCategory.homologyFunctor C (n + 1)).map T'.mor₂ by
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])

include hT hT'

private lemma epi_homologyFunctor_map_hom₃
    (h₁ : Epi ((DerivedCategory.homologyFunctor C n).map φ.hom₂))
    (h₂ : Epi ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₁))
    (h₃ : Mono ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₂)) :
    Epi ((DerivedCategory.homologyFunctor C n).map φ.hom₃) :=
  Abelian.epi_of_epi_of_epi_of_mono'' (k := 1) (by omega)
    ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅_exact T hT n
      (n + 1) rfl)
    ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅_exact T' hT' n
      (n + 1) rfl)
    (homologySequenceMap φ n) 1 2 3 4 rfl rfl rfl rfl h₁ h₂ h₃

private lemma mono_homologyFunctor_map_hom₃
    (h₀ : Epi ((DerivedCategory.homologyFunctor C n).map φ.hom₁))
    (h₁ : Mono ((DerivedCategory.homologyFunctor C n).map φ.hom₂))
    (h₃ : Mono ((DerivedCategory.homologyFunctor C (n + 1)).map φ.hom₁)) :
    Mono ((DerivedCategory.homologyFunctor C n).map φ.hom₃) :=
  Abelian.mono_of_epi_of_mono_of_mono'' (k := 0) (by omega)
    ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅_exact T hT n
      (n + 1) rfl)
    ((DerivedCategory.homologyFunctor C 0).homologySequenceComposableArrows₅_exact T' hT' n
      (n + 1) rfl)
    (homologySequenceMap φ n) 0 1 2 3 rfl rfl rfl rfl h₀ h₁ h₃

end FourLemma

/-! ### Shifts -/

private lemma homologyFunctor_map_shift_iff {X Y : DerivedCategory (ModuleCat.{u} R)}
    (f : X ⟶ Y) (n a a' : ℤ) (h : n + a = a') :
    (IsIso ((H a).map (f⟦n⟧')) ↔ IsIso ((H a').map f)) ∧
      (Epi ((H a).map (f⟦n⟧')) ↔ Epi ((H a').map f)) ∧
      (Mono ((H a).map (f⟦n⟧')) ↔ Mono ((H a').map f)) :=
  arrow_iff (((DerivedCategory.homologyFunctor _ 0).shiftIso n a a' h).app X)
    (((DerivedCategory.homologyFunctor _ 0).shiftIso n a a' h).app Y)
    ((DerivedCategory.homologyFunctor _ 0).shiftIso_hom_naturality n a a' h f)

/-- If `K` is `m`-pseudo-coherent, then `K[n]` is `(m - n)`-pseudo-coherent. -/
theorem mPseudoCoherent.shift {m : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : mPseudoCoherent R m K) (n : ℤ) : mPseudoCoherent R (m - n) (K⟦n⟧) := by
  obtain ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩ := hK
  refine ⟨E⟦n⟧, a - n, b - n, E.isStrictlyGE_shift a n (a - n) (by omega),
    E.isStrictlyLE_shift b n (b - n) (by omega), fun i ↦ hE (i + n),
    (DerivedCategory.Q.commShiftIso n).hom.app E ≫ α⟦n⟧', fun i hi ↦ ?_, ?_⟩
  · have := (homologyFunctor_map_shift_iff α n i (n + i) rfl).1.2 (hα (n + i) (by omega))
    rw [Functor.map_comp]
    infer_instance
  · have := (homologyFunctor_map_shift_iff α n (m - n) m (by omega)).2.1.2 hαm
    rw [Functor.map_comp]
    infer_instance

private lemma mPseudoCoherent_of_shift {m n : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : mPseudoCoherent R m (K⟦n⟧)) : mPseudoCoherent R (m + n) K := by
  have := hK.shift (-n)
  rw [sub_neg_eq_add] at this
  exact (mPseudoCoherent R _).prop_of_iso
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) n (-n) (by omega)).app K) this

/-! ### Distinguished triangles -/

private lemma epi_of_witness {m : ℤ} {X Y : DerivedCategory (ModuleCat.{u} R)} {α : X ⟶ Y}
    (hα : ∀ i, m < i → IsIso ((H i).map α)) (hαm : Epi ((H m).map α)) (i : ℤ) (hi : m ≤ i) :
    Epi ((H i).map α) := by
  rcases hi.lt_or_eq with hi | rfl
  · have := hα i hi
    infer_instance
  · exact hαm

private lemma mono_of_witness {m : ℤ} {X Y : DerivedCategory (ModuleCat.{u} R)} {α : X ⟶ Y}
    (hα : ∀ i, m < i → IsIso ((H i).map α)) (i : ℤ) (hi : m < i) : Mono ((H i).map α) := by
  have := hα i hi
  infer_instance

/-- Stacks 064R (1). In a distinguished triangle `K → L → M → K[1]`, if `K` is
`(m + 1)`-pseudo-coherent and `L` is `m`-pseudo-coherent, then `M` is `m`-pseudo-coherent. -/
theorem mPseudoCoherent_obj₃ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {m : ℤ} (h₁ : mPseudoCoherent R (m + 1) T.obj₁)
    (h₂ : mPseudoCoherent R m T.obj₂) : mPseudoCoherent R m T.obj₃ := by
  obtain ⟨P, b₁, hP₁, hP₂, hP, α, hα, hαm⟩ := exists_isStrictlyGE h₁
  obtain ⟨E, a₂, b₂, hE₁, hE₂, hE, β, hβ, hβm⟩ := h₂
  have : P.IsKProjective := by
    have (n : ℤ) : Projective (P.X n) := projective_of_finFree (hP n).1
    exact CochainComplex.isKProjective_of_projective P b₁
  have : P.IsStrictlyGE m := P.isStrictlyGE_of_ge m (m + 1) (by omega)
  obtain ⟨φ, hφ⟩ := exists_lift β hβ hβm (α ≫ T.mor₁)
  let T' := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)
  have hT' : T' ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished φ
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T' T hT' hT α β hφ
  let ψ : T' ⟶ T := Triangle.homMk _ _ α β c hφ hc₁ hc₂
  have hepi (i : ℤ) (hi : m ≤ i) : Epi ((H i).map c) :=
    epi_homologyFunctor_map_hom₃ hT' hT ψ i (epi_of_witness hβ hβm i hi)
      (epi_of_witness hα hαm (i + 1) (by omega)) (mono_of_witness hβ (i + 1) (by omega))
  refine ⟨CochainComplex.mappingCone φ, _, _, isStrictlyGE_mappingCone φ (m + 1) a₂,
    isStrictlyLE_mappingCone φ b₁ b₂, finFree_mappingCone φ hP hE, c, fun i hi ↦ ?_,
    hepi m le_rfl⟩
  exact @isIso_of_mono_of_epi _ _ _ _ _ _
    (mono_homologyFunctor_map_hom₃ hT' hT ψ i (epi_of_witness hα hαm i (by omega))
      (mono_of_witness hβ i hi) (mono_of_witness hα (i + 1) (by omega))) (hepi i hi.le)

/-- Stacks 064R (2). In a distinguished triangle `K → L → M → K[1]`, if `K` and `M` are
`m`-pseudo-coherent, then so is `L`. -/
theorem mPseudoCoherent_obj₂ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {m : ℤ} (h₁ : mPseudoCoherent R m T.obj₁)
    (h₃ : mPseudoCoherent R m T.obj₃) : mPseudoCoherent R m T.obj₂ := by
  have h := h₃.shift (-1)
  rw [sub_neg_eq_add] at h
  exact mPseudoCoherent_obj₃ (inv_rot_of_distTriang _ hT) h h₁

/-- Stacks 064R (3). In a distinguished triangle `K → L → M → K[1]`, if `L` is
`(m + 1)`-pseudo-coherent and `M` is `m`-pseudo-coherent, then `K` is
`(m + 1)`-pseudo-coherent. -/
theorem mPseudoCoherent_obj₁ {T : Triangle (DerivedCategory (ModuleCat.{u} R))}
    (hT : T ∈ distTriang _) {m : ℤ} (h₂ : mPseudoCoherent R (m + 1) T.obj₂)
    (h₃ : mPseudoCoherent R m T.obj₃) : mPseudoCoherent R (m + 1) T.obj₁ :=
  mPseudoCoherent_of_shift (n := 1) (mPseudoCoherent_obj₃ (rot_of_distTriang _ hT) h₂ h₃)

instance : (pseudoCoherent R).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun _ ↦
    mPseudoCoherent_of_isZero fun i _ ↦ (H i).map_isZero (isZero_zero _)⟩

instance : (pseudoCoherent R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK m ↦ by
    have := (hK (m + n)).shift n
    rwa [add_sub_cancel_right] at this⟩

/-- Stacks 064V. Pseudo-coherent objects form a triangulated subcategory of `D(R)`: two out of
three in a distinguished triangle. -/
instance : (pseudoCoherent R).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' fun _ hT h₁ h₃ m ↦ mPseudoCoherent_obj₂ hT (h₁ m) (h₃ m)

/-! ### Comparison of witnesses -/

/-- If `f : X ⟶ Y` induces isomorphisms on `Hⁱ` for `i > m` and a surjection on `Hᵐ`, and `X` is
`m`-pseudo-coherent, then so is `Y`. -/
theorem mPseudoCoherent.of_hom {m : ℤ} {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : ∀ i, m < i → IsIso ((H i).map f)) (hfm : Epi ((H m).map f))
    (hX : mPseudoCoherent R m X) : mPseudoCoherent R m Y := by
  obtain ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩ := hX
  refine ⟨E, a, b, ha, hb, hE, α ≫ f, fun i hi ↦ ?_, ?_⟩
  · have := hα i hi
    have := hf i hi
    rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance

/-! ### Complexes concentrated in degrees `≤ n` -/

section IsStrictlyLE

variable {E K : CochainComplex (ModuleCat.{u} R) ℤ} (n : ℤ) [K.IsStrictlyLE n]

/-- For a complex `K` concentrated in degrees `≤ n`, the projection `Kⁿ ⟶ Hⁿ(K)`. -/
private noncomputable def toHomologyOfIsStrictlyLE : K.X n ⟶ K.homology n :=
  (K.iCyclesIso n (n + 1) (by simp)
    ((K.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _)).inv ≫ K.homologyπ n

private lemma epi_toHomologyOfIsStrictlyLE : Epi (toHomologyOfIsStrictlyLE (K := K) n) := by
  dsimp [toHomologyOfIsStrictlyLE]
  infer_instance

private lemma homologyπ_homologyMap_eq (f : E ⟶ K) :
    E.homologyπ n ≫ HomologicalComplex.homologyMap f n =
      E.iCycles n ≫ f.f n ≫ toHomologyOfIsStrictlyLE n := by
  rw [HomologicalComplex.homologyπ_naturality, toHomologyOfIsStrictlyLE,
    ← HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc]

private lemma finite_homology_of_epi (f : E ⟶ K) (hE : Module.Finite R (E.X n))
    (hf : Epi (HomologicalComplex.homologyMap f n)) : Module.Finite R (K.homology n) := by
  have : Epi (E.iCycles n ≫ f.f n ≫ toHomologyOfIsStrictlyLE n) := by
    rw [← homologyπ_homologyMap_eq]
    infer_instance
  have hepi : Epi (f.f n ≫ toHomologyOfIsStrictlyLE n) := epi_of_epi (E.iCycles n) _
  exact Module.Finite.of_surjective (f.f n ≫ toHomologyOfIsStrictlyLE n).hom
    ((ModuleCat.epi_iff_surjective _).1 hepi)

end IsStrictlyLE

private lemma isKProjective_of_finFree (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [E.IsStrictlyLE b] (hE : FinFree E) : E.IsKProjective := by
  have (n : ℤ) : Projective (E.X n) := projective_of_finFree (hE n).1
  exact CochainComplex.isKProjective_of_projective E b

/-- Stacks 064S (1). If `K` is `m`-pseudo-coherent and `Hⁱ(K) = 0` for `i > m`, then `Hᵐ(K)` is a
finite `R`-module. -/
theorem finite_homology_of_mPseudoCoherent {m : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : mPseudoCoherent R m K) (hK' : ∀ i, m < i → IsZero ((H i).obj K)) :
    Module.Finite R ((H m).obj K) := by
  obtain ⟨E, a, b, ha, hb, hE, α, hα, hαm⟩ := hK
  have : K.IsLE m := (DerivedCategory.isLE_iff K m).2 hK'
  obtain ⟨K', hK'', ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE m
  have := isKProjective_of_finFree E b hE
  obtain ⟨f, hf⟩ := Q_map_surjective (α ≫ e.hom)
  have h₁ : Epi ((H m).map (DerivedCategory.Q.map f)) := by
    rw [hf, Functor.map_comp]
    infer_instance
  exact finite_of_iso
    ((H m).mapIso e ≪≫ (DerivedCategory.homologyFunctorFactors _ m).app K').symm
    (finite_homology_of_epi m f (hE m).2 ((homologyFunctor_map_Q_map_iff f m).2.1.1 h₁))

/-! ### Single complexes -/

private lemma finFree_single (F : ModuleCat.{u} R) [Module.Free R F] [Module.Finite R F]
    (n : ℤ) : FinFree ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj F) := by
  intro i
  by_cases hi : i = n
  · subst hi
    exact finFree_of_iso (HomologicalComplex.singleObjXSelf _ _ F).symm ⟨inferInstance, inferInstance⟩
  · exact finFree_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- A finite free module placed in a single degree is pseudo-coherent. -/
theorem pseudoCoherent_singleFunctor_obj (F : ModuleCat.{u} R) [Module.Free R F]
    [Module.Finite R F] (n : ℤ) :
    pseudoCoherent R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj F) :=
  (pseudoCoherent R).prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ _ n).app F).symm
    (pseudoCoherent_Q_obj_aux _ n n (finFree_single F n))

private lemma isZero_homology_singleFunctor_obj (M : ModuleCat.{u} R) (n i : ℤ) (hi : i ≠ n) :
    IsZero ((H i).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj M)) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE _ n i hi
  · exact DerivedCategory.isZero_of_isLE _ n i hi

/-- If `Hⁱ(K) = 0` for `i > n` and `Hⁿ(K)` is finite, there is a map from a finite free module
placed in degree `n` to `K` which is surjective on `Hⁿ`. -/
private lemma exists_singleFunctor_epi {n : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : ∀ i, n < i → IsZero ((H i).obj K)) (hfin : Module.Finite R ((H n).obj K)) :
    ∃ (k : ℕ) (α : (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin k → R)) ⟶ K), Epi ((H n).map α) := by
  have : K.IsLE n := (DerivedCategory.isLE_iff K n).2 hK
  obtain ⟨K', hK'', ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE n
  let e' : (H n).obj K ≅ K'.homology n :=
    (H n).mapIso e ≪≫ (DerivedCategory.homologyFunctorFactors _ n).app K'
  have : Module.Finite R (K'.homology n) := finite_of_iso e' hfin
  obtain ⟨k, π₀, hπ₀⟩ := Module.Finite.exists_fin' R (K'.homology n)
  let F := ModuleCat.of R (Fin k → R)
  have : Projective F := ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
  have := epi_toHomologyOfIsStrictlyLE (K := K') n
  let g : F ⟶ K'.X n := Projective.factorThru (ModuleCat.ofHom π₀) (toHomologyOfIsStrictlyLE n)
  have hg : g ≫ toHomologyOfIsStrictlyLE n = ModuleCat.ofHom π₀ := Projective.factorThru_comp _ _
  let χ := HomologicalComplex.mkHomFromSingle g (fun j hj ↦
    (K'.isZero_of_isStrictlyLE n j (by simp at hj; omega)).eq_of_tgt _ _)
  let S := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj F
  have hπ : IsIso (S.homologyπ n) := S.isIso_homologyπ (n - 1) n (by simp)
    ((HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_src _ _)
  have hi : IsIso (S.iCycles n) := S.isIso_iCycles n (n + 1) (by simp)
    ((HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_tgt _ _)
  have hχ : Epi (HomologicalComplex.homologyMap χ n) := by
    have hepi : Epi (S.homologyπ n ≫ HomologicalComplex.homologyMap χ n) := by
      rw [homologyπ_homologyMap_eq, HomologicalComplex.mkHomFromSingle_f, Category.assoc, hg]
      have : Epi (ModuleCat.ofHom π₀) := (ModuleCat.epi_iff_surjective _).2 hπ₀
      infer_instance
    exact epi_of_epi (S.homologyπ n) _
  refine ⟨k, ((DerivedCategory.singleFunctorIsoCompQ _ n).app F).hom ≫
    DerivedCategory.Q.map χ ≫ e.inv, ?_⟩
  have := (homologyFunctor_map_Q_map_iff χ n).2.1.2 hχ
  simp only [Functor.map_comp]
  infer_instance

/-- Stacks 064W (2). If `Hⁱ(K) = 0` for `i > m` and `Hᵐ(K)` is a finite `R`-module, then `K` is
`m`-pseudo-coherent. -/
theorem mPseudoCoherent_of_finite_homology {m : ℤ} {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : ∀ i, m < i → IsZero ((H i).obj K)) (hfin : Module.Finite R ((H m).obj K)) :
    mPseudoCoherent R m K := by
  obtain ⟨k, α, hα⟩ := exists_singleFunctor_epi hK hfin
  refine mPseudoCoherent.of_hom α (fun i hi ↦ ?_) hα (pseudoCoherent_singleFunctor_obj _ m m)
  exact isIso_of_source_target_iso_zero _
    (isZero_homology_singleFunctor_obj _ m i (by omega)).isoZero (hK i hi).isoZero

/-- Stacks 064T (1). A module `M` is `0`-pseudo-coherent, that is, `M[0]` is `0`-pseudo-coherent,
if and only if `M` is a finite `R`-module. -/
theorem mPseudoCoherent_zero_singleFunctor_iff (M : ModuleCat.{u} R) :
    mPseudoCoherent R 0 ((DerivedCategory.singleFunctor _ 0).obj M) ↔ Module.Finite R M := by
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app M
  have hz (i : ℤ) (hi : 0 < i) :
      IsZero ((H i).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) :=
    isZero_homology_singleFunctor_obj M 0 i (by omega)
  constructor
  · intro h
    exact finite_of_iso e (finite_homology_of_mPseudoCoherent h hz)
  · intro h
    exact mPseudoCoherent_of_finite_homology hz (finite_of_iso e.symm h)

end ModuleCat
