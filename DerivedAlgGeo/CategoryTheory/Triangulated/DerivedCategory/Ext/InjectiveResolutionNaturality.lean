/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom

/-!
# Functoriality of the injective-resolution presentation of `Ext`

Mathlib identifies `Ext X Y n` with cohomology classes of degree `n` from `X` to a chosen
injective resolution of `Y`, through `InjectiveResolution.extEquivCohomologyClass`, but records
no compatibility of that identification with a morphism in the second variable.

That compatibility is what a comparison theorem needs when the target sheaf varies — and in
particular it is what makes a scalar action visible on `Ext`: multiplication by a scalar is an
endomorphism of the sheaf, and the resolution presentation must carry it to the corresponding
endomorphism of the resolution.

The identification is post-composition with the augmentation `R.ι'`, so the proof is the
associativity of composition in `SmallShiftedHom`, once cohomology classes are equipped with
their own post-composition.
-/

universe w v u

open CategoryTheory Category Localization

namespace CategoryTheory.Localization.SmallShiftedHom

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {M : Type*} [AddMonoid M]
  [HasShift C M] [W.IsCompatibleWithShift M] {X Y Z : C}

/-- Composing two degree-zero shifted morphisms is the degree-zero shifted composition. -/
lemma mk₀_comp_mk₀' [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (SmallShiftedHom.mk₀ W m₀ hm₀ f).comp (SmallShiftedHom.mk₀ W m₀ hm₀ g)
        (by rw [hm₀, zero_add]) =
      SmallShiftedHom.mk₀ W m₀ hm₀ (f ≫ g) :=
  (SmallShiftedHom.equiv W W.Q).injective (by
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk₀,
      SmallShiftedHom.equiv_mk₀, Functor.map_comp, ShiftedHom.mk₀_comp_mk₀])

/-- Composing a shifted morphism with a degree-zero one is the shifted composition. -/
lemma mk_comp_mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    {m : M} (f : ShiftedHom X Y m) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    (SmallShiftedHom.mk W f).comp (SmallShiftedHom.mk₀ W m₀ hm₀ g)
        (by rw [hm₀, zero_add]) =
      SmallShiftedHom.mk W (f ≫ g⟦m⟧') :=
  (SmallShiftedHom.equiv W W.Q).injective (by
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, SmallShiftedHom.equiv_mk,
      SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀]
    simp [ShiftedHom.map])

end CategoryTheory.Localization.SmallShiftedHom

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Post-composition with a morphism of complexes, as a morphism of Hom complexes.

Mathlib builds `HomComplex A L` but leaves it un-functorial in `L`; this is the map a
comparison argument needs when the target complex varies. -/
noncomputable def postcompMap (A : CochainComplex C ℤ) {L L' : CochainComplex C ℤ}
    (g : L ⟶ L') : HomComplex A L ⟶ HomComplex A L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.comp (Cochain.ofHom g) (add_zero n)
      map_zero' := by
        ext p q hpq
        simp
      map_add' := fun z z' ↦ by
        ext p q hpq
        simp [Cochain.add_comp] }
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z g m

/-- Post-composition of cocycles with a morphism of complexes, as an additive map.

Cocycles rather than cochains because this is what the left-homology data of the Hom complex
names as its cycles object, and the naturality square below has to be typed against that. -/
@[simps]
def Cocycle.postcompAddMonoidHom (A : CochainComplex C ℤ) {L L' : CochainComplex C ℤ}
    (g : L ⟶ L') (n : ℤ) : Cocycle A L n →+ Cocycle A L' n where
  toFun z := z.postcomp g
  map_zero' := by
    apply Cocycle.ext
    ext p q hpq
    simp
  map_add' z z' := by
    apply Cocycle.ext
    ext p q hpq
    simp [Cochain.add_comp]

/-- Post-composition acts on a cochain by composing with the morphism, which is what makes the
differential square commute. -/
@[simp]
lemma postcompMap_f_apply (A : CochainComplex C ℤ) {L L' : CochainComplex C ℤ}
    (g : L ⟶ L') (n : ℤ) (z : Cochain A L n) :
    ((postcompMap A g).f n).hom z = z.comp (Cochain.ofHom g) (add_zero n) :=
  rfl

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L L' : CochainComplex C ℤ} {n : ℤ}

/-- Post-composition of cocycles with a morphism of complexes, as an additive map to
cohomology classes. -/
@[simps]
def postcompCocycleAddMonoidHom (g : L ⟶ L') :
    Cocycle K L n →+ CohomologyClass K L' n where
  toFun z := mk (z.postcomp g)
  map_zero' := by
    refine (congrArg mk (Cocycle.ext ?_)).trans (mk_zero K L' n)
    ext p q hpq
    simp
  map_add' z z' := by
    refine (congrArg mk (Cocycle.ext ?_)).trans (mk_add _ _)
    ext p q hpq
    simp [Cochain.add_comp]

/-- Post-composition of cohomology classes with a morphism of complexes. -/
def postcomp (g : L ⟶ L') : CohomologyClass K L n →+ CohomologyClass K L' n :=
  descAddMonoidHom (postcompCocycleAddMonoidHom g) (by
    rintro z ⟨m, hm, β, hβ⟩
    simp only [AddMonoidHom.mem_ker, postcompCocycleAddMonoidHom_apply]
    rw [mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
    refine ⟨β.comp (Cochain.ofHom g) (add_zero m), ?_⟩
    rw [δ_comp_ofHom]
    exact congrArg (fun w : Cochain K L n => w.comp (Cochain.ofHom g) (add_zero n)) hβ)

/-- Post-composition is computed on a representing cocycle, which is how every statement about
it is proved: `mk` is surjective. -/
@[simp]
lemma postcomp_mk (g : L ⟶ L') (z : Cocycle K L n) :
    postcomp (n := n) g (mk z) = mk (z.postcomp g) :=
  rfl

section Abelian

variable
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L']
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L L']
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L' L']

/-- Post-composition of cohomology classes matches composition of shifted morphisms. -/
lemma toSmallShiftedHom_postcomp (x : CohomologyClass K L n) (g : L ⟶ L') :
    (postcomp (n := n) g x).toSmallShiftedHom =
      x.toSmallShiftedHom.comp
        (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl g) (zero_add n) := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [postcomp_mk, toSmallShiftedHom_mk, toSmallShiftedHom_mk,
    SmallShiftedHom.mk_comp_mk₀, Cocycle.equivHomShift_symm_postcomp]

end Abelian

section HomologyNaturality

open ShortComplex

/-- The short-complex morphism induced by post-composition, in a fixed degree. -/
noncomputable abbrev postcompSc (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    (HomComplex A L).sc n ⟶ (HomComplex A L').sc n :=
  (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v}
    (ComplexShape.up ℤ) n).map (postcompMap A g)

/-- Post-composition on cocycles, typed against the left-homology data of the Hom complex. -/
noncomputable def cocyclePostcomp (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    (leftHomologyData A L n).K ⟶ (leftHomologyData A L' n).K :=
  AddCommGrpCat.ofHom (Cocycle.postcompAddMonoidHom A g n)

/-- Post-composition on cohomology classes, typed against the left-homology data. -/
noncomputable def classPostcomp (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    (leftHomologyData A L n).H ⟶ (leftHomologyData A L' n).H :=
  AddCommGrpCat.ofHom (CohomologyClass.postcomp (n := n) g)

/-- The cocycle and cochain forms of post-composition agree under the inclusion of cycles.

This is the whole content of the cycles-level naturality: both sides become the same cochain
composition once the mono `i` is cancelled. -/
lemma postcompAddMonoidHom_comp_i (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    cocyclePostcomp A g n ≫ (leftHomologyData A L' n).i =
      (leftHomologyData A L n).i ≫ (postcompSc A g n).τ₂ :=
  rfl

/-- Post-composition descends to classes, which is what lets the epi `homologyπ` be cancelled in
the homology-level statement. -/
lemma cocyclePostcomp_comp_π (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    cocyclePostcomp A g n ≫ (leftHomologyData A L' n).π =
      (leftHomologyData A L n).π ≫ classPostcomp A g n :=
  rfl

/-- The cycles of the Hom complex are the cocycles, compatibly with post-composition.

Proved by cancelling the mono `i` and reducing to the cochain level. -/
lemma cyclesIso_hom_naturality (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    cyclesMap (postcompSc A g n) ≫ (leftHomologyData A L' n).cyclesIso.hom =
      (leftHomologyData A L n).cyclesIso.hom ≫ cocyclePostcomp A g n := by
  rw [← cancel_mono (leftHomologyData A L' n).i]
  simp only [Category.assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    cyclesMap_i, postcompAddMonoidHom_comp_i]
  rw [← Category.assoc, LeftHomologyData.cyclesIso_hom_comp_i]

/-- The homology of the Hom complex is the group of cohomology classes, compatibly with
post-composition.

Both sides are determined by their restriction along the epi `homologyπ`, on which the statement
becomes the cycles-level one. -/
lemma homologyIso_hom_naturality (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ) :
    homologyMap (postcompSc A g n) ≫ (leftHomologyData A L' n).homologyIso.hom =
      (leftHomologyData A L n).homologyIso.hom ≫ classPostcomp A g n := by
  rw [← cancel_epi (((HomComplex A L).sc n).homologyπ)]
  simp only [homologyπ_naturality_assoc, Category.assoc,
    LeftHomologyData.homologyπ_comp_homologyIso_hom,
    LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [← Category.assoc, cyclesIso_hom_naturality, Category.assoc,
    cocyclePostcomp_comp_π]

/-- Elementwise form: the identification of the homology of a Hom complex with cohomology
classes carries the map induced by post-composition to post-composition of classes. -/
lemma homologyAddEquiv_naturality (A : CochainComplex C ℤ) (g : L ⟶ L') (n : ℤ)
    (x : (HomComplex A L).homology n) :
    homologyAddEquiv A L' n
        (HomologicalComplex.homologyMap (postcompMap A g) n x) =
      CohomologyClass.postcomp (n := n) g (homologyAddEquiv A L n x) :=
  ConcreteCategory.congr_hom (homologyIso_hom_naturality A g n) x

end HomologyNaturality

end CochainComplex.HomComplex.CohomologyClass

namespace CategoryTheory.InjectiveResolution

open CochainComplex CochainComplex.HomComplex Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y Y' : C} {n : ℕ}

/-- The canonical lift of a morphism to chosen injective resolutions.

`InjectiveResolution.desc` produces the map of `ℕ`-indexed resolutions; this packages it with
its degree-zero commutation, so that `Hom.hom'` and `Hom.ι'_comp_hom'` supply the lifted chain
map and the square it satisfies. -/
noncomputable def descHom {Y Y' : C} (φ : Y ⟶ Y')
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') :
    R.Hom R' φ :=
  ⟨InjectiveResolution.desc φ R' R, by
    simpa using InjectiveResolution.desc_commutes_zero φ R' R⟩

omit [HasExt.{w} C] in
/-- The underlying map of resolutions is Mathlib's `desc`; this is stated so that later rewrites
never need to unfold `descHom`. -/
@[simp]
lemma descHom_hom {Y Y' : C} (φ : Y ⟶ Y')
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') :
    (descHom φ R R').hom = InjectiveResolution.desc φ R' R :=
  rfl

/-- The injective-resolution presentation of `Ext` is compatible with a morphism in the second
variable, once that morphism is lifted to the resolutions.

The lift is an explicit hypothesis rather than a chosen descent: the Proj lane passes its
comparison data positionally, and a chosen lift would reintroduce exactly the ambiguity that
convention exists to remove. `InjectiveResolution.Hom.hom'` supplies `hΦ` for the canonical
lift of `φ`. -/
lemma extEquivCohomologyClass_naturality
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') (φ : Y ⟶ Y')
    (Φ : R.cochainComplex ⟶ R'.cochainComplex)
    (hΦ : R.ι' ≫ Φ = (CochainComplex.singleFunctor C 0).map φ ≫ R'.ι')
    (α : Ext.{w} X Y n) :
    R'.extEquivCohomologyClass (α.comp (Ext.mk₀ φ) (add_zero n)) =
      CohomologyClass.postcomp Φ (R.extEquivCohomologyClass α) := by
  have key : ∀ {Z : C} (S : InjectiveResolution Z) (β : Ext.{w} X Z n),
      CohomologyClass.equivOfIsKInjective (S.extEquivCohomologyClass β) =
        SmallShiftedHom.comp β (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl S.ι')
          (zero_add (n : ℤ)) :=
    fun S β ↦ CohomologyClass.equivOfIsKInjective.apply_symm_apply _
  apply CohomologyClass.equivOfIsKInjective.injective
  rw [key]
  show _ = (CohomologyClass.postcomp Φ (R.extEquivCohomologyClass α)).toSmallShiftedHom
  rw [CohomologyClass.toSmallShiftedHom_postcomp]
  show _ = (CohomologyClass.equivOfIsKInjective
    (R.extEquivCohomologyClass α)).comp _ (zero_add (n : ℤ))
  rw [key]
  have hcomp : α.comp (Ext.mk₀ φ) (add_zero n) =
      SmallShiftedHom.comp α (SmallShiftedHom.mk₀ _ (0 : ℤ) rfl
        ((CochainComplex.singleFunctor C 0).map φ)) (zero_add (n : ℤ)) := rfl
  rw [hcomp,
    SmallShiftedHom.comp_assoc (α := α) (h₁₂ := zero_add (n : ℤ))
      (h₂₃ := zero_add (0 : ℤ)) (h := by simp),
    SmallShiftedHom.comp_assoc (α := α) (h₁₂ := zero_add (n : ℤ))
      (h₂₃ := zero_add (0 : ℤ)) (h := by simp),
    SmallShiftedHom.mk₀_comp_mk₀', SmallShiftedHom.mk₀_comp_mk₀', hΦ]

end CategoryTheory.InjectiveResolution
