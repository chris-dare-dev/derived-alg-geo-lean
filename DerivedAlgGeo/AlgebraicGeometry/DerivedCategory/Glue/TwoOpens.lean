/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.MayerVietorisHom
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Descent

/-!
# Gluing derived objects over two opens

Let `Y = U ∪ V` with `U` and `V` open. Objects `A` on `U` and `B` on `V` with an isomorphism
`c : A|_{U∩V} ≅ B|_{U∩V}` glue to an object `F` of the derived category of `Y`, with
isomorphisms `F|_U ≅ A` and `F|_V ≅ B` that differ by `c` on `U ∩ V` (Stacks Tag 08DG (1)). The
object `F` is the cone of `j_{U∩V!}(A|_{U∩V}) ⟶ j_{U!} A ⊞ j_{V!} B`, whose components are the
comparison map and `c` followed by the comparison map. Morphisms `A ⟶ E|_U` and `B ⟶ E|_V` that
agree on `U ∩ V` extend to a morphism `F ⟶ E` (Stacks Tag 08DG (2)), and if `A` and `B` have
quasi-coherent cohomology so does `F`.

## Main results

* `AlgebraicGeometry.Scheme.exists_glue_two`: existence of the glued object, with no `Ext`
  vanishing hypothesis and no covering hypothesis.
* `AlgebraicGeometry.Scheme.exists_hom_of_glue_two`: extension of morphisms to the glued object.
* `AlgebraicGeometry.Scheme.schemeQuasicoherentCohomology_of_glue_two`: the glued object has
  quasi-coherent cohomology if `A` and `B` do.

## Implementation notes

Uniqueness of the glued object is not claimed, and fails in general: a negative `Ext` group of
the restrictions can be nonzero, for instance for `𝒪 ⊕ 𝒪(-1)⟦1⟧` on the projective line and its
restriction to the affine line, whose `Ext⁻¹` with itself contains `Γ(𝔸¹, 𝒪)`.

The restriction of the cone to `U` is the cone of a map into `j_{U!} A ⊞ j_{V!} B` whose component
into `j_{V!} B` becomes invertible after restriction, by the base change of derived extension by
zero, so it is identified with `A` by `isIso_map_inl_comp_of_isIso_map_snd`. The extension of
morphisms is the exactness of the Mayer–Vietoris sequence of morphisms at a pair of morphisms that
agree on the intersection, and needs the covering hypothesis because the triangle does.

## References

* Stacks Project, Tag 08DG.

## Tags

derived category, gluing, open cover, extension by zero
-/

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits Pretriangulated
open AlgebraicGeometry.DerivedCategory

noncomputable section

variable {Y : Scheme.{u}} {U V : Y.Opens} {W : Scheme.{u}} {kU : W ⟶ U} {kV : W ⟶ V} {w : W ⟶ Y}
  [IsOpenImmersion kU] [IsOpenImmersion kV] [IsOpenImmersion w]

section Square

variable (cU : derivedRestrict U.ι ⋙ derivedRestrict kU ≅ derivedRestrict w)
  (cV : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
  (A : SchemeDerivedCategory U) (B : SchemeDerivedCategory V)
  (c : (derivedRestrict kU).obj A ≅ (derivedRestrict kV).obj B)

/-- The first map of the gluing triangle, `j_{U∩V!} A|_{U∩V} ⟶ j_{U!} A ⊞ j_{V!} B`, with
components the comparison map for `A` and minus `c` followed by the comparison map for `B`. -/
def glueFirst :
    (derivedExtendByZero w).obj ((derivedRestrict kU).obj A) ⟶
      (derivedExtendByZero U.ι).obj A ⊞ (derivedExtendByZero V.ι).obj B :=
  biprod.lift (extendRestrictMap cU A)
    (-((derivedExtendByZero w).map c.hom ≫ extendRestrictMap cV B))

variable (hP : IsPullback kU kV U.ι V.ι)

include hP

/-- **Two-open gluing, for a pullback square through the intersection**: the glued object
exists, with isomorphisms to `A` and `B` that differ by `c` on the intersection. -/
theorem exists_glue_of_isPullback :
    ∃ (F : SchemeDerivedCategory Y) (a : (derivedRestrict U.ι).obj F ≅ A)
      (b : (derivedRestrict V.ι).obj F ≅ B),
      cU.inv.app F ≫ (derivedRestrict kU).map a.hom ≫ c.hom =
        cV.inv.app F ≫ (derivedRestrict kV).map b.hom := by
  obtain ⟨F, g, δ, hT⟩ := distinguished_cocone_triangle (glueFirst cU cV A B c)
  have hs : glueFirst cU cV A B c ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hAinv : IsIso ((derivedRestrict U.ι).map (biprod.inl ≫ g)) := by
    refine isIso_map_inl_comp_of_isIso_map_snd (derivedRestrict U.ι) _ g δ hT ?_
    rw [glueFirst, biprod.lift_snd, Functor.map_neg, Functor.map_comp]
    have := isIso_restrict_extendRestrictMap hP cV B
    exact isIso_neg _
  have hBinv : IsIso ((derivedRestrict V.ι).map (biprod.inr ≫ g)) := by
    refine isIso_map_inr_comp_of_isIso_map_fst (derivedRestrict V.ι) _ g δ hT ?_
    rw [glueFirst, biprod.lift_fst]
    exact isIso_restrict_extendRestrictMap hP.flip cU A
  have hK3 : extendRestrictMap cU A ≫ (biprod.inl ≫ g) =
      ((derivedExtendByZero w).map c.hom ≫ extendRestrictMap cV B) ≫ (biprod.inr ≫ g) := by
    have h : glueFirst cU cV A B c ≫ g = 0 := hs
    rw [glueFirst, biprod.lift_eq, Preadditive.add_comp, Preadditive.neg_comp] at h
    simp only [Category.assoc] at h ⊢
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
  have hK1 : (derivedRestrict kU).map ((derivedExtendByZeroAdjunction U.ι).unit.app A ≫
        (derivedRestrict U.ι).map (biprod.inl ≫ g)) ≫ cU.hom.app F =
      (derivedExtendByZeroAdjunction w).homEquiv _ _
        (extendRestrictMap cU A ≫ (biprod.inl ≫ g)) := by
    have hn := cU.hom.naturality (biprod.inl ≫ g)
    rw [Functor.comp_map] at hn
    rw [Adjunction.homEquiv_naturality_right, homEquiv_extendRestrictMap, Functor.map_comp,
      Category.assoc, hn, Category.assoc]
  have hK2 : c.hom ≫ (derivedRestrict kV).map ((derivedExtendByZeroAdjunction V.ι).unit.app B ≫
        (derivedRestrict V.ι).map (biprod.inr ≫ g)) ≫ cV.hom.app F =
      (derivedExtendByZeroAdjunction w).homEquiv _ _
        (((derivedExtendByZero w).map c.hom ≫ extendRestrictMap cV B) ≫ (biprod.inr ≫ g)) := by
    have hn := cV.hom.naturality (biprod.inr ≫ g)
    rw [Functor.comp_map] at hn
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      homEquiv_extendRestrictMap, Functor.map_comp, Category.assoc, hn]
    simp
  have key : (derivedRestrict kU).map ((derivedExtendByZeroAdjunction U.ι).unit.app A ≫
        (derivedRestrict U.ι).map (biprod.inl ≫ g)) ≫ cU.hom.app F =
      c.hom ≫ (derivedRestrict kV).map ((derivedExtendByZeroAdjunction V.ι).unit.app B ≫
        (derivedRestrict V.ι).map (biprod.inr ≫ g)) ≫ cV.hom.app F := by
    rw [hK1, hK2, hK3]
  have hAiso : IsIso ((derivedExtendByZeroAdjunction U.ι).unit.app A ≫
      (derivedRestrict U.ι).map (biprod.inl ≫ g)) := inferInstance
  have hBiso : IsIso ((derivedExtendByZeroAdjunction V.ι).unit.app B ≫
      (derivedRestrict V.ι).map (biprod.inr ≫ g)) := inferInstance
  refine ⟨F, (asIso ((derivedExtendByZeroAdjunction U.ι).unit.app A ≫
      (derivedRestrict U.ι).map (biprod.inl ≫ g))).symm,
    (asIso ((derivedExtendByZeroAdjunction V.ι).unit.app B ≫
      (derivedRestrict V.ι).map (biprod.inr ≫ g))).symm, ?_⟩
  generalize (derivedExtendByZeroAdjunction U.ι).unit.app A ≫
    (derivedRestrict U.ι).map (biprod.inl ≫ g) = ia at key hAiso ⊢
  generalize (derivedExtendByZeroAdjunction V.ι).unit.app B ≫
    (derivedRestrict V.ι).map (biprod.inr ≫ g) = ib at key hBiso ⊢
  have hN : IsIso (c.inv ≫ (derivedRestrict kU).map ia ≫ cU.hom.app F) := inferInstance
  refine (cancel_mono (c.inv ≫ (derivedRestrict kU).map ia ≫ cU.hom.app F)).1 ?_
  have e1 : cU.inv.app F ≫ (derivedRestrict kU).map (asIso ia).symm.hom ≫ c.hom ≫
      (c.inv ≫ (derivedRestrict kU).map ia ≫ cU.hom.app F) = 𝟙 _ := by
    simp
  have e2 : c.inv ≫ (derivedRestrict kU).map ia ≫ cU.hom.app F =
      (derivedRestrict kV).map ib ≫ cV.hom.app F := by
    rw [key, Iso.inv_hom_id_assoc]
  have e3 : cV.inv.app F ≫ (derivedRestrict kV).map (asIso ib).symm.hom ≫
      (c.inv ≫ (derivedRestrict kU).map ia ≫ cU.hom.app F) = 𝟙 _ := by
    rw [e2]
    simp
  simp only [Category.assoc]
  exact e1.trans e3.symm

variable (hUV : U ⊔ V = ⊤)

include hUV

/-- **Two-open gluing, extension of morphisms, for a pullback square through the intersection**:
a pair of morphisms `A ⟶ E|_U` and `B ⟶ E|_V` that agree on the intersection extends to a
morphism from any glued object to `E`. -/
theorem exists_hom_of_glue_of_isPullback
    {F : SchemeDerivedCategory Y} (a : (derivedRestrict U.ι).obj F ≅ A)
    (b : (derivedRestrict V.ι).obj F ≅ B)
    (hab : cU.inv.app F ≫ (derivedRestrict kU).map a.hom ≫ c.hom =
      cV.inv.app F ≫ (derivedRestrict kV).map b.hom)
    (E : SchemeDerivedCategory Y) (α : A ⟶ (derivedRestrict U.ι).obj E)
    (β : B ⟶ (derivedRestrict V.ι).obj E)
    (h : (derivedRestrict kU).map α ≫ cU.hom.app E =
      c.hom ≫ (derivedRestrict kV).map β ≫ cV.hom.app E) :
    ∃ φ : F ⟶ E, (derivedRestrict U.ι).map φ = a.hom ≫ α ∧
      (derivedRestrict V.ι).map φ = b.hom ≫ β := by
  have hz : mvDiff cU cV F E (a.hom ≫ α, b.hom ≫ β) = 0 := by
    change (cU.inv.app F ≫ (derivedRestrict kU).map (a.hom ≫ α) ≫ cU.hom.app E) -
      (cV.inv.app F ≫ (derivedRestrict kV).map (b.hom ≫ β) ≫ cV.hom.app E) = 0
    rw [sub_eq_zero]
    simp only [Functor.map_comp, Category.assoc]
    rw [h]
    have := congrArg (· ≫ ((derivedRestrict kV).map β ≫ cV.hom.app E)) hab
    simpa only [Category.assoc] using this
  obtain ⟨φ, hφ⟩ := (mvRes_exact_mvDiff cU cV hP hUV F E _).1 hz
  exact ⟨φ, congrArg Prod.fst hφ, congrArg Prod.snd hφ⟩

end Square

section Opens

variable (U V : Y.Opens)

/-- The isomorphisms `a : F|_U ≅ A` and `b : F|_V ≅ B` of a glued object, restricted to `U ⊓ V`
through the composition isomorphisms of `derivedRestrict`, differ by `c`. -/
def GlueTwoCompatible {A : SchemeDerivedCategory U} {B : SchemeDerivedCategory V}
    (c : (derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A ≅
      (derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B)
    {F : SchemeDerivedCategory Y} (a : (derivedRestrict U.ι).obj F ≅ A)
    (b : (derivedRestrict V.ι).obj F ≅ B) : Prop :=
  (restrictCompInfLeft U V).inv.app F ≫
      (derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U))).map a.hom ≫ c.hom =
    (restrictCompInfRight U V).inv.app F ≫
      (derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V))).map b.hom

/-- **Two-open gluing, existence only** (Stacks Tag 08DG (1)): objects `A` on `U` and `B` on `V`
with an isomorphism `c : A|_{U∩V} ≅ B|_{U∩V}` glue to an object `F` of the derived category
of `Y`, with `F|_U ≅ A` and `F|_V ≅ B` compatible with `c` on `U ∩ V`.

No `Ext` vanishing hypothesis is used, and no covering hypothesis either. No uniqueness is
claimed, and it fails in general: for instance `𝒪 ⊕ 𝒪(-1)⟦1⟧` on the projective line is
universally gluable, but the negative `Ext` of its restriction to the affine line with itself
contains `Γ(𝔸¹, 𝒪) ≠ 0`. -/
theorem exists_glue_two (A : SchemeDerivedCategory U) (B : SchemeDerivedCategory V)
    (c : (derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A ≅
      (derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B) :
    ∃ (F : SchemeDerivedCategory Y) (a : (derivedRestrict U.ι).obj F ≅ A)
      (b : (derivedRestrict V.ι).obj F ≅ B), GlueTwoCompatible U V c a b :=
  exists_glue_of_isPullback (restrictCompInfLeft U V) (restrictCompInfRight U V) A B c
    (isPullback_opens_inf U V)

/-- **Two-open gluing, extension of morphisms** (Stacks Tag 08DG (2)): for `Y = U ∪ V`, morphisms
`α : A ⟶ E|_U` and `β : B ⟶ E|_V` that agree on `U ∩ V` through `c` extend to a morphism
`φ : F ⟶ E` from a glued object. -/
theorem exists_hom_of_glue_two (hUV : U ⊔ V = ⊤) {A : SchemeDerivedCategory U}
    {B : SchemeDerivedCategory V}
    (c : (derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A ≅
      (derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B)
    {F : SchemeDerivedCategory Y} (a : (derivedRestrict U.ι).obj F ≅ A)
    (b : (derivedRestrict V.ι).obj F ≅ B) (hab : GlueTwoCompatible U V c a b)
    (E : SchemeDerivedCategory Y) (α : A ⟶ (derivedRestrict U.ι).obj E)
    (β : B ⟶ (derivedRestrict V.ι).obj E)
    (h : (derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U))).map α ≫
        (restrictCompInfLeft U V).hom.app E =
      c.hom ≫ (derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V))).map β ≫
        (restrictCompInfRight U V).hom.app E) :
    ∃ φ : F ⟶ E, (derivedRestrict U.ι).map φ = a.hom ≫ α ∧
      (derivedRestrict V.ι).map φ = b.hom ≫ β :=
  exists_hom_of_glue_of_isPullback (restrictCompInfLeft U V) (restrictCompInfRight U V) A B c
    (isPullback_opens_inf U V) hUV a b hab E α β h

end Opens

section Dqc

open AlgebraicGeometry.DerivedCategory.Dqc

variable (U V : Y.Opens)

/-- The two inclusions of a cover by two opens, indexed by `ULift Bool`. -/
private def coverMap : ∀ b : ULift.{u} Bool, (cond b.down U V : Scheme.{u}) ⟶ Y
  | ⟨true⟩ => U.ι
  | ⟨false⟩ => V.ι

private instance (b : ULift.{u} Bool) : IsOpenImmersion (coverMap U V b) := by
  rcases b with ⟨_ | _⟩
  · exact (inferInstance : IsOpenImmersion V.ι)
  · exact (inferInstance : IsOpenImmersion U.ι)

/-- Having quasi-coherent cohomology is local on a cover by two opens. -/
theorem schemeQuasicoherentCohomology_of_cover (hUV : U ⊔ V = ⊤) (E : SchemeDerivedCategory Y)
    (hU : schemeQuasicoherentCohomology U ((derivedRestrict U.ι).obj E))
    (hV : schemeQuasicoherentCohomology V ((derivedRestrict V.ι).obj E)) :
    schemeQuasicoherentCohomology Y E := by
  intro n
  have key : ∀ {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f],
      schemeQuasicoherentCohomology X ((derivedRestrict f).obj E) →
        ((Modules.pullback f).obj
          ((DerivedCategory.homologyFunctor Y.Modules n).obj E)).IsQuasicoherent :=
    fun f _ h ↦
      (SheafOfModules.isQuasicoherent.{u, u, u} _).prop_of_iso
        (mapDerivedCategoryHomologyIso (Modules.pullback f) inferInstance inferInstance
          inferInstance E n) (h n)
  refine Modules.isQuasicoherent_of_cover _ (ι := ULift.{u} Bool) (X := fun b ↦ cond b.down U V)
    (coverMap U V) ?_ ?_
  · refine top_le_iff.1 fun y _ ↦ ?_
    have hy : y ∈ U ⊔ V := by rw [hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hy with h | h
    · exact (le_iSup (fun b : ULift.{u} Bool ↦ (coverMap U V b).opensRange) ⟨true⟩) ⟨⟨y, h⟩, rfl⟩
    · exact (le_iSup (fun b : ULift.{u} Bool ↦ (coverMap U V b).opensRange) ⟨false⟩)
        ⟨⟨y, h⟩, rfl⟩
  · rintro ⟨_ | _⟩
    · exact key V.ι hV
    · exact key U.ι hU

/-- **The glued object has quasi-coherent cohomology if `A` and `B` do** (Stacks Tag 08DG, in
`Dqc`): quasi-coherence is local, so a glued object lies in `Dqc(Y)` when its restrictions to the
two opens do. -/
theorem schemeQuasicoherentCohomology_of_glue_two (hUV : U ⊔ V = ⊤) {A : SchemeDerivedCategory U}
    {B : SchemeDerivedCategory V} {F : SchemeDerivedCategory Y}
    (a : (derivedRestrict U.ι).obj F ≅ A) (b : (derivedRestrict V.ι).obj F ≅ B)
    (hA : schemeQuasicoherentCohomology U A) (hB : schemeQuasicoherentCohomology V B) :
    schemeQuasicoherentCohomology Y F :=
  schemeQuasicoherentCohomology_of_cover U V hUV F
    ((schemeQuasicoherentCohomology U).prop_of_iso a.symm hA)
    ((schemeQuasicoherentCohomology V).prop_of_iso b.symm hB)

end Dqc

end

end AlgebraicGeometry.Scheme
