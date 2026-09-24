/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Owner bridge for t-structure hearts

This module gives repository-owned public names to the small amount of
t-structure heart infrastructure that is not yet in Mathlib.  It contains no
stability-condition definitions.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Category
open scoped ZeroObject

universe v' u' v u

namespace CategoryTheory

theorem ObjectProperty.FullSubcategory.isZero_of_obj_isZero
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {P : ObjectProperty C} [HasZeroMorphisms P.FullSubcategory]
    [HasZeroObject P.FullSubcategory] {X : P.FullSubcategory}
    (hX : IsZero X.obj) : IsZero X := by
  let Z : P.FullSubcategory := 0
  have hZ : IsZero Z.obj := P.ι.map_isZero (isZero_zero P.FullSubcategory)
  exact (isZero_zero P.FullSubcategory).of_iso (P.isoMk (hX.iso hZ))

namespace Triangulated.TStructure

open _root_.CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] (t : TStructure C)

/-- Degree-zero cohomology in the heart of `t`, given by the pure truncation
`τ^[0,0]`. -/
noncomputable def heartH0Functor [IsTriangulated C] :
    C ⥤ t.heart.FullSubcategory :=
  ObjectProperty.lift _ (t.truncGELE 0 0) (fun _ ↦
    (t.mem_heart_iff _).mpr ⟨inferInstance, inferInstance⟩)

/-- Degree-zero cohomology is naturally the identity on the heart. -/
noncomputable def heartH0OnHeartIso [IsTriangulated C] :
    t.heart.ι ⋙ t.heartH0Functor ≅ 𝟭 t.heart.FullSubcategory := by
  let eLE : t.heart.ι ⋙ t.truncLE 0 ≅ t.heart.ι :=
    NatIso.ofComponents
      (fun E ↦ by
        haveI : t.IsLE E.obj 0 := ((t.mem_heart_iff E.obj).mp E.property).1
        exact asIso ((t.truncLEι 0).app E.obj))
      (by
        intro X Y f
        exact (t.truncLEι 0).naturality f.hom)
  let eGE : t.heart.ι ≅ t.heart.ι ⋙ t.truncGE 0 :=
    NatIso.ofComponents
      (fun E ↦ by
        haveI : t.IsGE E.obj 0 := ((t.mem_heart_iff E.obj).mp E.property).2
        exact asIso ((t.truncGEπ 0).app E.obj))
      (by
        intro X Y f
        exact (t.truncGEπ 0).naturality f.hom)
  let e : (t.heart.ι ⋙ t.truncLE 0) ⋙ t.truncGE 0 ≅ t.heart.ι :=
    Functor.isoWhiskerRight eLE (t.truncGE 0) ≪≫ eGE.symm
  refine NatIso.ofComponents (fun E ↦ t.heart.isoMk (e.app E)) ?_
  intro X Y f
  ext
  exact e.hom.naturality f

/-- Negative ambient Hom spaces between objects of a t-structure heart vanish. -/
theorem heart_hι
    {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H] :
    ∀ ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧),
      n < 0 → f = 0 := by
  intro X Y n f hn
  haveI : t.IsGE ((t.ιHeart.obj Y)⟦n⟧) (-n) := t.isGE_shift _ 0 n (-n)
  exact t.zero f 0 (-n) (by lia)

/-- Every heart morphism is admissible for Mathlib's abelian-subcategory criterion. -/
theorem heart_admissible
    {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H] :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  haveI hX₃_le : t.IsLE X₃ 0 := by
    apply t.isLE₂ _ (rot_of_distTriang _ hT) 0
    · change t.IsLE (t.ιHeart.obj X₂) 0
      infer_instance
    · change t.IsLE ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) 0
      haveI := t.isLE_shift (t.ιHeart.obj X₁) 0 1 (-1)
      exact t.isLE_of_le _ (-1) 0
  haveI hX₃_ge : t.IsGE X₃ (-1) := by
    apply t.isGE₂ _ (rot_of_distTriang _ hT) (-1)
    · change t.IsGE (t.ιHeart.obj X₂) (-1)
      exact t.isGE_of_ge _ (-1) 0
    · change t.IsGE ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) (-1)
      exact t.isGE_shift _ 0 1 (-1)
  have hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    apply t.isLE₂ _ (rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)) 0
    · exact hX₃_le
    · change t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) 0
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  have hQ : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  have hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    apply t.isGE₂ _ (inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)) (-1)
    · change t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) (-1)
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 :=
        t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · exact hX₃_ge
  haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  have hK : t.heart (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).mpr
      ⟨t.isLE_shift _ (-1) (-1) 0, t.isGE_shift _ (-1) (-1) 0⟩
  rw [← t.essImage_ιHeart H] at hQ hK
  obtain ⟨Q, ⟨eQ⟩⟩ := hQ
  obtain ⟨K, ⟨eK⟩⟩ := hK
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫
      (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ t.ιHeart.obj Q := (t.truncGEπ 0).app X₃ ≫ eQ.inv
  let γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    eQ.hom ≫ (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _
    (t.triangleLTGE_distinguished 0 X₃) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ
      (by dsimp [α, _root_.CategoryTheory.Triangulated.TStructure.triangleLTGE]; simp)
      (by dsimp [β, _root_.CategoryTheory.Triangulated.TStructure.triangleLTGE]; simp)
      (by dsimp [γ]; simp))⟩

/-- A heart satisfying the standard finite-product interface is abelian. -/
@[reducible]
noncomputable def heartAbelian
    {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]
    [IsTriangulated C] [HasFiniteProducts H] : Abelian H :=
  AbelianSubcategory.abelian t.ιHeart (heart_hι t) (heart_admissible t)

instance heart_containsZero : t.heart.ContainsZero where
  exists_zero := ⟨0, isZero_zero C,
    (t.mem_heart_iff _).mpr ⟨inferInstance, inferInstance⟩⟩

lemma heart_biprod (X Y : C) (hX : t.heart X) (hY : t.heart Y) :
    t.heart (X ⊞ Y) := by
  rw [t.mem_heart_iff] at hX hY ⊢
  exact ⟨t.isLE₂ _ (binaryBiproductTriangle_distinguished X Y) 0 hX.1 hY.1,
    t.isGE₂ _ (binaryBiproductTriangle_distinguished X Y) 0 hX.2 hY.2⟩

instance heart_closedUnderBinaryProducts : t.heart.IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    let A := F.obj ⟨WalkingPair.left⟩
    let B := F.obj ⟨WalkingPair.right⟩
    have eDiag : F ≅ pair A B := Discrete.natIso (fun ⟨j⟩ ↦ match j with
      | WalkingPair.left => Iso.refl _
      | WalkingPair.right => Iso.refl _)
    exact t.heart.prop_of_iso
      (biprod.isoProd A B ≪≫ (HasLimit.isoOfNatIso eDiag).symm)
      (heart_biprod t A B (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

instance heart_closedUnderFiniteProducts : t.heart.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

noncomputable instance heart_hasFiniteProducts :
    HasFiniteProducts t.heart.FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The canonical abelian-category instance on the full subcategory cut out
by the heart of a triangulated t-structure. -/
@[reducible]
noncomputable def heartFullSubcategoryAbelian [IsTriangulated C] :
    Abelian t.heart.FullSubcategory :=
  haveI := t.hasHeartFullSubcategory
  heartAbelian t

theorem heartFullSubcategory_shortExact_of_distTriang [IsTriangulated C]
    {A B Q : t.heart.FullSubcategory}
    {f : A ⟶ B} {g : B ⟶ Q} {δ : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f.hom g.hom δ ∈ distTriang C) :
    (ShortComplex.mk f g (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)).ShortExact := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let S : ShortComplex t.heart.FullSubcategory := ShortComplex.mk f g (by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hT)
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using AbelianSubcategory.isLimitKernelForkOfDistTriang
      (heart_hι t) f g δ hT
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (heart_hι t) f g δ hT
  have hExact : S.Exact := ShortComplex.exact_of_f_is_kernel (S := S) hKer
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer)
    (Cofork.IsColimit.epi hCok)

/-- A short exact sequence in the full heart extends to a distinguished
triangle in the ambient category. -/
theorem heartFullSubcategory_shortExact_triangle
    {A B Q : t.heart.FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ Q) (hfg : f ≫ g = 0)
    [Mono f] [Epi g]
    (hexact : ∀ {W : t.heart.FullSubcategory} (alpha : W ⟶ B), alpha ≫ g = 0 →
      ∃ beta : W ⟶ A, beta ≫ f = alpha) :
    ∃ delta : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧,
      Triangle.mk f.hom g.hom delta ∈ distTriang C := by
  letI := t.hasHeartFullSubcategory
  let inclusion := t.heart.ι
  obtain ⟨K, i, delta, hTriangle⟩ :=
    AbelianSubcategory.exists_distinguished_triangle_of_epi
      (heart_hι t) (heart_admissible t)
      g
  have hiZero : (inclusion.map i) ≫ g.hom = 0 :=
    comp_distTriang_mor_zero₁₂ _ hTriangle
  have hiZeroHeart : ObjectProperty.homMk (inclusion.map i) ≫ g = 0 := by
    ext
    exact hiZero
  obtain ⟨betaHom, hbeta⟩ := hexact (W := K)
    (ObjectProperty.homMk (inclusion.map i)) hiZeroHeart
  let beta : K ⟶ A := betaHom
  have hbetaF : beta ≫ f = i := by
    ext
    exact congrArg (fun k => k.hom) hbeta
  have hKernel :=
    AbelianSubcategory.isLimitKernelForkOfDistTriang
      (heart_hι t)
      i g delta hTriangle
  let gamma : A ⟶ K := hKernel.lift (KernelFork.ofι f hfg)
  have hgammaI : gamma ≫ i = f := Fork.IsLimit.lift_ι hKernel
  haveI : Mono i := Fork.IsLimit.mono hKernel
  have hbetaGamma : beta ≫ gamma = 𝟙 K := by
    apply (cancel_mono i).1
    rw [Category.assoc, hgammaI, hbetaF, Category.id_comp]
  have hgammaBeta : gamma ≫ beta = 𝟙 A := by
    rw [← cancel_mono f, Category.assoc, hbetaF, hgammaI, Category.id_comp]
  let eKA : K ≅ A := ⟨beta, gamma, hbetaGamma, hgammaBeta⟩
  refine ⟨delta ≫ (shiftFunctor C (1 : ℤ)).map (inclusion.map eKA.hom), ?_⟩
  refine isomorphic_distinguished _ hTriangle _
    (Triangle.isoMk _ _ (inclusion.mapIso eKA.symm) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom,
      Iso.symm_hom, Triangle.mk_mor₁]
    change f.hom = inclusion.map gamma ≫ inclusion.map i
    rw [← Functor.map_comp, hgammaI]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Triangle.mk_mor₃,
      Functor.mapIso_hom, Iso.symm_hom]
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp,
      ← inclusion.map_comp, hbetaGamma]
    change delta ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 (inclusion.obj K)) = delta
    have hmap : (shiftFunctor C (1 : ℤ)).map (𝟙 (inclusion.obj K)) =
        𝟙 ((shiftFunctor C (1 : ℤ)).obj (inclusion.obj K)) :=
      Functor.map_id (shiftFunctor C (1 : ℤ)) (inclusion.obj K)
    rw [hmap]
    exact Category.comp_id delta

@[reassoc]
theorem truncGE_map_comp_descTruncGE
    {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (n : ℤ) [t.IsGE Z n] :
    (t.truncGE n).map g ≫ t.descTruncGE f n = t.descTruncGE (g ≫ f) n := by
  apply t.from_truncGE_obj_ext
  rw [← Category.assoc, t.truncGEπ_naturality]
  calc
    (g ≫ (t.truncGEπ n).app Y) ≫ t.descTruncGE f n = g ≫ f := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ g ≫ k) (t.π_descTruncGE (f := f) (n := n))
    _ = (t.truncGEπ n).app X ≫ t.descTruncGE (g ≫ f) n :=
      (t.π_descTruncGE (f := g ≫ f) (n := n)).symm

/-- The octahedron associated to a truncation triangle, with the three
commutativities used by tilted-cohomology calculations exposed explicitly. -/
theorem exists_truncLT_octahedral_split [IsTriangulated C]
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) (a : ℤ) :
    ∃ (Z : C) (v : X₂ ⟶ Z) (w : Z ⟶ ((t.truncLT a).obj X₁)⟦(1 : ℤ)⟧)
      (m₁ : (t.truncGE a).obj X₁ ⟶ Z) (m₃ : Z ⟶ X₃),
      Triangle.mk ((t.truncLTι a).app X₁ ≫ f) v w ∈ distTriang C ∧
      Triangle.mk m₁ m₃
        (δ ≫ (shiftFunctor C (1 : ℤ)).map ((t.truncGEπ a).app X₁)) ∈ distTriang C ∧
      (t.truncGEπ a).app X₁ ≫ m₁ = f ≫ v ∧
      m₁ ≫ w = (t.truncGEδLT a).app X₁ ∧
      v ≫ m₃ = g := by
  obtain ⟨Z, v, w, hCone⟩ := distinguished_cocone_triangle ((t.truncLTι a).app X₁ ≫ f)
  let oct := Triangulated.someOctahedron rfl
    (t.triangleLTGE_distinguished a X₁) hT hCone
  exact ⟨Z, v, w, oct.m₁, oct.m₃, hCone, by simpa using oct.mem,
    oct.comm₁, oct.comm₂, oct.comm₃⟩

end Triangulated.TStructure

end CategoryTheory
