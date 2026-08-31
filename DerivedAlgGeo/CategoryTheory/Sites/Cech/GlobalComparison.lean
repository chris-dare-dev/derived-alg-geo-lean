/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.InjectiveAcyclic
import DerivedAlgGeo.CategoryTheory.Sites.Cech.SmallSiteResolution
import DerivedAlgGeo.CategoryTheory.Sites.Cech.TotalComparison
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Global sections and the injective Cech total complex

For a cover of the terminal object, the augmented Cech complex of a sheaf is exact in degree
zero.  Combined with positive Cech exactness for injective sheaves, this identifies the total
Cech complex of an injective resolution with the ordinary global-sections complex.

The file closes with the Cech-to-derived comparison itself, in two forms.  The general form
carries an explicit `InjectiveResolution` and an explicit `HasExt` witness, because neither is
available over an arbitrary site.  On the small site `Opens X` both are supplied by Mathlib's
Grothendieck-abelian instances, so the specialization at the end of the file states the theorem
with no witness arguments at all.

Importing `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt` is what makes the second
form possible: without it `HasExt` is not in scope as an instance, and instance search falls back
to unfolding the abbreviation and diverges.  `HasExt` is a `Prop`, so bringing the instance into
scope creates no diamond with the `HasExt.standard` witnesses used elsewhere.
-/

universe h a u

open CategoryTheory Category Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

omit [HasFiniteProducts C] in
private lemma evalOp_map_π
    {D : Type*} [Category D] [HasProducts D]
    (F : Cᵒᵖ ⥤ D) {V W : Limits.FormalCoproduct C} (m : V ⟶ W)
    (q : V.I) :
    ((Limits.FormalCoproduct.evalOp C D).obj F).map m.op ≫
        Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q =
      Limits.Pi.π (fun q ↦ F.obj (op (W.obj q))) (m.f q) ≫
        F.map (m.φ q).op := by
  rw [Limits.FormalCoproduct.evalOp_obj_map]
  change Limits.Pi.lift (fun i ↦
      Limits.Pi.π (fun j ↦ F.obj (op (W.obj j))) (m.f i) ≫
        F.map (m.φ i).op) ≫
      Limits.Pi.π (fun q ↦ F.obj (op (V.obj q))) q = _
  rw [Limits.Pi.lift_π]

/-- Restriction of a global section to the degree-zero term of a Cech complex. -/
noncomputable def globalSectionsToCechZero
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    G.obj.obj (op T) ⟶ ((cechComplexFunctor U).obj G.obj).X 0 := by
  let V := Limits.FormalCoproduct.mk index U
  change G.obj.obj (op T) ⟶
    ∏ᶜ fun q : (V.cech.obj (op (SimplexCategory.mk 0))).I ↦
      G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))
  exact Limits.Pi.lift fun q ↦
    G.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj q)).op

omit [HasSheafify J AddCommGrpCat] in
lemma globalSectionsToCechZero_comp_d
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    globalSectionsToCechZero hT U G ≫
      ((cechComplexFunctor U).obj G.obj).d 0 1 = 0 := by
  let V := Limits.FormalCoproduct.mk index U
  let Z := (Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj G.obj
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let T₁ : (V.cech.obj (op (SimplexCategory.mk 1))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 1))).obj r))
  change globalSectionsToCechZero hT U G ≫
    ((cechComplexFunctor U).obj G.obj).d 0 1 =
      (0 : G.obj.obj (op T) ⟶ ∏ᶜ T₁)
  apply Limits.Pi.hom_ext
  intro q
  rw [zero_comp]
  have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Z.δ i := by
    change AlgebraicTopology.AlternatingCofaceMapComplex.objD Z 0 = _
    rfl
  let m₀ := V.cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let m₁ := V.cech.map (SimplexCategory.δ (1 : Fin 2)).op
  have hZ₀ : Z.δ (0 : Fin 2) ≫ Limits.Pi.π
      (fun r : ((Limits.FormalCoproduct.mk index U).cech.obj
        (op (SimplexCategory.mk 1))).I ↦
          G.obj.obj (op (((Limits.FormalCoproduct.mk index U).cech.obj
            (op (SimplexCategory.mk 1))).obj r))) q =
      Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op := by
    exact evalOp_map_π G.obj m₀ q
  have hZ₁ : Z.δ (1 : Fin 2) ≫ Limits.Pi.π
      (fun r : ((Limits.FormalCoproduct.mk index U).cech.obj
        (op (SimplexCategory.mk 1))).I ↦
          G.obj.obj (op (((Limits.FormalCoproduct.mk index U).cech.obj
            (op (SimplexCategory.mk 1))).obj r))) q =
      Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op := by
    exact evalOp_map_π G.obj m₁ q
  have hglobal (r : (V.cech.obj (op (SimplexCategory.mk 0))).I) :
      globalSectionsToCechZero hT U G ≫ Limits.Pi.π T₀ r =
        G.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj r)).op := by
    dsimp [globalSectionsToCechZero, T₀]
    rw [Limits.Pi.lift_π]
  rw [hd, Fin.sum_univ_two]
  rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
    show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
  simp only [one_smul, neg_smul, Preadditive.comp_add, Preadditive.comp_neg,
    Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]
  erw [hZ₀, hZ₁]
  simp only [← Category.assoc]
  rw [hglobal (m₀.f q), hglobal (m₁.f q)]
  simp only [← G.obj.map_comp]
  have hop :
      (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj (m₀.f q))).op ≫
          (m₀.φ q).op =
        (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj (m₁.f q))).op ≫
          (m₁.φ q).op := by
    rw [← op_comp, ← op_comp]
    congr 1
    apply hT.hom_ext
  rw [hop, add_neg_cancel]

/-- Restriction to degree-zero Cech cochains is natural in the sheaf. -/
lemma globalSectionsToCechZero_naturality
    {T : C} (hT : IsTerminal T) (U : index → C)
    {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H) :
    globalSectionsToCechZero hT U G ≫
        ((cechComplexFunctor U).map f.hom).f 0 =
      f.hom.app (op T) ≫ globalSectionsToCechZero hT U H := by
  let V := Limits.FormalCoproduct.mk index U
  let TG : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun q ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))
  let TH : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun q ↦
    H.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))
  change globalSectionsToCechZero hT U G ≫ Limits.Pi.map (fun q ↦
      f.hom.app (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))) =
    f.hom.app (op T) ≫ globalSectionsToCechZero hT U H
  have hG (q : (V.cech.obj (op (SimplexCategory.mk 0))).I) :
      globalSectionsToCechZero hT U G ≫ Limits.Pi.π TG q =
        G.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj q)).op := by
    dsimp [globalSectionsToCechZero, TG]
    rw [Limits.Pi.lift_π]
  have hH (q : (V.cech.obj (op (SimplexCategory.mk 0))).I) :
      globalSectionsToCechZero hT U H ≫ Limits.Pi.π TH q =
        H.obj.map (hT.from ((V.cech.obj (op (SimplexCategory.mk 0))).obj q)).op := by
    dsimp [globalSectionsToCechZero, TH]
    rw [Limits.Pi.lift_π]
  apply Limits.Pi.hom_ext
  intro q
  dsimp [V, TG, TH] at hG hH ⊢
  rw [Category.assoc, Limits.Pi.map_π]
  rw [← Category.assoc, hG]
  rw [Category.assoc, hH]
  exact f.hom.naturality (hT.from ((V.cech.obj
    (op (SimplexCategory.mk 0))).obj q)).op

/-- Restriction of global sections to degree zero of the integer-extended Cech complex. -/
noncomputable def globalSectionsToCechZeroInt
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    G.obj.obj (op T) ⟶ ((cechCochainFunctorInt U).obj G).X 0 :=
  let K := (cechComplexFunctor U).obj G.obj
  globalSectionsToCechZero hT U G ≫
    (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv

lemma globalSectionsToCechZeroInt_comp_d
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    globalSectionsToCechZeroInt hT U G ≫
      ((cechCochainFunctorInt U).obj G).d 0 1 = 0 := by
  let K := (cechComplexFunctor U).obj G.obj
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have h1 : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  change (globalSectionsToCechZero hT U G ≫
      (K.extendXIso ComplexShape.embeddingUpNat h0).inv) ≫
    (K.extend ComplexShape.embeddingUpNat).d 0 1 = 0
  rw [K.extend_d_eq ComplexShape.embeddingUpNat h0 h1]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, globalSectionsToCechZero_comp_d, zero_comp]

lemma globalSectionsToCechZeroInt_naturality
    {T : C} (hT : IsTerminal T) (U : index → C)
    {G H : Sheaf J AddCommGrpCat.{a}} (f : G ⟶ H) :
    globalSectionsToCechZeroInt hT U G ≫
        ((cechCochainFunctorInt U).map f).f 0 =
      f.hom.app (op T) ≫ globalSectionsToCechZeroInt hT U H := by
  let KG := (cechComplexFunctor U).obj G.obj
  let KH := (cechComplexFunctor U).obj H.obj
  let φ := (cechComplexFunctor U).map f.hom
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  rw [← cancel_mono
    (KH.extendXIso ComplexShape.embeddingUpNat h0).hom]
  change ((globalSectionsToCechZero hT U G ≫
      (KG.extendXIso ComplexShape.embeddingUpNat h0).inv) ≫
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f 0) ≫
          (KH.extendXIso ComplexShape.embeddingUpNat h0).hom =
    (f.hom.app (op T) ≫ globalSectionsToCechZero hT U H ≫
      (KH.extendXIso ComplexShape.embeddingUpNat h0).inv) ≫
        (KH.extendXIso ComplexShape.embeddingUpNat h0).hom
  dsimp [KG, KH]
  rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat h0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [φ]
  exact globalSectionsToCechZero_naturality hT U f

/-- The sheaf gluing axiom identifies global sections with degree-zero Cech cocycles. -/
lemma globalSectionsToCechZero_exact
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (ShortComplex.mk (globalSectionsToCechZero hT U G)
      (((cechComplexFunctor U).obj G.obj).d 0 1)
      (globalSectionsToCechZero_comp_d hT U G)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  let F := G.obj ⋙ forget AddCommGrpCat.{a}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj
      (forget AddCommGrpCat.{a}) G.2
  let V := Limits.FormalCoproduct.mk index U
  let Zc := (Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj G.obj
  let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj r))
  let T₁ : (V.cech.obj (op (SimplexCategory.mk 1))).I → AddCommGrpCat.{a} := fun r ↦
    G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 1))).obj r))
  let m₀ := V.cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let m₁ := V.cech.map (SimplexCategory.δ (1 : Fin 2)).op
  let xV := Limits.Concrete.productEquiv T₀ x
  have hcocycle (q : (V.cech.obj (op (SimplexCategory.mk 1))).I) :
      (ConcreteCategory.hom (G.obj.map (m₀.φ q).op)) (xV (m₀.f q)) =
        (ConcreteCategory.hom (G.obj.map (m₁.φ q).op)) (xV (m₁.f q)) := by
    have hd : ((cechComplexFunctor U).obj G.obj).d 0 1 =
        ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Zc.δ i := by
      change AlgebraicTopology.AlternatingCofaceMapComplex.objD Zc 0 = _
      rfl
    have hZ₀ : Zc.δ (0 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op := by
      exact evalOp_map_π G.obj m₀ q
    have hZ₁ : Zc.δ (1 : Fin 2) ≫ Limits.Pi.π T₁ q =
        Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op := by
      exact evalOp_map_π G.obj m₁ q
    have hmor : ((cechComplexFunctor U).obj G.obj).d 0 1 ≫ Limits.Pi.π T₁ q =
        (Limits.Pi.π T₀ (m₀.f q) ≫ G.obj.map (m₀.φ q).op) -
          (Limits.Pi.π T₀ (m₁.f q) ≫ G.obj.map (m₁.φ q).op) := by
      rw [hd, Fin.sum_univ_two]
      rw [show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) = 1 by norm_num,
        show (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) = -1 by norm_num]
      simp only [one_smul, neg_smul, Preadditive.add_comp, Preadditive.neg_comp]
      rw [hZ₀, hZ₁]
      rw [sub_eq_add_neg]
    have hxq := congrArg
      (fun y ↦ (ConcreteCategory.hom (Limits.Pi.π T₁ q)) y) hx
    rw [map_zero] at hxq
    erw [← ConcreteCategory.comp_apply] at hxq
    erw [hmor] at hxq
    rw [show xV (m₀.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₀.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₀.f q),
      show xV (m₁.f q) =
        (ConcreteCategory.hom (Limits.Pi.π T₀ (m₁.f q))) x by
      exact Limits.Concrete.productEquiv_apply_apply T₀ x (m₁.f q)]
    change (G.obj.map (m₀.φ q).op).hom
        ((Limits.Pi.π T₀ (m₀.f q)).hom x) =
      (G.obj.map (m₁.φ q).op).hom
        ((Limits.Pi.π T₀ (m₁.f q)).hom x)
    exact sub_eq_zero.mp hxq
  let r (i : index) : Fin 1 → index := fun _ ↦ i
  let e (i : index) : (∏ᶜ (U ∘ r i)) ≅ U i :=
    Limits.productUniqueIso (U ∘ r i)
  let family : Presheaf.FamilyOfElementsOnObjects F U := fun i ↦
    F.map (e i).inv.op (xV (r i))
  have hfamily : family.IsCompatible := by
    intro Z i j f g
    let q : Fin 2 → index :=
      fun k ↦ Fin.cases i (fun _ ↦ j) k
    let l : Z ⟶ ∏ᶜ (U ∘ q) :=
      Limits.Pi.lift fun k ↦ Fin.cases f (fun _ ↦ g) k
    have hδ₀ (k : Fin 1) :
        (SimplexCategory.δ (0 : Fin 2)).toOrderHom k = (1 : Fin 2) := by
      fin_cases k
      rfl
    have hδ₁ (k : Fin 1) :
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom k = (0 : Fin 2) := by
      fin_cases k
      rfl
    have hqδ₀ : q ∘ (⇑(SimplexCategory.δ (0 : Fin 2)).toOrderHom : Fin 1 → Fin 2) =
        r j := by
      funext k
      fin_cases k
      rfl
    have hqδ₁ : q ∘ (⇑(SimplexCategory.δ (1 : Fin 2)).toOrderHom : Fin 1 → Fin 2) =
        r i := by
      funext k
      fin_cases k
      rfl
    have hpair :
        F.map (Limits.Pi.π (U ∘ q) 0).op (family i) =
          F.map (Limits.Pi.π (U ∘ q) 1).op (family j) := by
      have hc := (hcocycle q).symm
      dsimp [m₀, m₁, V] at hc
      have faceComparison (a : index)
          (p : (∏ᶜ (U ∘ q)) ⟶ U a)
          (qa : Fin 1 → index) (hqa : qa = r a)
          (phi : (∏ᶜ (U ∘ q)) ⟶ ∏ᶜ (U ∘ qa))
          (hphi : ∀ k, HEq (phi ≫ Limits.Pi.π (U ∘ qa) k) p) :
          (G.obj.map (p ≫ (e a).inv).op).hom (xV (r a)) =
            (G.obj.map phi.op).hom (xV qa) := by
        subst qa
        have hphi' : phi = p ≫ (e a).inv := by
          apply Limits.Pi.hom_ext
          intro k
          rw [eq_of_heq (hphi k)]
          rw [Category.assoc]
          dsimp [e]
          rw [Limits.productUniqueIso_inv_π]
          simp [r]
        rw [hphi']
      have projectionHEq {a b : Fin 2} (hab : a = b) :
          HEq (Limits.Pi.π (U ∘ q) a) (Limits.Pi.π (U ∘ q) b) := by
        subst b
        rfl
      have hleft := faceComparison i
        (Limits.Pi.π (U ∘ q) 0)
        (q ∘ (⇑(SimplexCategory.δ (1 : Fin 2)).toOrderHom : Fin 1 → Fin 2)) hqδ₁
        (Limits.Pi.lift (fun k : Fin 1 ↦
          Limits.Pi.π (U ∘ q)
            ((SimplexCategory.δ (1 : Fin 2)).toOrderHom k)))
        (by
          intro k
          exact (heq_of_eq (Limits.Pi.lift_π (fun k : Fin 1 ↦
            Limits.Pi.π (U ∘ q)
              ((SimplexCategory.δ (1 : Fin 2)).toOrderHom k)) k)).trans
            (projectionHEq (hδ₁ k)))
      have hright := faceComparison j
        (Limits.Pi.π (U ∘ q) 1)
        (q ∘ (⇑(SimplexCategory.δ (0 : Fin 2)).toOrderHom : Fin 1 → Fin 2)) hqδ₀
        (Limits.Pi.lift (fun k : Fin 1 ↦
          Limits.Pi.π (U ∘ q)
            ((SimplexCategory.δ (0 : Fin 2)).toOrderHom k)))
        (by
          intro k
          exact (heq_of_eq (Limits.Pi.lift_π (fun k : Fin 1 ↦
            Limits.Pi.π (U ∘ q)
              ((SimplexCategory.δ (0 : Fin 2)).toOrderHom k)) k)).trans
            (projectionHEq (hδ₀ k)))
      dsimp [family, F]
      erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp]
      exact hleft.trans (hc.trans hright.symm)
    have hpull := congrArg (fun y ↦ F.map l.op y) hpair
    have hpull' :
        F.map ((Limits.Pi.π (U ∘ q) 0).op ≫ l.op) (family i) =
          F.map ((Limits.Pi.π (U ∘ q) 1).op ≫ l.op)
            (family j) := by
      simpa only [F.map_comp, ConcreteCategory.comp_apply] using hpull
    have hlf : l ≫ Limits.Pi.π (U ∘ q) 0 = f := by
      dsimp [l]
      rw [Limits.Pi.lift_π]
      rfl
    have hlg : l ≫ Limits.Pi.π (U ∘ q) 1 = g := by
      dsimp [l]
      rw [Limits.Pi.lift_π]
      rfl
    rw [← op_comp, ← op_comp, hlf, hlg] at hpull'
    exact hpull'
  let s := hfamily.section_ hU hF
  refine ⟨s.1 (op T), ?_⟩
  apply (Limits.Concrete.productEquiv T₀).injective
  funext q
  rw [Limits.Concrete.productEquiv_apply_apply]
  let i : index := q 0
  have hq : q = r i := by
    funext k
    fin_cases k
    rfl
  have componentComparison (a : index) (qa : Fin 1 → index) (hqa : qa = r a) :
      (Limits.Pi.π T₀ qa).hom
          ((globalSectionsToCechZero hT U G).hom (s.1 (op T))) = xV qa := by
    subst qa
    dsimp [globalSectionsToCechZero]
    erw [← ConcreteCategory.comp_apply]
    change (ConcreteCategory.hom
      (Limits.Pi.lift (fun q : Fin 1 → index ↦
          G.obj.map (hT.from (∏ᶜ (U ∘ q))).op) ≫
        Limits.Pi.π (fun q : Fin 1 → index ↦
          G.obj.obj (op (∏ᶜ (U ∘ q)))) (r a))) (s.1 (op T)) = xV (r a)
    rw [Limits.Pi.lift_π]
    have hs : s.1 (op (U a)) = family a := hfamily.section_apply hU hF a
    dsimp [family, F] at hs
    have hs' : F.map (hT.from (U a)).op (s.1 (op T)) =
        F.map (e a).inv.op (xV (r a)) :=
      (s.property (hT.from (U a)).op).trans hs
    have hsG : (G.obj.map (hT.from (U a)).op).hom (s.1 (op T)) =
        (G.obj.map (e a).inv.op).hom (xV (r a)) := hs'
    have hterminal : hT.from (∏ᶜ (U ∘ r a)) =
        (e a).hom ≫ hT.from (U a) := hT.hom_ext _ _
    rw [hterminal, op_comp, G.obj.map_comp]
    erw [ConcreteCategory.comp_apply]
    rw [hsG]
    erw [← ConcreteCategory.comp_apply]
    rw [← G.obj.map_comp, ← op_comp, Iso.hom_inv_id, op_id, G.obj.map_id]
    rfl
  exact componentComparison i q hq

private def terminalElementSection {T : C} (hT : IsTerminal T)
    (F : Cᵒᵖ ⥤ Type a) (x : F.obj (op T)) : F.sections where
  val X := F.map (hT.from X.unop).op x
  property := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f : Y ⟶ X⟩
    change F.map f.op (F.map (hT.from X).op x) = F.map (hT.from Y).op x
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    congr 2
    rw [← op_comp]
    exact congrArg F.map (congrArg op (hT.hom_ext _ _))

/-- A covering family detects global sections. -/
lemma globalSectionsToCechZero_mono
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) : Mono (globalSectionsToCechZero hT U G) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  let F := G.obj ⋙ forget AddCommGrpCat.{a}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj
      (forget AddCommGrpCat.{a}) G.2
  let sx := terminalElementSection hT F x
  let sy := terminalElementSection hT F y
  have hs : sx = sy := by
    apply hU.sections_ext ⟨F, hF⟩
    intro i
    let r : Fin 1 → index := fun _ ↦ i
    let e : (∏ᶜ (U ∘ r)) ≅ U i := Limits.productUniqueIso (U ∘ r)
    let P : C := ∏ᶜ (U ∘ r)
    let V := Limits.FormalCoproduct.mk index U
    let T₀ : (V.cech.obj (op (SimplexCategory.mk 0))).I → AddCommGrpCat.{a} := fun q ↦
      G.obj.obj (op ((V.cech.obj (op (SimplexCategory.mk 0))).obj q))
    have hp := congrArg (fun z ↦ (Limits.Pi.π T₀ r).hom z) hxy
    have hproj : globalSectionsToCechZero hT U G ≫ Limits.Pi.π T₀ r =
        G.obj.map (hT.from P).op := by
      dsimp [globalSectionsToCechZero, T₀, P, V]
      rw [Limits.Pi.lift_π]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at hp
    rw [hproj] at hp
    have hp' := congrArg (fun z ↦ (G.obj.map (e.inv).op).hom z) hp
    dsimp [sx, sy, terminalElementSection]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp] at hp'
    have hterminal : e.inv ≫ hT.from P = hT.from (U i) := hT.hom_ext _ _
    rw [← op_comp, hterminal] at hp'
    exact hp'
  have hTself : hT.from T = 𝟙 T := hT.hom_ext _ _
  have hsT := congrArg (fun s : F.sections ↦ s.1 (op T)) hs
  simpa [sx, sy, terminalElementSection, hTself] using hsT

lemma globalSectionsToCechZeroInt_mono
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) : Mono (globalSectionsToCechZeroInt hT U G) := by
  letI : Mono (globalSectionsToCechZero hT U G) :=
    globalSectionsToCechZero_mono hT U hU G
  dsimp [globalSectionsToCechZeroInt]
  infer_instance

/-- The integer-extended augmented Cech complex is exact in degree zero. -/
lemma globalSectionsToCechZeroInt_exact
    {T : C} (hT : IsTerminal T) (U : index → C) (hU : J.CoversTop U)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (ShortComplex.mk (globalSectionsToCechZeroInt hT U G)
      (((cechCochainFunctorInt U).obj G).d 0 1)
      (globalSectionsToCechZeroInt_comp_d hT U G)).Exact := by
  let K := (cechComplexFunctor U).obj G.obj
  have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  have h1 : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  let S₀ := ShortComplex.mk (globalSectionsToCechZero hT U G) (K.d 0 1)
    (globalSectionsToCechZero_comp_d hT U G)
  let Sℤ := ShortComplex.mk (globalSectionsToCechZeroInt hT U G)
    (((cechCochainFunctorInt U).obj G).d 0 1)
    (globalSectionsToCechZeroInt_comp_d hT U G)
  let e : S₀ ≅ Sℤ := ShortComplex.isoMk (Iso.refl _)
    (K.extendXIso ComplexShape.embeddingUpNat h0).symm
    (K.extendXIso ComplexShape.embeddingUpNat h1).symm
    (by rfl)
    (by
      change (K.extendXIso ComplexShape.embeddingUpNat h0).inv ≫
        (K.extend ComplexShape.embeddingUpNat).d 0 1 =
          K.d 0 1 ≫ (K.extendXIso ComplexShape.embeddingUpNat h1).inv
      rw [K.extend_d_eq ComplexShape.embeddingUpNat h0 h1,
        Iso.inv_hom_id_assoc])
  exact ShortComplex.exact_of_iso e (globalSectionsToCechZero_exact hT U hU G)

/-- The augmented Cech row of a sheaf, with global sections placed in degree zero. -/
noncomputable def globalSectionsToCechRowMap
    {T : C} (hT : IsTerminal T) (U : index → C)
    (G : Sheaf J AddCommGrpCat.{a}) :
    (CochainComplex.singleFunctor AddCommGrpCat.{a} 0).obj (G.obj.obj (op T)) ⟶
      (cechCochainFunctorInt U).obj G :=
  HomologicalComplex.mkHomFromSingle (globalSectionsToCechZeroInt hT U G) (by
    intro k hk
    have hk' : k = 1 := by
      change 0 + 1 = k at hk
      omega
    subst k
    exact globalSectionsToCechZeroInt_comp_d hT U G)

/-- For a cover of a topological space, the augmented Cech row of an injective sheaf is a
quasi-isomorphism. -/
lemma globalSectionsToCechRowMap_quasiIso
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective G] :
    QuasiIso (globalSectionsToCechRowMap hT U G) := by
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    let φ := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u}
      (ComplexShape.up ℤ) (-1) 0 1).map
      (globalSectionsToCechRowMap hT U G)
    rw [ShortComplex.quasiIso_iff_of_zeros φ]
    · constructor
      · let S := ShortComplex.mk
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (G.obj.obj (op T))).hom ≫ globalSectionsToCechZeroInt hT U G)
          (((cechCochainFunctorInt U).obj G).d 0 1) (by
            rw [Category.assoc, globalSectionsToCechZeroInt_comp_d, comp_zero])
        let S₀ := ShortComplex.mk (globalSectionsToCechZeroInt hT U G)
          (((cechCochainFunctorInt U).obj G).d 0 1)
          (globalSectionsToCechZeroInt_comp_d hT U G)
        let e : S ≅ S₀ := ShortComplex.isoMk
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (G.obj.obj (op T)))
          (Iso.refl _) (Iso.refl _) (by simp [S, S₀]) (by simp [S, S₀])
        change S.Exact
        exact ShortComplex.exact_of_iso e (globalSectionsToCechZeroInt_exact hT U hU G)
      · letI : Mono (globalSectionsToCechZeroInt hT U G) :=
          globalSectionsToCechZeroInt_mono hT U hU G
        change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (G.obj.obj (op T))).hom ≫ globalSectionsToCechZeroInt hT U G)
        infer_instance
    · rfl
    · rfl
    · apply IsZero.eq_of_src
      dsimp [cechCochainFunctorInt]
      apply HomologicalComplex.isZero_extend_X
      intro m hm
      dsimp [ComplexShape.embeddingUpNat] at hm
      omega
  · have hsource :
        ((CochainComplex.singleFunctor AddCommGrpCat.{u} 0).obj
          (G.obj.obj (op T))).ExactAt n :=
      HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 _ n hn
    rw [quasiIsoAt_iff_exactAt (globalSectionsToCechRowMap hT U G) n hsource]
    let K := (cechComplexFunctor U).obj G.obj
    by_cases hnneg : n < 0
    · exact K.extend_exactAt ComplexShape.embeddingUpNat n (fun m hm ↦ by
        dsimp [ComplexShape.embeddingUpNat] at hm
        omega)
    · have hnpos : 0 < n := by omega
      let m : ℕ := n.toNat
      have hm : (m : ℤ) = n := by
        dsimp [m]
        rw [Int.toNat_of_nonneg (by omega)]
      rw [← hm]
      apply (K.extend_exactAt_iff ComplexShape.embeddingUpNat (j := m)
        (j' := (m : ℤ)) rfl).2
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (by
        dsimp [m]
        omega : m ≠ 0)
      rw [hk]
      exact cechComplex_exactAt_succ_of_injective U hU G k

/-- Global sections of an injective resolution map to its degree-zero Cech column. -/
noncomputable def injectiveResolutionSectionsToCechZeroColumn
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted T I ⟶
      (cechInjectiveBicomplex U I).X 0 where
  f q := globalSectionsToCechZeroInt hT U (I.cochainComplex.X q)
  comm' q r _ := globalSectionsToCechZeroInt_naturality hT U
    (I.cochainComplex.d q r)

/-- The augmented row map from the global-sections resolution, placed in Cech degree zero,
to the full injective Cech bicomplex. -/
noncomputable def globalSectionsToCechBicomplexMap
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂.singleZeroBicomplex
        (injectiveResolutionSectionsComplexUnlifted T I) ⟶
      cechInjectiveBicomplex U I := by
  let A := injectiveResolutionSectionsComplexUnlifted T I
  let g := injectiveResolutionSectionsToCechZeroColumn hT U I
  refine HomologicalComplex₂.homMk (fun pq ↦
    if hp : pq.1 = 0 then
      (HomologicalComplex₂.singleZeroXIso A pq.1 hp).hom.f pq.2 ≫ g.f pq.2 ≫
        (HomologicalComplex₂.XXIsoOfEq AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (cechInjectiveBicomplex U I) hp.symm rfl).hom
    else 0) ?_ ?_
  · intro p p' q hpp
    by_cases hp : p = 0
    · subst p
      have hp' : p' = 1 := by
        change 0 + 1 = p' at hpp
        omega
      subst p'
      simp only [dif_pos True.intro, dif_neg (by omega : ¬ (0 + 1 = (0 : ℤ))),
        comp_zero]
      rw [Category.assoc]
      change (HomologicalComplex₂.singleZeroXIso A 0 rfl).hom.f q ≫
        (globalSectionsToCechZeroInt hT U (I.cochainComplex.X q) ≫
          ((cechCochainFunctorInt U).obj (I.cochainComplex.X q)).d 0 1) = 0
      rw [globalSectionsToCechZeroInt_comp_d, comp_zero]
    · simp [hp, HomologicalComplex₂.singleZeroBicomplex]
  · intro p q q' hqq
    by_cases hp : p = 0
    · subst p
      simp only [dif_pos True.intro]
      exact (HomologicalComplex.Hom.comm
        ((HomologicalComplex₂.singleZeroXIso A 0 rfl).hom ≫ g) q q')
    · simp [hp]

/-- After flipping the augmented bicomplex, each fixed resolution degree is the corresponding
augmented Cech row, up to the canonical identification between evaluation and a single complex. -/
noncomputable def globalSectionsToCechBicomplexMapFlipRowIso
    {T : C} {F : Sheaf J AddCommGrpCat.{a}}
    (I : InjectiveResolution F) (q : ℤ) :
    ((HomologicalComplex₂.singleZeroBicomplex
        (injectiveResolutionSectionsComplexUnlifted T I)).flip.X q) ≅
      (CochainComplex.singleFunctor AddCommGrpCat.{a} 0).obj
        ((I.cochainComplex.X q).obj.obj (op T)) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) q)
    (ComplexShape.up ℤ) 0).app
      (injectiveResolutionSectionsComplexUnlifted T I)

lemma globalSectionsToCechBicomplexMap_flip_row
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) (q : ℤ) :
    ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (globalSectionsToCechBicomplexMap hT U I)).f q =
      (globalSectionsToCechBicomplexMapFlipRowIso I q).hom ≫
        globalSectionsToCechRowMap hT U (I.cochainComplex.X q) := by
  apply HomologicalComplex.Hom.ext
  funext p
  by_cases hp : p = 0
  · subst p
    simp [globalSectionsToCechBicomplexMap,
      globalSectionsToCechBicomplexMapFlipRowIso,
      globalSectionsToCechRowMap, HomologicalComplex₂.singleZeroXIso,
      injectiveResolutionSectionsToCechZeroColumn,
      injectiveResolutionSectionsComplexUnlifted, Category.assoc]
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((I.cochainComplex.X q).obj.obj (op T))
    change _ = _ ≫ e.inv ≫ e.hom ≫ _
    simp
  · apply IsZero.eq_of_src
    exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) q).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (injectiveResolutionSectionsComplexUnlifted T I) p hp)

private lemma singleZeroBicomplex_flip_verticallyConnective
    (A : CochainComplex AddCommGrpCat.{a} ℤ) :
    HomologicalComplex₂.IsVerticallyConnective
      (HomologicalComplex₂.singleZeroBicomplex A).flip := by
  intro p q hq
  change IsZero ((((CochainComplex.singleFunctor
    (CochainComplex AddCommGrpCat.{a} ℤ) 0).obj A).X q).X p)
  exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) p).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A q (by omega))

private lemma singleZeroBicomplex_flip_horizontallyConnective
    (A : CochainComplex AddCommGrpCat.{a} ℤ)
    (hA : ∀ p : ℤ, p < 0 → IsZero (A.X p)) :
    HomologicalComplex₂.IsHorizontallyConnective
      (HomologicalComplex₂.singleZeroBicomplex A).flip := by
  intro p q hp
  have hAp : IsZero (A.X p) := hA p hp
  by_cases hq : q = 0
  · subst q
    exact IsZero.of_iso hAp
      ((HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) p).mapIso
        (HomologicalComplex₂.singleZeroXIso A 0 rfl)).symm
  · change IsZero ((((CochainComplex.singleFunctor
      (CochainComplex AddCommGrpCat.{a} ℤ) 0).obj A).X q).X p)
    exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) p).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A q hq)

private lemma cechInjectiveBicomplex_flip_verticallyConnective
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂.IsVerticallyConnective
      (cechInjectiveBicomplex U I).flip := by
  intro p q hq
  exact cechInjectiveBicomplex_horizontallyConnective U I q p hq

private lemma cechInjectiveBicomplex_flip_horizontallyConnective
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    HomologicalComplex₂.IsHorizontallyConnective
      (cechInjectiveBicomplex U I).flip := by
  intro p q hp
  exact cechInjectiveBicomplex_verticallyConnective U I q p hp

/-- Each resolution-degree row of the flipped global-sections comparison is a
quasi-isomorphism. -/
lemma globalSectionsToCechBicomplexMap_flip_row_quasiIso
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℤ) :
    QuasiIso
      (((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
          (globalSectionsToCechBicomplexMap hT U I)).f q) := by
  rw [globalSectionsToCechBicomplexMap_flip_row]
  letI : QuasiIso (globalSectionsToCechRowMap hT U (I.cochainComplex.X q)) :=
    globalSectionsToCechRowMap_quasiIso hT U hU (I.cochainComplex.X q)
  infer_instance

/-- The global-sections resolution maps canonically to the total Cech complex through the
rowwise augmented Cech comparison. -/
noncomputable def injectiveResolutionSectionsToCechTotalMap
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted T I ⟶ cechInjectiveTotalComplex U I := by
  let A := injectiveResolutionSectionsComplexUnlifted T I
  let K := HomologicalComplex₂.singleZeroBicomplex A
  let L := cechInjectiveBicomplex U I
  exact (HomologicalComplex₂.singleZeroTotalIso A).inv ≫
    (K.totalFlipIso (ComplexShape.up ℤ)).inv ≫
    HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
          (globalSectionsToCechBicomplexMap hT U I)) (ComplexShape.up ℤ) ≫
    (L.totalFlipIso (ComplexShape.up ℤ)).hom

/-- For an open cover, the complex of global sections of an injective resolution and the
injective Cech total complex are quasi-isomorphic. -/
lemma injectiveResolutionSectionsToCechTotalMap_quasiIso
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    QuasiIso (injectiveResolutionSectionsToCechTotalMap hT U I) := by
  let A := injectiveResolutionSectionsComplexUnlifted T I
  let K := HomologicalComplex₂.singleZeroBicomplex A
  let L := cechInjectiveBicomplex U I
  let f := (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (globalSectionsToCechBicomplexMap hT U I)
  letI : QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
    apply HomologicalComplex₂.totalMap_quasiIso
    · exact singleZeroBicomplex_flip_verticallyConnective A
    · exact cechInjectiveBicomplex_flip_verticallyConnective U I
    · apply singleZeroBicomplex_flip_horizontallyConnective A
      intro p hp
      exact (sectionsAtFunctorUnlifted T).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE I.cochainComplex 0 p hp)
    · exact cechInjectiveBicomplex_flip_horizontallyConnective U I
    · intro q
      exact globalSectionsToCechBicomplexMap_flip_row_quasiIso hT U hU I q
  change QuasiIso ((HomologicalComplex₂.singleZeroTotalIso A).inv ≫
    (K.totalFlipIso (ComplexShape.up ℤ)).inv ≫
    HomologicalComplex₂.total.map f (ComplexShape.up ℤ) ≫
    (L.totalFlipIso (ComplexShape.up ℤ)).hom)
  infer_instance

/-- Integer extension does not change the Cech cohomology in a nonnegative degree. -/
noncomputable def cechCochainFunctorIntHomologyIso
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (n : ℕ) :
    ((cechCochainFunctorInt U).obj F).homology (n : ℤ) ≅
      cechCohomology U F.obj n := by
  change ((((cechComplexFunctor U).obj F.obj).extend
    ComplexShape.embeddingUpNat).homology (n : ℤ)) ≅
      ((cechComplexFunctor U).obj F.obj).homology n
  exact ((cechComplexFunctor U).obj F.obj).extendHomologyIso
    ComplexShape.embeddingUpNat rfl

/-- In one universe, the unlifted sections complex is canonically isomorphic to the
universe-lifted complex used by the existing `H'` comparison. -/
noncomputable def injectiveResolutionSectionsComplexUnliftedIso
    {X : TopCat.{u}} {T : Opens X} {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted T I ≅
      injectiveResolutionSectionsComplex T I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ AddEquiv.ulift.symm.toAddCommGrpIso) (by
      intro p q hpq
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change ULift.up _ = ULift.up _
      rfl)

/-- The Cech-to-sections half of the comparison, as a named isomorphism.

The four factors are each the homology of an explicit chain map, or its inverse; the acyclicity
hypothesis enters only through the proofs that two of them are quasi-isomorphisms, never through
the construction.  That is what makes the comparison compatible with a morphism of sheaves --
see `cechComparisonAddEquiv_naturality`. -/
noncomputable def cechToSectionsHomologyIso
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hcover : @IsCechAcyclicCover (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F) (n : ℕ) :
    (cechCohomology U F.obj n : AddCommGrpCat.{u}) ≅
      (injectiveResolutionSectionsComplex T I).homology (n : ℤ) := by
  letI : QuasiIso (injectiveResolutionSectionsToCechTotalMap hT U I) :=
    injectiveResolutionSectionsToCechTotalMap_quasiIso hT U hcover.1 I
  exact (cechCochainFunctorIntHomologyIso U n).symm ≪≫
    (@cechCohomologyIsoInjectiveTotalHomology (Opens X) _
      (Opens.grothendieckTopology X) _ _ index F U I hExt hcover.2 (n : ℤ)) ≪≫
    (isoOfQuasiIsoAt (injectiveResolutionSectionsToCechTotalMap hT U I) (n : ℤ)).symm ≪≫
    HomologicalComplex.homologyMapIso
      (injectiveResolutionSectionsComplexUnliftedIso I) (n : ℤ)

/-- **The Cech-to-derived comparison, as a named additive equivalence.**

The existential form below records only that some isomorphism exists, which is enough for a
vanishing statement and not enough for anything else: a scalar action on cohomology arrives as
the map induced by an endomorphism of the sheaf, and an unnamed isomorphism cannot be asked to
commute with it.  This is the comparison itself. -/
noncomputable def cechComparisonAddEquiv
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hcover : @IsCechAcyclicCover (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F) (n : ℕ) :
    (cechCohomology U F.obj n : AddCommGrpCat.{u}) ≃+
      @Sheaf.H (Opens X) _ (Opens.grothendieckTopology X) F _ hExt n :=
  (cechToSectionsHomologyIso hT U I hExt hcover n).addCommGroupIsoToAddEquiv |>.trans
    (@injectiveResolutionSectionsCohomologyAddEquivHPrime (Opens X) _
      (Opens.grothendieckTopology X) _ hExt F T I n) |>.trans
    (@HPrimeAddEquivH (Opens X) _ (Opens.grothendieckTopology X) _ hExt T hT F n)

/-- A Cech-acyclic open cover computes derived sheaf cohomology, relative to an explicit
injective resolution and an explicit `HasExt` witness.

Both stay explicit here because the statement is universe-general in the `HasExt` parameter `h`.
For the small site `Opens X` at `h = u`, see
`isCechAcyclicCover_cechComputesDerivedCohomology_opens`, which supplies both.

The isomorphism is `cechComparisonAddEquiv`; this states only that one exists, which is all a
vanishing argument needs. -/
theorem isCechAcyclicCover_cechComputesDerivedCohomology
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hcover : @IsCechAcyclicCover (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F) :
    @CechComputesDerivedCohomology (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F :=
  fun n ↦ ⟨cechComparisonAddEquiv hT U I hExt hcover n⟩

/-- A Cech-acyclic open cover computes derived sheaf cohomology, with no injective resolution
supplied.  The site `Opens X` is small, so Mathlib's Grothendieck-abelian chain gives enough
injectives and `canonicalInjectiveResolution` chooses one.

The `HasExt` witness stays **explicit, with a free universe `h`**, and deliberately so.
`Sheaf.H` is `abbrev H (n : ℕ) : Type w'`, so the cohomology groups live in the `HasExt` universe:
`HasExt.{u}` and `HasExt.{u + 1}` name genuinely different groups, not two proofs of one
statement.  The small site does permit pinning `h := u` through `IsGrothendieckAbelian.hasExt`,
but that would state the theorem about groups no other part of this library computes --
`Cohomology/Derived/AffineVanishing` and `Cohomology/Finiteness/FiniteDimensional` both work at
`HasExt.{u + 1}` through `HasExt.standard`.  Keeping the witness explicit also stops instance
search from silently resolving it to `u` inside `IsCechAcyclicCover`, which is why the hypothesis
and conclusion below name it positionally. -/
theorem isCechAcyclicCover_cechComputesDerivedCohomology_opens
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hcover : @IsCechAcyclicCover (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F) :
    @CechComputesDerivedCohomology (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F :=
  isCechAcyclicCover_cechComputesDerivedCohomology hT U
    (canonicalInjectiveResolution F) hExt hcover

/-- Degreewise form of `isCechAcyclicCover_cechComputesDerivedCohomology_opens`. -/
theorem isCechAcyclicCover_cechComputesDerivedCohomologyAt_opens
    {X : TopCat.{u}} {T : Opens X} (hT : IsTerminal T)
    {index : Type u} (U : index → Opens X)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hcover : @IsCechAcyclicCover (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F) (n : ℕ) :
    @CechComputesDerivedCohomologyAt (Opens X) _
      (Opens.grothendieckTopology X) _ hExt index _ U F n :=
  isCechAcyclicCover_cechComputesDerivedCohomology_opens hT U hExt hcover n

end CategoryTheory.Sheaf
