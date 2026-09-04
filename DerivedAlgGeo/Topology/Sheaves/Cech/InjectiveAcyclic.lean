/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.Cech.FreeAbelianYonedaStalk
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Positive Cech exactness for injective abelian sheaves

For an open cover of a topological space, the Cech complex of an injective abelian sheaf is
exact in every positive degree.

The proof constructs the chain complex of free abelian sheaves represented by the finite
intersections in the Cech nerve.  Around a point in one member of the cover, intersecting the
whole cover with that member gives an extra degeneracy.  The comparison back to the original
free Cech chain complex is an isomorphism on that stalk, by stalk-locality of free representable
sheaves.  Hence the free Cech chain complex is exact stalkwise, and therefore exact as a complex
of sheaves.

Applying `Hom(-, I)` to this exact chain complex is exact when `I` is injective.  The free
abelian Yoneda equivalence identifies the resulting cochain complex degreewise, including its
differential, with Mathlib's ordinary Cech complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
  Simplicial TopologicalSpace

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

local instance iicHasTerminal' (V : Opens X) : HasTerminal (Set.Iic V) :=
  (IsTerminal.ofUniqueHom (Y := (⟨V, by exact le_refl V⟩ : Set.Iic V))
    (fun U ↦ homOfLE U.2) (fun _ _ ↦ Subsingleton.elim _ _)).hasTerminal

local instance iicHasLimitPair' (V : Opens X) {U W : Set.Iic V} :
    HasLimit (pair U W) := by
  let P : Set.Iic V := ⟨U.1 ⊓ W.1, by
    show U.1 ⊓ W.1 ≤ V
    exact inf_le_left.trans U.2⟩
  let c : BinaryFan U W := BinaryFan.mk (P := P)
    (homOfLE inf_le_left) (homOfLE inf_le_right)
  exact HasLimit.mk ⟨c, BinaryFan.isLimitMk
    (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)⟩

local instance iicHasBinaryProducts' (V : Opens X) : HasBinaryProducts (Set.Iic V) :=
  hasBinaryProducts_of_hasLimit_pair (Set.Iic V)

local instance iicHasFiniteProducts' (V : Opens X) : HasFiniteProducts (Set.Iic V) :=
  hasFiniteProducts_of_has_binary_and_terminal

end TopologicalSpace.Opens

namespace CategoryTheory.Limits.FormalCoproduct

variable {C D : Type*} [Category C] [Category D]

private def mapFunctor' (F : Functor C D) :
    Functor (FormalCoproduct C) (FormalCoproduct D) where
  obj X := ⟨X.I, fun i ↦ F.obj (X.obj i)⟩
  map f := ⟨f.f, fun i ↦ F.map (f.φ i)⟩
  map_id X := by
    rw [hom_ext_iff]
    refine ⟨rfl, fun i ↦ ?_⟩
    dsimp
    rw [Category.comp_id]
    exact F.map_id (X.obj i)
  map_comp f g := by
    rw [hom_ext_iff]
    refine ⟨rfl, fun i ↦ ?_⟩
    dsimp
    rw [Category.comp_id]
    exact F.map_comp (f.φ i) (g.φ (f.f i))

end CategoryTheory.Limits.FormalCoproduct

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000

private lemma freeAbelianYonedaPresheafHomAddEquiv_precomp'
    {C : Type u} [Category.{u} C] {X Y : C} (f : X ⟶ Y)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (g : yoneda.obj Y ⋙ AddCommGrpCat.free ⟶ G) :
    freeAbelianYonedaPresheafHomAddEquiv X G
        (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫ g) =
      G.map f.op (freeAbelianYonedaPresheafHomAddEquiv Y G g) := by
  dsimp [freeAbelianYonedaPresheafHomAddEquiv]
  calc
    _ = g.app (op X) (FreeAbelianGroup.of f) := by
      congr 1
      change (AddCommGrpCat.free.map ((yoneda.map f).app (op X))).hom
        (FreeAbelianGroup.of (𝟙 X)) = FreeAbelianGroup.of f
      rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
      simp
    _ = G.map f.op (g.app (op Y) (FreeAbelianGroup.of (𝟙 Y))) := by
      have h := CategoryTheory.congr_fun (g.naturality f.op)
        (FreeAbelianGroup.of (𝟙 Y))
      simp only [Functor.comp_map, CategoryTheory.comp_apply] at h
      change g.app (op X)
          ((AddCommGrpCat.free.map ((yoneda.obj Y).map f.op)).hom
            (FreeAbelianGroup.of (𝟙 Y))) =
        G.map f.op (g.app (op Y) (FreeAbelianGroup.of (𝟙 Y))) at h
      rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of] at h
      simpa using h

private lemma freeAbelianYonedaSheafHomAddEquiv_precomp'
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] {X Y : C} (f : X ⟶ Y)
    (G : Sheaf J AddCommGrpCat.{u})
    (g : freeAbelianYonedaSheaf J Y ⟶ G) :
    freeAbelianYonedaSheafHomAddEquiv X G
        ((presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ g) =
      G.obj.map f.op (freeAbelianYonedaSheafHomAddEquiv Y G g) := by
  change freeAbelianYonedaPresheafHomAddEquiv X G.obj
      ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _
        ((presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeAbelianYonedaPresheafHomAddEquiv_precomp' f G.obj _

private noncomputable def freeAbelianYonedaSheafFunctor (X : TopCat.{u}) :
    Functor (Opens X) (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

private noncomputable def sheafStalkFunctor (X : TopCat.{u}) (x : X) :
    Functor (TopCat.Sheaf AddCommGrpCat.{u} X) AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

private noncomputable instance sheafStalkFunctor_additive (X : TopCat.{u}) (x : X) :
    (sheafStalkFunctor X x).Additive := by
  dsimp [sheafStalkFunctor]
  infer_instance

private lemma map_sigma_isIso_of_map_isIso
    {C D : Type*} [Category C] [Category D] {I : Type*}
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I D]
    (F : Functor C D) [PreservesColimitsOfShape (Discrete I) F]
    {A B : I → C} (f : ∀ i, A i ⟶ B i)
    [∀ i, IsIso (F.map (f i))] :
    IsIso (F.map (Limits.Sigma.map f)) := by
  let p : ∀ i, F.obj (A i) ⟶ F.obj (B i) := fun i ↦ F.map (f i)
  haveI : IsIso (Limits.Sigma.map p) := inferInstance
  apply IsIso.of_isIso_fac_left (f := sigmaComparison F A)
    (h := Limits.Sigma.map p ≫ sigmaComparison F B)
  apply Limits.Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc]
  rw [Limits.Sigma.ι_map_assoc]
  rw [ι_comp_sigmaComparison]
  rw [← F.map_comp, ← F.map_comp, Limits.Sigma.ι_map]

private def iicIncl' {X : Type*} [TopologicalSpace X] (V : Opens X) :
    Functor (Set.Iic V) (Opens X) where
  obj U := U.1
  map f := homOfLE (leOfHom f)

private noncomputable def freeAbelianCechChainComplex {X : TopCat.{u}} {I : Type u}
    (U : I → Opens X) :
    ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((FormalCoproduct.mk I U).cech ⋙
      (FormalCoproduct.eval.{u} (Opens X)
        (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
          (freeAbelianYonedaSheafFunctor X))

private noncomputable def freeAbelianCechStalkComplex {X : TopCat.{u}} {I : Type u}
    (U : I → Opens X) (x : X) : ChainComplex AddCommGrpCat.{u} ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((FormalCoproduct.mk I U).cech ⋙
      ((FormalCoproduct.eval.{u} (Opens X)
        (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
          (freeAbelianYonedaSheafFunctor X) ⋙ sheafStalkFunctor X x))

private structure FreeCechStalkData {X : TopCat.{u}} {I : Type u}
    (U : I → Opens X) (j : I) (x : X) (hx : x ∈ U j) where
  Kloc : ChainComplex AddCommGrpCat.{u} ℕ
  comparison : Kloc ⟶ freeAbelianCechStalkComplex U x
  exactAt_succ (n : ℕ) : Kloc.ExactAt (n + 1)
  isIso (n : ℕ) : IsIso (comparison.f n)

private noncomputable def freeCechStalkData {X : TopCat.{u}} {I : Type u}
    (U : I → Opens X) (j : I) (x : X) (hx : x ∈ U j) :
    FreeCechStalkData U j x hx := by
  let D := U j
  let Uj : I → Set.Iic D := fun i ↦ ⟨U i ⊓ D, by
    show U i ⊓ D ≤ D
    exact inf_le_right⟩
  letI : HasTerminal (Set.Iic D) := TopologicalSpace.Opens.iicHasTerminal' D
  letI : HasBinaryProducts (Set.Iic D) :=
    TopologicalSpace.Opens.iicHasBinaryProducts' D
  letI : HasFiniteProducts (Set.Iic D) :=
    TopologicalSpace.Opens.iicHasFiniteProducts' D
  let T : Set.Iic D := ⟨D, by exact le_refl D⟩
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun V ↦ homOfLE V.2) (fun _ _ ↦ Subsingleton.elim _ _)
  let d : T ⟶ Uj j := homOfLE (le_inf le_rfl le_rfl)
  let V := FormalCoproduct.mk I U
  let Vj := FormalCoproduct.mk I Uj
  let Xj := Vj.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl T hT)
  let edj : Xj.ExtraDegeneracy := Vj.extraDegeneracyCech hT d
  let F := iicIncl' D
  let MF := FormalCoproduct.mapFunctor' F
  let Xloc := ((SimplicialObject.Augmented.whiskering _ _).obj MF).obj Xj
  let edloc : Xloc.ExtraDegeneracy := edj.map MF
  let Z := Xloc.left
  let zToV : Z ⟶ V.cech :=
    { app := fun n ↦
        { f := id
          φ := fun q ↦ Pi.lift fun a ↦
            F.map (Pi.π (Uj ∘ q) a) ≫ homOfLE inf_le_left }
      naturality := by
        intro n m θ
        apply FormalCoproduct.hom_ext
        · intro q
          subsingleton
        · rfl }
  let FS := freeAbelianYonedaSheafFunctor X
  let Gs := (FormalCoproduct.eval.{u} (Opens X)
    (TopCat.Sheaf AddCommGrpCat.{u} X)).obj FS
  let H := sheafStalkFunctor X x
  let G := Gs ⋙ H
  let Y := V.cech ⋙ G
  let Yloc := Z ⋙ G
  let α : Yloc ⟶ Y := Functor.whiskerRight zToV G
  let K := AlgebraicTopology.AlternatingFaceMapComplex.obj Y
  let Kloc := AlgebraicTopology.AlternatingFaceMapComplex.obj Yloc
  let κ : Kloc ⟶ K := (AlgebraicTopology.alternatingFaceMapComplex
    AddCommGrpCat.{u}).map α
  change Kloc ⟶ freeAbelianCechStalkComplex U x at κ
  have hloc (n : ℕ) : Kloc.ExactAt (n + 1) := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (((SimplicialObject.whiskering _ _).obj G).obj Z)).ExactAt (n + 1)
    let edG : (((SimplicialObject.Augmented.whiskering _ _).obj G).obj Xloc).ExtraDegeneracy :=
      edloc.map G
    let qiso := edG.homotopyEquiv.hom
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (((SimplicialObject.whiskering _ _).obj G).obj Z)) ⟶ _ at qiso
    rw [exactAt_iff_of_quasiIsoAt qiso (n + 1)]
    exact ChainComplex.exactAt_succ_single_obj _ _
  have hκ (m : ℕ) : IsIso (κ.f m) := by
    change IsIso (G.map (zToV.app (op ⦋m⦌)))
    change IsIso (H.map (Gs.map (zToV.app (op ⦋m⦌))))
    let Q := Fin (m + 1) → I
    let A : Q → TopCat.Sheaf AddCommGrpCat.{u} X := fun q ↦
      FS.obj ((Z.obj (op ⦋m⦌)).obj q)
    let B : Q → TopCat.Sheaf AddCommGrpCat.{u} X := fun q ↦
      FS.obj ((V.cech.obj (op ⦋m⦌)).obj q)
    let p (q : Q) : A q ⟶ B q := FS.map ((zToV.app (op ⦋m⦌)).φ q)
    have hp (q : Q) : IsIso (H.map (p q)) := by
      let L : Opens X := (Z.obj (op ⦋m⦌)).obj q
      let O : Opens X := (V.cech.obj (op ⦋m⦌)).obj q
      let r : L ⟶ O := (zToV.app (op ⦋m⦌)).φ q
      by_cases hO : x ∈ O
      · have hL : x ∈ L := by
          let P : Set.Iic D := ⟨O ⊓ D, by
            show O ⊓ D ≤ D
            exact inf_le_right⟩
          let s : P ⟶ ∏ᶜ (Uj ∘ q) := Pi.lift fun a ↦ homOfLE
            (le_inf (inf_le_left.trans (leOfHom (Pi.π (U ∘ q) a))) inf_le_right)
          exact leOfHom (F.map s) ⟨hO, hx⟩
        change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (freeAbelianYonedaSheafMap r).hom)
        exact freeAbelianYonedaSheafMap_stalk_isIso r x hL
      · have hL : x ∉ L := fun h ↦ hO (leOfHom r h)
        have hzL := freeAbelianYonedaSheaf_stalk_isZero_of_not_mem L x hL
        have hzO := freeAbelianYonedaSheaf_stalk_isZero_of_not_mem O x hO
        exact hzL.isIso hzO _
    letI (q : Q) : IsIso (H.map (p q)) := hp q
    letI : PreservesColimitsOfShape (Discrete Q) H := by
      dsimp [H, sheafStalkFunctor]
      infer_instance
    have heval : Gs.map (zToV.app (op ⦋m⦌)) = Limits.Sigma.map p := by
      dsimp only [Gs]
      change (Limits.Sigma.desc fun q ↦ p q ≫ Limits.Sigma.ι B q) =
        Limits.Sigma.map p
      apply Limits.Sigma.hom_ext
      intro q
      exact (Limits.Sigma.ι_desc
        (fun q ↦ p q ≫ Limits.Sigma.ι B q) q).trans
          (Limits.Sigma.ι_map p q).symm
    rw [heval]
    exact map_sigma_isIso_of_map_isIso H p
  exact
    { Kloc := Kloc
      comparison := κ
      exactAt_succ := hloc
      isIso := hκ }

private lemma freeAbelianCechStalkComplex_exactAt_succ_of_mem
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (j : I) (x : X) (hx : x ∈ U j) (n : ℕ) :
    (freeAbelianCechStalkComplex U x).ExactAt (n + 1) := by
  let D := freeCechStalkData U j x hx
  letI (m : ℕ) : IsIso (D.comparison.f m) := D.isIso m
  haveI : IsIso D.comparison := HomologicalComplex.Hom.isIso_of_components D.comparison
  rw [← exactAt_iff_of_quasiIsoAt D.comparison (n + 1)]
  exact D.exactAt_succ n

private noncomputable def freeAbelianCechChainComplexMapStalkIso
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (x : X) :
    ((sheafStalkFunctor X x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (freeAbelianCechChainComplex U) ≅ freeAbelianCechStalkComplex U x := by
  let H := sheafStalkFunctor X x
  let Y := (FormalCoproduct.mk I U).cech ⋙
    (FormalCoproduct.eval.{u} (Opens X)
      (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
        (freeAbelianYonedaSheafFunctor X)
  change ((AlgebraicTopology.alternatingFaceMapComplex
    (TopCat.Sheaf AddCommGrpCat.{u} X) ⋙
      H.mapHomologicalComplex (ComplexShape.down ℕ)).obj Y) ≅ _
  rw [AlgebraicTopology.map_alternatingFaceMapComplex H]
  exact Iso.refl _

private lemma freeAbelianCechStalkComplex_isZero_X_of_not_mem
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (x : X)
    (hx : ∀ i, x ∉ U i) (n : ℕ) :
    IsZero ((freeAbelianCechStalkComplex U x).X n) := by
  let Q := Fin (n + 1) → I
  let S : Q → TopCat.Sheaf AddCommGrpCat.{u} X := fun q ↦
    freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
      (((Limits.FormalCoproduct.mk I U).cech.obj
        (Opposite.op (SimplexCategory.mk n))).obj q)
  let H := sheafStalkFunctor X x
  dsimp [freeAbelianCechStalkComplex,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_X,
    Limits.FormalCoproduct.eval]
  change IsZero (H.obj (∐ S))
  have hSq (q : Q) : IsZero (H.obj (S q)) := by
    apply freeAbelianYonedaSheaf_stalk_isZero_of_not_mem _ x
    intro hxq
    exact hx (q 0) (leOfHom (Limits.Pi.π (U ∘ q) 0) hxq)
  have hSigma : IsZero (∐ fun q ↦ H.obj (S q)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Limits.Sigma.hom_ext
    intro q
    exact (hSq q).eq_of_src _ _
  letI : PreservesColimitsOfShape (Discrete Q) H := by
    dsimp [H, sheafStalkFunctor]
    infer_instance
  let D := Discrete.functor S
  let e : H.obj (∐ S) ≅ ∐ fun q ↦ H.obj (S q) :=
    H.mapIso (Limits.Sigma.isoColimit D) ≪≫
      preservesColimitIso H D ≪≫
      (Limits.Sigma.isoColimit (D ⋙ H)).symm
  exact IsZero.of_iso hSigma e

private lemma freeAbelianCechStalkComplex_exactAt_succ
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (x : X) (n : ℕ) :
    (freeAbelianCechStalkComplex U x).ExactAt (n + 1) := by
  by_cases h : ∃ i, x ∈ U i
  · obtain ⟨i, hi⟩ := h
    exact freeAbelianCechStalkComplex_exactAt_succ_of_mem U i x hi n
  · apply HomologicalComplex.ExactAt.of_isZero
    exact freeAbelianCechStalkComplex_isZero_X_of_not_mem U x
      (by simpa only [not_exists] using h) (n + 1)

private lemma freeAbelianCechChainComplex_exactAt_succ_of_pointwise_cover
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (freeAbelianCechChainComplex U).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  obtain ⟨j, hx⟩ := hU x
  let H := sheafStalkFunctor X x
  have hs := freeAbelianCechStalkComplex_exactAt_succ_of_mem U j x hx n
  have hmapped := hs.of_iso (freeAbelianCechChainComplexMapStalkIso U x).symm
  change (((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (freeAbelianCechChainComplex U)).sc (n + 1)).Exact
  exact hmapped

private lemma freeAbelianCechChainComplex_exactAt_succ
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (n : ℕ) :
    (freeAbelianCechChainComplex U).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  let H := sheafStalkFunctor X x
  have hs := freeAbelianCechStalkComplex_exactAt_succ U x n
  have hmapped := hs.of_iso (freeAbelianCechChainComplexMapStalkIso U x).symm
  change (((H.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (freeAbelianCechChainComplex U)).sc (n + 1)).Exact
  exact hmapped

private lemma pointwise_cover_of_coversTop
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U) :
    ∀ x : X, ∃ i, x ∈ U i := by
  intro x
  obtain ⟨W, iW, ⟨i, ⟨g⟩⟩, hxW⟩ := hU (⊤ : Opens X) x (by simp)
  exact ⟨i, leOfHom g hxW⟩

private lemma freeAbelianCechChainComplex_exactAt_succ_of_coversTop
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U) (n : ℕ) :
    (freeAbelianCechChainComplex U).ExactAt (n + 1) :=
  freeAbelianCechChainComplex_exactAt_succ_of_pointwise_cover U
    (pointwise_cover_of_coversTop U hU) n

private noncomputable abbrev freeCechIntersection
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X) (n : ℕ)
    (q : Fin (n + 1) → I) : Opens X :=
  ∏ᶜ fun a ↦ U (q a)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sigmaHomAddEquiv
    {X : TopCat.{u}} {Q : Type u}
    (S : Q → TopCat.Sheaf AddCommGrpCat.{u} X)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) (T : Q → AddCommGrpCat.{u})
    [HasCoproduct S] [HasProduct T]
    (e : ∀ q, (S q ⟶ A) ≃+ ToType (T q)) :
    ((∐ S) ⟶ A) ≃+ ToType (∏ᶜ T : AddCommGrpCat.{u}) := by
  let eT := Limits.Concrete.productEquiv T
  refine
    { toFun := fun f ↦ eT.symm (fun q ↦ e q (Limits.Sigma.ι S q ≫ f))
      invFun := fun s ↦ Limits.Sigma.desc fun q ↦ (e q).symm (eT s q)
      left_inv := fun f ↦ by
        apply Limits.Sigma.hom_ext
        intro q
        rw [Limits.Sigma.ι_desc]
        apply (e q).injective
        rw [AddEquiv.apply_symm_apply]
        exact congrFun (eT.apply_symm_apply _) q
      right_inv := fun s ↦ by
        apply eT.injective
        rw [eT.apply_symm_apply]
        funext q
        rw [Limits.Sigma.ι_desc]
        exact AddEquiv.apply_symm_apply _ _
      map_add' := fun f g ↦ by
        apply eT.injective
        rw [eT.apply_symm_apply]
        funext q
        rw [Limits.Concrete.productEquiv_apply_apply]
        simp only [Preadditive.comp_add, _root_.map_add]
        rw [Limits.Concrete.productEquiv_symm_apply_π,
          Limits.Concrete.productEquiv_symm_apply_π] }

private lemma sigmaHomAddEquiv_apply
    {X : TopCat.{u}} {Q : Type u}
    (S : Q → TopCat.Sheaf AddCommGrpCat.{u} X)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) (T : Q → AddCommGrpCat.{u})
    [HasCoproduct S] [HasProduct T]
    (e : ∀ q, (S q ⟶ A) ≃+ ToType (T q))
    (f : (∐ S) ⟶ A) (q : Q) :
    (Limits.Concrete.productEquiv T) (sigmaHomAddEquiv S A T e f) q =
      e q (Limits.Sigma.ι S q ≫ f) := by
  exact congrFun (Equiv.apply_symm_apply _ _) q

private lemma comp_sum_comp
    {C : Type*} [Category C] [Preadditive C] {W X Y Z : C}
    {Q : Type*} [Fintype Q] (a : W ⟶ X) (b : Q → (X ⟶ Y))
    (c : Y ⟶ Z) (z : Q → ℤ) :
    a ≫ (∑ i, z i • b i) ≫ c = ∑ i, z i • (a ≫ b i ≫ c) := by
  rw [← Category.assoc, Preadditive.comp_sum Finset.univ,
    Preadditive.sum_comp Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]

private lemma addCommGrpCat_sum_zsmul_apply
    {M N : AddCommGrpCat.{u}} {Q : Type*} [Fintype Q]
    (z : Q → ℤ) (f : Q → (M ⟶ N)) (x : M) :
    (∑ i, z i • f i) x = ∑ i, z i • f i x := by
  change (AddCommGrpCat.homAddEquiv (∑ i, z i • f i)) x = _
  rw [_root_.map_sum, AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_zsmul]
  rfl

private lemma eval_ι_map
    {C D : Type*} [Category C] [Category D] [HasCoproducts D]
    (F : C ⥤ D) {V W : Limits.FormalCoproduct C} (m : V ⟶ W)
    (q : V.I) :
    Limits.Sigma.ι (fun i ↦ F.obj (V.obj i)) q ≫
        ((Limits.FormalCoproduct.eval C D).obj F).map m =
      F.map (m.φ q) ≫
        Limits.Sigma.ι (fun i ↦ F.obj (W.obj i)) (m.f q) := by
  rw [Limits.FormalCoproduct.eval_obj_map]
  change Limits.Sigma.ι (fun i ↦ F.obj (V.obj i)) q ≫
      Limits.Sigma.desc (fun i ↦ F.map (m.φ i) ≫
        Limits.Sigma.ι (fun j ↦ F.obj (W.obj j)) (m.f i)) = _
  rw [Limits.Sigma.ι_desc]

private lemma evalOp_map_π
    {C D : Type*} [Category C] [Category D] [HasProducts D]
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

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeAbelianCechChainHomAddEquiv
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((freeAbelianCechChainComplex U).X n ⟶ A) ≃+
      ((cechComplexFunctor U).obj A.obj).X n := by
  let Q := Fin (n + 1) → I
  let S : Q → TopCat.Sheaf AddCommGrpCat.{u} X := fun q ↦
    freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
      (freeCechIntersection U n q)
  let T : Q → AddCommGrpCat.{u} := fun q ↦
    A.obj.obj (op (freeCechIntersection U n q))
  change ((∐ S) ⟶ A) ≃+ ToType (∏ᶜ T : AddCommGrpCat.{u})
  exact sigmaHomAddEquiv S A T fun q ↦
    freeAbelianYonedaSheafHomAddEquiv (freeCechIntersection U n q) A

set_option backward.isDefEq.respectTransparency false in
private lemma freeAbelianCechChainHomAddEquiv_d
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (f : (freeAbelianCechChainComplex U).X n ⟶ A) :
    freeAbelianCechChainHomAddEquiv U A (n + 1)
        ((freeAbelianCechChainComplex U).d (n + 1) n ≫ f) =
      ((cechComplexFunctor U).obj A.obj).d n (n + 1)
        (freeAbelianCechChainHomAddEquiv U A n f) := by
  dsimp only [freeAbelianCechChainHomAddEquiv]
  apply (Limits.Concrete.productEquiv (fun q : Fin (n + 2) → I ↦
    A.obj.obj (op (freeCechIntersection U (n + 1) q)))).injective
  funext q
  simp only [id_eq]
  refine (sigmaHomAddEquiv_apply
    (fun q : Fin (n + 2) → I ↦
      freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
        (freeCechIntersection U (n + 1) q)) A
    (fun q : Fin (n + 2) → I ↦
      A.obj.obj (op (freeCechIntersection U (n + 1) q)))
    (fun q ↦ freeAbelianYonedaSheafHomAddEquiv
      (freeCechIntersection U (n + 1) q) A)
    ((freeAbelianCechChainComplex U).d (n + 1) n ≫ f) q).trans ?_
  rw [Limits.Concrete.productEquiv_apply_apply]
  let Y : SimplicialObject (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    (Limits.FormalCoproduct.mk I U).cech ⋙
    (Limits.FormalCoproduct.eval.{u} (Opens X)
      (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
        (freeAbelianYonedaSheafFunctor X)
  let Z := (Limits.FormalCoproduct.cosimplicialObjectFunctor
    (Limits.FormalCoproduct.mk I U).cech).obj A.obj
  have hkd : (freeAbelianCechChainComplex U).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Y.δ i := by
    exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq Y n
  have hd : ((cechComplexFunctor U).obj A.obj).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Z.δ i := by
    change (AlgebraicTopology.AlternatingCofaceMapComplex.obj Z).d n (n + 1) = _
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  rw [hkd, hd]
  let S₁ : (Fin (n + 2) → I) → TopCat.Sheaf AddCommGrpCat.{u} X := fun q ↦
    freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
      (freeCechIntersection U (n + 1) q)
  let T₁ : (Fin (n + 2) → I) → AddCommGrpCat.{u} := fun q ↦
    A.obj.obj (op (freeCechIntersection U (n + 1) q))
  have hsum : Limits.Sigma.ι S₁ q ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Y.δ i) ≫ f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (Limits.Sigma.ι S₁ q ≫ Y.δ i ≫ f) := by
    exact comp_sum_comp (Limits.Sigma.ι S₁ q) (fun i ↦ Y.δ i) f
      (fun i ↦ (-1 : ℤ) ^ (i : ℕ))
  rw [hsum, _root_.map_sum]
  simp only [_root_.map_zsmul]
  have hright :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Z.δ i) ≫
          Limits.Pi.π T₁ q =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Z.δ i ≫ Limits.Pi.π T₁ q) := by
    rw [Preadditive.sum_comp Finset.univ]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Preadditive.zsmul_comp]
  change _ = ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Z.δ i) ≫
    Limits.Pi.π T₁ q) ((sigmaHomAddEquiv
      (fun q : Fin (n + 1) → I ↦
        freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
          (freeCechIntersection U n q)) A
      (fun q : Fin (n + 1) → I ↦
        A.obj.obj (op (freeCechIntersection U n q)))
      (fun q ↦ freeAbelianYonedaSheafHomAddEquiv
        (freeCechIntersection U n q) A)) f)
  rw [hright]
  let s := (sigmaHomAddEquiv
    (fun q : Fin (n + 1) → I ↦
      freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
        (freeCechIntersection U n q)) A
    (fun q : Fin (n + 1) → I ↦
      A.obj.obj (op (freeCechIntersection U n q)))
    (fun q ↦ freeAbelianYonedaSheafHomAddEquiv
      (freeCechIntersection U n q) A)) f
  change _ = (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    (Z.δ i ≫ Limits.Pi.π T₁ q)) s
  rw [addCommGrpCat_sum_zsmul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  let V := Limits.FormalCoproduct.mk I U
  let m := V.cech.map (SimplexCategory.δ i).op
  let FS := freeAbelianYonedaSheafFunctor X
  have hYraw := eval_ι_map FS m q
  have hZraw := evalOp_map_π A.obj m q
  have hY : Limits.Sigma.ι S₁ q ≫ Y.δ i =
      FS.map (m.φ q) ≫ Limits.Sigma.ι
        (fun r ↦ FS.obj ((V.cech.obj (op ⦋n⦌)).obj r)) (m.f q) := by
    exact hYraw
  have hZ : Z.δ i ≫ Limits.Pi.π T₁ q =
      Limits.Pi.π
          (fun r ↦ A.obj.obj (op ((V.cech.obj (op ⦋n⦌)).obj r))) (m.f q) ≫
        A.obj.map (m.φ q).op := by
    exact hZraw
  rw [← Category.assoc, hY, Category.assoc, hZ]
  have hpre := freeAbelianYonedaSheafHomAddEquiv_precomp' (m.φ q) A
    (Limits.Sigma.ι
      (fun r ↦ FS.obj ((V.cech.obj (op ⦋n⦌)).obj r)) (m.f q) ≫ f)
  rw [show FS.map (m.φ q) =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        (Functor.whiskerRight (yoneda.map (m.φ q)) AddCommGrpCat.free) by rfl]
  have hpre' :
      (freeAbelianYonedaSheafHomAddEquiv (freeCechIntersection U (n + 1) q) A)
          ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
              (Functor.whiskerRight (yoneda.map (m.φ q)) AddCommGrpCat.free) ≫
            Limits.Sigma.ι
              (fun r ↦ FS.obj ((V.cech.obj (op ⦋n⦌)).obj r)) (m.f q) ≫ f) =
        A.obj.map (m.φ q).op
          ((freeAbelianYonedaSheafHomAddEquiv
              ((V.cech.obj (op ⦋n⦌)).obj (m.f q)) A)
            (Limits.Sigma.ι
              (fun r ↦ FS.obj ((V.cech.obj (op ⦋n⦌)).obj r)) (m.f q) ≫ f)) := by
    exact hpre
  rw [hpre']
  have hlower := sigmaHomAddEquiv_apply
    (fun q : Fin (n + 1) → I ↦
      freeAbelianYonedaSheaf (Opens.grothendieckTopology X)
        (freeCechIntersection U n q)) A
    (fun q : Fin (n + 1) → I ↦
      A.obj.obj (op (freeCechIntersection U n q)))
    (fun q ↦ freeAbelianYonedaSheafHomAddEquiv
      (freeCechIntersection U n q) A) f (m.f q)
  rw [Limits.Concrete.productEquiv_apply_apply] at hlower
  have hlower' :
      (freeAbelianYonedaSheafHomAddEquiv
          ((V.cech.obj (op ⦋n⦌)).obj (m.f q)) A)
        (Limits.Sigma.ι
          (fun r ↦ FS.obj ((V.cech.obj (op ⦋n⦌)).obj r)) (m.f q) ≫ f) =
      (Limits.Pi.π
        (fun r ↦ A.obj.obj (op ((V.cech.obj (op ⦋n⦌)).obj r))) (m.f q)) s := by
    symm
    exact hlower
  rw [hlower']
  rfl

/-- The Cech complex of an injective abelian sheaf on a topological space is exact in every
positive degree. -/
lemma cechComplex_exactAt_succ_of_injective
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective A] (n : ℕ) :
    ((cechComplexFunctor U).obj A.obj).ExactAt (n + 1) := by
  let K := freeAbelianCechChainComplex U
  let C := (cechComplexFunctor U).obj A.obj
  have hK : K.ExactAt (n + 1) :=
    freeAbelianCechChainComplex_exactAt_succ_of_coversTop U hU n
  have hK' : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1 hK
  rw [C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  let f : K.X (n + 1) ⟶ A :=
    (freeAbelianCechChainHomAddEquiv U A (n + 1)).symm x
  have hf : K.d (n + 2) (n + 1) ≫ f = 0 := by
    apply (freeAbelianCechChainHomAddEquiv U A (n + 2)).injective
    rw [freeAbelianCechChainHomAddEquiv_d]
    dsimp only [f]
    rw [AddEquiv.apply_symm_apply, map_zero]
    exact hx
  let g : K.X n ⟶ A := hK'.descToInjective f hf
  refine ⟨freeAbelianCechChainHomAddEquiv U A n g, ?_⟩
  change C.d n (n + 1) (freeAbelianCechChainHomAddEquiv U A n g) = x
  rw [← freeAbelianCechChainHomAddEquiv_d]
  dsimp only [g]
  have hcomp : (freeAbelianCechChainComplex U).d (n + 1) n ≫
      hK'.descToInjective f hf = f := by
    exact hK'.comp_descToInjective f hf
  rw [hcomp]
  exact AddEquiv.apply_symm_apply _ x

/-- The Cech complex of an injective abelian sheaf is exact in every positive degree for an
arbitrary family of opens. At a point outside the union all terms of the stalk complex vanish;
inside the union any member containing the point supplies the usual extra degeneracy. -/
lemma cechComplex_exactAt_succ_of_injective'
    {X : TopCat.{u}} {I : Type u} (U : I → Opens X)
    (A : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective A] (n : ℕ) :
    ((cechComplexFunctor U).obj A.obj).ExactAt (n + 1) := by
  let K := freeAbelianCechChainComplex U
  let C := (cechComplexFunctor U).obj A.obj
  have hK : K.ExactAt (n + 1) :=
    freeAbelianCechChainComplex_exactAt_succ U n
  have hK' : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1 hK
  rw [C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  let f : K.X (n + 1) ⟶ A :=
    (freeAbelianCechChainHomAddEquiv U A (n + 1)).symm x
  have hf : K.d (n + 2) (n + 1) ≫ f = 0 := by
    apply (freeAbelianCechChainHomAddEquiv U A (n + 2)).injective
    rw [freeAbelianCechChainHomAddEquiv_d]
    dsimp only [f]
    rw [AddEquiv.apply_symm_apply, map_zero]
    exact hx
  let g : K.X n ⟶ A := hK'.descToInjective f hf
  refine ⟨freeAbelianCechChainHomAddEquiv U A n g, ?_⟩
  change C.d n (n + 1) (freeAbelianCechChainHomAddEquiv U A n g) = x
  rw [← freeAbelianCechChainHomAddEquiv_d]
  dsimp only [g]
  have hcomp : (freeAbelianCechChainComplex U).d (n + 1) n ≫
      hK'.descToInjective f hf = f := by
    exact hK'.comp_descToInjective f hf
  rw [hcomp]
  exact AddEquiv.apply_symm_apply _ x

end CategoryTheory.Sheaf
