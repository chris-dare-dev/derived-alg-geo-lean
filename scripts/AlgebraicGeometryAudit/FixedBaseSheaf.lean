import DerivedAlgGeo.AlgebraicGeometry.Modules.FixedBaseSheaf

/-! # SF11 fixed-base-ring sheaf and two-open limit audit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

#print axioms AlgebraicGeometry.modulesToFixedBaseSheaf
#print axioms AlgebraicGeometry.modulesToFixedBaseSheaf_smul
#print axioms AlgebraicGeometry.fixedBaseSectionsFunctor
#print axioms AlgebraicGeometry.fixedBaseSectionsTwoOpenLimit

-- No affineness or finiteness hypothesis is needed for the underived sheaf
-- pullback cone over a fixed base ring.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) :
    IsLimit (TopCat.Sheaf.interUnionPullbackCone
      ((modulesToFixedBaseSheaf Y φ).obj M) U V) :=
  fixedBaseSectionsTwoOpenLimit Y φ M U V

-- Evaluating the sections functor is definitionally evaluation of the
-- fixed-base sheaf, with its R-module action.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U : Y.Opens) :
    (fixedBaseSectionsFunctor Y φ U).obj M =
      ((modulesToFixedBaseSheaf Y φ).obj M).presheaf.obj (.op U) :=
  rfl

-- The new sheaf has the original section carriers and restriction maps.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U : Y.Opens) :
    (↑(((modulesToFixedBaseSheaf Y φ).obj M).presheaf.obj (.op U)) : Type u) =
      Γ(M, U) :=
  rfl

example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) {U V : Y.Opens} (h : U ≤ V) (x : Γ(M, V)) :
    (((modulesToFixedBaseSheaf Y φ).obj M).presheaf.map (homOfLE h).op).hom x =
      M.presheaf.map (homOfLE h).op x :=
  rfl

-- The fixed-base action is the structure-sheaf action after restricting φ(r)
-- from Y to the chosen open.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U : Y.Opens) (r : R)
    (x : ((modulesToFixedBaseSheaf Y φ).obj M).presheaf.obj (.op U)) :
    r • x = (M.smul (Y.presheaf.map U.leTop.op (φ.hom r))).hom x :=
  rfl

-- The point and legs of the fixed-ring pullback cone are the original
-- sections and restriction maps on the union and its two members.
example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) :
    (↑(TopCat.Sheaf.interUnionPullbackCone
      ((modulesToFixedBaseSheaf Y φ).obj M) U V).pt : Type u) = Γ(M, U ⊔ V) :=
  rfl

example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) (x : Γ(M, U ⊔ V)) :
    (TopCat.Sheaf.interUnionPullbackCone
      ((modulesToFixedBaseSheaf Y φ).obj M) U V).fst.hom x =
        M.presheaf.map (homOfLE le_sup_left).op x :=
  rfl

example {R : CommRingCat.{u}} (Y : Scheme.{u}) (φ : R ⟶ Γ(Y, ⊤))
    (M : Y.Modules) (U V : Y.Opens) (x : Γ(M, U ⊔ V)) :
    (TopCat.Sheaf.interUnionPullbackCone
      ((modulesToFixedBaseSheaf Y φ).obj M) U V).snd.hom x =
        M.presheaf.map (homOfLE le_sup_right).op x :=
  rfl
