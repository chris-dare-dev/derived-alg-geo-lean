/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization

/-!
# Fixed-target arrows on affine basic opens

For a noetherian affine scheme, every arrow into the restriction of a fixed coherent sheaf
to `D(r)` extends from some coherent sheaf on the ambient affine scheme, up to an isomorphism
on its source. The proof transports the affine localization theorem across the coherent
pullback equivalence induced by `basicOpenIsoSpecAway r`.

This is an underived arrow theorem for one basic open. It does not assert that the extended
arrow is monic or construct a global extension across a quasi-compact open in a general scheme.
-/

open CategoryTheory AlgebraicGeometry

universe u₁ u₂ u₃ v₁ v₂ v₃

/-- A proof-local transport of fixed-target arrows through an equivalence on the codomain
and a natural isomorphism of the two composite functors. -/
private theorem fixedTargetArrowExtension_of_comp_equivalence
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) (H : B ⥤ C) (G : A ⥤ C)
    [H.IsEquivalence] (α : G ≅ F ⋙ H)
    (E : A) (hF : Subobject.FixedTargetArrowExtension F E) :
    Subobject.FixedTargetArrowExtension G E := by
  intro Z β
  let L : B := H.objPreimage Z
  let c : Z ≅ H.obj L := (H.objObjPreimageIso Z).symm
  let βH : H.obj L ⟶ H.obj (F.obj E) := c.inv ≫ β ≫ (α.app E).hom
  let βF : L ⟶ F.obj E := H.preimage βH
  obtain ⟨Y, f, d, hd⟩ := hF βF
  let z : Z ≅ G.obj Y := c ≪≫ H.mapIso d ≪≫ (α.app Y).symm
  refine ⟨Y, f, z, ?_⟩
  apply (cancel_mono (α.app E).hom).mp
  have hnat : G.map f ≫ (α.app E).hom =
      (α.app Y).hom ≫ (F ⋙ H).map f := α.hom.naturality f
  have h1 : β ≫ (α.app E).hom = c.hom ≫ H.map βF := by
    rw [H.map_preimage]
    dsimp [βH]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  have h2 : c.hom ≫ H.map βF =
      c.hom ≫ H.map (d.hom ≫ F.map f) := by rw [hd]
  let p : Z ⟶ (F ⋙ H).obj Y := c.hom ≫ H.map d.hom
  have h3 : c.hom ≫ H.map (d.hom ≫ F.map f) =
      p ≫ (F ⋙ H).map f := by
    dsimp [p]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hα : (α.app Y).inv ≫ G.map f ≫ (α.app E).hom =
      (F ⋙ H).map f := by
    rw [hnat]
    simp only [Iso.inv_hom_id_assoc]
  have h4 : p ≫ (F ⋙ H).map f =
      (z.hom ≫ G.map f) ≫ (α.app E).hom := by
    have hz : z.hom = p ≫ (α.app Y).inv := by
      dsimp [z, p]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc]
      rfl
    calc
      p ≫ (F ⋙ H).map f =
          p ≫ ((α.app Y).inv ≫ G.map f ≫ (α.app E).hom) :=
        congrArg (fun t => p ≫ t) hα.symm
      _ = (z.hom ≫ G.map f) ≫ (α.app E).hom := by
        rw [hz]
        simp only [Category.assoc]
  exact h1.trans (h2.trans (h3.trans h4))

namespace AlgebraicGeometry.Coh

/-- Fixed-target arrow extension for coherent sheaves along the actual basic-open immersion
`D(r) ↪ Spec R`. The target `E` stays fixed, and only the arrow's source is replaced by an
isomorphic coherent pullback. This is ordinary coherent pullback, not a derived arrow. -/
theorem fixedTargetArrowExtension_pullbackBasicOpen
    {R : CommRingCat.{u₁}} [IsNoetherianRing R]
    (r : R) (E : Coh (Spec R)) :
    Subobject.FixedTargetArrowExtension
      (pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))) E := by
  let e := basicOpenIsoSpecAway r
  let k := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let F := pullback k
  let H := pullback e.hom
  let G := pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))
  let α : G ≅ F ⋙ H := pullbackBasicOpenIsoSpecAway r
  letI : H.IsEquivalence := (pullbackEquivalence e).isEquivalence_functor
  have hF : Subobject.FixedTargetArrowExtension F E :=
    fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization
      (Submonoid.powers r) E
  change Subobject.FixedTargetArrowExtension G E
  exact fixedTargetArrowExtension_of_comp_equivalence F H G α E hF

end AlgebraicGeometry.Coh
