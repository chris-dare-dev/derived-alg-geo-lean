/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Naturality of the total-complex symmetry isomorphism

Mathlib constructs `HomologicalComplex₂.totalFlipIso`, identifying the total complex of a
flipped bicomplex with the total complex of the original, but states no naturality lemma for it.
Naturality is what a comparison argument needs when the bicomplex varies: a morphism of
bicomplexes induces morphisms of both total complexes, and the two identifications must agree.

The proof is the universal property of the total complex: both sides are determined by their
restrictions along the canonical inclusions `ιTotal`, on which the flip isomorphism is a signed
inclusion and the induced total map is componentwise.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]
    [K.HasTotal c] [L.HasTotal c] [DecidableEq J]

/-- The flip of a morphism of bicomplexes, with its source and target named as flips rather
than as values of `flipFunctor`. -/
noncomputable abbrev flipMap : K.flip ⟶ L.flip := (flipFunctor C c₁ c₂).map φ

/-- Instance bridging the two spellings of the flip: `flipFunctor` is a `def`, so a total-complex
instance stated for `M.flip` is not found for `(flipFunctor _ _ _).obj M` without this. -/
instance flipFunctor_hasTotal (M : HomologicalComplex₂ C c₁ c₂) [M.HasTotal c] :
    ((flipFunctor C c₁ c₂).obj M).HasTotal c :=
  inferInstanceAs (M.flip.HasTotal c)

set_option backward.isDefEq.respectTransparency false in
/-- The total-complex symmetry isomorphism commutes with morphisms of bicomplexes.

Both sides are determined by their restrictions along the canonical inclusions `ιTotal`, where
the flip is a signed inclusion and the induced total map is componentwise. -/
@[reassoc]
lemma totalFlipIso_naturality :
    total.map (flipMap φ) c ≫ (L.totalFlipIso c).hom =
      (K.totalFlipIso c).hom ≫ total.map φ c := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply total.hom_ext
  intro i₂ i₁ h
  simp only [HomologicalComplex.comp_f, totalFlipIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [← Category.assoc, ιTotal_map, Category.assoc]
  dsimp only [totalFlipIsoX]
  rw [ι_totalDesc, ι_totalDesc_assoc]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, ιTotal_map]
  rfl

/-- Inverse form of `totalFlipIso_naturality`. -/
@[reassoc]
lemma totalFlipIso_inv_naturality :
    total.map φ c ≫ (L.totalFlipIso c).inv =
      (K.totalFlipIso c).inv ≫ total.map (flipMap φ) c := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    totalFlipIso_naturality]

end HomologicalComplex₂
