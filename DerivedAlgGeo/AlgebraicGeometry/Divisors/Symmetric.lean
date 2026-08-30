/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# Symmetry of the tensor product on invertible sheaves

The presheaf braiding descends through module sheafification. Naturality and both hexagon
identities reduce to the corresponding symmetric-monoidal identities for presheaves; the reverse
hexagon is obtained from the forward hexagon using involutivity of the commutor.
-/

open CategoryTheory MonoidalCategory BraidedCategory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

local instance : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

lemma tensorCommIso_naturality
    {L₁ L₂ M₁ M₂ : X.Modules} (f : L₁ ⟶ L₂) (g : M₁ ⟶ M₂) :
    tensorHom f g ≫ (tensorCommIso L₂ M₂).hom =
      (tensorCommIso L₁ M₁).hom ≫ tensorHom g f := by
  dsimp [tensorHom, tensorCommIso]
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map f ⊗ₘ (toPresheafOfModules X).map g) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (β_ ((toPresheafOfModules X).obj L₂) ((toPresheafOfModules X).obj M₂)).hom =
    (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (β_ ((toPresheafOfModules X).obj L₁) ((toPresheafOfModules X).obj M₁)).hom ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          ((toPresheafOfModules X).map g ⊗ₘ (toPresheafOfModules X).map f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact BraidedCategory.braiding_naturality
    ((toPresheafOfModules X).map f) ((toPresheafOfModules X).map g)

private lemma tensorHexagonForward (L M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N)] :
    (tensorAssocIso L M N).hom ≫
        (tensorCommIso L (tensorObj M N)).hom ≫
          (tensorAssocIso M N L).hom =
      tensorHom (tensorCommIso L M).hom (𝟙 N) ≫
        (tensorAssocIso M L N).hom ≫
          tensorHom (𝟙 M) (tensorCommIso L N).hom := by
  let A := (toPresheafOfModules X).obj L
  let B := (toPresheafOfModules X).obj M
  let C := (toPresheafOfModules X).obj N
  let r₀ := tensorSheafificationComparisonRight (A ⊗ B) N
  let l₀ := tensorSheafificationComparisonLeft L (B ⊗ C)
  let r₁ := tensorSheafificationComparisonRight (B ⊗ C) L
  let l₁ := tensorSheafificationComparisonLeft M (C ⊗ A)
  let r₂ := tensorSheafificationComparisonRight (B ⊗ A) N
  let l₂ := tensorSheafificationComparisonLeft M (A ⊗ C)
  haveI : IsIso r₀ := by dsimp only [r₀]; infer_instance
  haveI : IsIso l₁ := by dsimp only [l₁]; infer_instance
  rw [← cancel_epi r₀, ← cancel_mono (inv l₁)]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [tensorSheafificationComparisonRight_comp_tensorAssocIso L M N]
  let ηBC := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (B ⊗ C)
  have hBraiding := BraidedCategory.braiding_naturality (𝟙 A) ηBC
  change (𝟙 A ⊗ₘ ηBC) ≫
      (β_ A ((toPresheafOfModules X).obj (tensorObj M N))).hom =
    (β_ A (B ⊗ C)).hom ≫ (ηBC ⊗ₘ 𝟙 A) at hBraiding
  slice_lhs 2 3 =>
    change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 A ⊗ₘ ηBC) ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (β_ A ((toPresheafOfModules X).obj (tensorObj M N))).hom
    rw [← Functor.map_comp, hBraiding, Functor.map_comp]
  have hr₁ : r₁ = (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (ηBC ⊗ₘ 𝟙 A) := by rfl
  slice_lhs 3 4 =>
    rw [← hr₁, tensorSheafificationComparisonRight_comp_tensorAssocIso M N L]
  slice_lhs 4 5 =>
    change l₁ ≫ inv l₁
    rw [IsIso.hom_inv_id]
  let ηAB := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (A ⊗ B)
  have hR := tensorSheafificationComparisonRight_naturality (X := X)
    (f := (β_ A B).hom) (g := 𝟙 N)
  rw [(toPresheafOfModules X).map_id] at hR
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map ((β_ A B).hom ⊗ₘ 𝟙 C) ≫
      r₂ = r₀ ≫ tensorHom (tensorCommIso L M).hom (𝟙 N) at hR
  slice_rhs 1 2 => rw [← hR]
  slice_rhs 2 3 => rw [tensorSheafificationComparisonRight_comp_tensorAssocIso M L N]
  have hL := tensorSheafificationComparisonLeft_naturality (X := X)
    (𝟙 M) (β_ A C).hom
  rw [(toPresheafOfModules X).map_id] at hL
  change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map (𝟙 B ⊗ₘ (β_ A C).hom) ≫
      l₁ = l₂ ≫ tensorHom (𝟙 M) (tensorCommIso L N).hom at hL
  slice_rhs 3 4 => rw [← hL]
  slice_rhs 4 5 =>
    change l₁ ≫ inv l₁
    rw [IsIso.hom_inv_id]
  rw [Category.comp_id, Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1
  exact BraidedCategory.hexagon_forward A B C

private noncomputable def tensorIso
    {L₁ L₂ M₁ M₂ : X.Modules} (e : L₁ ≅ L₂) (f : M₁ ≅ M₂) :
    tensorObj L₁ M₁ ≅ tensorObj L₂ M₂ where
  hom := tensorHom e.hom f.hom
  inv := tensorHom e.inv f.inv
  hom_inv_id := by
    rw [tensorHom_comp_tensorHom, e.hom_inv_id, f.hom_inv_id,
      tensorHom_id_id]
  inv_hom_id := by
    rw [tensorHom_comp_tensorHom, e.inv_hom_id, f.inv_hom_id,
      tensorHom_id_id]

lemma tensorCommIso_symmetry (L M : X.Modules) :
    (tensorCommIso L M).hom ≫ (tensorCommIso M L).hom =
      𝟙 (tensorObj L M) := by
  dsimp [tensorCommIso]
  change (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (β_ ((toPresheafOfModules X).obj L) ((toPresheafOfModules X).obj M)).hom ≫
    (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map
        (β_ ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj L)).hom = 𝟙 _
  rw [← Functor.map_comp, SymmetricCategory.symmetry]
  exact (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).map_id _

lemma tensorCommIso_inv (L M : X.Modules) :
    (tensorCommIso L M).inv = (tensorCommIso M L).hom := by
  rw [← cancel_epi (tensorCommIso L M).hom]
  rw [Iso.hom_inv_id, tensorCommIso_symmetry]

private lemma tensorHexagonReverse (L M N : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from N)] :
    (tensorAssocIso L M N).inv ≫
        (tensorCommIso (tensorObj L M) N).hom ≫
          (tensorAssocIso N L M).inv =
      tensorHom (𝟙 L) (tensorCommIso M N).hom ≫
        (tensorAssocIso L N M).inv ≫
          tensorHom (tensorCommIso L N).hom (𝟙 M) := by
  let p : tensorObj (tensorObj N L) M ≅ tensorObj L (tensorObj M N) :=
    tensorAssocIso N L M ≪≫ tensorCommIso N (tensorObj L M) ≪≫
      tensorAssocIso L M N
  let q : tensorObj (tensorObj N L) M ≅ tensorObj L (tensorObj M N) :=
    tensorIso (tensorCommIso N L) (Iso.refl M) ≪≫
      tensorAssocIso L N M ≪≫
        tensorIso (Iso.refl L) (tensorCommIso N M)
  have hpq : p = q := Iso.ext (tensorHexagonForward N L M)
  have hinv := congrArg Iso.inv hpq
  change (tensorAssocIso L M N).inv ≫
        (tensorCommIso N (tensorObj L M)).inv ≫
          (tensorAssocIso N L M).inv =
      tensorHom (𝟙 L) (tensorCommIso N M).inv ≫
        (tensorAssocIso L N M).inv ≫
          tensorHom (tensorCommIso N L).inv (𝟙 M) at hinv
  rw [tensorCommIso_inv N (tensorObj L M),
    tensorCommIso_inv N M, tensorCommIso_inv N L] at hinv
  exact hinv

noncomputable instance invertibleSheafBraidedCategory : BraidedCategory (InvertibleSheaf X) where
  braiding L M := (isInvertible X).isoMk (tensorCommIso L.1 M.1)
  braiding_naturality_right := by
    intro L M N f
    apply ObjectProperty.hom_ext
    exact tensorCommIso_naturality (𝟙 L.1) f.hom
  braiding_naturality_left := by
    intro L M f N
    apply ObjectProperty.hom_ext
    exact tensorCommIso_naturality f.hom (𝟙 N.1)
  hexagon_forward := by
    intro L M N
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from L.1) := L.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from M.1) := M.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from N.1) := N.2
    apply ObjectProperty.hom_ext
    change (tensorAssocIso L.1 M.1 N.1).hom ≫
        (tensorCommIso L.1 (tensorObj M.1 N.1)).hom ≫
          (tensorAssocIso M.1 N.1 L.1).hom =
      tensorHom (tensorCommIso L.1 M.1).hom (𝟙 N.1) ≫
        (tensorAssocIso M.1 L.1 N.1).hom ≫
          tensorHom (𝟙 M.1) (tensorCommIso L.1 N.1).hom
    exact tensorHexagonForward L.1 M.1 N.1
  hexagon_reverse := by
    intro L M N
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from L.1) := L.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from M.1) := M.2
    letI : SheafOfModules.IsInvertible.{u, u, u}
        (show SheafOfModules X.ringCatSheaf from N.1) := N.2
    apply ObjectProperty.hom_ext
    change (tensorAssocIso L.1 M.1 N.1).inv ≫
        (tensorCommIso (tensorObj L.1 M.1) N.1).hom ≫
          (tensorAssocIso N.1 L.1 M.1).inv =
      tensorHom (𝟙 L.1) (tensorCommIso M.1 N.1).hom ≫
        (tensorAssocIso L.1 N.1 M.1).inv ≫
          tensorHom (tensorCommIso L.1 N.1).hom (𝟙 M.1)
    exact tensorHexagonReverse L.1 M.1 N.1

noncomputable instance invertibleSheafSymmetricCategory : SymmetricCategory (InvertibleSheaf X) where
  symmetry := by
    intro L M
    apply ObjectProperty.hom_ext
    change (tensorCommIso L.1 M.1).hom ≫
      (tensorCommIso M.1 L.1).hom = 𝟙 (tensorObj L.1 M.1)
    dsimp [tensorCommIso]
    change (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (β_ ((toPresheafOfModules X).obj L.1) ((toPresheafOfModules X).obj M.1)).hom ≫
      (PresheafOfModules.sheafification
        (𝟙 X.ringCatSheaf.obj)).map
          (β_ ((toPresheafOfModules X).obj M.1) ((toPresheafOfModules X).obj L.1)).hom =
      𝟙 _
    rw [← Functor.map_comp]
    rw [SymmetricCategory.symmetry]
    exact (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map_id _

end

end AlgebraicGeometry.Scheme.Modules
