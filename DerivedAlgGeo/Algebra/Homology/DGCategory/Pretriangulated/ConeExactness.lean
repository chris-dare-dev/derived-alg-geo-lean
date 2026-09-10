/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone

/-!
# A cone functor preserves shifts

`DGFunctor.PreservesShifts` and `PreservesChosenCones` are the two dg-level
capabilities from which `H⁰ F` is triangulated.  Until now the only functors
carrying either were the identity and composites of functors that already had
them: nothing interesting was known to be exact.

This file proves the first half for cone functors.  If `α : F ⟶ G` is a closed
degree-zero dg natural transformation and both `F` and `G` preserve shifts, then
so does `Cone(α)`.  Since the twist candidate of a dg adjunction *is* a cone
functor, that gives the twist a `PreservesShifts` witness as soon as the
adjoints have one, and with it a `CommShift` on `H⁰`.

## The proof is the splitting, not a computation

A morphism into a cone splits uniquely along `inl` and `inr`
(`IsConeOf.bijective`), and right composition with the cone lift respects that
splitting: `inl` picks up `(-1)^p` times the `F`-component
(`inl_comp_homogeneousLift_strict`) and `inr` picks up the `G`-component
(`inr_comp_homogeneousLift`).  So right composition with `Cone(α).map (-n) s.hom`
is, through the splitting, the product of right composition with
`F.map (-n) s.hom` and with `G.map (-n) s.hom`, up to a sign on the first
factor.  Both of those are bijective because `F` and `G` preserve shifts, and a
sign is a unit, so the product is bijective.

No property of `α` beyond being a closed degree-zero transformation is used, and
the argument never touches the differential.

## What this does not give

The other half.  `PreservesChosenCones` for a cone functor is the statement that
`Cone(α)` carries a cone of `f` to a cone of `Cone(α)(f)`, which is a 3-by-3
lemma and is not proved here.  So `H⁰ (Cone α)` is not yet known to be
triangulated; what it has is a shift comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans.ConeData

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  {F G : DGFunctor C D} {α : HomogeneousNatTrans F G 0} (K : ConeData α)

/-- **Right composition with the cone lift, read through the splitting.**

A morphism into `Cone(α) X` of degree `p` is `a ≫ inl + b ≫ inr`; composing on
the right with `Cone(α).map (-n) s.hom` sends it to the same expression built
from `a ≫ F.map (-n) s.hom` and `b ≫ G.map (-n) s.hom`, with the sign
`(-1)^(-n)` on the first.  That sign is `inl_comp_homogeneousLift_strict`'s and
nothing more. -/
theorem compRight_functor_map {X Y : C} {n : ℤ} (s : IsShiftBy X n Y) (W : D)
    (p q : ℤ) (h : p + -n = q)
    (a : (dgHom W (F.obj X)).X (p + 1)) (b : (dgHom W (G.obj X)).X p) :
    dgComp p (-n) q h
        (dgComp (p + 1) (-1) p (by omega) a (K.isCone X).inl +
          dgComp p 0 p (by omega) b (K.isCone X).inr)
        (K.functor.map (-n) s.hom) =
      dgComp (q + 1) (-1) q (by omega)
          ((-n).negOnePow •
            dgComp (p + 1) (-n) (q + 1) (by omega) a (F.map (-n) s.hom))
          (K.isCone Y).inl +
        dgComp q 0 q (by omega)
          (dgComp p (-n) q (by omega) b (G.map (-n) s.hom)) (K.isCone Y).inr := by
  rw [map_add, AddMonoidHom.add_apply,
    dgComp_assoc (p + 1) (-1) (-n) p (-1 + -n) q (by omega) (by omega) (by omega),
    dgComp_assoc p 0 (-n) p (0 + -n) q (by omega) (by omega) (by omega),
    K.functor_map,
    (K.isCone X).inl_comp_homogeneousLift_strict_general (K.isCone Y) (-n)
      (-1 + -n) (by omega) (by omega) (F.map (-n) s.hom) (G.map (-n) s.hom),
    (K.isCone X).inr_comp_homogeneousLift_general (K.isCone Y) (-n) (0 + -n)
      (by omega) (by omega) (F.map (-n) s.hom) (G.map (-n) s.hom) 0,
    dgComp_units_smul_right,
    ← dgComp_assoc (p + 1) (-n) (-1) (q + 1) (-1 + -n) q
      (by omega) (by omega) (by omega),
    ← dgComp_assoc p (-n) 0 q (0 + -n) q (by omega) (by omega) (by omega),
    dgComp_units_smul_left]

/-- **A cone functor preserves shifts.**

The shift element of the image is the image of the shift element, and right
composition with it is bijective because, through the cone splitting, it is the
product of right composition with the two shift elements `F` and `G` supply,
one of them scaled by a sign. -/
noncomputable def preservesShifts (hF : PreservesShifts F)
    (hG : PreservesShifts G) : PreservesShifts K.functor where
  mapShift {X Y n} s :=
    { hom := K.functor.map (-n) s.hom
      hom_closed := by
        rw [← K.functor.map_d (-n) (-n + 1) s.hom, s.hom_closed, map_zero]
      bijective W p q hpn := by
        -- Through the two splittings the map is a product of two bijections,
        -- so `Function.Bijective.of_comp_iff'` transfers bijectivity back.
        have hsplitX := (K.isCone X).bijective W p (p + 1) (by omega)
        have hsplitY := (K.isCone Y).bijective W q (q + 1) (by omega)
        have hFb := (hF.mapShift s).bijective W (p + 1) (q + 1) (by omega)
        have hGb := (hG.mapShift s).bijective W p q (by omega)
        rw [hF.mapShift_hom s] at hFb
        rw [hG.mapShift_hom s] at hGb
        have hsmul : Function.Bijective
            (fun x : (dgHom W (F.obj Y)).X (q + 1) => (-n).negOnePow • x) :=
          (MulAction.toPerm ((-n).negOnePow)).bijective
        have hprod : Function.Bijective
            (fun ab : (dgHom W (F.obj X)).X (p + 1) × (dgHom W (G.obj X)).X p =>
              ((-n).negOnePow •
                  dgComp (p + 1) (-n) (q + 1) (by omega) ab.1 (F.map (-n) s.hom),
                dgComp p (-n) q (by omega) ab.2 (G.map (-n) s.hom))) :=
          Function.Bijective.prodMap (hsmul.comp hFb) hGb
        have hcomp : ∀ ab : (dgHom W (F.obj X)).X (p + 1) ×
              (dgHom W (G.obj X)).X p,
            compRight W (K.functor.map (-n) s.hom) p q hpn
                (dgComp (p + 1) (-1) p (by omega) ab.1 (K.isCone X).inl +
                  dgComp p 0 p (by omega) ab.2 (K.isCone X).inr) =
              dgComp (q + 1) (-1) q (by omega)
                  ((-n).negOnePow •
                    dgComp (p + 1) (-n) (q + 1) (by omega) ab.1
                      (F.map (-n) s.hom))
                  (K.isCone Y).inl +
                dgComp q 0 q (by omega)
                  (dgComp p (-n) q (by omega) ab.2 (G.map (-n) s.hom))
                  (K.isCone Y).inr :=
          fun ab => K.compRight_functor_map s W p q hpn ab.1 ab.2
        -- Chase the two splittings by hand.  Mathlib's `of_comp_iff` lemmas
        -- both assume the *outer* map bijective, which is the one being
        -- proved here, so neither applies.
        constructor
        · intro φ₁ φ₂ hφ
          obtain ⟨ab₁, rfl⟩ := hsplitX.surjective φ₁
          obtain ⟨ab₂, rfl⟩ := hsplitX.surjective φ₂
          rw [hcomp ab₁, hcomp ab₂] at hφ
          have hab : ab₁ = ab₂ := hprod.injective (hsplitY.injective hφ)
          rw [hab]
        · intro ψ
          obtain ⟨uv, rfl⟩ := hsplitY.surjective ψ
          obtain ⟨ab, hab⟩ := hprod.surjective uv
          refine ⟨dgComp (p + 1) (-1) p (by omega) ab.1 (K.isCone X).inl +
            dgComp p 0 p (by omega) ab.2 (K.isCone X).inr, ?_⟩
          rw [← hab]
          exact hcomp ab }
  mapShift_hom _ := rfl


end DGFunctor.HomogeneousNatTrans.ConeData

namespace DGAdjunction

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  {L : DGFunctor C D} {R : DGFunctor D C} (A : DGAdjunction L R)

/-- **The twist candidate preserves shifts, as soon as the adjoints do.**

The twist is the cone of the counit `L R ⟶ id_D`, so this is the cone-functor
result with `F := R.comp L` and `G := id`.  It is half of exactness: the other
half, `PreservesChosenCones`, is a 3-by-3 lemma and is not available. -/
noncomputable def CounitConeData.preservesShifts (K : A.CounitConeData)
    (hL : DGFunctor.PreservesShifts L) (hR : DGFunctor.PreservesShifts R) :
    DGFunctor.PreservesShifts K.twist :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesShifts K
    (DGFunctor.PreservesShifts.comp hR hL) (DGFunctor.PreservesShifts.id D)

/-- The unit cone preserves shifts too. -/
noncomputable def UnitConeData.preservesShifts (K : A.UnitConeData)
    (hL : DGFunctor.PreservesShifts L) (hR : DGFunctor.PreservesShifts R) :
    DGFunctor.PreservesShifts K.unitCone :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesShifts K
    (DGFunctor.PreservesShifts.id C) (DGFunctor.PreservesShifts.comp hL hR)

end DGAdjunction

end CategoryTheory
