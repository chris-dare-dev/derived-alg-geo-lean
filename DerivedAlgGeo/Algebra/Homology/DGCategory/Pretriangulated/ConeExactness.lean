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

## Both halves

`preservesChosenCones` is the other one: the 3-by-3 lemma, in the strict form
the capability asks for.  Its proof has the same shape with four factors instead
of two, and the point is that in those coordinates the map is *block diagonal*
rather than merely triangular.

With both, `H⁰ (Cone α)` is a triangulated functor.  For the twist candidate of
a dg adjunction that is exactness, and it is what the word "twist" is supposed
to mean once the twist/cotwist conditions make it an equivalence.

## What this does not give

Nothing about sphericality.  Exactness and invertibility of the twist are two of
Anno--Logvinenko's conditions, not all four, and the implication from the
recorded pair to the rest needs Morita quasi-functors.
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


/-! ### Cones

The second capability.  A cone of `f` in the source goes to a cone of
`Cone(α)(f)`, so a cone functor preserves chosen cones when its two ends do.

The argument is the same shape as for shifts, with four factors instead of
two.  A morphism into `Cone(α) Z` splits along the `Z`-cone of `α` into an
`F Z` part and a `G Z` part, and each of those splits again along the image
under `F` or `G` of the cone of `f`.  A pair of morphisms into `Cone(α) X` and
`Cone(α) Y` splits along the `X`- and `Y`-cones of `α` into the same four
groups, in a different order.  In those coordinates the map is *block
diagonal*, not merely triangular: the `F` block is the cone splitting `F`
supplies and the `G` block is the one `G` supplies, with a single sign on one
factor coming from `inl_comp_homogeneousLift_strict`. -/

/-- **The cone splitting of `Cone(α)`, in coordinates.**

Both inclusions of the cone of `Cone(α)(f)` are computed on a morphism already
split along the `X`- and `Y`-cones of `α`.  The result is split along the
`Z`-cone of `α`, and each component is the corresponding cone splitting of `F`
or of `G`. -/
theorem coneSplit_functor_map {X Y Z : C} {f : (dgHom X Y).X 0}
    (hc : IsConeOf f Z) (W : D) (p : ℤ)
    (a₁ : (dgHom W (F.obj X)).X (p + 1 + 1))
    (a₂ : (dgHom W (G.obj X)).X (p + 1))
    (b₁ : (dgHom W (F.obj Y)).X (p + 1))
    (b₂ : (dgHom W (G.obj Y)).X p) :
    dgComp (p + 1) (-1) p (by omega)
        (dgComp (p + 1 + 1) (-1) (p + 1) (by omega) a₁ (K.isCone X).inl +
          dgComp (p + 1) 0 (p + 1) (by omega) a₂ (K.isCone X).inr)
        (K.functor.map (-1) hc.inl) +
      dgComp p 0 p (by omega)
        (dgComp (p + 1) (-1) p (by omega) b₁ (K.isCone Y).inl +
          dgComp p 0 p (by omega) b₂ (K.isCone Y).inr)
        (K.functor.map 0 hc.inr) =
    dgComp (p + 1) (-1) p (by omega)
        (dgComp (p + 1 + 1) (-1) (p + 1) (by omega)
            ((-1 : ℤ).negOnePow • a₁) (F.map (-1) hc.inl) +
          dgComp (p + 1) 0 (p + 1) (by omega) b₁ (F.map 0 hc.inr))
        (K.isCone Z).inl +
      dgComp p 0 p (by omega)
        (dgComp (p + 1) (-1) p (by omega) a₂ (G.map (-1) hc.inl) +
          dgComp p 0 p (by omega) b₂ (G.map 0 hc.inr))
        (K.isCone Z).inr := by
  rw [map_add, AddMonoidHom.add_apply, map_add, AddMonoidHom.add_apply,
    K.functor_map, K.functor_map,
    -- the four `inl`/`inr` composites with the two lifts
    dgComp_assoc (p + 1 + 1) (-1) (-1) (p + 1) (-1 + -1) p
      (by omega) (by omega) (by omega),
    dgComp_assoc (p + 1) 0 (-1) (p + 1) (0 + -1) p
      (by omega) (by omega) (by omega),
    dgComp_assoc (p + 1) (-1) 0 p (-1 + 0) p
      (by omega) (by omega) (by omega),
    dgComp_assoc p 0 0 p (0 + 0) p (by omega) (by omega) (by omega),
    (K.isCone X).inl_comp_homogeneousLift_strict_general (K.isCone Z) (-1)
      (-1 + -1) (by omega) (by omega) (F.map (-1) hc.inl) (G.map (-1) hc.inl),
    (K.isCone X).inr_comp_homogeneousLift_general (K.isCone Z) (-1) (0 + -1)
      (by omega) (by omega) (F.map (-1) hc.inl) (G.map (-1) hc.inl) 0,
    (K.isCone Y).inl_comp_homogeneousLift_strict_general (K.isCone Z) 0
      (-1 + 0) (by omega) (by omega) (F.map 0 hc.inr) (G.map 0 hc.inr),
    (K.isCone Y).inr_comp_homogeneousLift_general (K.isCone Z) 0 (0 + 0)
      (by omega) (by omega) (F.map 0 hc.inr) (G.map 0 hc.inr) 0,
    -- reassociate each of the four back onto `inl_Z` or `inr_Z`
    dgComp_units_smul_right, dgComp_units_smul_right,
    ← dgComp_assoc (p + 1 + 1) (-1) (-1) (p + 1) (-1 + -1) p
      (by omega) (by omega) (by omega),
    ← dgComp_assoc (p + 1) (-1) 0 p (0 + -1) p
      (by omega) (by omega) (by omega),
    ← dgComp_assoc (p + 1) 0 (-1) (p + 1) (-1 + 0) p
      (by omega) (by omega) (by omega),
    ← dgComp_assoc p 0 0 p (0 + 0) p (by omega) (by omega) (by omega)]
  -- The sign is left as `(-1)^(-1) •`, exactly as
  -- `inl_comp_homogeneousLift_strict` produces it; only its position moves.
  simp only [Int.negOnePow_zero, one_smul, map_add, AddMonoidHom.add_apply,
    dgComp_units_smul_left]
  abel

/-- **A cone functor preserves chosen cones.**

The 3-by-3 lemma, in the strict dg form the capability asks for.  Both
inclusions of the image cone are the images of the inclusions, and the
splitting is `coneSplit_functor_map`: in the four coordinates the map is block
diagonal, with the `F` block and the `G` block the cone splittings that `F` and
`G` supply. -/
noncomputable def preservesChosenCones (hF : PreservesChosenCones F)
    (hG : PreservesChosenCones G) : PreservesChosenCones K.functor where
  mapCone {X Y Z f} hc :=
    { inr := K.functor.map 0 hc.inr
      inr_closed := by
        rw [← K.functor.map_d 0 1 hc.inr, hc.inr_closed, map_zero]
      inl := K.functor.map (-1) hc.inl
      δ_inl := by
        rw [← K.functor.map_d (-1) 0 hc.inl, hc.δ_inl,
          K.functor.map_comp 0 0 0 (by omega)]
      bijective W p q hq := by
        cases hq
        have hsX := (K.isCone X).bijective W (p + 1) (p + 1 + 1) (by omega)
        have hsY := (K.isCone Y).bijective W p (p + 1) (by omega)
        have hsZ := (K.isCone Z).bijective W p (p + 1) (by omega)
        have hFc := (hF.mapCone hc).bijective W (p + 1) (p + 1 + 1) (by omega)
        have hGc := (hG.mapCone hc).bijective W p (p + 1) (by omega)
        rw [hF.mapCone_inl hc, hF.mapCone_inr hc] at hFc
        rw [hG.mapCone_inl hc, hG.mapCone_inr hc] at hGc
        have hsign : Function.Bijective
            (fun x : (dgHom W (F.obj X)).X (p + 1 + 1) =>
              (-1 : ℤ).negOnePow • x) :=
          (MulAction.toPerm ((-1 : ℤ).negOnePow)).bijective
        -- Each `injective` below is applied to an explicitly ascribed
        -- equation.  Without the ascription Lean has to solve `?pair.1 = …`,
        -- a projection of a metavariable, and unification fails.
        constructor
        · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
          obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hsX.surjective a
          obtain ⟨⟨b₁, b₂⟩, rfl⟩ := hsY.surjective b
          obtain ⟨⟨a₁', a₂'⟩, rfl⟩ := hsX.surjective a'
          obtain ⟨⟨b₁', b₂'⟩, rfl⟩ := hsY.surjective b'
          simp only at hab
          rw [K.coneSplit_functor_map hc W p a₁ a₂ b₁ b₂,
            K.coneSplit_functor_map hc W p a₁' a₂' b₁' b₂'] at hab
          have hz : ((dgComp (p + 1 + 1) (-1) (p + 1) (by omega)
                    ((-1 : ℤ).negOnePow • a₁) (F.map (-1) hc.inl) +
                  dgComp (p + 1) 0 (p + 1) (by omega) b₁ (F.map 0 hc.inr),
                dgComp (p + 1) (-1) p (by omega) a₂ (G.map (-1) hc.inl) +
                  dgComp p 0 p (by omega) b₂ (G.map 0 hc.inr)) :
                (dgHom W (F.obj Z)).X (p + 1) × (dgHom W (G.obj Z)).X p) =
              (dgComp (p + 1 + 1) (-1) (p + 1) (by omega)
                    ((-1 : ℤ).negOnePow • a₁') (F.map (-1) hc.inl) +
                  dgComp (p + 1) 0 (p + 1) (by omega) b₁' (F.map 0 hc.inr),
                dgComp (p + 1) (-1) p (by omega) a₂' (G.map (-1) hc.inl) +
                  dgComp p 0 p (by omega) b₂' (G.map 0 hc.inr)) :=
            hsZ.injective hab
          have hf : ((-1 : ℤ).negOnePow • a₁, b₁) =
              ((-1 : ℤ).negOnePow • a₁', b₁') := by
            refine hFc.injective ?_
            simpa using congrArg _root_.Prod.fst hz
          have hg : (a₂, b₂) = (a₂', b₂') := by
            refine hGc.injective ?_
            simpa using congrArg _root_.Prod.snd hz
          -- `Prod.fst` here is the projection, not `CategoryTheory.Prod.fst`,
          -- and the sign is cancelled with the group action's injectivity.
          have ha : a₁ = a₁' :=
            MulAction.injective ((-1 : ℤ).negOnePow) (congrArg _root_.Prod.fst hf)
          have hb : b₁ = b₁' := congrArg _root_.Prod.snd hf
          have hc₂ : a₂ = a₂' := congrArg _root_.Prod.fst hg
          have hd : b₂ = b₂' := congrArg _root_.Prod.snd hg
          rw [ha, hb, hc₂, hd]
        · intro c
          obtain ⟨⟨c₁, c₂⟩, rfl⟩ := hsZ.surjective c
          obtain ⟨⟨u, v⟩, hu⟩ := hFc.surjective c₁
          obtain ⟨⟨u', v'⟩, hu'⟩ := hGc.surjective c₂
          obtain ⟨a₁, ha₁⟩ := hsign.surjective u
          have ha₁' : (-1 : ℤ).negOnePow • a₁ = u := ha₁
          have hu₂ : dgComp (p + 1 + 1) (-1) (p + 1) (by omega) u
                (F.map (-1) hc.inl) +
              dgComp (p + 1) 0 (p + 1) (by omega) v (F.map 0 hc.inr) = c₁ := hu
          have hu₃ : dgComp (p + 1) (-1) p (by omega) u'
                (G.map (-1) hc.inl) +
              dgComp p 0 p (by omega) v' (G.map 0 hc.inr) = c₂ := hu'
          refine ⟨(dgComp (p + 1 + 1) (-1) (p + 1) (by omega) a₁
                (K.isCone X).inl +
              dgComp (p + 1) 0 (p + 1) (by omega) u' (K.isCone X).inr,
            dgComp (p + 1) (-1) p (by omega) v (K.isCone Y).inl +
              dgComp p 0 p (by omega) v' (K.isCone Y).inr), ?_⟩
          simp only
          rw [K.coneSplit_functor_map hc W p a₁ u' v v', ha₁', hu₂, hu₃] }
  mapCone_inr _ := rfl
  mapCone_inl _ := rfl

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

/-- **The twist candidate preserves chosen cones.**  The 3-by-3 lemma applied
to the counit's cone: with `preservesShifts` this is full dg-level exactness
data for the twist. -/
noncomputable def CounitConeData.preservesChosenCones (K : A.CounitConeData)
    (hL : DGFunctor.PreservesChosenCones L)
    (hR : DGFunctor.PreservesChosenCones R) :
    DGFunctor.PreservesChosenCones K.twist :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesChosenCones K
    (DGFunctor.PreservesChosenCones.comp hR hL)
    (DGFunctor.PreservesChosenCones.id D)

/-- The unit cone preserves chosen cones too. -/
noncomputable def UnitConeData.preservesChosenCones (K : A.UnitConeData)
    (hL : DGFunctor.PreservesChosenCones L)
    (hR : DGFunctor.PreservesChosenCones R) :
    DGFunctor.PreservesChosenCones K.unitCone :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesChosenCones K
    (DGFunctor.PreservesChosenCones.id C)
    (DGFunctor.PreservesChosenCones.comp hL hR)

/-- The unit cone preserves shifts too. -/
noncomputable def UnitConeData.preservesShifts (K : A.UnitConeData)
    (hL : DGFunctor.PreservesShifts L) (hR : DGFunctor.PreservesShifts R) :
    DGFunctor.PreservesShifts K.unitCone :=
  DGFunctor.HomogeneousNatTrans.ConeData.preservesShifts K
    (DGFunctor.PreservesShifts.id C) (DGFunctor.PreservesShifts.comp hL hR)

end DGAdjunction

end CategoryTheory
