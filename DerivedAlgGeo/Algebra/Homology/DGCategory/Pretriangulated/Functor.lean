/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift

/-!
# Preservation of pretriangulated dg structure

Every dg functor preserves the representability witnesses that define shifts:
`DGFunctor.preservesShifts` supplies the dg-level capability automatically.
Preservation of chosen cone witnesses remains genuine extra data, recorded by
`DGFunctor.PreservesChosenCones`, but this capability transports across
isomorphisms in `Z⁰ (DGFunctor C D)`.  Transport to the ordinary shift functors
and cone triangles on `H⁰` belongs to the dg-enhancement layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u''

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} {E : Type u''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E]

/-- A dg functor preserves shifts when it sends every dg shift witness to a
shift witness on the image objects, with the defining homogeneous element
given by the dg functor's map.

No pretriangulated instance is required to state the capability: callers may
provide individual witnesses, while `H⁰` adapters add existence assumptions
only when they choose shifts for every object. -/
structure PreservesShifts (F : DGFunctor C D) where
  /-- The target shift witness associated to a source shift witness. -/
  mapShift {X Y : C} {n : ℤ} (s : IsShiftBy X n Y) :
    IsShiftBy (F.obj X) n (F.obj Y)
  /-- The associated shift element is the image of the source element. -/
  mapShift_hom {X Y : C} {n : ℤ} (s : IsShiftBy X n Y) :
    (mapShift s).hom = F.map (-n) s.hom

namespace PreservesShifts

/-- The identity dg functor preserves shift witnesses. -/
def id (C : Type u) [DGCategory.{v} C] : PreservesShifts (DGFunctor.id C) where
  mapShift s := s
  mapShift_hom _ := rfl

/-- Shift preservation is closed under composition of dg functors. -/
def comp {F : DGFunctor C D} {G : DGFunctor D E}
    (hF : PreservesShifts F) (hG : PreservesShifts G) :
    PreservesShifts (F.comp G) where
  mapShift s := hG.mapShift (hF.mapShift s)
  mapShift_hom s := by
    rw [hG.mapShift_hom, hF.mapShift_hom]
    rfl

end PreservesShifts

/-- **Every dg functor preserves shifts.**

A shift element is a closed, two-sided invertible element of degree `-n`:
`IsShiftBy.inv` extracts the inverse from surjectivity of right composition, and
`hom_inv` and `inv_hom` are the two identities.  A dg functor preserves the
graded composition and the identities on the nose, so it carries an invertible
element to an invertible element, and right composition with the image is
bijective with right composition with the image of the inverse.

So `PreservesShifts` is not a hypothesis anybody has to discharge; it is
supplied here for every dg functor.  The structure stays because it names the
capability and because `mapShift` is the useful accessor, but a caller that used
to take a `PreservesShifts` argument can now call this instead.

`PreservesChosenCones` is a genuine hypothesis and stays one: a cone is not an
invertible element, and a dg functor need not preserve the splitting of maps
into a cone. -/
noncomputable def preservesShifts (F : DGFunctor C D) : PreservesShifts F where
  mapShift {X Y n} s :=
    { hom := F.map (-n) s.hom
      hom_closed := by
        rw [← F.map_d (-n) (-n + 1) s.hom, s.hom_closed, map_zero]
      bijective W p q hpn := by
        refine Function.bijective_iff_has_inverse.2
          ⟨fun f => dgComp q n p (by omega) f (F.map n s.inv), ?_, ?_⟩
        · intro a
          show dgComp q n p (by omega)
            (dgComp p (-n) q hpn a (F.map (-n) s.hom)) (F.map n s.inv) = a
          rw [dgComp_assoc p (-n) n q 0 p (by omega) (by omega) (by omega),
            ← F.map_comp (-n) n 0 (by omega), s.hom_inv, F.map_id, dgComp_id]
        · intro f
          show dgComp p (-n) q hpn
            (dgComp q n p (by omega) f (F.map n s.inv)) (F.map (-n) s.hom) = f
          rw [dgComp_assoc q n (-n) p 0 q (by omega) (by omega) (by omega),
            ← F.map_comp n (-n) 0 (by omega), s.inv_hom, F.map_id, dgComp_id] }
  mapShift_hom _ := rfl

/-- Apply a dg functor to a chosen homotopy-commutative square.  The homotopy
itself is mapped, so this construction retains the witness needed by later
cone maps rather than merely proving that the image square commutes in `H⁰`. -/
def mapHomotopySquare (F : DGFunctor C D)
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}
    (s : DGCategory.HomotopySquare f₁ f₂ a b) :
    DGCategory.HomotopySquare
      (F.map 0 f₁) (F.map 0 f₂) (F.map 0 a) (F.map 0 b) :=
  DGCategory.HomotopySquare.ofBoundary
    (by rw [← F.map_d 0 1 a, s.a_closed, map_zero])
    (by rw [← F.map_d 0 1 b, s.b_closed, map_zero])
    (F.map (-1) s.homotopy)
    (by rw [← F.map_d (-1) 0 s.homotopy, s.boundary, map_sub,
      F.map_comp, F.map_comp])

@[simp]
lemma mapHomotopySquare_homotopy (F : DGFunctor C D)
    {X₁ Y₁ X₂ Y₂ : C}
    {f₁ : (dgHom X₁ Y₁).X 0} {f₂ : (dgHom X₂ Y₂).X 0}
    {a : (dgHom X₁ X₂).X 0} {b : (dgHom Y₁ Y₂).X 0}
    (s : DGCategory.HomotopySquare f₁ f₂ a b) :
    (F.mapHomotopySquare s).homotopy = F.map (-1) s.homotopy :=
  rfl

/-- Strong dg-level preservation of cone witnesses.

For every supplied cone witness, the image object is equipped with a cone
witness whose two inclusions are exactly the images of the source inclusions.
This chosen, composable capability is intentionally stronger than the later
`H⁰` proposition that an image triangle is merely isomorphic to some cone
triangle. -/
structure PreservesChosenCones (F : DGFunctor C D) where
  /-- The target cone witness carried by the image object. -/
  mapCone {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    IsConeOf (F.map 0 f) (F.obj Z)
  /-- The target cone inclusion is the image of the source cone inclusion. -/
  mapCone_inr {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (mapCone hc).inr = F.map 0 hc.inr
  /-- The shifted source inclusion is the image of the source cone inclusion. -/
  mapCone_inl {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (mapCone hc).inl = F.map (-1) hc.inl

namespace PreservesChosenCones

variable {F : DGFunctor C D}

/-- The identity dg functor preserves chosen cone witnesses. -/
def id (C : Type u) [DGCategory.{v} C] :
    PreservesChosenCones (DGFunctor.id C) where
  mapCone hc := hc
  mapCone_inr _ := rfl
  mapCone_inl _ := rfl

/-- Strong cone preservation is closed under composition of dg functors. -/
def comp {F : DGFunctor C D} {G : DGFunctor D E}
    (hF : PreservesChosenCones F) (hG : PreservesChosenCones G) :
    PreservesChosenCones (F.comp G) where
  mapCone hc := hG.mapCone (hF.mapCone hc)
  mapCone_inr hc := by
    rw [hG.mapCone_inr, hF.mapCone_inr]
    rfl
  mapCone_inl hc := by
    rw [hG.mapCone_inl, hF.mapCone_inl]
    rfl

section Iso

variable {F G : Z0 (DGFunctor C D)}

private lemma iso_hom_inv_app (e : F ≅ G) (X : C) :
    dgComp 0 0 0 (by omega)
        (HomogeneousNatTrans.app e.hom.val X)
        (HomogeneousNatTrans.app e.inv.val X) =
      dgId ((Z0.of (DGFunctor C D) F).obj X) := by
  have h := congrArg Subtype.val e.hom_inv_id
  change HomogeneousNatTrans.composition
      (Z0.of (DGFunctor C D) F) (Z0.of (DGFunctor C D) G)
      (Z0.of (DGFunctor C D) F) 0 0 0 (by omega)
      e.hom.val e.inv.val =
    HomogeneousNatTrans.id (Z0.of (DGFunctor C D) F) at h
  have hX := congrArg (fun θ => HomogeneousNatTrans.app θ X) h
  rw [HomogeneousNatTrans.composition_apply_app,
    HomogeneousNatTrans.id_app] at hX
  exact hX

private lemma iso_inv_hom_app (e : F ≅ G) (X : C) :
    dgComp 0 0 0 (by omega)
        (HomogeneousNatTrans.app e.inv.val X)
        (HomogeneousNatTrans.app e.hom.val X) =
      dgId ((Z0.of (DGFunctor C D) G).obj X) := by
  have h := congrArg Subtype.val e.inv_hom_id
  change HomogeneousNatTrans.composition
      (Z0.of (DGFunctor C D) G) (Z0.of (DGFunctor C D) F)
      (Z0.of (DGFunctor C D) G) 0 0 0 (by omega)
      e.inv.val e.hom.val =
    HomogeneousNatTrans.id (Z0.of (DGFunctor C D) G) at h
  have hX := congrArg (fun θ => HomogeneousNatTrans.app θ X) h
  rw [HomogeneousNatTrans.composition_apply_app,
    HomogeneousNatTrans.id_app] at hX
  exact hX

private lemma compRight_hom_bijective (e : F ≅ G) (W : D) (X : C) (p : ℤ) :
    Function.Bijective (fun f : (dgHom W ((Z0.of (DGFunctor C D) F).obj X)).X p =>
      dgComp p 0 p (by omega) f (HomogeneousNatTrans.app e.hom.val X)) := by
  constructor
  · intro f g hfg
    have h := congrArg (fun k => dgComp p 0 p (by omega) k
      (HomogeneousNatTrans.app e.inv.val X)) hfg
    simpa only [dgComp_assoc p 0 0 p 0 p (by omega) (by omega) (by omega),
      iso_hom_inv_app e X, dgComp_id] using h
  · intro g
    refine ⟨dgComp p 0 p (by omega) g (HomogeneousNatTrans.app e.inv.val X), ?_⟩
    change dgComp p 0 p (by omega)
      (dgComp p 0 p (by omega) g (HomogeneousNatTrans.app e.inv.val X))
      (HomogeneousNatTrans.app e.hom.val X) = g
    rw [dgComp_assoc p 0 0 p 0 p (by omega) (by omega) (by omega),
      iso_inv_hom_app e X, dgComp_id]

private lemma compRight_inv_bijective (e : F ≅ G) (W : D) (X : C) (p : ℤ) :
    Function.Bijective (fun f : (dgHom W ((Z0.of (DGFunctor C D) G).obj X)).X p =>
      dgComp p 0 p (by omega) f (HomogeneousNatTrans.app e.inv.val X)) := by
  constructor
  · intro f g hfg
    have h := congrArg (fun k => dgComp p 0 p (by omega) k
      (HomogeneousNatTrans.app e.hom.val X)) hfg
    simpa only [dgComp_assoc p 0 0 p 0 p (by omega) (by omega) (by omega),
      iso_inv_hom_app e X, dgComp_id] using h
  · intro g
    refine ⟨dgComp p 0 p (by omega) g (HomogeneousNatTrans.app e.hom.val X), ?_⟩
    change dgComp p 0 p (by omega)
      (dgComp p 0 p (by omega) g (HomogeneousNatTrans.app e.hom.val X))
      (HomogeneousNatTrans.app e.inv.val X) = g
    rw [dgComp_assoc p 0 0 p 0 p (by omega) (by omega) (by omega),
      iso_hom_inv_app e X, dgComp_id]

private def ofIsoAux (hF : PreservesChosenCones (Z0.of (DGFunctor C D) F))
    (e : F ≅ G) : PreservesChosenCones (Z0.of (DGFunctor C D) G) where
  mapCone {X Y Z f} hc :=
    { inr := (Z0.of (DGFunctor C D) G).map 0 hc.inr
      inr_closed := by
        rw [← (Z0.of (DGFunctor C D) G).map_d 0 1 hc.inr,
          hc.inr_closed, map_zero]
      inl := (Z0.of (DGFunctor C D) G).map (-1) hc.inl
      δ_inl := by
        rw [← (Z0.of (DGFunctor C D) G).map_d (-1) 0 hc.inl,
          hc.δ_inl, (Z0.of (DGFunctor C D) G).map_comp]
      bijective := by
        intro W p q hq
        have hX := compRight_inv_bijective e W X q
        have hY := compRight_inv_bijective e W Y p
        have hpair : Function.Bijective (fun ab :
            (dgHom W ((Z0.of (DGFunctor C D) G).obj X)).X q ×
              (dgHom W ((Z0.of (DGFunctor C D) G).obj Y)).X p =>
            (dgComp q 0 q (by omega) ab.1
                (HomogeneousNatTrans.app e.inv.val X),
              dgComp p 0 p (by omega) ab.2
                (HomogeneousNatTrans.app e.inv.val Y))) := by
          constructor
          · intro ab ab' hab
            apply Prod.ext
            · exact hX.injective (congrArg (fun pair => pair.1) hab)
            · exact hY.injective (congrArg (fun pair => pair.2) hab)
          · intro ab
            obtain ⟨a, ha⟩ := hX.surjective ab.1
            obtain ⟨b, hb⟩ := hY.surjective ab.2
            exact ⟨(a, b), Prod.ext ha hb⟩
        have hZ := compRight_hom_bijective e W Z p
        have hnatInl := HomogeneousNatTrans.naturality e.hom.val (-1) (-1)
          (by omega) (by omega) hc.inl
        rw [zero_mul, Int.negOnePow_zero, one_smul] at hnatInl
        have hnatInr := HomogeneousNatTrans.naturality e.hom.val 0 0
          (by omega) (by omega) hc.inr
        rw [zero_mul, Int.negOnePow_zero, one_smul] at hnatInr
        have htermX (a : (dgHom W ((Z0.of (DGFunctor C D) G).obj X)).X q) :
            dgComp p 0 p (by omega)
                (dgComp q (-1) p (by omega)
                  (dgComp q 0 q (by omega) a (HomogeneousNatTrans.app e.inv.val X))
                  ((Z0.of (DGFunctor C D) F).map (-1) hc.inl))
                (HomogeneousNatTrans.app e.hom.val Z) =
              dgComp q (-1) p (by omega) a
                ((Z0.of (DGFunctor C D) G).map (-1) hc.inl) := by
          calc
            _ = dgComp q (-1) p (by omega)
                (dgComp q 0 q (by omega) a (HomogeneousNatTrans.app e.inv.val X))
                (dgComp (-1) 0 (-1) (by omega)
                  ((Z0.of (DGFunctor C D) F).map (-1) hc.inl)
                  (HomogeneousNatTrans.app e.hom.val Z)) :=
              dgComp_assoc q (-1) 0 p (-1) p
                (by omega) (by omega) (by omega) _ _ _
            _ = dgComp q (-1) p (by omega)
                (dgComp q 0 q (by omega) a (HomogeneousNatTrans.app e.inv.val X))
                (dgComp 0 (-1) (-1) (by omega)
                  (HomogeneousNatTrans.app e.hom.val X)
                  ((Z0.of (DGFunctor C D) G).map (-1) hc.inl)) := by
              rw [hnatInl]
            _ = dgComp q (-1) p (by omega)
                (dgComp q 0 q (by omega)
                  (dgComp q 0 q (by omega) a (HomogeneousNatTrans.app e.inv.val X))
                  (HomogeneousNatTrans.app e.hom.val X))
                ((Z0.of (DGFunctor C D) G).map (-1) hc.inl) := by
              exact (dgComp_assoc q 0 (-1) q (-1) p
                (by omega) (by omega) (by omega) _ _ _).symm
            _ = dgComp q (-1) p (by omega)
                (dgComp q 0 q (by omega) a
                  (dgComp 0 0 0 (by omega)
                    (HomogeneousNatTrans.app e.inv.val X)
                    (HomogeneousNatTrans.app e.hom.val X)))
                ((Z0.of (DGFunctor C D) G).map (-1) hc.inl) := by
              exact congrArg (fun k :
                  (dgHom W ((Z0.of (DGFunctor C D) G).obj X)).X q =>
                  dgComp q (-1) p (by omega) k
                    ((Z0.of (DGFunctor C D) G).map (-1) hc.inl))
                (dgComp_assoc q 0 0 q 0 q
                  (by omega) (by omega) (by omega) a
                  (HomogeneousNatTrans.app e.inv.val X)
                  (HomogeneousNatTrans.app e.hom.val X))
            _ = _ := by rw [iso_inv_hom_app e X, dgComp_id]
        have htermY (b : (dgHom W ((Z0.of (DGFunctor C D) G).obj Y)).X p) :
            dgComp p 0 p (by omega)
                (dgComp p 0 p (by omega)
                  (dgComp p 0 p (by omega) b (HomogeneousNatTrans.app e.inv.val Y))
                  ((Z0.of (DGFunctor C D) F).map 0 hc.inr))
                (HomogeneousNatTrans.app e.hom.val Z) =
              dgComp p 0 p (by omega) b
                ((Z0.of (DGFunctor C D) G).map 0 hc.inr) := by
          calc
            _ = dgComp p 0 p (by omega)
                (dgComp p 0 p (by omega) b (HomogeneousNatTrans.app e.inv.val Y))
                (dgComp 0 0 0 (by omega)
                  ((Z0.of (DGFunctor C D) F).map 0 hc.inr)
                  (HomogeneousNatTrans.app e.hom.val Z)) :=
              dgComp_assoc p 0 0 p 0 p
                (by omega) (by omega) (by omega) _ _ _
            _ = dgComp p 0 p (by omega)
                (dgComp p 0 p (by omega) b (HomogeneousNatTrans.app e.inv.val Y))
                (dgComp 0 0 0 (by omega)
                  (HomogeneousNatTrans.app e.hom.val Y)
                  ((Z0.of (DGFunctor C D) G).map 0 hc.inr)) := by
              rw [hnatInr]
            _ = dgComp p 0 p (by omega)
                (dgComp p 0 p (by omega)
                  (dgComp p 0 p (by omega) b (HomogeneousNatTrans.app e.inv.val Y))
                  (HomogeneousNatTrans.app e.hom.val Y))
                ((Z0.of (DGFunctor C D) G).map 0 hc.inr) := by
              exact (dgComp_assoc p 0 0 p 0 p
                (by omega) (by omega) (by omega) _ _ _).symm
            _ = dgComp p 0 p (by omega)
                (dgComp p 0 p (by omega) b
                  (dgComp 0 0 0 (by omega)
                    (HomogeneousNatTrans.app e.inv.val Y)
                    (HomogeneousNatTrans.app e.hom.val Y)))
                ((Z0.of (DGFunctor C D) G).map 0 hc.inr) := by
              exact congrArg (fun k :
                  (dgHom W ((Z0.of (DGFunctor C D) G).obj Y)).X p =>
                  dgComp p 0 p (by omega) k
                    ((Z0.of (DGFunctor C D) G).map 0 hc.inr))
                (dgComp_assoc p 0 0 p 0 p
                  (by omega) (by omega) (by omega) b
                  (HomogeneousNatTrans.app e.inv.val Y)
                  (HomogeneousNatTrans.app e.hom.val Y))
            _ = _ := by rw [iso_inv_hom_app e Y, dgComp_id]
        have hfactor : (fun ab :
            (dgHom W ((Z0.of (DGFunctor C D) G).obj X)).X q ×
              (dgHom W ((Z0.of (DGFunctor C D) G).obj Y)).X p =>
            dgComp q (-1) p (by omega) ab.1
                ((Z0.of (DGFunctor C D) G).map (-1) hc.inl) +
              dgComp p 0 p (by omega) ab.2
                ((Z0.of (DGFunctor C D) G).map 0 hc.inr)) =
            (fun z => dgComp p 0 p (by omega) z
                (HomogeneousNatTrans.app e.hom.val Z)) ∘
              (fun ab =>
                dgComp q (-1) p (by omega) ab.1 (hF.mapCone hc).inl +
                  dgComp p 0 p (by omega) ab.2 (hF.mapCone hc).inr) ∘
              (fun ab =>
                (dgComp q 0 q (by omega) ab.1
                    (HomogeneousNatTrans.app e.inv.val X),
                  dgComp p 0 p (by omega) ab.2
                    (HomogeneousNatTrans.app e.inv.val Y))) := by
          funext ab
          simp only [Function.comp_apply]
          rw [hF.mapCone_inl, hF.mapCone_inr]
          rw [map_add, AddMonoidHom.add_apply, htermX, htermY]
        rw [hfactor]
        exact hZ.comp ((hF.mapCone hc).bijective W p q hq |>.comp hpair) }
  mapCone_inr _ := rfl
  mapCone_inl _ := rfl

end Iso

/-- Strong preservation of the chosen cone witnesses is invariant under an
isomorphism of dg functors in the closed degree-zero category. -/
def ofIso {F G : DGFunctor C D} (hF : PreservesChosenCones F)
    (e : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from G)) : PreservesChosenCones G :=
  ofIsoAux hF e

/-- The projection from an image cone to its source is the image of the source
cone projection.  This is forced by uniqueness of the cone splitting; it is
not an additional field of `PreservesChosenCones`. -/
lemma mapCone_fst (hF : PreservesChosenCones F)
    {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (hF.mapCone hc).fst = F.map 1 hc.fst := by
  symm
  refine ((hF.mapCone hc).splitId_unique
    (a := F.map 1 hc.fst) (b := F.map 0 hc.snd) ?_).1
  rw [hF.mapCone_inl, hF.mapCone_inr,
    ← F.map_comp, ← F.map_comp, ← map_add,
    hc.fst_inl_add_snd_inr, F.map_id]

/-- The projection from an image cone to its target is the image of the source
cone projection, again derived from uniqueness of the cone splitting. -/
lemma mapCone_snd (hF : PreservesChosenCones F)
    {X Y Z : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z) :
    (hF.mapCone hc).snd = F.map 0 hc.snd := by
  symm
  refine ((hF.mapCone hc).splitId_unique
    (a := F.map 1 hc.fst) (b := F.map 0 hc.snd) ?_).2
  rw [hF.mapCone_inl, hF.mapCone_inr,
    ← F.map_comp, ← F.map_comp, ← map_add,
    hc.fst_inl_add_snd_inr, F.map_id]

/-- A cone-preserving, shift-preserving dg functor carries the connecting map
of a supplied cone to the connecting map built from the corresponding image
witnesses. -/
lemma mapCone_toShift (hCone : PreservesChosenCones F)
    (hShift : PreservesShifts F)
    {X Y Z X' : C} {f : (dgHom X Y).X 0}
    (hc : IsConeOf f Z) (s : IsShiftBy X 1 X') :
    F.map 0 (hc.toShift s) =
      (hCone.mapCone hc).toShift (hShift.mapShift s) := by
  rw [IsConeOf.toShift, IsConeOf.toShift, F.map_comp,
    hCone.mapCone_fst, hShift.mapShift_hom]

end PreservesChosenCones

variable {F : DGFunctor C D}

/-- The inverse of the image shift witness is forced by the image of the
source inverse. This removes the `Classical.choice` hidden in `IsShiftBy.inv`
from every later transport calculation. -/
lemma mapShift_inv_eq (hF : PreservesShifts F) {X Y : C} {n : ℤ}
    (s : IsShiftBy X n Y) :
    (hF.mapShift s).inv = F.map n s.inv := by
  symm
  apply IsShiftBy.inv_unique (hF.mapShift s)
  rw [hF.mapShift_hom]
  rw [← F.map_comp, s.inv_hom, F.map_id]

/-- `F` commutes with the dg action on morphisms induced by a shift witness. -/
lemma map_mapShift (hF : PreservesShifts F) {X X' Y Y' : C} {n : ℤ}
    (s : IsShiftBy X n Y) (s' : IsShiftBy X' n Y')
    (f : (dgHom X X').X 0) :
    F.map 0 (IsShiftBy.mapShift s s' f) =
      IsShiftBy.mapShift (hF.mapShift s) (hF.mapShift s') (F.map 0 f) := by
  rw [IsShiftBy.mapShift, IsShiftBy.mapShift, F.map_comp, F.map_comp,
    mapShift_inv_eq hF s, hF.mapShift_hom]

/-- `F` commutes with comparisons between two shifts of the same object. -/
lemma map_compare (hF : PreservesShifts F) {X Y Y' : C} {n : ℤ}
    (s : IsShiftBy X n Y) (t : IsShiftBy X n Y') :
    F.map 0 (IsShiftBy.compare s t) =
      IsShiftBy.compare (hF.mapShift s) (hF.mapShift t) := by
  rw [IsShiftBy.compare_eq_mapShift, map_mapShift hF, F.map_id,
    IsShiftBy.compare_eq_mapShift]

end DGFunctor

end CategoryTheory
