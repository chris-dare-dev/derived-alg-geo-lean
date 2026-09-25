/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ImageFactorisation
import DerivedAlgGeo.CategoryTheory.Subobject.NoetherianObject
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# A t-structure is determined by its aisle, and restrictions along a functor

Section 4 of arXiv:1902.08184 calls a t-structure `τ` on `𝒟` **`S`-local** when
for every quasi-compact open `U ⊆ S` there is a t-structure `τ_U` on `𝒟_U`
making the restriction functor t-exact, and Remark 4.6(1) observes that `τ_U` is
then unique. The categorical layer owns the one-functor restriction and
uniqueness vocabulary; the family-level quantifier and its geometric witnesses
remain in `Families/SLocal.lean`.

This file supplies the categorical half, for one functor at a time.
It also transfers Noetherianity across an anchored lift of subobject chains.
For triangulated t-exact functors, exactness of the induced heart functor
supplies preservation of binary joins, so pointwise lifts along each target
chain suffice. The image-factorisation step turns fixed-target arrow extension
into pointwise subobject lifts; constructing those arrows geometrically remains
an explicit input.

**Uniqueness is really a statement about aisles.** A t-structure carries two
object properties, but they determine each other: `t.ge (n + 1)` is the right
orthogonal of `t.le n` and conversely, by Mathlib's
`TStructure.isGE_iff_orthogonal` and `isLE_iff_orthogonal`. So two t-structures
with the same coconnective half are equal, and `ext_le` is the form Remark
4.6(1) consumes -- once one knows the aisle of `τ_U` is pinned, `τ_U` itself is.

**`Restriction` is the data, `RestrictsAlong` the proposition.** Quantifying
either over the quasi-compact opens of a base is what `S`-locality will be; that
quantifier is geometric and is not taken here, because the categories `𝒟_U`
vary with `U` and the base-change layer owns them.

Nothing here constructs a t-structure. `Restriction` is inhabited only by
someone who already has `τ_U`, and the uniqueness statement says which `τ_U`
that must be, not that one exists.
-/

universe v v' u u'

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A t-structure is its two object properties: every remaining field is a
proposition. -/
theorem ext {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) (hge : t₁.ge = t₂.ge) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  subst hle
  subst hge
  rfl

/-- The connective half is the right orthogonal of the coconnective half, so the
coconnective half determines it. -/
theorem ge_eq_of_le_eq {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) :
    t₁.ge = t₂.ge := by
  funext n
  funext X
  have key : ∀ (t : TStructure C) (m : ℤ) (Y : C),
      t.ge m Y ↔ ∀ (Z : C) (f : Z ⟶ Y), t.le (m - 1) Z → f = 0 := by
    intro t m Y
    constructor
    · intro hY Z f hZ
      letI : t.IsGE Y m := ⟨hY⟩
      letI : t.IsLE Z (m - 1) := ⟨hZ⟩
      exact t.zero f (m - 1) m (by lia)
    · intro hY
      have := (t.isGE_iff_orthogonal (m - 1) m (by lia) Y).2
        (fun Z f hf ↦ hY Z f hf.le)
      exact this.ge
  rw [key t₁ n X, key t₂ n X, hle]

/-- **A t-structure is determined by its aisle.** This is the engine behind the
uniqueness in Remark 4.6(1) of arXiv:1902.08184: pinning the coconnective half
of `τ_U` pins `τ_U`. -/
theorem ext_le {t₁ t₂ : TStructure C} (hle : t₁.le = t₂.le) : t₁ = t₂ :=
  ext hle (ge_eq_of_le_eq hle)

end TStructure

end CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### Noetherian hearts

The paper calls a t-structure noetherian when its heart satisfies the
ascending-chain condition.  The heart in this repository is an object
property, so the literal categorical formulation uses its full subcategory.
This predicate is intentionally independent of any geometric finiteness
theorem; the latter belongs to the base-change owner. -/

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The heart of `t` is noetherian when every heart object is a noetherian
object of the heart full subcategory. -/
def IsNoetherian (t : TStructure C) : Prop :=
  ∀ X : t.heart.FullSubcategory, IsNoetherianObject X

/-- A t-structure on the target of `F` making `F` t-exact.

This is one clause of `S`-locality, at one functor. `S`-locality quantifies it
over the quasi-compact opens of the base; that quantifier is geometric, because
the target category varies with the open. -/
structure Restriction (t : TStructure C) (F : C ⥤ D) where
  /-- The t-structure on the target. -/
  tStructure : TStructure D
  /-- The functor is t-exact for the two. -/
  isTExact : F.IsTExact t tStructure

/-- The proposition that `t` restricts along `F`, forgetting which t-structure
witnesses it. -/
def RestrictsAlong (t : TStructure C) (F : C ⥤ D) : Prop :=
  Nonempty (t.Restriction F)

namespace Restriction

variable {t : TStructure C} {F : C ⥤ D}

theorem restrictsAlong (r : t.Restriction F) : t.RestrictsAlong F :=
  ⟨r⟩

/-- Two restrictions of `t` along `F` that agree on aisles are the same
t-structure. Remark 4.6(1) is this together with a proof that the aisle of the
restriction is pinned -- which is geometric, and is not claimed here. -/
theorem tStructure_eq_of_le_eq (r₁ r₂ : t.Restriction F)
    (hle : r₁.tStructure.le = r₂.tStructure.le) :
    r₁.tStructure = r₂.tStructure :=
  ext_le hle

/-- Equality of restriction data once their target t-structures agree.

The remaining field is a proposition, so proof irrelevance closes the
restriction structure after the target equality has been transported. -/
theorem ext {r₁ r₂ : t.Restriction F}
    (h : r₁.tStructure = r₂.tStructure) : r₁ = r₂ := by
  cases r₁
  cases r₂
  cases h
  rfl

/-- The functor induced on the two hearts by a t-exact restriction.

This is the categorical map used by the noetherian-locality and filtration
interfaces.  It is constructed from the ambient functor and the theorem that
t-exact functors carry hearts to hearts; no heart-level functor is supplied as
a second, potentially inconsistent carrier. -/
noncomputable def heartFunctor (r : t.Restriction F) :
    t.heart.FullSubcategory ⥤ r.tStructure.heart.FullSubcategory where
  obj X := by
    letI : F.IsTExact t r.tStructure := r.isTExact
    exact ⟨F.obj X.obj, Functor.heart_map_of_isTExact X.obj X.property⟩
  map f := ObjectProperty.homMk (F.map f.hom)

@[simp]
theorem heartFunctor_obj (r : t.Restriction F)
    (X : t.heart.FullSubcategory) :
    (r.heartFunctor.obj X).obj = F.obj X.obj :=
  rfl

@[simp]
theorem heartFunctor_map (r : t.Restriction F)
    {X Y : t.heart.FullSubcategory} (f : X ⟶ Y) :
    (r.heartFunctor.map f).hom = F.map f.hom :=
  rfl

/-- The objectwise comparison underlying the natural degree-zero heart
cohomology comparison below. -/
noncomputable def heartH0Comparison
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) (X : C) :
    r.heartFunctor.obj (t.heartH0Functor.obj X) ≅
      (r.tStructure.heartH0Functor).obj (F.obj X) := by
  letI : F.IsTExact t r.tStructure := r.isTExact
  refine ObjectProperty.isoMk _ ?_
  change F.obj ((t.truncGE 0).obj ((t.truncLE 0).obj X)) ≅
    (r.tStructure.truncGE 0).obj ((r.tStructure.truncLE 0).obj (F.obj X))
  exact (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)) ≪≫
    (r.tStructure.truncGE 0).mapIso (F.mapTruncLEIso t r.tStructure 0 X)

private theorem heartH0Comparison_hom
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) (X : C) [F.IsTExact t r.tStructure] :
    (r.heartH0Comparison X).hom.hom =
      (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)).hom ≫
        (r.tStructure.truncGE 0).map
          (F.mapTruncLEIso t r.tStructure 0 X).hom := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero heart cohomology commutes naturally with a t-exact
triangulated functor, after restriction to the two hearts. -/
noncomputable def heartH0ComparisonNatIso
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) :
    t.heartH0Functor ⋙ r.heartFunctor ≅
      F ⋙ r.tStructure.heartH0Functor := by
  letI : F.IsTExact t r.tStructure := r.isTExact
  refine NatIso.ofComponents (fun X => r.heartH0Comparison X) ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  change F.map ((t.truncGE 0).map ((t.truncLE 0).map f)) ≫
      (r.heartH0Comparison Y).hom.hom =
      (r.heartH0Comparison X).hom.hom ≫
        (r.tStructure.truncGE 0).map
          ((r.tStructure.truncLE 0).map (F.map f))
  rw [heartH0Comparison_hom r X,
    heartH0Comparison_hom r Y]
  calc
    F.map ((t.truncGE 0).map ((t.truncLE 0).map f)) ≫
        (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj Y)).hom ≫
          (r.tStructure.truncGE 0).map
            (F.mapTruncLEIso t r.tStructure 0 Y).hom =
      (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)).hom ≫
        (r.tStructure.truncGE 0).map
          (F.map ((t.truncLE 0).map f)) ≫
            (r.tStructure.truncGE 0).map
              (F.mapTruncLEIso t r.tStructure 0 Y).hom := by
                simpa only [Category.assoc] using
                  congrArg (fun g => g ≫
                    (r.tStructure.truncGE 0).map
                      (F.mapTruncLEIso t r.tStructure 0 Y).hom)
                    (F.mapTruncGEIso_hom_naturality t r.tStructure 0
                      ((t.truncLE 0).map f))
    _ = _ := by
      have hLE := F.mapTruncLEIso_hom_naturality t r.tStructure 0 f
      calc
        (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)).hom ≫
            (r.tStructure.truncGE 0).map (F.map ((t.truncLE 0).map f)) ≫
              (r.tStructure.truncGE 0).map
                (F.mapTruncLEIso t r.tStructure 0 Y).hom =
          (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)).hom ≫
            (r.tStructure.truncGE 0).map
              (F.map ((t.truncLE 0).map f) ≫
                (F.mapTruncLEIso t r.tStructure 0 Y).hom) := by
                  simp only [Functor.map_comp]
        _ = (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X)).hom ≫
            (r.tStructure.truncGE 0).map
              ((F.mapTruncLEIso t r.tStructure 0 X).hom ≫
                (r.tStructure.truncLE 0).map (F.map f)) := by
                  rw [hLE]
        _ = _ := by
          simp only [Functor.map_comp, Category.assoc]

noncomputable section AmbientArrowExtension

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem heartH0Comparison_on_heart
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) (X : t.heart.FullSubcategory) :
    (r.heartH0Comparison X.obj).hom ≫
      (r.tStructure.heartH0OnHeartIso.app (r.heartFunctor.obj X)).hom =
      r.heartFunctor.map (t.heartH0OnHeartIso.app X).hom := by
  letI : F.IsTExact t r.tStructure := r.isTExact
  letI : t.IsLE X.obj 0 := ((t.mem_heart_iff X.obj).mp X.property).1
  letI : t.IsGE X.obj 0 := ((t.mem_heart_iff X.obj).mp X.property).2
  letI : r.tStructure.IsLE (F.obj X.obj) 0 :=
    ((r.tStructure.mem_heart_iff (F.obj X.obj)).mp
      (r.heartFunctor.obj X).property).1
  letI : r.tStructure.IsGE (F.obj X.obj) 0 :=
    ((r.tStructure.mem_heart_iff (F.obj X.obj)).mp
      (r.heartFunctor.obj X).property).2
  apply ObjectProperty.hom_ext
  change
    ((F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X.obj)).hom ≫
        (r.tStructure.truncGE 0).map
          (F.mapTruncLEIso t r.tStructure 0 X.obj).hom) ≫
      ((r.tStructure.truncGE 0).map
          ((r.tStructure.truncLEι 0).app (F.obj X.obj)) ≫
        inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj))) =
      F.map ((t.truncGE 0).map ((t.truncLEι 0).app X.obj) ≫
        inv ((t.truncGEπ 0).app X.obj))
  have hGE :
      (F.mapTruncGEIso t r.tStructure 0 X.obj).hom ≫
          inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj)) =
        F.map (inv ((t.truncGEπ 0).app X.obj)) := by
    have hπ := F.mapTruncGEIso_π_comp_hom t r.tStructure 0 X.obj
    have hπ' : F.map (inv ((t.truncGEπ 0).app X.obj)) ≫
        (r.tStructure.truncGEπ 0).app (F.obj X.obj) =
          (F.mapTruncGEIso t r.tStructure 0 X.obj).hom := by
      rw [← hπ, ← Category.assoc, ← F.map_comp]
      simp
    rw [← hπ', Category.assoc]
    simp
  calc
    _ = (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X.obj)).hom ≫
        (r.tStructure.truncGE 0).map
          ((F.mapTruncLEIso t r.tStructure 0 X.obj).hom ≫
            (r.tStructure.truncLEι 0).app (F.obj X.obj)) ≫
          inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj)) := by
            simp only [Functor.map_comp, Category.assoc]
    _ = (F.mapTruncGEIso t r.tStructure 0 ((t.truncLE 0).obj X.obj)).hom ≫
        (r.tStructure.truncGE 0).map
          (F.map ((t.truncLEι 0).app X.obj)) ≫
          inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj)) := by
            rw [F.mapTruncLEIso_hom_comp_ι]
    _ = F.map ((t.truncGE 0).map ((t.truncLEι 0).app X.obj)) ≫
        (F.mapTruncGEIso t r.tStructure 0 X.obj).hom ≫
          inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj)) := by
            simpa only [Functor.id_obj, Category.assoc] using
              congrArg (fun g => g ≫
                inv ((r.tStructure.truncGEπ 0).app (F.obj X.obj)))
                (F.mapTruncGEIso_hom_naturality t r.tStructure 0
                  ((t.truncLEι 0).app X.obj)).symm
    _ = F.map ((t.truncGE 0).map ((t.truncLEι 0).app X.obj)) ≫
        F.map (inv ((t.truncGEπ 0).app X.obj)) := by rw [hGE]
    _ = _ := by rw [F.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Ambient fixed-target arrow extension induces fixed-target arrow
extension on hearts after applying degree-zero cohomology. This transfers a
geometric ambient extension hypothesis; it does not prove that hypothesis. -/
theorem fixedTargetArrowExtension_of_ambient
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) (X : t.heart.FullSubcategory)
    (h : Subobject.FixedTargetArrowExtension F X.obj) :
    Subobject.FixedTargetArrowExtension r.heartFunctor X := by
  intro Z β
  obtain ⟨Y, f, e, hβ⟩ := h β.hom
  let aZ := r.tStructure.heartH0OnHeartIso.app Z
  let aX := r.tStructure.heartH0OnHeartIso.app (r.heartFunctor.obj X)
  let cY := r.heartH0Comparison Y
  let cX := r.heartH0Comparison X.obj
  let YH := t.heartH0Functor.obj Y
  let fH : YH ⟶ X :=
    t.heartH0Functor.map f ≫ (t.heartH0OnHeartIso.app X).hom
  let eH : Z ≅ r.heartFunctor.obj YH :=
    aZ.symm ≪≫ (r.tStructure.heartH0Functor).mapIso e ≪≫ cY.symm
  refine ⟨YH, fH, eH, ?_⟩
  have hβH : (r.tStructure.heartH0Functor).map β.hom =
      (r.tStructure.heartH0Functor).map e.hom ≫
        (r.tStructure.heartH0Functor).map (F.map f) := by
    rw [hβ, Functor.map_comp]
  have hNatX : (r.tStructure.heartH0Functor).map β.hom ≫ aX.hom =
      aZ.hom ≫ β := by
    exact (r.tStructure.heartH0OnHeartIso.hom.naturality β)
  have hNatF : r.heartFunctor.map (t.heartH0Functor.map f) ≫ cX.hom =
      cY.hom ≫ (r.tStructure.heartH0Functor).map (F.map f) := by
    exact (r.heartH0ComparisonNatIso.hom.naturality f)
  have hNatF' : (r.tStructure.heartH0Functor).map (F.map f) =
      cY.inv ≫ r.heartFunctor.map (t.heartH0Functor.map f) ≫ cX.hom := by
    calc
      _ = cY.inv ≫ cY.hom ≫
          (r.tStructure.heartH0Functor).map (F.map f) := by simp
      _ = cY.inv ≫ r.heartFunctor.map (t.heartH0Functor.map f) ≫ cX.hom := by
        rw [← hNatF]
  calc
    β = aZ.inv ≫ (r.tStructure.heartH0Functor).map β.hom ≫ aX.hom := by
      rw [hNatX]
      simp
    _ = aZ.inv ≫ (r.tStructure.heartH0Functor).map e.hom ≫
        (r.tStructure.heartH0Functor).map (F.map f) ≫ aX.hom := by
      rw [hβH]
      simp only [Category.assoc]
    _ = aZ.inv ≫ (r.tStructure.heartH0Functor).map e.hom ≫ cY.inv ≫
        r.heartFunctor.map (t.heartH0Functor.map f) ≫ cX.hom ≫ aX.hom := by
      rw [hNatF']
      simp only [Category.assoc]
    _ = aZ.inv ≫ (r.tStructure.heartH0Functor).map e.hom ≫ cY.inv ≫
        r.heartFunctor.map (t.heartH0Functor.map f) ≫
          r.heartFunctor.map (t.heartH0OnHeartIso.app X).hom := by
      rw [heartH0Comparison_on_heart r X]
    _ = eH.hom ≫ r.heartFunctor.map fH := by
      simp only [eH, fH, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc]

end AmbientArrowExtension

/-- The restriction to hearts is additive when the ambient functor is additive. -/
noncomputable instance heartFunctor_additive
    [F.Additive] (r : t.Restriction F) :
    r.heartFunctor.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    change F.map (f.hom + g.hom) = F.map f.hom + F.map g.hom
    simp

/-- A triangulated, t-exact functor restricts to a functor preserving
monomorphisms on hearts. This uses the triangle associated to a heart mono;
t-exactness alone, without preservation of triangles, is insufficient. -/
noncomputable instance heartFunctor_preservesMonomorphisms
    [IsTriangulated D] [F.CommShift ℤ]
    [F.IsTriangulated] (r : t.Restriction F) :
    r.heartFunctor.PreservesMonomorphisms where
  preserves {X Y} f _ := by
    letI := t.hasHeartFullSubcategory
    obtain ⟨Q, q, δ, hT⟩ :=
      exists_distinguished_triangle_of_heart_mono t f
    letI := r.tStructure.hasHeartFullSubcategory
    have hF : Triangle.mk ((r.heartFunctor.map f).hom)
        ((r.heartFunctor.map q).hom)
        (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app X.obj) ∈ distTriang D := by
      have hF0 := F.map_distinguished _ hT
      change Triangle.mk (F.map f.hom) (F.map q.hom)
        (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app X.obj) ∈ distTriang D at hF0
      exact hF0
    have hS := r.tStructure.heartFullSubcategory_shortExact_of_distTriang
      (f := r.heartFunctor.map f) (g := r.heartFunctor.map q) hF
    exact hS.mono_f

attribute [local instance] heartFullSubcategoryAbelian

/-- A triangulated t-exact functor sends short exact sequences in the source
heart to short exact sequences in the target heart. -/
theorem heartFunctor_shortExact
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (S : ShortComplex t.heart.FullSubcategory) (hS : S.ShortExact) :
    (S.map r.heartFunctor).ShortExact := by
  letI := t.hasHeartFullSubcategory
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  obtain ⟨δ, hT⟩ := t.heartFullSubcategory_shortExact_triangle S.f S.g S.zero
    (fun {W} α hα =>
      ⟨hS.fIsKernel.lift (KernelFork.ofι α hα),
       hS.fIsKernel.fac (KernelFork.ofι α hα) WalkingParallelPair.zero⟩)
  have hTF : Triangle.mk ((r.heartFunctor.map S.f).hom)
      ((r.heartFunctor.map S.g).hom)
      (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app S.X₁.obj) ∈ distTriang D := by
    have hTF0 := F.map_distinguished _ hT
    change Triangle.mk (F.map S.f.hom) (F.map S.g.hom)
      (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app S.X₁.obj) ∈ distTriang D at hTF0
    exact hTF0
  exact r.tStructure.heartFullSubcategory_shortExact_of_distTriang
    (f := r.heartFunctor.map S.f) (g := r.heartFunctor.map S.g) hTF

/-- Exactness on heart short exact sequences gives preservation of finite
limits and colimits. -/
theorem heartFunctor_finiteExact
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) :
    PreservesFiniteLimits r.heartFunctor ∧
      PreservesFiniteColimits r.heartFunctor := by
  exact ((Functor.exact_tfae r.heartFunctor).out 0 3).1
    (heartFunctor_shortExact r)

/-- The restricted heart functor preserves binary joins of subobjects.
This is the categorical finite-sum step needed after pointwise lifts. -/
theorem heartFunctor_mapFunctor_sup
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F) (X : t.heart.FullSubcategory)
    (p q : Subobject X) :
    Subobject.mapFunctor r.heartFunctor (p ⊔ q) =
      Subobject.mapFunctor r.heartFunctor p ⊔
        Subobject.mapFunctor r.heartFunctor q := by
  letI : PreservesFiniteLimits r.heartFunctor := (heartFunctor_finiteExact r).1
  letI : PreservesFiniteColimits r.heartFunctor := (heartFunctor_finiteExact r).2
  exact Subobject.mapFunctor_sup r.heartFunctor p q

/-- Noetherianity transfers to a restricted heart when every ascending chain
of subobjects of each target-heart object lifts to subobjects of one
source-heart object, with the ambient and subobjects identified after applying
the heart functor. This is the categorical consequence of an anchored
filtration lift; constructing such lifts is a separate geometric obligation. -/
theorem isNoetherian_of_liftedSubobjectChains
    (r : t.Restriction F) [r.heartFunctor.PreservesMonomorphisms]
    (hglobal : t.IsNoetherian)
    (hlift : ∀ (Y : r.tStructure.heart.FullSubcategory)
      (c : ℕ →o Subobject Y),
      ∃ (X : t.heart.FullSubcategory)
        (e : r.heartFunctor.obj X ≅ Y) (d : ℕ →o Subobject X),
        ∀ n, (Subobject.map e.hom).obj
          (Subobject.mapFunctor r.heartFunctor (d n)) = c n) :
    r.tStructure.IsNoetherian := by
  intro Y
  apply CategoryTheory.isNoetherianObject_of_liftedSubobjectChains r.heartFunctor Y
  intro c
  obtain ⟨X, e, d, hd⟩ := hlift Y c
  exact ⟨X, e, d, hglobal X, hd⟩

/-- Pointwise lifts of each member of an ascending target-heart subobject
chain into one source-heart ambient object imply Noetherianity. The geometric
pointwise-lifting obligation remains explicit; finite-join preservation now
follows from the exactness of the restricted heart functor. -/
theorem isNoetherian_of_pointwiseChainLifts
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (hglobal : t.IsNoetherian)
    (hlift : ∀ (Y : r.tStructure.heart.FullSubcategory)
      (c : ℕ →o Subobject Y),
      ∃ (X : t.heart.FullSubcategory) (e : r.heartFunctor.obj X ≅ Y),
        ∀ n : ℕ, ∃ q : Subobject X,
          (Subobject.map e.hom).obj
            (Subobject.mapFunctor r.heartFunctor q) = c n) :
    r.tStructure.IsNoetherian := by
  letI := t.hasHeartFullSubcategory
  letI := r.tStructure.hasHeartFullSubcategory
  apply r.isNoetherian_of_liftedSubobjectChains hglobal
  intro Y c
  obtain ⟨X, e, hpt⟩ := hlift Y c
  obtain ⟨d, hd⟩ := CategoryTheory.anchored_chain_of_pointwise_lifts_iso
    r.heartFunctor X e (r.heartFunctor_mapFunctor_sup X) c hpt
  exact ⟨X, e, d, hd⟩

/-- A convenient whole-subobject lifting criterion for the chainwise result.
The chosen source ambient object is fixed for each target-heart object. -/
theorem isNoetherian_of_pointwiseSubobjectLifts
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (hglobal : t.IsNoetherian)
    (hlift : ∀ (Y : r.tStructure.heart.FullSubcategory),
      ∃ (X : t.heart.FullSubcategory) (e : r.heartFunctor.obj X ≅ Y),
        ∀ p : Subobject Y, ∃ q : Subobject X,
          (Subobject.map e.hom).obj
            (Subobject.mapFunctor r.heartFunctor q) = p) :
    r.tStructure.IsNoetherian := by
  apply r.isNoetherian_of_pointwiseChainLifts hglobal
  intro Y c
  obtain ⟨X, e, hpt⟩ := hlift Y
  exact ⟨X, e, fun n => hpt (c n)⟩

/-- For each target-heart object, choose a source lift whose fixed target
admits extension of monomorphisms. This pointwise criterion implies
Noetherianity without requiring arrow extension at unrelated source objects. -/
theorem isNoetherian_of_fixedTargetMonoExtensions
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (hglobal : t.IsNoetherian)
    (hlift : ∀ Y : r.tStructure.heart.FullSubcategory,
      ∃ X : t.heart.FullSubcategory, Nonempty (r.heartFunctor.obj X ≅ Y) ∧
        Subobject.FixedTargetMonoExtension r.heartFunctor X) :
    r.tStructure.IsNoetherian := by
  letI : PreservesFiniteLimits r.heartFunctor := (heartFunctor_finiteExact r).1
  letI : PreservesFiniteColimits r.heartFunctor := (heartFunctor_finiteExact r).2
  apply r.isNoetherian_of_pointwiseSubobjectLifts hglobal
  intro Y
  obtain ⟨X, ⟨⟨e⟩, hExt⟩⟩ := hlift Y
  refine ⟨X, e, ?_⟩
  intro p
  let E := Subobject.mapIsoToOrderIso e
  obtain ⟨q, hq⟩ :=
    Subobject.mapFunctor_surjective_of_fixedTargetMonoExtension
      r.heartFunctor X hExt (E.symm p)
  refine ⟨q, ?_⟩
  change E (Subobject.mapFunctor r.heartFunctor q) = p
  rw [hq]
  exact E.apply_symm_apply p

/-- Extension of every arrow into every fixed source-heart target is a
stronger geometric criterion. The zero arrow also supplies each target-heart
object as the image of some source object, so no separate object-lift premise
is needed. -/
theorem isNoetherian_of_fixedTargetArrowExtensions
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (hglobal : t.IsNoetherian)
    (hExt : ∀ X : t.heart.FullSubcategory,
      Subobject.FixedTargetArrowExtension r.heartFunctor X) :
    r.tStructure.IsNoetherian := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  letI : HasZeroObject t.heart.FullSubcategory := inferInstance
  letI : Zero t.heart.FullSubcategory := HasZeroObject.zero' _
  apply r.isNoetherian_of_fixedTargetMonoExtensions hglobal
  intro Y
  obtain ⟨X, _, e, _⟩ := hExt (0 : t.heart.FullSubcategory)
    (0 : Y ⟶ r.heartFunctor.obj (0 : t.heart.FullSubcategory))
  exact ⟨X, ⟨e.symm⟩, fun β _ => hExt X β⟩

/-- An ambient fixed-target arrow-extension hypothesis suffices for
Noetherianity of the restricted heart. Establishing this hypothesis for the
bounded-coherent geometric functor remains a separate obligation. -/
theorem isNoetherian_of_ambientFixedTargetArrowExtensions
    [IsTriangulated C] [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated]
    (r : t.Restriction F)
    (hglobal : t.IsNoetherian)
    (hExt : ∀ X : t.heart.FullSubcategory,
      Subobject.FixedTargetArrowExtension F X.obj) :
    r.tStructure.IsNoetherian :=
  r.isNoetherian_of_fixedTargetArrowExtensions hglobal
    (fun X => r.fixedTargetArrowExtension_of_ambient X (hExt X))

/-- The identity functor restricts every t-structure to itself. -/
def id (t : TStructure C) : t.Restriction (𝟭 C) where
  tStructure := t
  isTExact :=
    letI : (𝟭 C).IsRightTExact t t := ⟨fun _ _ hX ↦ hX⟩
    letI : (𝟭 C).IsLeftTExact t t := ⟨fun _ _ hX ↦ hX⟩
    Functor.isTExact_of

end Restriction

end CategoryTheory.Triangulated.TStructure
