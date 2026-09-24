/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ImageFactorisation
import DerivedAlgGeo.CategoryTheory.Subobject.NoetherianObject
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
Pointwise lifts suffice when the heart functor preserves binary joins of
subobjects; both that preservation and the pointwise lifts remain explicit
inputs to the categorical result.

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

/-- Pointwise lifting of target-heart subobjects into one source-heart ambient
object implies Noetherianity when the restricted heart functor preserves binary
joins of source subobjects. This separates the finite-join step in the proof of
Lemma 4.16(3) from the geometric pointwise-lifting obligation. -/
theorem isNoetherian_of_pointwiseSubobjectLifts
    [HasImages t.heart.FullSubcategory]
    [HasBinaryCoproducts t.heart.FullSubcategory]
    (r : t.Restriction F) [r.heartFunctor.PreservesMonomorphisms]
    [HasImages r.tStructure.heart.FullSubcategory]
    [HasBinaryCoproducts r.tStructure.heart.FullSubcategory]
    (hglobal : t.IsNoetherian)
    (hjoin : ∀ (X : t.heart.FullSubcategory) (p q : Subobject X),
      Subobject.mapFunctor r.heartFunctor (p ⊔ q) =
        Subobject.mapFunctor r.heartFunctor p ⊔
          Subobject.mapFunctor r.heartFunctor q)
    (hlift : ∀ (Y : r.tStructure.heart.FullSubcategory),
      ∃ (X : t.heart.FullSubcategory) (e : r.heartFunctor.obj X ≅ Y),
        ∀ p : Subobject Y, ∃ q : Subobject X,
          (Subobject.map e.hom).obj
            (Subobject.mapFunctor r.heartFunctor q) = p) :
    r.tStructure.IsNoetherian := by
  letI := t.hasHeartFullSubcategory
  letI := r.tStructure.hasHeartFullSubcategory
  apply r.isNoetherian_of_liftedSubobjectChains hglobal
  intro Y c
  obtain ⟨X, e, hpt⟩ := hlift Y
  obtain ⟨d, hd⟩ := CategoryTheory.anchored_chain_of_pointwise_lifts_iso
    r.heartFunctor X e (hjoin X) c (fun n => hpt (c n))
  exact ⟨X, e, d, hd⟩

/-- The identity functor restricts every t-structure to itself. -/
def id (t : TStructure C) : t.Restriction (𝟭 C) where
  tStructure := t
  isTExact :=
    letI : (𝟭 C).IsRightTExact t t := ⟨fun _ _ hX ↦ hX⟩
    letI : (𝟭 C).IsLeftTExact t t := ⟨fun _ _ hX ↦ hX⟩
    Functor.isTExact_of

end Restriction

end CategoryTheory.Triangulated.TStructure
