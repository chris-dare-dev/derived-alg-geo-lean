/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformation

/-!
# Whiskering homogeneous dg natural transformations

A homogeneous dg natural transformation can be precomposed with a dg functor
on the source side and postcomposed with one on the target side.  Both
operations keep the degree, and neither introduces a sign.

## Where the Koszul sign is, and where it is not

It is tempting to expect a sign in `whiskerRight`, because it applies a
functor to a morphism of degree `n`.  There is none: a `DGFunctor` preserves
the graded composition on the nose (`DGFunctor.map_comp` carries no sign), so
transporting `η`'s graded naturality through `K` transports the sign
unchanged.  Likewise `whiskerLeft` is naturality of `η` evaluated at
`F.map p f`, again with `η`'s own sign and no other.

The sign appears one level up, in the **interchange law**.  For
`α : F ⟶ F'` of degree `n` and `β : G ⟶ G'` of degree `m` the two ways of
reading the horizontal composite differ by `(-1)^(m * n)`:

`(α ◁ G) ≫ (F' ▷ β) = (-1)^(m n) • ((F ▷ β) ≫ (α ◁ G'))`.

That is exactly graded naturality of `β` evaluated at the degree-`n` morphism
`α X`, which is why the sign is `β`'s degree times `α`'s and not something
new.  The two horizontal composites agree on the nose exactly when `m * n` is
even.

## Degrees

Whiskering does not change the degree, so both operations are additive in the
transformation and are packaged as `AddMonoidHom`s.  Vertical composition is
where degrees add, and `whiskerLeft_composition` and
`whiskerRight_composition` say whiskering is a homomorphism for it in every
result degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u'' u'''

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor.HomogeneousNatTrans

variable {C : Type u} {D : Type u'} {E : Type u''} {B : Type u'''}
  [DGCategory.{v} C] [DGCategory.{v} D] [DGCategory.{v} E] [DGCategory.{v} B]

/-! ### Left whiskering -/

section WhiskerLeft

variable (F : DGFunctor C D) {G H I : DGFunctor D E} {n m : ℤ}

/-- **Precomposition with a dg functor.**

The component at `X` is `η`'s component at `F.obj X`, and graded naturality is
`η`'s own, evaluated at `F.map p f`. -/
def whiskerLeft (η : HomogeneousNatTrans G H n) :
    HomogeneousNatTrans (F.comp G) (F.comp H) n :=
  ⟨fun X => app η (F.obj X), by
    intro X Y p r hpn hnp f
    exact naturality η p r hpn hnp (F.map p f)⟩

@[simp]
theorem whiskerLeft_app (η : HomogeneousNatTrans G H n) (X : C) :
    app (whiskerLeft F η) X = app η (F.obj X) :=
  rfl

@[simp]
theorem whiskerLeft_zero :
    whiskerLeft F (0 : HomogeneousNatTrans G H n) = 0 := by
  ext X
  rfl

theorem whiskerLeft_add (η θ : HomogeneousNatTrans G H n) :
    whiskerLeft F (η + θ) = whiskerLeft F η + whiskerLeft F θ := by
  ext X
  rfl

/-- Left whiskering as an additive map. -/
def whiskerLeftHom (G H : DGFunctor D E) (n : ℤ) :
    HomogeneousNatTrans G H n →+ HomogeneousNatTrans (F.comp G) (F.comp H) n :=
  AddMonoidHom.mk' (whiskerLeft F) (whiskerLeft_add F)

@[simp]
theorem whiskerLeftHom_apply (η : HomogeneousNatTrans G H n) :
    whiskerLeftHom F G H n η = whiskerLeft F η :=
  rfl

/-- Left whiskering takes the identity transformation to the identity. -/
@[simp]
theorem whiskerLeft_id (G : DGFunctor D E) :
    whiskerLeft F (id G) = id (F.comp G) :=
  rfl

/-- Left whiskering is a homomorphism for vertical composition, in every
result degree. -/
theorem whiskerLeft_composition (η : HomogeneousNatTrans G H n)
    (θ : HomogeneousNatTrans H I m) (r : ℤ) (h : n + m = r) :
    whiskerLeft F (composition G H I n m r h η θ) =
      composition (F.comp G) (F.comp H) (F.comp I) n m r h
        (whiskerLeft F η) (whiskerLeft F θ) := by
  ext X
  rw [whiskerLeft_app, composition_apply_app, composition_apply_app,
    whiskerLeft_app, whiskerLeft_app]
  rfl

/-- Left whiskering commutes with the pointwise differential. -/
@[simp]
theorem whiskerLeft_differential (η : HomogeneousNatTrans G H n) :
    differential (whiskerLeft F η) = whiskerLeft F (differential η) :=
  rfl

/-- A whiskered closed transformation is closed. -/
theorem IsClosed.whiskerLeft {η : HomogeneousNatTrans G H n} (hη : IsClosed η) :
    IsClosed (HomogeneousNatTrans.whiskerLeft F η) := by
  ext X
  rw [whiskerLeft_differential, whiskerLeft_app, zero_app]
  exact congrArg (fun σ => app σ (F.obj X)) hη

end WhiskerLeft

/-! ### Right whiskering -/

section WhiskerRight

variable {F G H : DGFunctor C D} {n m : ℤ}

/-- **Postcomposition with a dg functor.**

The component at `X` is `K` applied to `η`'s component, in the same degree
`n`.  No sign appears: `K` preserves the graded composition on the nose, so it
carries `η`'s naturality equation across sign and all. -/
def whiskerRight (η : HomogeneousNatTrans F G n) (K : DGFunctor D E) :
    HomogeneousNatTrans (F.comp K) (G.comp K) n :=
  ⟨fun X => K.map n (app η X), by
    intro X Y p r hpn hnp f
    show dgComp p n r hpn (K.map p (F.map p f)) (K.map n (app η Y)) =
      (n * p).negOnePow •
        dgComp n p r hnp (K.map n (app η X)) (K.map p (G.map p f))
    rw [← K.map_comp p n r hpn, ← K.map_comp n p r hnp,
      naturality η p r hpn hnp f]
    simp [Units.smul_def, map_zsmul]⟩

@[simp]
theorem whiskerRight_app (η : HomogeneousNatTrans F G n) (K : DGFunctor D E)
    (X : C) :
    app (whiskerRight η K) X = K.map n (app η X) :=
  rfl

@[simp]
theorem whiskerRight_zero (K : DGFunctor D E) :
    whiskerRight (0 : HomogeneousNatTrans F G n) K = 0 := by
  ext X
  exact map_zero (K.map n)

theorem whiskerRight_add (η θ : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    whiskerRight (η + θ) K = whiskerRight η K + whiskerRight θ K := by
  ext X
  exact map_add (K.map n) (app η X) (app θ X)

/-- Right whiskering as an additive map. -/
def whiskerRightHom (F G : DGFunctor C D) (n : ℤ) (K : DGFunctor D E) :
    HomogeneousNatTrans F G n →+ HomogeneousNatTrans (F.comp K) (G.comp K) n :=
  AddMonoidHom.mk' (fun η => whiskerRight η K)
    (fun η θ => whiskerRight_add η θ K)

@[simp]
theorem whiskerRightHom_apply (η : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    whiskerRightHom F G n K η = whiskerRight η K :=
  rfl

/-- Right whiskering takes the identity transformation to the identity.  This
is `DGFunctor.map_id`, and it is the one place where right whiskering needs
more than additivity of `K.map`. -/
@[simp]
theorem whiskerRight_id (F : DGFunctor C D) (K : DGFunctor D E) :
    whiskerRight (id F) K = id (F.comp K) := by
  ext X
  exact K.map_id (F.obj X)

/-- Right whiskering is a homomorphism for vertical composition, in every
result degree.  This is `DGFunctor.map_comp`. -/
theorem whiskerRight_composition (η : HomogeneousNatTrans F G n)
    (θ : HomogeneousNatTrans G H m) (r : ℤ) (h : n + m = r)
    (K : DGFunctor D E) :
    whiskerRight (composition F G H n m r h η θ) K =
      composition (F.comp K) (G.comp K) (H.comp K) n m r h
        (whiskerRight η K) (whiskerRight θ K) := by
  ext X
  rw [whiskerRight_app, composition_apply_app, composition_apply_app,
    whiskerRight_app, whiskerRight_app, K.map_comp n m r h]
  rfl

/-- Right whiskering commutes with the pointwise differential.  This is
`DGFunctor.map_d`. -/
@[simp]
theorem whiskerRight_differential (η : HomogeneousNatTrans F G n)
    (K : DGFunctor D E) :
    differential (whiskerRight η K) = whiskerRight (differential η) K := by
  ext X
  rw [differential_app, whiskerRight_app, whiskerRight_app, differential_app,
    K.map_d n (n + 1)]
  rfl

/-- A whiskered closed transformation is closed. -/
theorem IsClosed.whiskerRight {η : HomogeneousNatTrans F G n} (hη : IsClosed η)
    (K : DGFunctor D E) :
    IsClosed (HomogeneousNatTrans.whiskerRight η K) := by
  ext X
  rw [whiskerRight_differential, whiskerRight_app, zero_app]
  have h := congrArg (fun σ => app σ X) hη
  simp only [zero_app] at h
  rw [h, map_zero]
  rfl

end WhiskerRight

/-! ### Whiskering by a composite

All three laws hold by `rfl`, because `DGFunctor.comp` composes the object maps
and the `AddMonoidHom`s directly.  They are what makes horizontal composition
of dg natural transformations strictly associative. -/

section Compat

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {n m : ℤ}

/-- Whiskering twice on the right is whiskering by the composite. -/
theorem whiskerRight_whiskerRight (α : HomogeneousNatTrans F F' n)
    (G : DGFunctor D E) (K : DGFunctor E B) :
    whiskerRight (whiskerRight α G) K = whiskerRight α (G.comp K) :=
  rfl

/-- Whiskering twice on the left is whiskering by the composite. -/
theorem whiskerLeft_whiskerLeft (F : DGFunctor C D) (G : DGFunctor D E)
    {K K' : DGFunctor E B} (β : HomogeneousNatTrans K K' n) :
    whiskerLeft F (whiskerLeft G β) = whiskerLeft (F.comp G) β :=
  rfl

/-- Whiskering on the two sides commutes. -/
theorem whiskerRight_whiskerLeft (F : DGFunctor C D)
    (β : HomogeneousNatTrans G G' m) (K : DGFunctor E B) :
    whiskerRight (whiskerLeft F β) K = whiskerLeft F (whiskerRight β K) :=
  rfl

end Compat

/-! ### The interchange law -/

section Interchange

variable {F F' : DGFunctor C D} {G G' : DGFunctor D E} {n m : ℤ}

/-- **The Godement interchange law, componentwise.**

Reading the horizontal composite of `α` and `β` in the two possible orders
differs by `(-1)^(m * n)`.  The identity is nothing but graded naturality of
`β` evaluated at the degree-`n` morphism `α X`, which is why the sign is
`β`'s degree times `α`'s and not something new. -/
theorem interchange_app (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (hnm : n + m = r)
    (hmn : m + n = r) (X : C) :
    dgComp n m r hnm (G.map n (app α X)) (app β (F'.obj X)) =
      (m * n).negOnePow •
        dgComp m n r hmn (app β (F.obj X)) (G'.map n (app α X)) :=
  naturality β n r hnm hmn (app α X)

/-- **The Godement interchange law.**

`(α ◁ G) ≫ (F' ▷ β) = (-1)^(m n) • ((F ▷ β) ≫ (α ◁ G'))`, with `n` the degree
of `α` and `m` the degree of `β`.  Both sides are transformations
`F ⋙ G ⟶ F' ⋙ G'` of degree `r`; the two vertical composites are taken in the
two orders, which is why `r` comes with both `n + m = r` and `m + n = r`. -/
theorem interchange (α : HomogeneousNatTrans F F' n)
    (β : HomogeneousNatTrans G G' m) (r : ℤ) (hnm : n + m = r)
    (hmn : m + n = r) :
    composition (F.comp G) (F'.comp G) (F'.comp G') n m r hnm
        (whiskerRight α G) (whiskerLeft F' β) =
      (m * n).negOnePow •
        composition (F.comp G) (F.comp G') (F'.comp G') m n r hmn
          (whiskerLeft F β) (whiskerRight α G') := by
  ext X
  rw [composition_apply_app, whiskerRight_app, whiskerLeft_app,
    units_smul_app, composition_apply_app, whiskerLeft_app, whiskerRight_app]
  exact interchange_app α β r hnm hmn X

end Interchange

end DGFunctor.HomogeneousNatTrans

end CategoryTheory
