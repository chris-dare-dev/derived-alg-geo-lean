/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Basic
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# A Serre functor is unique up to natural isomorphism

Any two Serre functors on the same `k`-linear category are naturally isomorphic, and the
isomorphism compatible with both duality isomorphisms is unique. The argument is Yoneda: `S A`
represents `B ↦ Dual (A ⟶ B)`, representing objects are unique up to unique isomorphism, and
naturality in `A` promotes the pointwise isomorphisms to a natural isomorphism of functors.

## The representability step is public API, not a private step

`isoOfLinearYonedaIso` is stated on `linearYoneda` alone and proved **without reference to
`SerreFunctorData`**, because a downstream lane needs it on a functor that is not a Serre functor.
It is `Functor.preimageIso` against Mathlib's `full_linearYoneda` and `faithful_linearYoneda`, so
nothing about representability is hand-rolled here.

## Trap: which variable the Yoneda argument runs in

`Hom(A,B)` is contravariant in `A` and covariant in `B`, and the dual flips both — so
`Dual (A ⟶ B)` is **covariant in `A`** and **contravariant in `B`**, matching `Hom(B, S A)`.

The Yoneda argument therefore runs in the `B` variable with `A` fixed, which is why the right
functor is `linearYoneda` and not `linearCoyoneda`. In this repository
`(linearCoyoneda k C).obj (op X)` is the *covariant* `Hom(X, −)`, so running the argument there
produces a statement that typechecks against the opposite functor and proves nothing about `S`.
Naturality in `A` is a separate step, and it is what promotes the pointwise isomorphisms to a
natural transformation.

Concretely: `yonedaIso` below is natural in `B` by `naturality_right`, and `uniqueIso` is natural
in `A` by `naturality_left`. Two different fields of `SerreFunctorData`, for two different reasons.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SerreFunctor

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-! ### Representability, independent of any Serre functor -/

section Representability

variable (k C)

/-- **Representing objects are unique.** A natural isomorphism of the linear Yoneda presheaves
gives an isomorphism of the representing objects.

Public and `SerreFunctorData`-free on purpose; see the module docstring. This is
`Functor.preimageIso` against Mathlib's `full_linearYoneda` and `faithful_linearYoneda`. -/
noncomputable def isoOfLinearYonedaIso {X Y : C}
    (e : (linearYoneda k C).obj X ≅ (linearYoneda k C).obj Y) : X ≅ Y :=
  (linearYoneda k C).preimageIso e

@[simp]
theorem map_isoOfLinearYonedaIso {X Y : C}
    (e : (linearYoneda k C).obj X ≅ (linearYoneda k C).obj Y) :
    (linearYoneda k C).mapIso (isoOfLinearYonedaIso k C e) = e := by
  ext : 1
  exact (linearYoneda k C).map_preimage e.hom

/-- Two morphisms agreeing after the linear Yoneda embedding are equal. -/
theorem hom_ext_of_linearYoneda {X Y : C} {f g : X ⟶ Y}
    (h : (linearYoneda k C).map f = (linearYoneda k C).map g) : f = g :=
  (linearYoneda k C).map_injective h

end Representability

/-! ### Uniqueness of the Serre functor -/

namespace SerreFunctorData

variable (D D' : SerreFunctorData k C)

/-- The comparison of the two duality isomorphisms at a fixed pair, as a linear equivalence
`(B ⟶ S A) ≃ₗ (B ⟶ S' A)`. -/
noncomputable def compareEquiv (A B : C) : (B ⟶ D.S.obj A) ≃ₗ[k] (B ⟶ D'.S.obj A) :=
  (D.eta A B).symm.trans (D'.eta A B)

theorem compareEquiv_apply (A B : C) (psi : B ⟶ D.S.obj A) :
    D.compareEquiv D' A B psi = D'.eta A B ((D.eta A B).symm psi) := rfl

/-- **Naturality in `B`**, from `naturality_right`. This is the step the Yoneda argument runs
on. -/
theorem compareEquiv_naturality_right {A B B' : C} (g : B' ⟶ B) (psi : B ⟶ D.S.obj A) :
    D.compareEquiv D' A B' (g ≫ psi) = g ≫ D.compareEquiv D' A B psi := by
  have hphi : (D.eta A B').symm (g ≫ psi) =
      ((D.eta A B).symm psi).comp (Linear.rightComp k A g) := by
    apply (D.eta A B').injective
    rw [LinearEquiv.apply_symm_apply, D.naturality_right g ((D.eta A B).symm psi),
      LinearEquiv.apply_symm_apply]
  rw [compareEquiv_apply, compareEquiv_apply, hphi,
    D'.naturality_right g ((D.eta A B).symm psi)]

/-- The two representing objects have isomorphic linear Yoneda presheaves, at each `A`. -/
noncomputable def yonedaIso (A : C) :
    (linearYoneda k C).obj (D.S.obj A) ≅ (linearYoneda k C).obj (D'.S.obj A) :=
  NatIso.ofComponents
    (fun B ↦ (D.compareEquiv D' A B.unop).toModuleIso)
    (by
      intro B B' g
      refine ModuleCat.hom_ext (LinearMap.ext fun psi ↦ ?_)
      exact D.compareEquiv_naturality_right D' g.unop psi)

/-- **The comparison isomorphism at an object.** -/
noncomputable def uniqueIsoApp (A : C) : D.S.obj A ≅ D'.S.obj A :=
  isoOfLinearYonedaIso k C (D.yonedaIso D' A)

/-- The defining property of `uniqueIsoApp`: it is what the duality isomorphisms say it is. -/
theorem comp_uniqueIsoApp_hom {A B : C} (psi : B ⟶ D.S.obj A) :
    psi ≫ (D.uniqueIsoApp D' A).hom = D.compareEquiv D' A B psi := by
  have h := congrArg (fun e ↦ (e.hom.app (Opposite.op B)) psi)
    (map_isoOfLinearYonedaIso k C (D.yonedaIso D' A))
  exact h

/-- Evaluating the defining property at the identity. -/
theorem uniqueIsoApp_hom_eq (A : C) :
    (D.uniqueIsoApp D' A).hom = D.compareEquiv D' A (D.S.obj A) (𝟙 _) := by
  have h := D.comp_uniqueIsoApp_hom D' (𝟙 (D.S.obj A))
  rwa [Category.id_comp] at h

/-- **Naturality in `A`**, from `naturality_left`. This is the step that promotes the pointwise
isomorphisms to a natural isomorphism of functors; see the module docstring on why it is a
different field from the one `yonedaIso` uses. -/
theorem uniqueIsoApp_naturality {A A' : C} (f : A ⟶ A') :
    D.S.map f ≫ (D.uniqueIsoApp D' A').hom = (D.uniqueIsoApp D' A).hom ≫ D'.S.map f := by
  set phi := (D.eta A (D.S.obj A)).symm (𝟙 (D.S.obj A)) with hphi
  have hkey : (D.eta A' (D.S.obj A)).symm (D.S.map f) =
      phi.comp (Linear.leftComp k (D.S.obj A) f) := by
    apply (D.eta A' (D.S.obj A)).injective
    rw [LinearEquiv.apply_symm_apply, D.naturality_left f phi, hphi,
      LinearEquiv.apply_symm_apply, Category.id_comp]
  rw [D.comp_uniqueIsoApp_hom D' (D.S.map f), compareEquiv_apply, hkey,
    D'.naturality_left f phi, ← compareEquiv_apply, ← uniqueIsoApp_hom_eq]

/-- **A Serre functor is unique up to natural isomorphism.** -/
noncomputable def uniqueIso : D.S ≅ D'.S :=
  NatIso.ofComponents (fun A ↦ D.uniqueIsoApp D' A) (fun f ↦ D.uniqueIsoApp_naturality D' f)

@[simp]
theorem uniqueIso_hom_app (A : C) :
    (D.uniqueIso D').hom.app A = (D.uniqueIsoApp D' A).hom := rfl

/-- **The compatibility with the two duality isomorphisms**, which is what characterises the
comparison. -/
theorem uniqueIso_compat {A B : C} (phi : Module.Dual k (A ⟶ B)) :
    D.eta A B phi ≫ (D.uniqueIso D').hom.app A = D'.eta A B phi := by
  rw [uniqueIso_hom_app, D.comp_uniqueIsoApp_hom D', compareEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- **Uniqueness of the comparison.** Any natural transformation compatible with both duality
isomorphisms is `uniqueIso`. This is the form a downstream coherence argument consumes, so it is
not optional polish. -/
theorem uniqueIso_unique (alpha : D.S ⟶ D'.S)
    (h : ∀ (A B : C) (phi : Module.Dual k (A ⟶ B)),
      D.eta A B phi ≫ alpha.app A = D'.eta A B phi) :
    alpha = (D.uniqueIso D').hom := by
  ext A
  have hid : D.eta A (D.S.obj A) ((D.eta A (D.S.obj A)).symm (𝟙 _)) = 𝟙 (D.S.obj A) :=
    LinearEquiv.apply_symm_apply _ _
  have h1 := h A (D.S.obj A) ((D.eta A (D.S.obj A)).symm (𝟙 _))
  have h2 := D.uniqueIso_compat D' ((D.eta A (D.S.obj A)).symm (𝟙 (D.S.obj A)))
  rw [hid, Category.id_comp] at h1
  rw [hid, Category.id_comp] at h2
  rw [h1, ← h2, uniqueIso_hom_app]

/-! ### Coherence

So a downstream user can move a statement between two chosen Serre functors without re-deriving
the comparison. Each is `uniqueIso_unique` applied to the obvious candidate. -/

theorem uniqueIso_refl : D.uniqueIso D = Iso.refl D.S := by
  refine Iso.ext ?_
  exact (D.uniqueIso_unique D (𝟙 D.S) (fun A B phi ↦ by rw [NatTrans.id_app, Category.comp_id])).symm

theorem uniqueIso_trans (D'' : SerreFunctorData k C) :
    (D.uniqueIso D').hom ≫ (D'.uniqueIso D'').hom = (D.uniqueIso D'').hom := by
  refine D.uniqueIso_unique D'' _ fun A B phi ↦ ?_
  rw [NatTrans.comp_app, ← Category.assoc, D.uniqueIso_compat D' phi,
    D'.uniqueIso_compat D'' phi]

theorem uniqueIso_symm : (D.uniqueIso D').symm = D'.uniqueIso D := by
  refine Iso.ext ?_
  refine D'.uniqueIso_unique D _ fun A B phi ↦ ?_
  have h : (D.eta A B phi ≫ (D.uniqueIso D').hom.app A) ≫ (D.uniqueIso D').inv.app A =
      D.eta A B phi := by
    rw [Category.assoc, ← NatTrans.comp_app, (D.uniqueIso D').hom_inv_id,
      NatTrans.id_app, Category.comp_id]
  rwa [D.uniqueIso_compat D' phi] at h

/-- **`HasSerreFunctor` determines `S` up to natural isomorphism**, so "the" Serre functor is a
well-defined statement about `C`. -/
theorem exists_uniqueIso (D D' : SerreFunctorData k C) : Nonempty (D.S ≅ D'.S) :=
  ⟨D.uniqueIso D'⟩

end SerreFunctorData

end CategoryTheory.SerreFunctor
