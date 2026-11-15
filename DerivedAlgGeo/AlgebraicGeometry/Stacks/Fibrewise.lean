/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.UniversallyStable
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty

/-!
# Properties of the fibres over field-valued points

Let `F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat` be a category-valued pseudofunctor on schemes over
`S`, and let `Φ` assign to every field `k` and every point `t : Spec k ⟶ S` a property of objects
of the fibre of `F` over `t`. An object `M` of `F` over `T` satisfies `fibrewise Φ` when its
pullback along every field-valued point of `T` satisfies `Φ`; "every fibre is semistable" is of
this form.

If every `Φ k t` is closed under isomorphisms, `fibrewise Φ` is preserved by pullback. If `Φ`
moreover descends along field extensions, `fibrewise Φ` is local for the fpqc topology on
`Over S`, so for a stack `F`, `StackInGroupoids.ofObjectProperty F (fibrewise Φ)` is the stack of
objects of `F` all of whose fibres over field-valued points satisfy `Φ`.

## Main definitions

* `AlgebraicGeometry.FieldPointProperty F`: a property of objects of `F` over every field-valued
  point of `S`.
* `AlgebraicGeometry.FieldPointProperty.atPoints`: `Φ` as an object property of `F`, on the
  objects of `Over S` that are field-valued points.
* `AlgebraicGeometry.FieldPointProperty.DescendsAlongExtensions`: `Φ` holds of `N` whenever it
  holds of the pullback of `N` along a field extension.
* `AlgebraicGeometry.Pseudofunctor.ObjectProperty.fibrewise Φ : F.ObjectProperty`.

## Main results

* `fibrewise_prop_iff`: `M` satisfies `fibrewise Φ` iff its pullback along every field-valued
  point satisfies `Φ`.
* `fibrewise_isClosedUnderMapObj`: `fibrewise Φ` is preserved by pullback.
* `fibrewise_isLocal`: if `Φ` descends along field extensions, `fibrewise Φ` is local for the
  fpqc topology; `fibrewise_isLocal_of_le` for every topology whose covering sieves contain
  jointly surjective families.

## Implementation notes

A field-valued point of `T : Over S` is taken to be a morphism `Over.mk t ⟶ T` of `Over S` with
`t : Spec k ⟶ S`, rather than a morphism `Spec k ⟶ T.left`. Composing with `g : T' ⟶ T` keeps
this form, so no two objects of `Over S` that are only propositionally equal, such as
`Over.mk (t' ≫ T'.hom)` and `Over.mk ((t' ≫ g.left) ≫ T.hom)`, ever have to be identified.
`fibrewise Φ` is the universally stable closure `universallyStable Φ.atPoints`, so its pullback
stability and closure under isomorphisms are those of `universallyStable`.

## References

* A. Bayer, M. Lahoz, E. Macrì, H. Nuer, A. Perry, P. Stellari, *Stability conditions in
  families*, arXiv:1902.08184, Definition 9.1 and the proof of Proposition 9.2.

## Tags

fibrewise, field-valued point, substack, local property, descent
-/

universe w v u

namespace AlgebraicGeometry

open CategoryTheory Opposite Limits Bicategory

variable {S : Scheme.{u}} (F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{v, w})

/-- A property of objects over every field-valued point of `S`: for every field `k` and every
`t : Spec k ⟶ S`, a property of the objects of `F` over `Over.mk t`. -/
abbrev FieldPointProperty :=
  ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S), ObjectProperty (F.obj (.mk (op (Over.mk t))))

variable {F} (Φ : FieldPointProperty F)

namespace FieldPointProperty

/-- `Φ` on the objects of `Over S` that are field-valued points of `S`: `M` over `X` satisfies
`Φ.atPoints` when its transport along every identification `Over.mk t ≅ X` of `X` with a
field-valued point `t` satisfies `Φ`. Over an `X` that is not a field-valued point it holds
vacuously. -/
def atPoints : F.ObjectProperty where
  prop X M := ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S) (e : Over.mk t ≅ X.as.unop),
    Φ k t ((F.map e.hom.op.toLoc).toFunctor.obj M)

instance atPoints_isClosedUnderIsomorphisms
    [∀ (k : Type u) [Field k] t, (Φ k t).IsClosedUnderIsomorphisms] :
    Φ.atPoints.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms _ :=
    { of_iso := fun e hM k _ t e' =>
        (Φ k t).prop_of_iso ((F.map e'.hom.op.toLoc).toFunctor.mapIso e) (hM k t e') }

/-- `Φ` descends along field extensions: for a field extension `k ⊆ k'`, a point
`t : Spec k ⟶ S` and an object `N` over `t`, if the pullback of `N` to `Spec k'` satisfies `Φ`,
then so does `N`. -/
def DescendsAlongExtensions : Prop :=
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (t : Spec (.of k) ⟶ S)
    (N : F.obj (.mk (op (Over.mk t)))),
    Φ k' (Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ t)
      ((F.map (Over.homMk (V := Over.mk t)
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).op.toLoc).toFunctor.obj N) →
    Φ k t N

end FieldPointProperty

namespace Pseudofunctor.ObjectProperty

/-- An object `M` of `F` over `T` satisfies `fibrewise Φ` when its pullback along every
field-valued point of `T` satisfies `Φ` (`fibrewise_prop_iff`). This is the condition of
Definition 9.1 of arXiv:1902.08184 on the fibres of a family, and the proof of Proposition 9.2
there shows that such conditions can be checked locally.

All field-valued points are used, not only the residue fields of the points of `T`: a
field-valued point of `T` composed with `g : T' ⟶ T` is a field-valued point of `T'`, so
`fibrewise Φ` is preserved by pullback (`fibrewise_isClosedUnderMapObj`) without any base-change
theorem for `Φ`. -/
def fibrewise : F.ObjectProperty :=
  Φ.atPoints.universallyStable

variable [∀ (k : Type u) [Field k] t, (Φ k t).IsClosedUnderIsomorphisms]

instance fibrewise_isClosedUnderIsomorphisms : (fibrewise Φ).IsClosedUnderIsomorphisms :=
  inferInstanceAs Φ.atPoints.universallyStable.IsClosedUnderIsomorphisms

instance fibrewise_isClosedUnderMapObj : (fibrewise Φ).IsClosedUnderMapObj :=
  inferInstanceAs Φ.atPoints.universallyStable.IsClosedUnderMapObj

/-- `M` satisfies `fibrewise Φ` iff its pullback along every field-valued point of the base
satisfies `Φ`. -/
theorem fibrewise_prop_iff {X : LocallyDiscrete (Over S)ᵒᵖ} (M : F.obj X) :
    (fibrewise Φ).prop X M ↔ ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S)
      (p : Over.mk t ⟶ X.as.unop), Φ k t ((F.map p.op.toLoc).toFunctor.obj M) := by
  refine ⟨fun hM k _ t p => ?_, fun hM Y f k _ t e => ?_⟩
  · exact (Φ k t).prop_of_iso ((Cat.Hom.toNatIso (F.mapId' _)).app _)
      (hM (.mk (op (Over.mk t))) p.op.toLoc k t (Iso.refl _))
  · exact (Φ k t).prop_of_iso
      ((Cat.Hom.toNatIso (F.mapComp' f e.hom.op.toLoc (e.hom ≫ f.as.unop).op.toLoc rfl)).app M)
      (hM k t (e.hom ≫ f.as.unop))

variable {Φ}

/-- If `Φ` descends along field extensions, `fibrewise Φ` is local for every topology `J` whose
covering sieves contain jointly surjective families: a field-valued point of the base lifts,
after a field extension, to a field-valued point of some member of the family. -/
theorem fibrewise_isLocal_of_le (hΦ : Φ.DescendsAlongExtensions)
    {J : GrothendieckTopology Scheme.{u}} (hJ : J ≤ Scheme.grothendieckTopology ⊤) :
    (fibrewise Φ).IsLocal (J.over S) where
  of_sieve {T} M R hR h := by
    rw [fibrewise_prop_iff]
    intro k _ t p
    obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology (hJ _ hR)
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq (p.left (default : Spec (.of k)))
    obtain ⟨x, -⟩ := Scheme.Pullback.exists_preimage_pullback z _ hz
    -- Only a field-valued point of the pullback is used, not that its field is a residue field.
    obtain ⟨K, _, ⟨a⟩⟩ : ∃ (K : Type u) (_ : Field K),
        Nonempty (Spec (.of K) ⟶ pullback (𝒰.f i) p.left) :=
      ⟨_, inferInstance, ⟨(pullback (𝒰.f i) p.left).fromSpecResidueField x⟩⟩
    let : Algebra k K := (Spec.preimage (a ≫ pullback.snd _ _)).hom.toAlgebra
    have ha : Spec.map (CommRingCat.ofHom (algebraMap k K)) = a ≫ pullback.snd _ _ :=
      Spec.map_preimage (a ≫ pullback.snd _ _)
    let g : Over.mk (𝒰.f i ≫ T.hom) ⟶ T := Over.homMk (𝒰.f i)
    let q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶
        Over.mk (𝒰.f i ≫ T.hom) :=
      Over.homMk (a ≫ pullback.fst _ _) (by simp [ha, pullback.condition_assoc])
    let e : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t) ⟶ Over.mk t :=
      Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    have hcomp : e ≫ p = q ≫ g := by
      ext
      simp [e, q, g, ha, pullback.condition]
    have hg := (fibrewise_prop_iff Φ _).1
      (h g ((Sieve.overEquiv_iff R _).1 (h𝒰 _ _ (Presieve.ofArrows.mk i)))) _ _ q
    have e₁ := (Cat.Hom.toNatIso (F.mapComp' g.op.toLoc q.op.toLoc (q ≫ g).op.toLoc rfl)).app M
    have e₂ := (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc e.op.toLoc (q ≫ g).op.toLoc
      (by rw [← hcomp]; rfl))).app M
    exact hΦ k K t _ ((Φ K _).prop_of_iso (e₁.symm ≪≫ e₂) hg)

/-- If `Φ` descends along field extensions, `fibrewise Φ` is local for the fpqc topology on
`Over S`. So if `F` is a stack, `StackInGroupoids.ofObjectProperty F (fibrewise Φ)` is the stack
of objects of `F` whose fibres over all field-valued points satisfy `Φ`.

Descent along field extensions cannot be dropped. Let `S = Spec ℝ`, let `F` be the constant
pseudofunctor with value the category with one object, and let `Φ k t` hold exactly when `k`
contains a square root of `-1`; every property of objects of a category with one object is
closed under isomorphisms. Over `Spec ℂ` every field-valued point makes its field a
`ℂ`-algebra, so `fibrewise Φ` holds there, and the single morphism `Spec ℂ ⟶ Spec ℝ` is an fpqc
covering. Over `Spec ℝ`, `fibrewise Φ` fails at the identity point. So `fibrewise Φ` is not local,
and `Φ` does not descend along `ℝ ⊆ ℂ`. -/
theorem fibrewise_isLocal (hΦ : Φ.DescendsAlongExtensions) :
    (fibrewise Φ).IsLocal (Scheme.fpqcTopology.over S) :=
  fibrewise_isLocal_of_le hΦ <| Precoverage.toGrothendieck_mono <|
    Scheme.propQCPrecoverage_le_precoverage.trans (Scheme.precoverage_mono le_top)

end Pseudofunctor.ObjectProperty

end AlgebraicGeometry
