/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.Basic
import DerivedAlgGeo.CategoryTheory.Sites.Over

/-!
# Change of base for algebraic spaces

Let `T` be a scheme over `S` and `π : G ⟶ yoneda.obj T` a morphism of presheaves on `Over S`.
The fibres of `π` form a presheaf on `Over T.left`: its value on `W` is the set of sections of
`G` over `W`, viewed over `S`, that `π` sends to the structure morphism of `W`. Then `G` is an
algebraic space over `S` exactly when this presheaf is an algebraic space over `T.left`. This is
the object-level content of Stacks 04SG: an algebraic space over `T.left` is the same as an
algebraic space over `S` with a map to `T`.

## Main definitions

* `AlgebraicGeometry.changeOfBaseSlice π`: the fibres of `π`, as a presheaf on the slice
  `Over T` of `Over S`.
* `AlgebraicGeometry.changeOfBase π`: the fibres of `π`, as a presheaf on `Over T.left`.
* `AlgebraicGeometry.changeOfBaseIso π`: `changeOfBase π` is `changeOfBaseSlice π` read through
  `Over.iteratedSliceEquiv T`.

## Main results

The three conditions of `AlgebraicGeometry.isAlgebraicSpace` correspond one by one.
* `AlgebraicGeometry.isSheaf_iff_isSheaf_changeOfBase`: `G` is an fppf sheaf over `S` if and only
  if `changeOfBase π` is one over `T.left`.
* `AlgebraicGeometry.relativelyRepresentable_diag_iff_changeOfBase`: the diagonal of `G` is
  representable by schemes over `S` if and only if that of `changeOfBase π` is representable by
  schemes over `T.left`.
* `AlgebraicGeometry.exists_presheaf_iff_changeOfBase`: for `Q` respecting isomorphisms, some
  scheme over `S` maps to `G` by a morphism whose base changes have `Q`, if and only if some
  scheme over `T.left` maps to `changeOfBase π` by one.
* `AlgebraicGeometry.isAlgebraicSpace_iff_changeOfBase`: the combined statement, Stacks 04SG on
  objects.

## Implementation notes

A section `x` of `changeOfBase π` over `W` is a section `x.1` of `G` over
`(Over.map T.hom).obj W`. The comparison of the two sides goes through one statement,
`AlgebraicGeometry.isPullback_changeOfBase_iff`: a square of representable presheaves over
`changeOfBase π` is a pullback exactly when its image over `G` is. Pullbacks of representable
presheaves are read pointwise, as unique factorizations of pairs of morphisms with equal
restrictions. A section `a` of `G` over `U` defines an object of `Over T.left`, the
`T.left`-component of `π a : U ⟶ T`, whose image under `Over.map T.hom` is isomorphic to `U`, not
equal to it; the representability statements are transported along that isomorphism. The
diagonal of `T` plays no role: in a pullback square over `G`, the two legs already agree over
`T`, because they agree after `π`.

The sheaf condition goes through the slice `Over T`: `G` is the total presheaf
`CategoryTheory.Over.totalPresheaf` of `changeOfBaseSlice π`, so
`CategoryTheory.GrothendieckTopology.isSheaf_over_iff_isSheaf_totalPresheaf` compares `G` with
`changeOfBaseSlice π`, and the continuity of both functors of `Over.iteratedSliceEquiv T` compares
`changeOfBaseSlice π` with `changeOfBase π`. The representable presheaf `yoneda.obj T` is an fppf
sheaf because the fppf topology is subcanonical.

## References

* [Stacks, Section 65.16 (Tag 03I3)](https://stacks.math.columbia.edu/tag/03I3)

## Tags

algebraic space, change of base, slice category, fibre
-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A square of representable presheaves is a pullback exactly when the two sections agree after
restriction and every pair of morphisms along which they agree factors uniquely. -/
private theorem isPullback_yoneda_iff {C : Type*} [Category.{v} C] {F : Cᵒᵖ ⥤ Type v}
    {W V V' : C} (f : W ⟶ V) (s : W ⟶ V') (x : F.obj (op V)) (x' : F.obj (op V')) :
    IsPullback (yoneda.map f) (yoneda.map s) (yonedaEquiv.symm x) (yonedaEquiv.symm x') ↔
      F.map f.op x = F.map s.op x' ∧ ∀ ⦃Z : C⦄ (a : Z ⟶ V) (b : Z ⟶ V'),
        F.map a.op x = F.map b.op x' → ∃! c : Z ⟶ W, c ≫ f = a ∧ c ≫ s = b := by
  rw [IsPullback.iff_app]
  simp only [Types.isPullback_iff]
  constructor
  · intro h
    refine ⟨by simpa using ConcreteCategory.congr_hom (h (op W)).1 (𝟙 W), fun Z a b hab ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂⟩ := (h (op Z)).2.2 a b (by simpa using hab)
    simp at hc₁ hc₂
    exact ⟨c, ⟨hc₁, hc₂⟩, fun c' ⟨h₁, h₂⟩ ↦
      (h (op Z)).2.1 c' c ⟨by simp [h₁, hc₁], by simp [h₂, hc₂]⟩⟩
  · rintro ⟨hw, hu⟩ ⟨Z⟩
    refine ⟨?_, fun c c' ⟨h₁, h₂⟩ ↦ ?_, fun a b hab ↦ ?_⟩
    · ext a
      simp [hw]
    · simp at h₁ h₂
      obtain ⟨d, -, hd⟩ := hu (c ≫ f) (c ≫ s) (by simp [hw])
      exact (hd c ⟨rfl, rfl⟩).trans (hd c' ⟨h₁.symm, h₂.symm⟩).symm
    · obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := hu a b (by simpa using hab)
      exact ⟨c, hc₁, hc₂⟩

variable {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type u} {T : Over S} (π : G ⟶ yoneda.obj T)

/-- The fibres of `π : G ⟶ yoneda.obj T` as a presheaf on the slice `Over T`: its value on
`V : Over T` is the set of sections of `G` over `V.left` that `π` sends to `V.hom`. -/
def changeOfBaseSlice : (Over T)ᵒᵖ ⥤ Type u where
  obj V := {x : G.obj (op V.unop.left) // π.app _ x = V.unop.hom}
  map h := ↾fun x ↦ ⟨G.map h.unop.left.op x.1, by
    rw [NatTrans.naturality_apply, x.2]; exact Over.w h.unop⟩
  map_id V := by ext x; simp
  map_comp h h' := by ext x; simp

/-- The **change of base** of `π : G ⟶ yoneda.obj T` to `T.left`: the presheaf on
`Over T.left` whose value on `W` is the set of sections of `G` over `(Over.map T.hom).obj W`, the
scheme `W` viewed over `S`, that `π` sends to `W.hom`, viewed as a morphism over `S`.

It is `changeOfBaseSlice π` read through `Over.iteratedSliceEquiv T`
(`AlgebraicGeometry.changeOfBaseIso`). -/
def changeOfBase : (Over T.left)ᵒᵖ ⥤ Type u where
  obj W := {x : G.obj (op ((Over.map T.hom).obj W.unop)) // π.app _ x = Over.homMk W.unop.hom}
  map f := ↾fun x ↦ ⟨G.map ((Over.map T.hom).map f.unop).op x.1, by
    rw [NatTrans.naturality_apply, x.2]; exact Over.OverMorphism.ext (by simp)⟩
  map_id W := by ext x; simp
  map_comp f f' := by ext x; simp

/-- The change of base is the fibre presheaf on the slice `Over T`, read on `Over T.left` through
the iterated slice equivalence. The components are identities. -/
def changeOfBaseIso :
    changeOfBase π ≅ (Over.iteratedSliceEquiv T).inverse.op ⋙ changeOfBaseSlice π :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

variable {π}

/-- Restriction in the change of base is restriction in `G` along the morphism viewed over `S`. -/
@[simp]
theorem changeOfBase_map_coe {W V : Over T.left} (f : W ⟶ V) (x : (changeOfBase π).obj (op V)) :
    ((changeOfBase π).map f.op x).1 = G.map ((Over.map T.hom).map f).op x.1 :=
  rfl

/-- A section of the change of base over `V` lies over the structure morphism of `V`. -/
theorem changeOfBase_app_coe {V : Over T.left} (x : (changeOfBase π).obj (op V)) :
    π.app _ x.1 = Over.homMk V.hom :=
  x.2

/-- Two sections of the change of base whose images in `G` agree after restriction along `a` and
`b` force `a` and `b` to agree over `T.left`: apply `π`. -/
private lemma left_comp_eq {V V' : Over T.left} {x : (changeOfBase π).obj (op V)}
    {x' : (changeOfBase π).obj (op V')} {Z : Over S} {a : Z ⟶ (Over.map T.hom).obj V}
    {b : Z ⟶ (Over.map T.hom).obj V'} (h : G.map a.op x.1 = G.map b.op x'.1) :
    a.left ≫ V.hom = b.left ≫ V'.hom := by
  have := congrArg (π.app _) h
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, changeOfBase_app_coe,
    changeOfBase_app_coe] at this
  simpa using congrArg CommaMorphism.left this

/-- A square of representable presheaves over `changeOfBase π` is a pullback exactly when its
image under `Over.map T.hom` is a pullback over `G`. -/
theorem isPullback_changeOfBase_iff {W V V' : Over T.left} (f : W ⟶ V) (s : W ⟶ V')
    (x : (changeOfBase π).obj (op V)) (x' : (changeOfBase π).obj (op V')) :
    IsPullback (yoneda.map f) (yoneda.map s) (yonedaEquiv.symm x) (yonedaEquiv.symm x') ↔
      IsPullback (yoneda.map ((Over.map T.hom).map f)) (yoneda.map ((Over.map T.hom).map s))
        (yonedaEquiv.symm x.1) (yonedaEquiv.symm x'.1) := by
  rw [isPullback_yoneda_iff, isPullback_yoneda_iff]
  have key {Z : Over T.left} (a : Z ⟶ V) (b : Z ⟶ V') :
      (changeOfBase π).map a.op x = (changeOfBase π).map b.op x' ↔
        G.map ((Over.map T.hom).map a).op x.1 = G.map ((Over.map T.hom).map b).op x'.1 :=
    Subtype.ext_iff
  rw [key]
  refine and_congr_right fun _ ↦ ⟨fun h Z₀ a₀ b₀ hab ↦ ?_, fun h Z a b hab ↦ ?_⟩
  · have ht := left_comp_eq hab
    let Z : Over T.left := Over.mk (a₀.left ≫ V.hom)
    let i : (Over.map T.hom).obj Z ≅ Z₀ := Over.isoMk (Iso.refl _) (by
      simpa [Z] using (Over.w a₀).symm)
    let a : Z ⟶ V := Over.homMk a₀.left
    let b : Z ⟶ V' := Over.homMk b₀.left ht.symm
    have ha : (Over.map T.hom).map a = i.hom ≫ a₀ := by ext; simp [a, i]
    have hb : (Over.map T.hom).map b = i.hom ≫ b₀ := by ext; simp [b, i]
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := h a b ((key a b).2 (by
      rw [ha, hb, op_comp, op_comp, G.map_comp, G.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, hab]))
    refine ⟨i.inv ≫ (Over.map T.hom).map c, ⟨?_, ?_⟩, fun c₀ ⟨h₁, h₂⟩ ↦ ?_⟩
    · rw [Category.assoc, ← Functor.map_comp, hc₁, ha, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, ← Functor.map_comp, hc₂, hb, Iso.inv_hom_id_assoc]
    · have h₁' : c₀.left ≫ f.left = a₀.left := congrArg CommaMorphism.left h₁
      have h₂' : c₀.left ≫ s.left = b₀.left := congrArg CommaMorphism.left h₂
      let c' : Z ⟶ W := Over.homMk c₀.left (by
        dsimp [Z]; rw [← Over.w f, ← Category.assoc, h₁'])
      have := hc c' ⟨by ext; simp [c', a, h₁'], by ext; simp [c', b, h₂']⟩
      ext
      rw [← this]
      exact (Category.id_comp _).symm
  · obtain ⟨c₀, ⟨h₁, h₂⟩, hc₀⟩ := h _ _ ((key a b).1 hab)
    have h₁' : c₀.left ≫ f.left = a.left := congrArg CommaMorphism.left h₁
    have h₂' : c₀.left ≫ s.left = b.left := congrArg CommaMorphism.left h₂
    refine ⟨Over.homMk c₀.left (by rw [← Over.w f, ← Category.assoc, h₁', Over.w a]),
      ⟨by ext; simp [h₁'], by ext; simp [h₂']⟩, fun c ⟨h₁'', h₂''⟩ ↦ ?_⟩
    have := hc₀ ((Over.map T.hom).map c) ⟨by rw [← Functor.map_comp, h₁''],
      by rw [← Functor.map_comp, h₂'']⟩
    ext
    simp [← this]

section Lift

variable (π) {U : Over S} (a : G.obj (op U))

/-- The object of `Over T.left` defined by a section `a` of `G` over `U`: the
`T.left`-component of `π a`. -/
private def liftObj : Over T.left := Over.mk (π.app _ a).left

/-- The object `liftObj π a`, viewed over `S`, is isomorphic to `U`. -/
private def liftIso : (Over.map T.hom).obj (liftObj π a) ≅ U :=
  Over.isoMk (Iso.refl _) (by simp [liftObj])

/-- A section `a` of `G` over `U`, as a section of the change of base over `liftObj π a`. -/
private def liftPt : (changeOfBase π).obj (op (liftObj π a)) :=
  ⟨G.map (liftIso π a).hom.op a, by
    rw [NatTrans.naturality_apply]; exact Over.OverMorphism.ext (Category.id_comp _)⟩

private lemma yonedaEquiv_symm_liftPt :
    yonedaEquiv.symm (liftPt π a).1 = yoneda.map (liftIso π a).hom ≫ yonedaEquiv.symm a :=
  yonedaEquiv_symm_map _ _

end Lift

/-- Precomposing the second leg of a pullback square of representables with an isomorphism. -/
private lemma isPullback_comp_iso {C : Type*} [Category.{v} C] {F F' : Cᵒᵖ ⥤ Type v}
    {f : F ⟶ F'} {b U U' : C} {fst : yoneda.obj b ⟶ F} {snd : b ⟶ U'} (i : U' ≅ U)
    {g : yoneda.obj U ⟶ F'} (h : IsPullback fst (yoneda.map snd) f (yoneda.map i.hom ≫ g)) :
    IsPullback fst (yoneda.map (snd ≫ i.hom)) f g :=
  h.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso i) (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

/-- A pullback square over `G` of two sections of the change of base, with an arbitrary corner
`c` over `S`, gives a pullback square over the change of base with corner `c` viewed over
`T.left`. -/
private lemma isPullback_mk_of_isPullback {W V' : Over T.left} {x : (changeOfBase π).obj (op W)}
    {x' : (changeOfBase π).obj (op V')} {c : Over S} {f₀ : c ⟶ (Over.map T.hom).obj W}
    {snd : c ⟶ (Over.map T.hom).obj V'}
    (h : IsPullback (yoneda.map f₀) (yoneda.map snd) (yonedaEquiv.symm x.1)
      (yonedaEquiv.symm x'.1)) (hw : f₀.left ≫ W.hom = snd.left ≫ V'.hom) :
    IsPullback (yoneda.map (Over.homMk f₀.left hw : Over.mk (snd.left ≫ V'.hom) ⟶ W))
      (yoneda.map (Over.homMk snd.left : Over.mk (snd.left ≫ V'.hom) ⟶ V'))
      (yonedaEquiv.symm x) (yonedaEquiv.symm x') := by
  rw [isPullback_changeOfBase_iff]
  let d : (Over.map T.hom).obj (Over.mk (snd.left ≫ V'.hom)) ≅ c :=
    Over.isoMk (Iso.refl _) (by simpa using (Over.w snd).symm)
  refine h.of_iso (yoneda.mapIso d.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← Functor.map_comp]
    congr 1
  · simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← Functor.map_comp]
    congr 1

/-- Let `Q` be a property of morphisms of schemes that respects isomorphisms. A section `x` of the
change of base defines a morphism from a representable presheaf to `changeOfBase π` and one to
`G`. The first has `Q.over` after every base change to a scheme over `T.left` exactly when the
second has `Q.over` after every base change to a scheme over `S`. Compare Stacks 03I6. -/
theorem presheaf_iff_presheaf_changeOfBase (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    {W : Over T.left} (x : (changeOfBase π).obj (op W)) :
    (Q.over (X := S)).presheaf (yonedaEquiv.symm x.1) ↔
      (Q.over (X := T.left)).presheaf (yonedaEquiv.symm x) := by
  have : (Q.over (X := S)).RespectsIso :=
    inferInstanceAs (Q.inverseImage (Over.forget S)).RespectsIso
  have : (Q.over (X := T.left)).RespectsIso :=
    inferInstanceAs (Q.inverseImage (Over.forget T.left)).RespectsIso
  constructor
  · intro h
    refine MorphismProperty.relative.of_exists fun V' h' ↦ ?_
    obtain ⟨x', rfl⟩ := yonedaEquiv.symm.surjective h'
    obtain ⟨c, snd, fst, sq⟩ := h.rep (yonedaEquiv.symm x'.1)
    obtain ⟨f₀, rfl⟩ := yoneda.map_surjective fst
    have hw := left_comp_eq ((isPullback_yoneda_iff _ _ _ _).1 sq).1
    exact ⟨_, _, _, isPullback_mk_of_isPullback sq hw, h.property _ _ _ sq⟩
  · intro h
    refine MorphismProperty.relative.of_exists fun U' g' ↦ ?_
    obtain ⟨b, rfl⟩ := yonedaEquiv.symm.surjective g'
    obtain ⟨c, s, fst, sq⟩ := h.rep (yonedaEquiv.symm (liftPt π b))
    obtain ⟨f, rfl⟩ := yoneda.map_surjective fst
    have hQ : Q s.left := h.property _ _ _ sq
    rw [isPullback_changeOfBase_iff, yonedaEquiv_symm_liftPt] at sq
    refine ⟨_, _, _, isPullback_comp_iso (liftIso π b) sq, ?_⟩
    change Q (((Over.map T.hom).map s).left ≫ (liftIso π b).hom.left)
    exact MorphismProperty.RespectsIso.postcomp Q ((Over.forget S).mapIso (liftIso π b)).hom _
      hQ

variable (π) in
/-- **Diagonal.** The diagonal of `G` is representable by schemes over `S` if and only if the
diagonal of its change of base is representable by schemes over `T.left`. -/
theorem relativelyRepresentable_diag_iff_changeOfBase :
    yoneda.relativelyRepresentable (diag G) ↔
      yoneda.relativelyRepresentable (diag (changeOfBase π)) := by
  have key {W : Over T.left} (x : (changeOfBase π).obj (op W)) :
      yoneda.relativelyRepresentable (yonedaEquiv.symm x.1) ↔
        yoneda.relativelyRepresentable (yonedaEquiv.symm x) := by
    have h := presheaf_iff_presheaf_changeOfBase (π := π) ⊤ x
    exact ⟨fun hx ↦ (h.1 ⟨hx, fun _ _ _ _ _ _ ↦ trivial⟩).1,
      fun hx ↦ (h.2 ⟨hx, fun _ _ _ _ _ _ ↦ trivial⟩).1⟩
  rw [Functor.relativelyRepresentable.diag_iff, Functor.relativelyRepresentable.diag_iff]
  refine ⟨fun h W g ↦ ?_, fun h U g ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective g
    exact (key x).1 (h _)
  · obtain ⟨a, rfl⟩ := yonedaEquiv.symm.surjective g
    have := (key (liftPt π a)).2 (h _)
    rw [yonedaEquiv_symm_liftPt] at this
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 this

variable (π) in
/-- **Atlas.** For `Q` respecting isomorphisms, some scheme over `S` maps to `G` by a morphism
whose base changes to schemes over `S` have `Q`, if and only if some scheme over `T.left` maps to
the change of base by a morphism whose base changes to schemes over `T.left` have `Q`. -/
theorem exists_presheaf_iff_changeOfBase (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso] :
    (∃ (U : Over S) (p : yoneda.obj U ⟶ G), (Q.over (X := S)).presheaf p) ↔
      ∃ (W : Over T.left) (p : yoneda.obj W ⟶ changeOfBase π),
        (Q.over (X := T.left)).presheaf p := by
  refine ⟨fun ⟨U, p, hp⟩ ↦ ?_, fun ⟨W, p, hp⟩ ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := yonedaEquiv.symm.surjective p
    refine ⟨_, _, (presheaf_iff_presheaf_changeOfBase Q (liftPt π a)).1 ?_⟩
    rw [yonedaEquiv_symm_liftPt]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hp
  · obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective p
    exact ⟨_, _, (presheaf_iff_presheaf_changeOfBase Q x).2 hp⟩

/-- Two elements of the total presheaf of `changeOfBaseSlice π` with the same section agree. -/
private lemma totalPresheaf_ext {Y : Over S} {p q : Y ⟶ T} (x : G.obj (op Y))
    (hp : π.app _ x = p) (hq : π.app _ x = q) :
    (⟨p, x, hp⟩ : (Over.totalPresheaf (changeOfBaseSlice π)).obj (op Y)) = ⟨q, x, hq⟩ := by
  subst hp hq
  rfl

variable (π) in
/-- A presheaf `G` over `yoneda.obj T` is the total presheaf of its fibres: a section `x` of `G`
corresponds to the pair `(π x, x)`. -/
def isoTotalPresheafChangeOfBaseSlice : G ≅ Over.totalPresheaf (changeOfBaseSlice π) :=
  NatIso.ofComponents (fun Y ↦ Equiv.toIso
    { toFun x := ⟨π.app Y x, x, rfl⟩
      invFun s := s.2.1
      left_inv _ := rfl
      right_inv s := totalPresheaf_ext _ _ s.2.2 })
    fun f ↦ by
      ext x
      exact totalPresheaf_ext _ _ (NatTrans.naturality_apply π f x)

variable (π) in
/-- **Sheaf condition.** `G` is an fppf sheaf over `S` if and only if its change of base is an
fppf sheaf over `T.left`. -/
theorem isSheaf_iff_isSheaf_changeOfBase :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) G ↔
      Presieve.IsSheaf (Scheme.fppfTopology.over T.left) (changeOfBase π) := by
  have hT : Presieve.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj T) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let e := Over.iteratedSliceEquiv T
  have iso : e.functor.op ⋙ e.inverse.op ⋙ changeOfBaseSlice π ≅ changeOfBaseSlice π :=
    Functor.isoWhiskerRight (NatIso.op e.unitIso) (changeOfBaseSlice π)
  calc Presieve.IsSheaf (Scheme.fppfTopology.over S) G
      ↔ Presieve.IsSheaf (Scheme.fppfTopology.over S)
          (Over.totalPresheaf (changeOfBaseSlice π)) :=
        ⟨Presieve.isSheaf_iso _ (isoTotalPresheafChangeOfBaseSlice π),
          Presieve.isSheaf_iso _ (isoTotalPresheafChangeOfBaseSlice π).symm⟩
    _ ↔ Presieve.IsSheaf ((Scheme.fppfTopology.over S).over T) (changeOfBaseSlice π) :=
        (GrothendieckTopology.isSheaf_over_iff_isSheaf_totalPresheaf _ hT _).symm
    _ ↔ Presieve.IsSheaf (Scheme.fppfTopology.over T.left)
          (e.inverse.op ⋙ changeOfBaseSlice π) :=
        ⟨fun h ↦ Functor.op_comp_isSheaf_of_isSheaf_type e.inverse _ h, fun h ↦
          Presieve.isSheaf_iso _ iso (Functor.op_comp_isSheaf_of_isSheaf_type e.functor _ h)⟩
    _ ↔ Presieve.IsSheaf (Scheme.fppfTopology.over T.left) (changeOfBase π) :=
        ⟨Presieve.isSheaf_iso _ (changeOfBaseIso π).symm,
          Presieve.isSheaf_iso _ (changeOfBaseIso π)⟩

variable (π) in
/-- **Change of base for algebraic spaces.** A presheaf `G` on `Over S` with a morphism
`π : G ⟶ yoneda.obj T` is an algebraic space over `S` if and only if its change of base is an
algebraic space over `T.left`. This is Stacks 04SG on objects: an algebraic space over `T.left`
is the same as an algebraic space over `S` with a morphism to `T`. -/
@[stacks 04SG]
theorem isAlgebraicSpace_iff_changeOfBase :
    isAlgebraicSpace S G ↔ isAlgebraicSpace T.left (changeOfBase π) := by
  have : (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).RespectsIso := by
    have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.inf _ _
  exact and_congr (isSheaf_iff_isSheaf_changeOfBase π)
    (and_congr (relativelyRepresentable_diag_iff_changeOfBase π)
      (exists_presheaf_iff_changeOfBase π _))

end AlgebraicGeometry

