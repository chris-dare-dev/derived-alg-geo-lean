/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Restrict
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.ExtendByZero
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Locality
import DerivedAlgGeo.CategoryTheory.Triangulated.PretriangulatedBiproduct

/-!
# The Mayer–Vietoris triangle

Let `Y` be a scheme and `Y = U ∪ V` with `U` and `V` open. For `E` in the derived category of
module sheaves on `Y` there is a distinguished triangle
`j_{U∩V!} E|_{U∩V} ⟶ j_{U!} E|_U ⊞ j_{V!} E|_V ⟶ E ⟶ j_{U∩V!} E|_{U∩V}⟦1⟧`
(Stacks Tag 08BU). Its first map has the two comparison maps as components, one with a sign, and
its second map is the sum of the two counits of `j_! ⊣ j^*`.

The triangle lives in the derived category of all module sheaves. It does not live in `Dqc`,
because `j_! 𝒪_U` is not quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Scheme.extendRestrictMap`: the comparison map `g_! k^* M ⟶ f_! M` for
  open immersions `k` and `f` with composite `g`.
* `AlgebraicGeometry.Scheme.mayerVietorisTriangleOfSquare`: the triangle, for a pullback square
  of open immersions through the intersection.
* `AlgebraicGeometry.Scheme.mayerVietorisTriangle`: the triangle for two opens `U` and `V`.

## Main results

* `AlgebraicGeometry.Scheme.mayerVietorisTriangle_distinguished`: the triangle is distinguished
  when `U ⊔ V = ⊤`.

## Implementation notes

The proof does not compute stalks. Write `θ_U : j_{U∩V!} E|_{U∩V} ⟶ j_{U!} E|_U` and `θ_V` for the
comparison maps, `ε_U` and `ε_V` for the counits, and let `Z` be a cone of the first map
`(θ_U, -θ_V)`. Because `ε_U θ_U = ε_V θ_V`, the sum of the counits factors through a map
`Z ⟶ E`. To see that it is invertible, restrict to `U`: restriction is triangulated, restriction
to `U` of `j_{V!} E|_V` is the extension by zero of `E|_{U∩V}` along `U∩V ⟶ U` (the derived
base change of `Glue.ExtendByZero`), so the component of `(θ_U, -θ_V)` into `j_{V!} E|_V` becomes
invertible, and by `isIso_inl_comp_of_isIso_snd` the cone is identified with `j_{U!} E|_U`, on
which `ε_U` is invertible. The same argument works on `V`, and a morphism whose restrictions to
`U` and to `V` are invertible is invertible, because a derived object whose restrictions vanish
has vanishing cohomology sheaves, and vanishing of a module sheaf is local.

The comparison map is built from the composition isomorphism of derived extension by zero, which
is the uniqueness of left adjoints for the composite adjunction, so that its relation to the
counits is formal.

## References

* Stacks Project, Tag 08BU.

## Tags

derived category, Mayer–Vietoris, extension by zero, open cover
-/

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits Pretriangulated
open scoped ZeroObject
open AlgebraicGeometry.DerivedCategory

noncomputable section

variable {Y : Scheme.{u}}

section ExtendRestrict

variable {A B C : Scheme.{u}} {k : A ⟶ B} {f : B ⟶ C} {g : A ⟶ C}
  [IsOpenImmersion k] [IsOpenImmersion f] [IsOpenImmersion g]

/-- The comparison map `g_! k^* M ⟶ f_! M` for open immersions `k` and `f` with composite `g`,
given the composition isomorphism of restriction. It is `f_!` of the counit of `k_! ⊣ k^*`,
after the composition isomorphism of extension by zero. -/
def extendRestrictMap (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (M : SchemeDerivedCategory B) :
    (derivedExtendByZero g).obj ((derivedRestrict k).obj M) ⟶ (derivedExtendByZero f).obj M :=
  (derivedExtendComp c).hom.app ((derivedRestrict k).obj M) ≫
    (derivedExtendByZero f).map ((derivedExtendByZeroAdjunction k).counit.app M)

private lemma homEquiv_leftAdjointUniq_hom_app_comp {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    {F F' : D₁ ⥤ D₂} {G : D₂ ⥤ D₁} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) (X : D₁) {Z : D₂}
    (h : F'.obj X ⟶ Z) :
    adj₁.homEquiv X Z ((Adjunction.leftAdjointUniq adj₁ adj₂).hom.app X ≫ h) =
      adj₂.homEquiv X Z h := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

/-- Under the adjunction `g_! ⊣ g^*`, the comparison map corresponds to the unit of `f_! ⊣ f^*`
followed by the composition isomorphism of restriction. -/
lemma homEquiv_extendRestrictMap (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (M : SchemeDerivedCategory B) :
    (derivedExtendByZeroAdjunction g).homEquiv _ _ (extendRestrictMap c M) =
      (derivedRestrict k).map ((derivedExtendByZeroAdjunction f).unit.app M) ≫
        c.hom.app ((derivedExtendByZero f).obj M) := by
  unfold extendRestrictMap derivedExtendComp
  rw [homEquiv_leftAdjointUniq_hom_app_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  simp [Adjunction.homEquiv_unit]

/-- The comparison map `g_! g^* E ⟶ f_! f^* E`. -/
def thetaApp (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (E : SchemeDerivedCategory C) :
    (derivedExtendByZero g).obj ((derivedRestrict g).obj E) ⟶
      (derivedExtendByZero f).obj ((derivedRestrict f).obj E) :=
  (derivedExtendByZero g).map (c.inv.app E) ≫ extendRestrictMap c ((derivedRestrict f).obj E)

private lemma thetaApp_eq (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (E : SchemeDerivedCategory C) :
    thetaApp c E = (derivedExtendComp c).hom.app ((derivedRestrict g).obj E) ≫
      (derivedExtendByZero f).map ((derivedExtendByZero k).map (c.inv.app E) ≫
        (derivedExtendByZeroAdjunction k).counit.app ((derivedRestrict f).obj E)) := by
  unfold thetaApp extendRestrictMap
  have := (derivedExtendComp c).hom.naturality (c.inv.app E)
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  erw [this]
  simp

/-- The two counits are compatible with the comparison map: `ε_f ∘ θ = ε_g`. -/
lemma thetaApp_comp_counit (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (E : SchemeDerivedCategory C) :
    thetaApp c E ≫ (derivedExtendByZeroAdjunction f).counit.app E =
      (derivedExtendByZeroAdjunction g).counit.app E := by
  rw [thetaApp_eq, ← Adjunction.leftAdjointUniq_hom_app_counit (derivedExtendByZeroAdjunction g)
    (((derivedExtendByZeroAdjunction k).comp (derivedExtendByZeroAdjunction f)).ofNatIsoRight c) E]
  simp [derivedExtendComp]

/-- Under `g_! ⊣ g^*`, the comparison map followed by the transpose of `a` corresponds to
the restriction of `a` along `k`. -/
lemma homEquiv_thetaApp (c : derivedRestrict f ⋙ derivedRestrict k ≅ derivedRestrict g)
    (E F : SchemeDerivedCategory C) (a : (derivedRestrict f).obj E ⟶ (derivedRestrict f).obj F) :
    (derivedExtendByZeroAdjunction g).homEquiv _ _
        (thetaApp c E ≫ ((derivedExtendByZeroAdjunction f).homEquiv _ _).symm a) =
      c.inv.app E ≫ (derivedRestrict k).map a ≫ c.hom.app F := by
  rw [thetaApp, Category.assoc, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  erw [homEquiv_extendRestrictMap]
  have hn := c.hom.naturality (((derivedExtendByZeroAdjunction f).homEquiv _ _).symm a)
  rw [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← hn, ← Category.assoc ((derivedRestrict k).map _), ← Functor.map_comp]
  erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

end ExtendRestrict

section Square

variable {U V : Y.Opens} {W : Scheme.{u}} {kU : W ⟶ U} {kV : W ⟶ V} {w : W ⟶ Y}
  [IsOpenImmersion kU] [IsOpenImmersion kV] [IsOpenImmersion w]

/-- Restriction to `U` of the comparison map `kV_!`-after-`kV^*` for a pullback square is
invertible. -/
lemma isIso_restrict_extendRestrictMap (hP : IsPullback kU kV U.ι V.ι)
    (c : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
    (B : SchemeDerivedCategory V) :
    IsIso ((derivedRestrict U.ι).map (extendRestrictMap c B)) := by
  unfold extendRestrictMap
  rw [Functor.map_comp]
  have := isIso_restrict_map_extend_counit hP B
  infer_instance

/-- Restriction to `U` of the comparison map `θ_V : w_! w^* E ⟶ V_! V^* E` is invertible. -/
lemma isIso_restrict_thetaApp (hP : IsPullback kU kV U.ι V.ι)
    (c : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)
    (E : SchemeDerivedCategory Y) :
    IsIso ((derivedRestrict U.ι).map (thetaApp c E)) := by
  unfold thetaApp
  rw [Functor.map_comp]
  have := isIso_restrict_extendRestrictMap hP c ((derivedRestrict V.ι).obj E)
  infer_instance

variable (cU : derivedRestrict U.ι ⋙ derivedRestrict kU ≅ derivedRestrict w)
  (cV : derivedRestrict V.ι ⋙ derivedRestrict kV ≅ derivedRestrict w)

/-- The first map of the Mayer–Vietoris triangle, with components `θ_U` and `-θ_V`. -/
def mvFirst (E : SchemeDerivedCategory Y) :
    (derivedExtendByZero w).obj ((derivedRestrict w).obj E) ⟶
      (derivedExtendByZero U.ι).obj ((derivedRestrict U.ι).obj E) ⊞
        (derivedExtendByZero V.ι).obj ((derivedRestrict V.ι).obj E) :=
  biprod.lift (thetaApp cU E) (-thetaApp cV E)

/-- The second map of the Mayer–Vietoris triangle: the sum of the two counits. -/
def mvSecond (U V : Y.Opens) (E : SchemeDerivedCategory Y) :
    (derivedExtendByZero U.ι).obj ((derivedRestrict U.ι).obj E) ⊞
        (derivedExtendByZero V.ι).obj ((derivedRestrict V.ι).obj E) ⟶ E :=
  biprod.desc ((derivedExtendByZeroAdjunction U.ι).counit.app E)
    ((derivedExtendByZeroAdjunction V.ι).counit.app E)

lemma mvFirst_comp_mvSecond (E : SchemeDerivedCategory Y) :
    mvFirst cU cV E ≫ mvSecond U V E = 0 := by
  simp [mvFirst, mvSecond, thetaApp_comp_counit]

/-- A derived object of `Y` is zero if its restrictions to two opens covering `Y` are zero. -/
lemma isZero_of_isZero_derivedRestrict (hUV : U ⊔ V = ⊤) (C : SchemeDerivedCategory Y)
    (hU : IsZero ((derivedRestrict U.ι).obj C)) (hV : IsZero ((derivedRestrict V.ι).obj C)) :
    IsZero C := by
  have key : ∀ (n : ℤ) {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f],
      IsZero ((derivedRestrict f).obj C) →
        IsZero ((Modules.pullback f).obj ((DerivedCategory.homologyFunctor Y.Modules n).obj C)) :=
    fun n X f _ hf ↦
      IsZero.of_iso ((DerivedCategory.homologyFunctor _ n).map_isZero hf)
        (mapDerivedCategoryHomologyIso (Modules.pullback f) inferInstance inferInstance
          inferInstance C n).symm
  have hH : ∀ n, IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj C) := fun n ↦ by
    refine Modules.isZero_of_isZero_restrict _ (fun b : Bool ↦ cond b U V) ?_ ?_
    · intro y
      have : y ∈ U ⊔ V := by rw [hUV]; trivial
      rcases TopologicalSpace.Opens.mem_sup.mp this with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · rintro (_ | _)
      · exact IsZero.of_iso (key n V.ι hV) ((Modules.restrictFunctorIsoPullback V.ι).app _)
      · exact IsZero.of_iso (key n U.ι hU) ((Modules.restrictFunctorIsoPullback U.ι).app _)
  have : IsIso (0 : (0 : SchemeDerivedCategory Y) ⟶ C) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    exact ((DerivedCategory.homologyFunctor Y.Modules n).map_isZero (isZero_zero _)).isIso
      (hH n) _
  exact IsZero.of_iso (isZero_zero _) (asIso (0 : (0 : SchemeDerivedCategory Y) ⟶ C)).symm

/-- The cone of the first map is `E`: the second map exhibits `E` as the third vertex of a
distinguished triangle. -/
lemma exists_mayerVietoris_triangle (hP : IsPullback kU kV U.ι V.ι) (hUV : U ⊔ V = ⊤)
    (E : SchemeDerivedCategory Y) :
    ∃ δ : E ⟶ ((derivedExtendByZero w).obj ((derivedRestrict w).obj E))⟦(1 : ℤ)⟧,
      Triangle.mk (mvFirst cU cV E) (mvSecond U V E) δ ∈ distTriang (SchemeDerivedCategory Y) := by
  obtain ⟨Z, g, δ₀, hT⟩ := distinguished_cocone_triangle (mvFirst cU cV E)
  obtain ⟨ν, hν⟩ := Triangle.yoneda_exact₂ _ hT (mvSecond U V E) (mvFirst_comp_mvSecond cU cV E)
  have hg : g ≫ ν = mvSecond U V E := hν.symm
  have hνU : IsIso ((derivedRestrict U.ι).map ν) := by
    have h1 := isIso_map_inl_comp_of_isIso_map_snd (derivedRestrict U.ι) (mvFirst cU cV E) g δ₀ hT
      (by
        have := isIso_restrict_thetaApp hP cV E
        rw [mvFirst, biprod.lift_snd, Functor.map_neg]
        exact isIso_neg _)
    have h2 : (derivedRestrict U.ι).map (biprod.inl ≫ g) ≫ (derivedRestrict U.ι).map ν =
        (derivedRestrict U.ι).map ((derivedExtendByZeroAdjunction U.ι).counit.app E) := by
      rw [← Functor.map_comp, Category.assoc, hg, mvSecond, biprod.inl_desc]
    have h3 := isIso_restrict_counit U.ι E
    rw [← h2] at h3
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((derivedRestrict U.ι).map (biprod.inl ≫ g))
      ((derivedRestrict U.ι).map ν) h1 h3
  have hνV : IsIso ((derivedRestrict V.ι).map ν) := by
    have h1 := isIso_map_inr_comp_of_isIso_map_fst (derivedRestrict V.ι) (mvFirst cU cV E) g δ₀ hT
      (by
        have := isIso_restrict_thetaApp hP.flip cU E
        rwa [mvFirst, biprod.lift_fst])
    have h2 : (derivedRestrict V.ι).map (biprod.inr ≫ g) ≫ (derivedRestrict V.ι).map ν =
        (derivedRestrict V.ι).map ((derivedExtendByZeroAdjunction V.ι).counit.app E) := by
      rw [← Functor.map_comp, Category.assoc, hg, mvSecond, biprod.inr_desc]
    have h3 := isIso_restrict_counit V.ι E
    rw [← h2] at h3
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((derivedRestrict V.ι).map (biprod.inr ≫ g))
      ((derivedRestrict V.ι).map ν) h1 h3
  have hiso : IsIso ν := by
    obtain ⟨C, a, b, hC⟩ := distinguished_cocone_triangle ν
    have key : ∀ {X : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f],
        IsIso ((derivedRestrict f).map ν) → IsZero ((derivedRestrict f).obj C) :=
      fun f _ hf ↦
        (Triangle.isZero₃_iff_isIso₁ _
          (Functor.map_distinguished (derivedRestrict f) _ hC)).2 hf
    exact (Triangle.isZero₃_iff_isIso₁ _ hC).1
      (isZero_of_isZero_derivedRestrict hUV C (key U.ι hνU) (key V.ι hνV))
  refine ⟨inv ν ≫ δ₀, isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso ν).symm ?_ ?_ ?_
  · simp
  · simp [hν]
  · simp

/-- The Mayer–Vietoris triangle `w_! w^* E ⟶ U_! U^* E ⊞ V_! V^* E ⟶ E ⟶ w_! w^* E⟦1⟧` for a
pullback square of open immersions through the intersection `w`. -/
def mayerVietorisTriangleOfSquare (hP : IsPullback kU kV U.ι V.ι) (hUV : U ⊔ V = ⊤)
    (E : SchemeDerivedCategory Y) : Triangle (SchemeDerivedCategory Y) :=
  Triangle.mk (mvFirst cU cV E) (mvSecond U V E)
    (Classical.choose (exists_mayerVietoris_triangle cU cV hP hUV E))

theorem mayerVietorisTriangleOfSquare_distinguished (hP : IsPullback kU kV U.ι V.ι)
    (hUV : U ⊔ V = ⊤) (E : SchemeDerivedCategory Y) :
    mayerVietorisTriangleOfSquare cU cV hP hUV E ∈ distTriang (SchemeDerivedCategory Y) :=
  Classical.choose_spec (exists_mayerVietoris_triangle cU cV hP hUV E)

end Square

section Opens

variable (U V : Y.Opens)

/-- Restriction to `U` and then to `U ⊓ V` is restriction to `U ⊓ V`. -/
def restrictCompInfLeft :
    derivedRestrict U.ι ⋙ derivedRestrict (Y.homOfLE (inf_le_left : U ⊓ V ≤ U)) ≅
      derivedRestrict (U ⊓ V).ι :=
  derivedRestrictComp _ _ ≪≫ derivedRestrictCongr (Y.homOfLE_ι _)

/-- Restriction to `V` and then to `U ⊓ V` is restriction to `U ⊓ V`. -/
def restrictCompInfRight :
    derivedRestrict V.ι ⋙ derivedRestrict (Y.homOfLE (inf_le_right : U ⊓ V ≤ V)) ≅
      derivedRestrict (U ⊓ V).ι :=
  derivedRestrictComp _ _ ≪≫ derivedRestrictCongr (Y.homOfLE_ι _)

/-- **The Mayer–Vietoris triangle** (Stacks Tag 08BU), for `Y = U ∪ V`:
`j_{U∩V!}(E|_{U∩V}) ⟶ j_{U!}(E|_U) ⊞ j_{V!}(E|_V) ⟶ E ⟶ j_{U∩V!}(E|_{U∩V})⟦1⟧`.

The first map has the comparison maps as components, the second is the sum of the counits of
`j_! ⊣ j^*`, and the third is a chosen map making the triangle distinguished. The hypothesis
`U ⊔ V = ⊤` is needed: for `U = V = ⊥` and `E ≠ 0` the triangle would be `0 ⟶ 0 ⟶ E ⟶ 0`. The
triangle lives in the derived category of all module sheaves, not in `Dqc`, since `j_! 𝒪_U` is
not quasi-coherent. -/
def mayerVietorisTriangle (hUV : U ⊔ V = ⊤) (E : SchemeDerivedCategory Y) :
    Triangle (SchemeDerivedCategory Y) :=
  mayerVietorisTriangleOfSquare (restrictCompInfLeft U V) (restrictCompInfRight U V)
    (isPullback_opens_inf U V) hUV E

/-- The Mayer–Vietoris triangle is distinguished (Stacks Tag 08BU). -/
theorem mayerVietorisTriangle_distinguished (hUV : U ⊔ V = ⊤) (E : SchemeDerivedCategory Y) :
    mayerVietorisTriangle U V hUV E ∈ distTriang (SchemeDerivedCategory Y) :=
  mayerVietorisTriangleOfSquare_distinguished _ _ _ _ E

end Opens

end

end AlgebraicGeometry.Scheme
