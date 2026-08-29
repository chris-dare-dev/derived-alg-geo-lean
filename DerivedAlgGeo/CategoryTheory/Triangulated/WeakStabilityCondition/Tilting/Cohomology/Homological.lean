/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Shift
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Homologicality of original-heart cohomology

For any t-structure `t`, degree-zero heart cohomology sends distinguished
triangles to exact short complexes in `t.heart.FullSubcategory`.  The proof is
independent of stability functions and Harder--Narasimhan data.

The argument first uses the alternative normal form
`τ≤0(τ≥0 X)` for `H⁰_t(X)`.  On a distinguished triangle contained in
`D^{≤0}`, this normal form sends the second arrow to a cokernel.  An
octahedral truncation then reduces a triangle with nonpositive source to that
case.  Finally, splitting an arbitrary source at degree one compares it with
the nonpositive-source triangle by isomorphisms on the first two terms and a
monomorphism on the third.
-/

namespace CategoryTheory.Triangulated.Tilting

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

attribute [local instance] CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

/-! ## The alternative degree-zero normal form -/

/-- Degree-zero cohomology in the normal form `τ≤0(τ≥0 X)`. -/
private noncomputable def originalHeartH0prime (t : TStructure C) (X : C) :
    t.heart.FullSubcategory :=
  ⟨(t.truncLEGE 0 0).obj X, by
    rw [t.mem_heart_iff]
    constructor
    · exact show t.IsLE ((t.truncLE 0).obj ((t.truncGE 0).obj X)) 0 by infer_instance
    · letI : t.IsGE ((t.truncGE 0).obj X) 0 := by infer_instance
      exact show t.IsGE ((t.truncLE 0).obj ((t.truncGE 0).obj X)) 0 by infer_instance⟩

/-- The alternative degree-zero normal form as a functor. -/
private noncomputable def originalHeartH0primeFunctor (t : TStructure C) :
    C ⥤ t.heart.FullSubcategory where
  obj := originalHeartH0prime t
  map {X Y} f := ObjectProperty.homMk ((t.truncLEGE 0 0).map f)
  map_id X := by
    ext
    simp [originalHeartH0prime, TStructure.truncLEGE]
  map_comp f g := by
    ext
    simp [originalHeartH0prime, TStructure.truncLEGE]

private instance originalHeartH0primeFunctor_additive (t : TStructure C) :
    Functor.Additive (originalHeartH0primeFunctor t) where
  map_add := by
    intro X Y f g
    ext
    change (t.truncLE 0).map ((t.truncGE 0).map (f + g)) =
      (t.truncLE 0).map ((t.truncGE 0).map f) +
        (t.truncLE 0).map ((t.truncGE 0).map g)
    simp [Functor.map_add]

/-- The two standard degree-zero normal forms agree objectwise. -/
private noncomputable def originalHeartH0ObjIsoH0prime
    (t : TStructure C) (X : C) :
    (originalHeartCohFunctor t 0).obj X ≅ originalHeartH0prime t X := by
  refine ObjectProperty.isoMk _ ?_
  simpa [originalHeartCohFunctor, originalHeartH0prime] using
    ((shiftFunctorZero C ℤ).app ((t.truncGELE 0 0).obj X) ≪≫
      (t.truncGELEIsoLEGE 0 0).app X)

@[reassoc]
private theorem originalHeartH0ObjIsoH0prime_hom_naturality
    (t : TStructure C) {X Y : C} (f : X ⟶ Y) :
    (originalHeartCohFunctor t 0).map f ≫
        (originalHeartH0ObjIsoH0prime t Y).hom =
      (originalHeartH0ObjIsoH0prime t X).hom ≫
        (originalHeartH0primeFunctor t).map f := by
  ext
  change
    (shiftFunctor C 0).map ((t.truncGE 0).map ((t.truncLE 0).map f)) ≫
        (shiftFunctorZero C ℤ).hom.app
          ((t.truncGE 0).obj ((t.truncLE 0).obj Y)) ≫
          (t.truncGELEIsoLEGE 0 0).hom.app Y =
      ((shiftFunctorZero C ℤ).hom.app
          ((t.truncGE 0).obj ((t.truncLE 0).obj X)) ≫
          (t.truncGELEIsoLEGE 0 0).hom.app X) ≫
        (t.truncLE 0).map ((t.truncGE 0).map f)
  calc
    _ = ((shiftFunctorZero C ℤ).hom.app
          ((t.truncGE 0).obj ((t.truncLE 0).obj X)) ≫
          (t.truncGE 0).map ((t.truncLE 0).map f)) ≫
          (t.truncGELEIsoLEGE 0 0).hom.app Y := by
      rw [← Category.assoc]
      simpa using
        congrArg (fun k => k ≫ (t.truncGELEIsoLEGE 0 0).hom.app Y)
          (NatTrans.naturality (shiftFunctorZero C ℤ).hom
            ((t.truncGE 0).map ((t.truncLE 0).map f)))
    _ = ((shiftFunctorZero C ℤ).hom.app
          ((t.truncGE 0).obj ((t.truncLE 0).obj X)) ≫
          (t.truncGELEIsoLEGE 0 0).hom.app X) ≫
          (t.truncLE 0).map ((t.truncGE 0).map f) := by
      simpa [TStructure.truncGELE, TStructure.truncLEGE, Category.assoc] using
        congrArg
          (fun k =>
            (shiftFunctorZero C ℤ).hom.app
                ((t.truncGE 0).obj ((t.truncLE 0).obj X)) ≫ k)
          (NatTrans.naturality ((t.truncGELEIsoLEGE 0 0).hom) f)

/-- The two degree-zero normal forms agree naturally. -/
private noncomputable def originalHeartH0FunctorIsoH0primeFunctor
    (t : TStructure C) :
    originalHeartCohFunctor t 0 ≅ originalHeartH0primeFunctor t :=
  NatIso.ofComponents (fun X => originalHeartH0ObjIsoH0prime t X)
    (fun f => originalHeartH0ObjIsoH0prime_hom_naturality t f)

/-! ## Exactness on nonpositive triangles -/

/-- For a nonpositive object, the defining inclusion of the alternative
degree-zero normal form into `τ≥0 X` is an isomorphism. -/
private noncomputable def originalHeartH0primeObjIsoTruncGEOfIsLE
    (t : TStructure C) (X : C) [t.IsLE X 0] :
    (originalHeartH0prime t X).obj ≅ (t.truncGE 0).obj X := by
  have hLE : t.IsLE ((t.truncGE 0).obj X) 0 := by infer_instance
  exact @asIso _ _ _ _ ((t.truncLEι 0).app ((t.truncGE 0).obj X))
    ((t.isLE_iff_isIso_truncLEι_app 0 ((t.truncGE 0).obj X)).mp hLE)

/-- Read a morphism from alternative `H⁰` to a heart object as an ambient
morphism from a nonpositive object. -/
private noncomputable def fromOriginalHeartH0primeHomOfIsLE
    (t : TStructure C) {X : C} [t.IsLE X 0]
    (E : t.heart.FullSubcategory) (f : originalHeartH0prime t X ⟶ E) :
    X ⟶ E.obj :=
  (t.truncGEπ 0).app X ≫
    (originalHeartH0primeObjIsoTruncGEOfIsLE t X).inv ≫ f.hom

/-- Construct a morphism from alternative `H⁰` to a heart object from an
ambient morphism whose source is nonpositive. -/
private noncomputable def toOriginalHeartH0primeHomOfIsLE
    (t : TStructure C) {X : C} [t.IsLE X 0]
    (E : t.heart.FullSubcategory) (f : X ⟶ E.obj) :
    originalHeartH0prime t X ⟶ E :=
  letI : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
  ObjectProperty.homMk
    ((originalHeartH0primeObjIsoTruncGEOfIsLE t X).hom ≫
      t.descTruncGE f 0)

@[simp]
private theorem fromOriginalHeartH0primeHomOfIsLE_toOriginalHeartH0primeHomOfIsLE
    (t : TStructure C) {X : C} [t.IsLE X 0]
    (E : t.heart.FullSubcategory) (f : X ⟶ E.obj) :
    fromOriginalHeartH0primeHomOfIsLE t E
      (toOriginalHeartH0primeHomOfIsLE t E f) = f := by
  letI : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
  simp only [fromOriginalHeartH0primeHomOfIsLE,
    toOriginalHeartH0primeHomOfIsLE, ObjectProperty.homMk_hom,
    Iso.inv_hom_id_assoc]
  exact t.π_descTruncGE f 0

@[simp]
private theorem toOriginalHeartH0primeHomOfIsLE_fromOriginalHeartH0primeHomOfIsLE
    (t : TStructure C) {X : C} [t.IsLE X 0]
    (E : t.heart.FullSubcategory) (f : originalHeartH0prime t X ⟶ E) :
    toOriginalHeartH0primeHomOfIsLE t E
      (fromOriginalHeartH0primeHomOfIsLE t E f) = f := by
  letI : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
  apply ObjectProperty.hom_ext
  change
    (originalHeartH0primeObjIsoTruncGEOfIsLE t X).hom ≫
        t.descTruncGE
          ((t.truncGEπ 0).app X ≫
            (originalHeartH0primeObjIsoTruncGEOfIsLE t X).inv ≫ f.hom) 0 =
      f.hom
  calc
    _ = (originalHeartH0primeObjIsoTruncGEOfIsLE t X).hom ≫
        ((originalHeartH0primeObjIsoTruncGEOfIsLE t X).inv ≫ f.hom) := by
      congr 1
      apply t.from_truncGE_obj_ext
      rw [t.π_descTruncGE]
      rfl
    _ = f.hom := by simp

@[simp]
private theorem fromOriginalHeartH0primeHomOfIsLE_zero
    (t : TStructure C) {X : C} [t.IsLE X 0]
    (E : t.heart.FullSubcategory) :
    fromOriginalHeartH0primeHomOfIsLE t E
      (0 : originalHeartH0prime t X ⟶ E) = 0 := by
  simp [fromOriginalHeartH0primeHomOfIsLE]

@[reassoc]
private theorem toOriginalHeartH0primeHomOfIsLE_comp
    (t : TStructure C) {X Y : C} [t.IsLE X 0] [t.IsLE Y 0]
    (E : t.heart.FullSubcategory) (f : X ⟶ Y) (g : Y ⟶ E.obj) :
    toOriginalHeartH0primeHomOfIsLE t E (f ≫ g) =
      (originalHeartH0primeFunctor t).map f ≫
        toOriginalHeartH0primeHomOfIsLE t E g := by
  letI : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
  apply ObjectProperty.hom_ext
  change
    (originalHeartH0primeObjIsoTruncGEOfIsLE t X).hom ≫
        t.descTruncGE (f ≫ g) 0 =
      (t.truncLE 0).map ((t.truncGE 0).map f) ≫
        (originalHeartH0primeObjIsoTruncGEOfIsLE t Y).hom ≫
          t.descTruncGE g 0
  rw [← CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE t (C := C) f g 0]
  simpa [originalHeartH0primeObjIsoTruncGEOfIsLE, Category.assoc] using
    congrArg (fun k => k ≫ t.descTruncGE g 0)
      ((t.truncLEι 0).naturality ((t.truncGE 0).map f)).symm

@[reassoc]
private theorem fromOriginalHeartH0primeHomOfIsLE_naturality
    (t : TStructure C) {X Y : C} [t.IsLE X 0] [t.IsLE Y 0]
    (E : t.heart.FullSubcategory) (f : X ⟶ Y)
    (g : originalHeartH0prime t Y ⟶ E) :
    fromOriginalHeartH0primeHomOfIsLE t E
        ((originalHeartH0primeFunctor t).map f ≫ g) =
      f ≫ fromOriginalHeartH0primeHomOfIsLE t E g := by
  have hEq := toOriginalHeartH0primeHomOfIsLE_comp t E f
    (fromOriginalHeartH0primeHomOfIsLE t E g)
  rw [toOriginalHeartH0primeHomOfIsLE_fromOriginalHeartH0primeHomOfIsLE] at hEq
  have hEq' := congrArg (fromOriginalHeartH0primeHomOfIsLE t E) hEq
  simpa using hEq'.symm

/-- Alternative `H⁰` sends a distinguished triangle contained in `D^{≤0}`
to an exact short complex. -/
private theorem originalHeartH0primeFunctor_map_distinguished_exact_of_isLE
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
    [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    ((shortComplexOfDistTriangle T hT).map
      (originalHeartH0primeFunctor t)).Exact := by
  let S := (shortComplexOfDistTriangle T hT).map
    (originalHeartH0primeFunctor t)
  apply ShortComplex.exact_of_g_is_cokernel
  have kernel_condition {E : t.heart.FullSubcategory}
      (k : S.X₂ ⟶ E) (hk : S.f ≫ k = 0) :
      T.mor₁ ≫ fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k = 0 := by
    have hk₀ : (originalHeartH0primeFunctor t).map T.mor₁ ≫ k = 0 := by
      simpa [S] using hk
    have hnat := fromOriginalHeartH0primeHomOfIsLE_naturality t
      (X := T.obj₁) (Y := T.obj₂) E T.mor₁ k
    calc
      T.mor₁ ≫ fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k =
          fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₁) E
            ((originalHeartH0primeFunctor t).map T.mor₁ ≫ k) := hnat.symm
      _ = fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₁) E 0 :=
        congrArg (fun q : originalHeartH0prime t T.obj₁ ⟶ E =>
          fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₁) E q) hk₀
      _ = 0 := fromOriginalHeartH0primeHomOfIsLE_zero t (X := T.obj₁) E
  let desc : ∀ {E : t.heart.FullSubcategory} (k : S.X₂ ⟶ E)
      (hk : S.f ≫ k = 0), S.X₃ ⟶ E :=
    fun {E} k hk => toOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E
      ((T.yoneda_exact₂ hT
        (fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k)
        (kernel_condition k hk)).choose)
  refine CokernelCofork.IsColimit.ofπ S.g S.zero desc ?_ ?_
  · intro E k hk
    let k' := fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k
    let l' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose
    have hl' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose_spec
    have hfac :
        fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E (S.g ≫ desc k hk) =
          fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k := by
      rw [show desc k hk =
        toOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E l' by rfl]
      rw [show S.g = (originalHeartH0primeFunctor t).map T.mor₂ by rfl]
      have hnat := fromOriginalHeartH0primeHomOfIsLE_naturality t
        (X := T.obj₂) (Y := T.obj₃) E T.mor₂
        (toOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E l')
      calc
        _ = T.mor₂ ≫ fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E
              (toOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E l') := hnat
        _ = T.mor₂ ≫ l' := by
          rw [fromOriginalHeartH0primeHomOfIsLE_toOriginalHeartH0primeHomOfIsLE]
        _ = fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k := by
          simpa [k', l'] using hl'.symm
    have hfac' := congrArg
      (toOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E) hfac
    simpa using hfac'
  · intro E k hk m hm
    let k' := fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E k
    let l' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose
    have hm₀ : (originalHeartH0primeFunctor t).map T.mor₂ ≫ m = k := by
      simpa [S] using hm
    have hm' := congrArg
      (fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₂) E) hm₀
    have hm'' :
        T.mor₂ ≫ fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E m = k' := by
      have hnat := fromOriginalHeartH0primeHomOfIsLE_naturality t
        (X := T.obj₂) (Y := T.obj₃) E T.mor₂ m
      exact hnat.symm.trans (by simpa [k'] using hm')
    have hl' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose_spec
    have hzero :
        T.mor₂ ≫
          (fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E m - l') = 0 := by
      rw [Preadditive.comp_sub, hm'', ← hl']
      simp
    obtain ⟨q, hq⟩ := T.yoneda_exact₃ hT
      (fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E m - l') hzero
    have hqzero : q = 0 := by
      letI : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
        t.isLE_shift T.obj₁ 0 1 (-1) (by lia)
      letI : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
      exact t.zero q (-1) 0 (by lia)
    have hmEq : fromOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E m = l' := by
      rw [← sub_eq_zero]
      simpa [hqzero] using hq
    have hmEq' := congrArg
      (toOriginalHeartH0primeHomOfIsLE t (X := T.obj₃) E) hmEq
    simpa [desc, l'] using hmEq'

/-! ## Reduction to a nonpositive source -/

/-- Alternative `H⁰` sends the canonical map `τ≤0 X ⟶ X` to an
isomorphism. -/
private theorem isIso_originalHeartH0primeFunctor_map_truncLEι
    (t : TStructure C) (X : C) :
    IsIso ((originalHeartH0primeFunctor t).map ((t.truncLEι 0).app X)) := by
  haveI hH0 : IsIso
      ((originalHeartCohFunctor t 0).map ((t.truncLEι 0).app X)) := by
    let eH0 :
        (originalHeartCohFunctor t 0).obj ((t.truncLE 0).obj X) ≅
          (originalHeartCohFunctor t 0).obj X := by
      refine ObjectProperty.isoMk _ ?_
      simpa [originalHeartCohFunctor] using
        (shiftFunctor C (0 : ℤ)).mapIso
          ((t.truncGE 0).mapIso
            (asIso ((t.truncLE 0).map ((t.truncLEι 0).app X))))
    have heH0 :
        (originalHeartCohFunctor t 0).map ((t.truncLEι 0).app X) = eH0.hom := by
      ext
      rfl
    rw [heH0]
    infer_instance
  let e := originalHeartH0FunctorIsoH0primeFunctor t
  haveI hcomp : IsIso
      (e.hom.app ((t.truncLE 0).obj X) ≫
        (originalHeartH0primeFunctor t).map ((t.truncLEι 0).app X)) := by
    rw [← e.hom.naturality ((t.truncLEι 0).app X)]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app ((t.truncLE 0).obj X))
    ((originalHeartH0primeFunctor t).map ((t.truncLEι 0).app X))

/-- Alternative `H⁰` sends a distinguished triangle with nonpositive source
to an exact short complex. -/
private theorem originalHeartH0primeFunctor_map_distinguished_exact_of_obj₁_isLE
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
    [t.IsLE T.obj₁ 0] :
    ((shortComplexOfDistTriangle T hT).map
      (originalHeartH0primeFunctor t)).Exact := by
  let a : T.obj₁ ⟶ (t.truncLE 0).obj T.obj₂ :=
    t.liftTruncLE T.mor₁ 0
  obtain ⟨Q, q, d, hQ⟩ := distinguished_cocone_triangle a
  let oct := Triangulated.someOctahedron (t.liftTruncLE_ι T.mor₁ 0)
    hQ (t.triangleLEGT_distinguished 0 T.obj₂) hT
  have hQLE : t.IsLE Q 0 := by
    letI : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
      t.isLE_shift T.obj₁ 0 1 (-1) (by lia)
    have hAshLE : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) 0 :=
      t.isLE_of_le _ (-1) 0
    exact t.isLE₂ (Triangle.mk a q d).rotate
      (rot_of_distTriang _ hQ) 0 (by dsimp; infer_instance) (by
        dsimp
        exact hAshLE)
  let TQ := oct.triangle
  let TX₃ := (t.triangleLEGT 0).obj T.obj₃
  obtain ⟨e, he⟩ := t.triangle_iso_exists oct.mem
    (t.triangleLEGT_distinguished 0 T.obj₃) (Iso.refl T.obj₃) 0 1
    (by simpa [TQ] using hQLE)
    (by dsimp [TQ, oct]; exact t.isGE_truncGT_obj T.obj₂ 0 1)
    (by dsimp [TX₃]; exact t.isLE_truncLE_obj T.obj₃ 0 0)
    (by dsimp [TX₃]; exact t.isGE_truncGT_obj T.obj₃ 0 1)
  let eQ : Q ≅ (t.truncLE 0).obj T.obj₃ := Triangle.π₁.mapIso e
  have heQ : oct.m₁ = eQ.hom ≫ (t.truncLEι 0).app T.obj₃ := by
    have hecomm := e.hom.comm₁
    change oct.m₁ ≫ e.hom.hom₂ =
      eQ.hom ≫ (t.truncLEι 0).app T.obj₃ at hecomm
    rw [he] at hecomm
    simpa using hecomm
  have hq : q ≫ eQ.hom = (t.truncLE 0).map T.mor₂ := by
    apply t.to_truncLE_obj_ext
    rw [Category.assoc, ← heQ]
    exact oct.comm₁.trans (by
      simpa using ((t.truncLEι 0).naturality T.mor₂).symm)
  let Tle : Triangle C :=
    Triangle.mk a ((t.truncLE 0).map T.mor₂) (eQ.inv ≫ d)
  have hTle : Tle ∈ distTriang C := by
    refine isomorphic_distinguished _ hQ Tle ?_
    exact (Triangle.isoMk (Triangle.mk a q d) Tle
      (Iso.refl _) (Iso.refl _) eQ
      (by simp [Tle])
      (by simpa [Tle] using hq)
      (by simp [Tle])).symm
  letI hTleLE₁ : t.IsLE Tle.obj₁ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₂ : t.IsLE Tle.obj₂ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₃ : t.IsLE Tle.obj₃ 0 := by
    dsimp [Tle]
    infer_instance
  have hExactLE :
      ((shortComplexOfDistTriangle Tle hTle).map
        (originalHeartH0primeFunctor t)).Exact :=
    originalHeartH0primeFunctor_map_distinguished_exact_of_isLE t Tle hTle
  let Sle := (shortComplexOfDistTriangle Tle hTle).map
    (originalHeartH0primeFunctor t)
  let S := (shortComplexOfDistTriangle T hT).map
    (originalHeartH0primeFunctor t)
  letI hIso₂ : IsIso ((originalHeartH0primeFunctor t).map
      ((t.truncLEι 0).app T.obj₂)) :=
    isIso_originalHeartH0primeFunctor_map_truncLEι t T.obj₂
  letI hIso₃ : IsIso ((originalHeartH0primeFunctor t).map
      ((t.truncLEι 0).app T.obj₃)) :=
    isIso_originalHeartH0primeFunctor_map_truncLEι t T.obj₃
  let e₂ := @asIso _ _ _ _
    ((originalHeartH0primeFunctor t).map ((t.truncLEι 0).app T.obj₂)) hIso₂
  let e₃ := @asIso _ _ _ _
    ((originalHeartH0primeFunctor t).map ((t.truncLEι 0).app T.obj₃)) hIso₃
  let eS : Sle ≅ S := ShortComplex.isoMk
    (Iso.refl _) e₂ e₃
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [Category.id_comp]
      rw [← Functor.map_comp]
      exact congrArg ((originalHeartH0primeFunctor t).map)
        (by simpa [a] using (t.liftTruncLE_ι T.mor₁ 0).symm))
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [← Functor.map_comp]
      simpa using congrArg ((originalHeartH0primeFunctor t).map)
        ((t.truncLEι 0).naturality T.mor₂).symm)
  exact (ShortComplex.exact_iff_of_iso eS).mp
    (by simpa [Sle] using hExactLE)

/-! ## The strictly positive source -/

/-- A morphism from a heart object into `X` factors canonically through the
alternative degree-zero normal form. -/
private noncomputable def toOriginalHeartH0primeHom
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (f : E.obj ⟶ X) : E ⟶ originalHeartH0prime t X :=
  letI : t.IsLE E.obj 0 := (t.mem_heart_iff _).mp E.property |>.1
  ObjectProperty.homMk
    (t.liftTruncLE (f ≫ (t.truncGEπ 0).app X) 0)

@[reassoc (attr := simp)]
private theorem toOriginalHeartH0primeHom_hom
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (f : E.obj ⟶ X) :
    (toOriginalHeartH0primeHom t E f).hom ≫
        (t.truncLEι 0).app ((t.truncGE 0).obj X) =
      f ≫ (t.truncGEπ 0).app X := by
  letI : t.IsLE E.obj 0 := (t.mem_heart_iff _).mp E.property |>.1
  change t.liftTruncLE (f ≫ (t.truncGEπ 0).app X) 0 ≫
      (t.truncLEι 0).app ((t.truncGE 0).obj X) =
    f ≫ (t.truncGEπ 0).app X
  simpa using t.liftTruncLE_ι (f ≫ (t.truncGEπ 0).app X) 0

private theorem hom_ext_toOriginalHeartH0prime
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    {β₁ β₂ : E ⟶ originalHeartH0prime t X}
    (hβ :
      β₁.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) =
        β₂.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X)) :
    β₁ = β₂ := by
  letI : t.IsLE E.obj 0 := (t.mem_heart_iff _).mp E.property |>.1
  ext
  exact t.to_truncLE_obj_ext hβ

private theorem toOriginalHeartH0primeHom_eq
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (f : E.obj ⟶ X) (β : E ⟶ originalHeartH0prime t X)
    (hβ :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) =
        f ≫ (t.truncGEπ 0).app X) :
    β = toOriginalHeartH0primeHom t E f := by
  apply hom_ext_toOriginalHeartH0prime t E
  rw [hβ, toOriginalHeartH0primeHom_hom t E f]

@[reassoc]
private theorem toOriginalHeartH0primeHom_comp_map
    (t : TStructure C) (E : t.heart.FullSubcategory) {X Y : C}
    (f : E.obj ⟶ X) (g : X ⟶ Y) :
    toOriginalHeartH0primeHom t E f ≫
        (originalHeartH0primeFunctor t).map g =
      toOriginalHeartH0primeHom t E (f ≫ g) := by
  apply hom_ext_toOriginalHeartH0prime t E
  rw [toOriginalHeartH0primeHom_hom t E (f ≫ g)]
  let lhs :=
    (toOriginalHeartH0primeHom t E f).hom ≫
      (t.truncLE 0).map ((t.truncGE 0).map g) ≫
        (t.truncLEι 0).app ((t.truncGE 0).obj Y)
  let mid :=
    (toOriginalHeartH0primeHom t E f).hom ≫
      (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
        (t.truncGE 0).map g
  let rhs := f ≫ (t.truncGEπ 0).app X ≫ (t.truncGE 0).map g
  have h₁ : lhs = mid := by
    simpa only [lhs, mid, Category.assoc, Functor.id_map] using
      congrArg (fun k => (toOriginalHeartH0primeHom t E f).hom ≫ k)
        ((t.truncLEι 0).naturality ((t.truncGE 0).map g))
  have h₂ : mid = rhs := by
    dsimp [mid, rhs]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ (t.truncGE 0).map g)
      (toOriginalHeartH0primeHom_hom t E f)
  have h₃ : rhs = f ≫ g ≫ (t.truncGEπ 0).app Y := by
    simpa only [rhs, Category.assoc] using
      congrArg (fun k => f ≫ k) (t.truncGEπ_naturality 0 g)
  simpa [originalHeartH0primeFunctor, TStructure.truncLEGE,
    Category.assoc, lhs] using h₁.trans (h₂.trans h₃)

@[simp]
private theorem toOriginalHeartH0primeHom_zero
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C} :
    toOriginalHeartH0primeHom t E (0 : E.obj ⟶ X) = 0 := by
  apply hom_ext_toOriginalHeartH0prime t E
  rw [toOriginalHeartH0primeHom_hom t E (0 : E.obj ⟶ X)]
  simp

@[simp]
private theorem toOriginalHeartH0primeHom_add
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (f g : E.obj ⟶ X) :
    toOriginalHeartH0primeHom t E (f + g) =
      toOriginalHeartH0primeHom t E f +
        toOriginalHeartH0primeHom t E g := by
  apply hom_ext_toOriginalHeartH0prime t E
  rw [toOriginalHeartH0primeHom_hom t E (f + g)]
  rw [Preadditive.add_comp]
  change
    f ≫ (t.truncGEπ 0).app X + g ≫ (t.truncGEπ 0).app X =
      ((toOriginalHeartH0primeHom t E f).hom +
        (toOriginalHeartH0primeHom t E g).hom) ≫
          (t.truncLEι 0).app ((t.truncGE 0).obj X)
  rw [Preadditive.add_comp]
  rw [toOriginalHeartH0primeHom_hom t E f,
    toOriginalHeartH0primeHom_hom t E g]

/-- If the lower obstruction vanishes, a morphism into alternative `H⁰`
lifts to an ambient morphism. -/
private theorem exists_toOriginalHeartH0primeHom_eq_of_obstruction_zero
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (β : E ⟶ originalHeartH0prime t X)
    (hβ :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
          (t.truncGEδLT 0).app X = 0) :
    ∃ f : E.obj ⟶ X, β = toOriginalHeartH0primeHom t E f := by
  let b : E.obj ⟶ (t.truncGE 0).obj X :=
    β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X)
  have hb : b ≫ (t.truncGEδLT 0).app X = 0 := by
    simpa [b, Category.assoc] using hβ
  obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₃ _
    (t.triangleLTGE_distinguished 0 X) b hb
  refine ⟨f, toOriginalHeartH0primeHom_eq t E f β ?_⟩
  simpa [b] using hf

/-- Vanishing after alternative `H⁰(g)` can be tested after the defining
inclusion into `τ≥0`. -/
private theorem comp_originalHeartH0primeFunctor_map_eq_zero_iff
    (t : TStructure C) (E : t.heart.FullSubcategory) {X Y : C}
    (β : E ⟶ originalHeartH0prime t X) (g : X ⟶ Y) :
    β ≫ (originalHeartH0primeFunctor t).map g = 0 ↔
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
        (t.truncGE 0).map g = 0 := by
  constructor
  · intro hβ
    have hβ' : β.hom ≫ (t.truncLE 0).map ((t.truncGE 0).map g) = 0 := by
      simpa [originalHeartH0primeFunctor, originalHeartH0prime,
        TStructure.truncLEGE] using congrArg (fun f => f.hom) hβ
    have hβ'' :
        β.hom ≫ (t.truncLE 0).map ((t.truncGE 0).map g) ≫
          (t.truncLEι 0).app ((t.truncGE 0).obj Y) = 0 := by
      simpa [Category.assoc] using
        congrArg (fun k => k ≫
          (t.truncLEι 0).app ((t.truncGE 0).obj Y)) hβ'
    calc
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
          (t.truncGE 0).map g =
        β.hom ≫ (t.truncLE 0).map ((t.truncGE 0).map g) ≫
          (t.truncLEι 0).app ((t.truncGE 0).obj Y) := by
            simpa [Category.assoc] using
              congrArg (fun k => β.hom ≫ k)
                (((t.truncLEι 0).naturality ((t.truncGE 0).map g)).symm)
      _ = 0 := hβ''
  · intro hβ
    apply hom_ext_toOriginalHeartH0prime t E
    have hcomp :
        (β ≫ (originalHeartH0primeFunctor t).map g).hom ≫
            (t.truncLEι 0).app ((t.truncGE 0).obj Y) =
          β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
            (t.truncGE 0).map g := by
      simpa [originalHeartH0primeFunctor, originalHeartH0prime,
        TStructure.truncLEGE, Category.assoc] using
        congrArg (fun k => β.hom ≫ k)
          ((t.truncLEι 0).naturality ((t.truncGE 0).map g))
    have hzero :
        β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj X) ≫
            (t.truncGE 0).map g =
          0 ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Y) := by
      simpa [hβ]
    exact hcomp.trans hzero

private theorem toOriginalHeartH0primeHom_eq_zero_iff
    (t : TStructure C) (E : t.heart.FullSubcategory) {X : C}
    (f : E.obj ⟶ X) :
    toOriginalHeartH0primeHom t E f = 0 ↔
      f ≫ (t.truncGEπ 0).app X = 0 := by
  constructor
  · intro hf
    simpa [hf] using (toOriginalHeartH0primeHom_hom t E f).symm
  · intro hf
    apply hom_ext_toOriginalHeartH0prime t E
    simpa [hf] using toOriginalHeartH0primeHom_hom t E f

/-- Alternative degree-zero cohomology vanishes on `D^{≥1}`. -/
private theorem isZero_originalHeartH0prime_of_isGE_one
    (t : TStructure C) {X : C} [t.IsGE X 1] :
    IsZero (originalHeartH0prime t X) := by
  refine CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  change IsZero ((t.truncLE 0).obj ((t.truncGE 0).obj X))
  exact t.isZero_truncLE_obj_of_isGE 0 1 rfl ((t.truncGE 0).obj X)

/-- If `τ<0` maps the second triangle arrow isomorphically, applying
alternative `H⁰` and evaluating at a heart object is exact. -/
private theorem originalHeartH0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map
    (t : TStructure C) {A Z X₃ : C}
    {m₁ : A ⟶ Z} {m₃ : Z ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ ∈ distTriang C)
    (hm₃LT : IsIso ((t.truncLT 0).map m₃))
    (E : t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk m₁ m₃ δ) hT).map
      (originalHeartH0primeFunctor t ⋙
        preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro β hβ
  letI := hm₃LT
  have hkernel :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
          (t.truncGE 0).map m₃ = 0 :=
    (comp_originalHeartH0primeFunctor_map_eq_zero_iff t E β m₃).mp hβ
  have hkernel' :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
          (t.truncGE 0).map m₃ ≫ (t.truncGEδLT 0).app X₃ = 0 := by
    simpa [Category.assoc] using
      congrArg (fun k => k ≫ (t.truncGEδLT 0).app X₃) hkernel
  have hobsComp :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
          (t.truncGEδLT 0).app Z ≫
            ((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' = 0 := by
    calc
      _ = β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
          (t.truncGE 0).map m₃ ≫ (t.truncGEδLT 0).app X₃ := by
            simpa [Category.assoc] using
              congrArg
                (fun k =>
                  β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫ k)
                ((t.truncGEδLT 0).naturality m₃).symm
      _ = 0 := hkernel'
  have hobs :
      β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
          (t.truncGEδLT 0).app Z = 0 := by
    have hobsComp' :
        β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
            (t.truncGEδLT 0).app Z ≫
              ((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' =
          0 ≫ ((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' := by
      simpa using hobsComp
    have hobsComp'' :
        (β.hom ≫ (t.truncLEι 0).app ((t.truncGE 0).obj Z) ≫
            (t.truncGEδLT 0).app Z) ≫
              ((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' =
          0 ≫ ((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧' := by
      simpa [Category.assoc] using hobsComp'
    exact (cancel_mono (((t.truncLT 0).map m₃)⟦(1 : ℤ)⟧')).1 hobsComp''
  obtain ⟨f, hfβ⟩ :=
    exists_toOriginalHeartH0primeHom_eq_of_obstruction_zero t E β hobs
  change E.obj ⟶ Z at f
  have hfm₃π : f ≫ m₃ ≫ (t.truncGEπ 0).app X₃ = 0 := by
    have hβ' :
        toOriginalHeartH0primeHom t E f ≫
            (originalHeartH0primeFunctor t).map m₃ = 0 := by
      simpa [hfβ] using hβ
    have hzeroTo :
        toOriginalHeartH0primeHom t E (f ≫ m₃) = 0 := by
      calc
        _ = toOriginalHeartH0primeHom t E f ≫
            (originalHeartH0primeFunctor t).map m₃ := by
              symm
              exact toOriginalHeartH0primeHom_comp_map t E f m₃
        _ = 0 := hβ'
    simpa [Category.assoc] using
      (toOriginalHeartH0primeHom_eq_zero_iff t E (f ≫ m₃)).mp hzeroTo
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _
    (t.triangleLTGE_distinguished 0 X₃) (f ≫ m₃)
    (by simpa using hfm₃π)
  change E.obj ⟶ (t.truncLT 0).obj X₃ at u
  let u' : E.obj ⟶ (t.truncLT 0).obj Z :=
    u ≫ inv ((t.truncLT 0).map m₃)
  have hu' :
      u' ≫ (t.truncLTι 0).app Z ≫ m₃ = f ≫ m₃ := by
    have hu₁ :
        u' ≫ (t.truncLTι 0).app Z ≫ m₃ =
          u' ≫ (t.truncLT 0).map m₃ ≫ (t.truncLTι 0).app X₃ := by
      simpa [Category.assoc] using
        congrArg (fun k => u' ≫ k) ((t.truncLTι 0).naturality m₃).symm
    have hu₂ :
        u' ≫ (t.truncLT 0).map m₃ ≫ (t.truncLTι 0).app X₃ =
          u ≫ (t.truncLTι 0).app X₃ := by
      dsimp [u']
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    have hu₃ : u ≫ (t.truncLTι 0).app X₃ = f ≫ m₃ := by
      simpa using hu.symm
    exact hu₁.trans (hu₂.trans hu₃)
  let n : E.obj ⟶ Z := u' ≫ (t.truncLTι 0).app Z
  have hn : n ≫ m₃ = f ≫ m₃ := by
    simpa [n] using hu'
  let f' : E.obj ⟶ Z := f + (-n)
  have hf'm₃ : f' ≫ m₃ = 0 := by
    simp [f', hn]
  have hu'zero : toOriginalHeartH0primeHom t E n = 0 := by
    have hz :
        (t.truncLTι 0).app Z ≫ (t.truncGEπ 0).app Z = 0 :=
      comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished 0 Z)
    apply (toOriginalHeartH0primeHom_eq_zero_iff t E n).2
    simpa [n, Category.assoc] using congrArg (fun k => u' ≫ k) hz
  have hnegzero : toOriginalHeartH0primeHom t E (-n) = 0 := by
    apply (toOriginalHeartH0primeHom_eq_zero_iff t E (-n)).2
    simpa using congrArg Neg.neg
      ((toOriginalHeartH0primeHom_eq_zero_iff t E n).mp hu'zero)
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hT f' hf'm₃
  have hf'Eq :
      toOriginalHeartH0primeHom t E f' =
        toOriginalHeartH0primeHom t E f := by
    apply hom_ext_toOriginalHeartH0prime t E
    simp [f', hnegzero]
  have hfβ' : toOriginalHeartH0primeHom t E f = β := by
    simpa using hfβ.symm
  have hcomp₁ :
      toOriginalHeartH0primeHom t E a ≫
          (originalHeartH0primeFunctor t).map m₁ =
        toOriginalHeartH0primeHom t E (a ≫ m₁) :=
    toOriginalHeartH0primeHom_comp_map t E a m₁
  have hcomp₂ :
      toOriginalHeartH0primeHom t E (a ≫ m₁) =
        toOriginalHeartH0primeHom t E f' := by
    simpa using congrArg (toOriginalHeartH0primeHom t E) ha.symm
  refine ⟨toOriginalHeartH0primeHom t E a, ?_⟩
  exact hcomp₁.trans (hcomp₂.trans (hf'Eq.trans hfβ'))

/-- If the first vertex is in `D^{≥1}`, evaluation of alternative `H⁰` on
the triangle is exact. -/
private theorem originalHeartH0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one
    (t : TStructure C) {A Z X₃ : C} [t.IsGE A 1]
    {m₁ : A ⟶ Z} {m₃ : Z ⟶ X₃} {δ : X₃ ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk m₁ m₃ δ ∈ distTriang C)
    (E : t.heart.FullSubcategory) :
    ((shortComplexOfDistTriangle (Triangle.mk m₁ m₃ δ) hT).map
      (originalHeartH0primeFunctor t ⋙
        preadditiveCoyoneda.obj (Opposite.op E))).Exact := by
  letI : t.IsGE A 0 := t.isGE_of_ge A 0 1 (by lia)
  have hm₃LT : IsIso ((t.truncLT 0).map m₃) := by
    let T : Triangle C := Triangle.mk m₁ m₃ δ
    have hrot : T.rotate ∈ distTriang C := by
      simpa [T] using rot_of_distTriang _ hT
    have hGE : t.IsGE (T.rotate.obj₃) 0 := by
      change t.IsGE (A⟦(1 : ℤ)⟧) 0
      simpa [T] using t.isGE_shift A 1 1 0 (by lia)
    simpa [T] using t.isIso₁_truncLT_map_of_isGE T.rotate hrot 0 hGE
  exact originalHeartH0primeFunctor_preadditiveCoyoneda_exact_of_isIso_truncLT_map
    t hT hm₃LT E

/-- If the first vertex is strictly positive, alternative `H⁰` maps the
second triangle arrow to a monomorphism. -/
private theorem mono_originalHeartH0primeFunctor_map_mor₂_of_obj₁_isGE_one
    (t : TStructure C) (T : Triangle C) (hT : T ∈ distTriang C)
    [t.IsGE T.obj₁ 1] :
    Mono ((originalHeartH0primeFunctor t).map T.mor₂) := by
  constructor
  intro E u v huv
  let F := preadditiveCoyoneda.obj (Opposite.op E)
  let S := (shortComplexOfDistTriangle T hT).map
    (originalHeartH0primeFunctor t ⋙ F)
  letI : t.IsGE (shortComplexOfDistTriangle T hT).X₁ 1 := by
    dsimp
    infer_instance
  have hTriangle : Triangle.mk T.mor₁ T.mor₂ T.mor₃ = T := by
    cases T
    rfl
  have hExact : S.Exact := by
    simpa [S, F, hTriangle] using
      originalHeartH0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one
        t (A := T.obj₁) (Z := T.obj₂) (X₃ := T.obj₃) hT E
  have hzeroObj : IsZero S.X₁ := by
    exact F.map_isZero (isZero_originalHeartH0prime_of_isGE_one t)
  have hzero : S.f = 0 := hzeroObj.eq_of_src _ _
  letI : Mono S.g := hExact.mono_g hzero
  exact (AddCommGrpCat.mono_iff_injective S.g).mp inferInstance
    (by simpa [S, F] using huv)

/-! ## Unconditional homologicality -/

/-- The alternative degree-zero normal form is a homological functor. -/
private theorem originalHeartH0primeFunctor_isHomological
    (t : TStructure C) :
    Functor.IsHomological (originalHeartH0primeFunctor t) := by
  refine ⟨fun T hT => ?_⟩
  obtain ⟨Z, v, w, m₁, m₃, h13, h23, _hm₁, _hmw, hm₃⟩ :=
    CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split t (C := C) hT 1
  let Tle : Triangle C :=
    Triangle.mk ((t.truncLTι 1).app T.obj₁ ≫ T.mor₁) v w
  let Tge : Triangle C :=
    Triangle.mk m₁ m₃
      (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
        ((t.truncGEπ 1).app T.obj₁))
  letI : t.IsLE Tle.obj₁ 0 := by
    dsimp [Tle]
    exact t.isLE_truncLT_obj T.obj₁ 1 0 (by lia)
  have hExactLE :
      ((shortComplexOfDistTriangle Tle h13).map
        (originalHeartH0primeFunctor t)).Exact :=
    originalHeartH0primeFunctor_map_distinguished_exact_of_obj₁_isLE
      t Tle h13
  letI : t.IsGE Tge.obj₁ 1 := by
    dsimp [Tge]
    exact t.isGE_truncGE_obj T.obj₁ 1 1
  letI hmono₃ : Mono ((originalHeartH0primeFunctor t).map m₃) :=
    mono_originalHeartH0primeFunctor_map_mor₂_of_obj₁_isGE_one
      t Tge h23
  let Sle := (shortComplexOfDistTriangle Tle h13).map
    (originalHeartH0primeFunctor t)
  let S := (shortComplexOfDistTriangle T hT).map
    (originalHeartH0primeFunctor t)
  haveI hIso₁ : IsIso ((originalHeartH0primeFunctor t).map
      ((t.truncLTι 1).app T.obj₁)) := by
    have h := isIso_originalHeartH0primeFunctor_map_truncLEι t T.obj₁
    norm_num [TStructure.truncLE, TStructure.truncLEι] at h
    exact h
  let α : Sle ⟶ S :=
    { τ₁ := (originalHeartH0primeFunctor t).map
        ((t.truncLTι 1).app T.obj₁)
      τ₂ := 𝟙 _
      τ₃ := (originalHeartH0primeFunctor t).map m₃
      comm₁₂ := by
        dsimp [Sle, S, Tle]
        simp only [Category.comp_id, ← Functor.map_comp]
      comm₂₃ := by
        dsimp [Sle, S, Tle]
        simp only [Category.id_comp, ← Functor.map_comp]
        exact congrArg ((originalHeartH0primeFunctor t).map) hm₃.symm }
  haveI : IsIso α.τ₁ := by
    dsimp [α]
    exact hIso₁
  haveI : Epi α.τ₁ := by infer_instance
  haveI : IsIso α.τ₂ := by
    dsimp [α]
    exact Iso.isIso_hom (Iso.refl _)
  haveI : Mono α.τ₃ := by
    dsimp [α]
    exact hmono₃
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
    (by simpa [Sle] using hExactLE)

/-- The proposition that degree-`n` original-heart cohomology is
homological. -/
abbrev OriginalHeartCohomologyIsHomological (t : TStructure C) (n : ℤ) : Prop :=
  Functor.IsHomological (originalHeartCohFunctor t n)

/-- Degree-zero cohomology of any t-structure sends distinguished triangles
to exact short complexes in the heart. -/
@[implicit_reducible]
private noncomputable def originalHeartCohFunctor_zero_isHomological
    (t : TStructure C) :
    Functor.IsHomological (originalHeartCohFunctor t 0) := by
  letI : Functor.IsHomological (originalHeartH0primeFunctor t) :=
    originalHeartH0primeFunctor_isHomological t
  exact Functor.IsHomological.of_iso
    (originalHeartH0FunctorIsoH0primeFunctor t).symm

/-- Shifting the input before applying degree-zero heart cohomology preserves
homologicality. The shifted distinguished triangle scales both maps in its
short complex by the same unit `(-1)^n`, so exactness is unchanged. -/
@[implicit_reducible]
private noncomputable def shiftFunctorCompOriginalHeartH0IsHomological
    (t : TStructure C) (n : ℤ) :
    Functor.IsHomological
      (shiftFunctor C n ⋙ originalHeartCohFunctor t 0) := by
  letI : Functor.IsHomological (originalHeartCohFunctor t 0) :=
    originalHeartCohFunctor_zero_isHomological t
  apply Functor.IsHomological.mk'
  intro T hT
  refine ⟨T, Iso.refl _, ?_⟩
  let Tn := (shiftFunctor (Triangle C) n).obj T
  have hTn : Tn ∈ distTriang C := Triangle.shift_distinguished T hT n
  let S := (shortComplexOfDistTriangle T hT).map
    (shiftFunctor C n ⋙ originalHeartCohFunctor t 0)
  let Sn := (shortComplexOfDistTriangle Tn hTn).map
    (originalHeartCohFunctor t 0)
  let e₂ : S.X₂ ≅ Sn.X₂ := n.negOnePow • Iso.refl _
  refine ShortComplex.exact_of_iso ?_
    (Functor.map_distinguished_exact (originalHeartCohFunctor t 0) Tn hTn)
  exact ShortComplex.isoMk (Iso.refl _) e₂ (Iso.refl _) (by
      change _ = _ ≫ e₂.hom
      change _ = _ ≫ (n.negOnePow • (𝟙 _ : S.X₂ ⟶ S.X₂))
      dsimp [Tn]
      rw [Category.id_comp, Functor.map_units_smul,
        Linear.comp_units_smul, Category.comp_id]
      let f₁ := (originalHeartCohFunctor t 0).map
        ((shiftFunctor C n).map T.mor₁)
      change f₁ = n.negOnePow • n.negOnePow • f₁
      calc
        f₁ = (1 : ℤˣ) • f₁ := (one_smul _ _).symm
        _ = (n.negOnePow * n.negOnePow) • f₁ := by
          rw [Int.units_mul_self]
        _ = n.negOnePow • n.negOnePow • f₁ := mul_smul ..) (by
      change e₂.hom ≫ _ = _
      change (n.negOnePow • (𝟙 _ : S.X₂ ⟶ S.X₂)) ≫ _ = _
      dsimp [Tn]
      rw [Category.comp_id, Functor.map_units_smul,
        Linear.units_smul_comp, Category.id_comp])

/-- Heart cohomology in every degree sends distinguished triangles to exact
short complexes in the heart. -/
noncomputable instance originalHeartCohFunctor_isHomological
    (t : TStructure C) (n : ℤ) :
    Functor.IsHomological (originalHeartCohFunctor t n) := by
  letI : Functor.IsHomological
      (shiftFunctor C n ⋙ originalHeartCohFunctor t 0) :=
    shiftFunctorCompOriginalHeartH0IsHomological t n
  exact Functor.IsHomological.of_iso (originalHeartCohShiftNatIso t n).symm

end CategoryTheory.Triangulated.Tilting
