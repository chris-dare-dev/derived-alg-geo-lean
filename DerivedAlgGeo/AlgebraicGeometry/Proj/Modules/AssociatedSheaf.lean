/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Localization
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The sheaf associated to a graded module on `Proj`

For an `ℕ`-graded ring `A = ⨁ i, 𝒜 i` and a compatibly graded `A`-module
`M = ⨁ i, 𝓜 i`, this file constructs the sheaf usually denoted `M̃` on `Proj 𝒜`.
Its fiber at a homogeneous prime is the degree-zero homogeneous localization from
`AlgebraicGeometry.Proj.Modules.GradedLocalization`, and its sections are the dependent
functions which are locally represented by one homogeneous module fraction.

The construction deliberately mirrors Mathlib's `ProjectiveSpectrum.StructureSheaf`: the
underlying topological space, restrictions, structure-sheaf scalars, and stalk evaluation maps
are the existing Mathlib ones.
-/

noncomputable section

open scoped DirectSum Pointwise

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace

open GradedModule

namespace AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-! ## Local homogeneous module fractions -/

/-- The degree-zero homogeneous localization of `M` at a point of `Proj 𝒜`. -/
abbrev Fiber (x : ProjectiveSpectrum 𝒜) :=
  DegreeZeroLocalization 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl

/-- A dependent module section is a single homogeneous fraction on an open set. -/
def IsFraction {U : Opens X} (f : ∀ x : U, Fiber 𝒜 𝓜 x.1) : Prop :=
  ∃ (i : ℕ) (r : 𝓜 i) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∉ x.1.asHomogeneousIdeal),
      ∀ x : U, f x = DegreeZeroLocalization.mk
        { deg := i
          num := r
          den := s
          den_mem := s_nin x }

/-- The fixed-fraction predicate is preserved by restriction. -/
def isFractionPrelocal : PrelocalPredicate fun x : X => Fiber 𝒜 𝓜 x where
  pred f := IsFraction 𝒜 𝓜 f
  res := by
    rintro V U j f ⟨i, r, s, hs, h⟩
    exact ⟨i, r, s, fun x => hs (j x), fun x => h (j x)⟩

/-- The local predicate defining `M̃`: locally, a section is one homogeneous fraction. -/
def isLocallyFraction : LocalPredicate fun x : X => Fiber 𝒜 𝓜 x :=
  (isFractionPrelocal 𝒜 𝓜).sheafify

namespace Sections

variable {𝒜 𝓜}

theorem zero_mem' (U : Opens X) :
    (isLocallyFraction 𝒜 𝓜).pred (0 : ∀ x : U, Fiber 𝒜 𝓜 x.1) := fun x =>
  ⟨U, x.2, 𝟙 U, 0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩,
    fun y => (Ideal.IsPrime.one_notMem inferInstance), fun y => by
      apply DegreeZeroLocalization.ext
      simp [NumDenSameDeg.embedding]⟩

theorem add_mem' (U : Opens X) (a b : ∀ x : U, Fiber 𝒜 𝓜 x.1)
    (ha : (isLocallyFraction 𝒜 𝓜).pred a)
    (hb : (isLocallyFraction 𝒜 𝓜).pred b) :
    (isLocallyFraction 𝒜 𝓜).pred (a + b) := fun x => by
  obtain ⟨Va, hxa, ia, da, ra, sa, hsa, wa⟩ := ha x
  obtain ⟨Vb, hxb, ib, db, rb, sb, hsb, wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨hxa, hxb⟩, Opens.infLELeft _ _ ≫ ia, da + db,
    ⟨(sb : A) • (ra : M) + (sa : A) • (rb : M), ?_⟩,
    ⟨(sa : A) * (sb : A), SetLike.mul_mem_graded sa.2 sb.2⟩,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩), fun y => ?_⟩
  · exact add_mem
      (add_comm db da ▸ SetLike.GradedSMul.smul_mem sb.2 ra.2)
      (SetLike.GradedSMul.smul_mem sa.2 rb.2)
  · let ya : Va := Opens.infLELeft Va Vb y
    let yb : Vb := Opens.infLERight Va Vb y
    refine (congrArg₂ (· + ·) (wa ya) (wb yb)).trans ?_
    apply DegreeZeroLocalization.ext
    simp only [DegreeZeroLocalization.coe_add, DegreeZeroLocalization.coe_mk,
      NumDenSameDeg.embedding]
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

theorem neg_mem' (U : Opens X) (a : ∀ x : U, Fiber 𝒜 𝓜 x.1)
    (ha : (isLocallyFraction 𝒜 𝓜).pred a) :
    (isLocallyFraction 𝒜 𝓜).pred (-a) := fun x => by
  obtain ⟨V, hxV, i, d, r, s, hs, h⟩ := ha x
  refine ⟨V, hxV, i, d, ⟨-(r : M), neg_mem r.2⟩, s, hs, fun y => ?_⟩
  refine (congrArg Neg.neg (h y)).trans ?_
  apply DegreeZeroLocalization.ext
  simpa only [DegreeZeroLocalization.coe_neg, DegreeZeroLocalization.coe_mk,
    NumDenSameDeg.embedding] using
      (LocalizedModule.mk_neg
        (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) (M := M)
        (m := (r : M))
        (s := (⟨(s : A), hs y⟩ : y.1.asHomogeneousIdeal.toIdeal.primeCompl))).symm

end Sections

/-! ## Module-valued sheaf -/

/-- The locally fractional sections form an additive subgroup. -/
def sectionsAddSubgroup (U : Opens X) :
    AddSubgroup (∀ x : U, Fiber 𝒜 𝓜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 𝓜).pred f}
  zero_mem' := Sections.zero_mem' U
  add_mem' := Sections.add_mem' U _ _
  neg_mem' := Sections.neg_mem' U _

/-- Evaluation of a structure-sheaf section makes every fiber a module over the ring of
sections on the ambient open. -/
noncomputable instance sectionFiberModule (U : Opens X) (x : U) :
    Module (𝒪.1.obj (op U)) (Fiber 𝒜 𝓜 x.1) :=
  Module.compHom _
    (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2).hom

/-- The locally fractional sections form a module over Mathlib's structure-sheaf sections. -/
def sectionsSubmodule (U : Opens X) :
    Submodule (𝒪.1.obj (op U)) (∀ x : U, Fiber 𝒜 𝓜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 𝓜).pred f}
  zero_mem' := Sections.zero_mem' U
  add_mem' := Sections.add_mem' U _ _
  smul_mem' r a ha x := by
    obtain ⟨V, hxV, i, dr, rr, sr, hsr, hr⟩ := r.2 x
    obtain ⟨W, hxW, j, dm, rm, sm, hsm, hm⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ i, dr + dm,
      ⟨(rr : A) • (rm : M), SetLike.GradedSMul.smul_mem rr.2 rm.2⟩,
      ⟨(sr : A) * (sm : A), SetLike.mul_mem_graded sr.2 sm.2⟩,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
        (hsr ⟨y.1, y.2.1⟩) (hsm ⟨y.1, y.2.2⟩), fun y => ?_⟩
    let yr : V := Opens.infLELeft V W y
    let ym : W := Opens.infLERight V W y
    refine (congrArg₂ (· • ·) (hr yr) (hm ym)).trans ?_
    apply DegreeZeroLocalization.ext
    change (algebraMap
        (HomogeneousLocalization 𝒜 y.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (HomogeneousLocalization.mk
          { deg := dr
            num := rr
            den := sr
            den_mem := hsr ⟨y.1, y.2.1⟩ })) •
        LocalizedModule.mk (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (rm : M) (⟨(sm : A), hsm ⟨y.1, y.2.2⟩⟩) =
      LocalizedModule.mk (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
        ((rr : A) • (rm : M))
          (⟨(sr : A) * (sm : A),
            y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
              (hsr ⟨y.1, y.2.1⟩) (hsm ⟨y.1, y.2.2⟩)⟩)
    rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
      LocalizedModule.mk_smul_mk]
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

/-- The `Type`-valued sheaf underlying the associated graded-module sheaf. -/
def associatedSheafInType : Sheaf (Type u) X :=
  subsheafToTypes (isLocallyFraction 𝒜 𝓜)

instance (U : (Opens X)ᵒᵖ) :
    AddCommGroup ((associatedSheafInType 𝒜 𝓜).1.obj U) :=
  (sectionsAddSubgroup 𝒜 𝓜 U.unop).toAddCommGroup

instance (U : (Opens X)ᵒᵖ) :
    Module (𝒪.1.obj U) ((associatedSheafInType 𝒜 𝓜).1.obj U) :=
  (sectionsSubmodule 𝒜 𝓜 U.unop).module

/-- The additive presheaf underlying `M̃`. -/
def associatedPresheafInAddCommGrp : Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of ((associatedSheafInType 𝒜 𝓜).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (associatedSheafInType 𝒜 𝓜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The presheaf of modules over Mathlib's structure presheaf. -/
def associatedPresheaf :
    PresheafOfModules (𝒪.1 ⋙ forget₂ CommRingCat RingCat) :=
  letI (U : (Opens X)ᵒᵖ) :
      Module ((𝒪.1 ⋙ forget₂ CommRingCat RingCat).obj U)
        ((associatedPresheafInAddCommGrp 𝒜 𝓜).obj U) := by
    dsimp [associatedPresheafInAddCommGrp]
    change Module (𝒪.1.obj U) ((associatedSheafInType 𝒜 𝓜).1.obj U)
    infer_instance
  .ofPresheaf (associatedPresheafInAddCommGrp 𝒜 𝓜) fun _ _ _ _ _ => rfl

/-- Forgetting the additive structure recovers the locally-fractional `Type`-valued sheaf. -/
def associatedPresheafCompForget :
    associatedPresheafInAddCommGrp 𝒜 𝓜 ⋙ forget AddCommGrpCat ≅
      (associatedSheafInType 𝒜 𝓜).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- The sheaf `M̃` of modules on `Proj 𝒜` associated to the graded module `M`. -/
def associatedSheaf : (AlgebraicGeometry.Proj 𝒜).Modules where
  val := associatedPresheaf (𝓜 := 𝓜) 𝒜
  isSheaf :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
      (associatedPresheaf (𝓜 := 𝓜) 𝒜).presheaf).mpr
      (TopCat.Presheaf.isSheaf_of_iso (associatedPresheafCompForget 𝒜 𝓜).symm
        (associatedSheafInType 𝒜 𝓜).2)

/-! ## Restrictions and stalks -/

@[simp]
theorem associatedPresheaf_res_apply {U V : (Opens X)ᵒᵖ} (i : V ⟶ U)
    (s : (associatedSheafInType 𝒜 𝓜).1.obj V) (x : U.unop) :
    ((associatedSheafInType 𝒜 𝓜).1.map i s).1 x = s.1 (i.unop x) :=
  rfl

@[ext]
theorem section_ext {U : (Opens X)ᵒᵖ}
    {s t : (associatedSheafInType 𝒜 𝓜).1.obj U} (h : s.1 = t.1) : s = t :=
  Subtype.ext h

/-- A homogeneous module fraction at `x` defines a section on the basic open cut out by its
denominator. -/
def sectionInBasicOpen (x : ProjectiveSpectrum 𝒜)
    (c : NumDenSameDeg 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (associatedSheafInType 𝒜 𝓜).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 c.den)) :=
  ⟨fun y => DegreeZeroLocalization.mk
      { deg := c.deg
        num := c.num
        den := c.den
        den_mem := y.2 },
    fun y =>
      ⟨ProjectiveSpectrum.basicOpen 𝒜 c.den, y.2, 𝟙 _, c.deg, c.num, c.den,
        fun z => z.2, fun _ => rfl⟩⟩

@[simp]
theorem sectionInBasicOpen_apply (x : ProjectiveSpectrum 𝒜)
    (c : NumDenSameDeg 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl)
    (y : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    (sectionInBasicOpen 𝒜 𝓜 x c).1 y = DegreeZeroLocalization.mk
      { deg := c.deg
        num := c.num
        den := c.den
        den_mem := y.2 } :=
  rfl

omit [AddCommGroup M] [Module A M] [AddSubgroupClass σM M]
    [SetLike.GradedSMul 𝒜 𝓜] in
set_option backward.isDefEq.respectTransparency false in
theorem mem_basicOpen_den (x : X)
    (c : NumDenSameDeg 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    x ∈ ProjectiveSpectrum.basicOpen 𝒜 c.den := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact c.den_mem

/-- Evaluation of germs gives the canonical map from the stalk of `M̃` to the degree-zero
homogeneous localization at `x`. -/
def stalkToFiber (x : X) :
    (associatedSheafInType 𝒜 𝓜).presheaf.stalk x ⟶ Fiber 𝒜 𝓜 x :=
  TopCat.stalkToFiber (isLocallyFraction 𝒜 𝓜) x

@[simp]
theorem stalkToFiber_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) :
    stalkToFiber 𝒜 𝓜 x ((associatedSheafInType 𝒜 𝓜).presheaf.germ U x hx s) =
      s.1 ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ (isLocallyFraction 𝒜 𝓜) U x hx s

theorem stalkToFiber_surjective (x : X) :
    Function.Surjective (stalkToFiber 𝒜 𝓜 x) := by
  apply TopCat.stalkToFiber_surjective (isLocallyFraction 𝒜 𝓜) x
  intro z
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  let U : OpenNhds x :=
    ⟨ProjectiveSpectrum.basicOpen 𝒜 c.den, mem_basicOpen_den 𝒜 𝓜 x c⟩
  refine ⟨U, fun y => (sectionInBasicOpen 𝒜 𝓜 x c).1 y, ?_, ?_⟩
  · exact (sectionInBasicOpen 𝒜 𝓜 x c).2
  · apply DegreeZeroLocalization.ext
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem stalkToFiber_injective (x : X) :
    Function.Injective (stalkToFiber 𝒜 𝓜 x) := by
  apply TopCat.stalkToFiber_injective (isLocallyFraction 𝒜 𝓜) x
  intro U V fU hU fV hV hEq
  obtain ⟨WU, hxWU, iU, dU, rU, sU, hsU, eU⟩ := hU ⟨x, U.2⟩
  obtain ⟨WV, hxWV, iV, dV, rV, sV, hsV, eV⟩ := hV ⟨x, V.2⟩
  let cU : NumDenSameDeg 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
    { deg := dU
      num := rU
      den := sU
      den_mem := hsU ⟨x, hxWU⟩ }
  let cV : NumDenSameDeg 𝒜 𝓜 x.asHomogeneousIdeal.toIdeal.primeCompl :=
    { deg := dV
      num := rV
      den := sV
      den_mem := hsV ⟨x, hxWV⟩ }
  have hmk :
      DegreeZeroLocalization.mk cU = DegreeZeroLocalization.mk cV := by
    rw [← eU ⟨x, hxWU⟩, ← eV ⟨x, hxWV⟩]
    exact hEq
  obtain ⟨q, hq⟩ := (DegreeZeroLocalization.mk_eq_mk_iff _ _).mp hmk
  let Wopen := (WU ⊓ WV) ⊓ ProjectiveSpectrum.basicOpen 𝒜 (q : A)
  let W : OpenNhds x := ⟨Wopen, ⟨⟨hxWU, hxWV⟩, q.2⟩⟩
  let toWU : W.1 ⟶ WU :=
    Opens.infLELeft (WU ⊓ WV) (ProjectiveSpectrum.basicOpen 𝒜 (q : A)) ≫
      Opens.infLELeft WU WV
  let toWV : W.1 ⟶ WV :=
    Opens.infLELeft (WU ⊓ WV) (ProjectiveSpectrum.basicOpen 𝒜 (q : A)) ≫
      Opens.infLERight WU WV
  let jU : W.1 ⟶ U.1 := toWU ≫ iU
  let jV : W.1 ⟶ V.1 := toWV ≫ iV
  refine ⟨W, jU, jV, fun w => ?_⟩
  let cwU : NumDenSameDeg 𝒜 𝓜 w.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    { deg := dU
      num := rU
      den := sU
      den_mem := hsU (toWU w) }
  let cwV : NumDenSameDeg 𝒜 𝓜 w.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    { deg := dV
      num := rV
      den := sV
      den_mem := hsV (toWV w) }
  have hw : DegreeZeroLocalization.mk cwU = DegreeZeroLocalization.mk cwV :=
    (DegreeZeroLocalization.mk_eq_mk_iff cwU cwV).mpr ⟨⟨q, w.2.2⟩, hq⟩
  exact (eU (toWU w)).trans (hw.trans (eV (toWV w)).symm)

/-- The stalk of the associated sheaf at `x` is the degree-zero homogeneous localization of the
graded module at the corresponding homogeneous prime. -/
def stalkEquiv (x : X) :
    (associatedSheafInType 𝒜 𝓜).presheaf.stalk x ≃ Fiber 𝒜 𝓜 x :=
  Equiv.ofBijective (stalkToFiber 𝒜 𝓜 x)
    ⟨stalkToFiber_injective 𝒜 𝓜 x, stalkToFiber_surjective 𝒜 𝓜 x⟩

@[simp]
theorem stalkEquiv_germ (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) :
    stalkEquiv 𝒜 𝓜 x ((associatedSheafInType 𝒜 𝓜).presheaf.germ U x hx s) =
      s.1 ⟨x, hx⟩ :=
  stalkToFiber_germ 𝒜 𝓜 U x hx s

/-! ## Changing the grading by a membership equivalence

The section-level counterpart of `DegreeZeroLocalization.linearEquivOfMemIff`. Applied
pointwise, it moves nothing: the underlying dependent function and the local fraction's
numerator and denominator are unchanged, and only the membership certificate is rebuilt. -/

/-- Sections of the associated sheaf depend only on the membership predicates of the graded
pieces. -/
noncomputable def sectionAddEquivOfMemIff {σN : Type u} [SetLike σN M] [AddSubgroupClass σN M]
    (𝓝 : ℕ → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) (U : Opens X) :
    (associatedSheafInType 𝒜 𝓜).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 𝓝).1.obj (op U) where
  toFun s := by
    refine ⟨fun x => DegreeZeroLocalization.linearEquivOfMemIff
      (𝒜 := 𝒜) (𝓜 := 𝓜) 𝓝 hmem (s.1 x), ?_⟩
    intro x
    obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
    refine ⟨V, hxV, i, e, ⟨(r : M), (hmem e (r : M)).mp r.2⟩, t, ht, fun y => ?_⟩
    have hy := h y
    dsimp only at hy ⊢
    rw [hy]
    rfl
  invFun s := by
    refine ⟨fun x => DegreeZeroLocalization.linearEquivOfMemIff
      (𝒜 := 𝒜) (𝓜 := 𝓝) 𝓜 (fun i m => (hmem i m).symm) (s.1 x), ?_⟩
    intro x
    obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
    refine ⟨V, hxV, i, e, ⟨(r : M), (hmem e (r : M)).mpr r.2⟩, t, ht, fun y => ?_⟩
    have hy := h y
    dsimp only at hy ⊢
    rw [hy]
    rfl
  left_inv s := by
    apply section_ext
    funext x
    rfl
  right_inv s := by
    apply section_ext
    funext x
    rfl
  map_add' s t := by
    apply section_ext
    funext x
    rfl

@[simp]
theorem sectionAddEquivOfMemIff_apply {σN : Type u} [SetLike σN M] [AddSubgroupClass σN M]
    (𝓝 : ℕ → σN) [SetLike.GradedSMul 𝒜 𝓝]
    (hmem : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) (U : Opens X)
    (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) (x : U) :
    (sectionAddEquivOfMemIff 𝒜 𝓜 𝓝 hmem U s).1 x =
      DegreeZeroLocalization.linearEquivOfMemIff (𝒜 := 𝒜) (𝓜 := 𝓜) 𝓝 hmem (s.1 x) :=
  rfl

/-! ## Sections on a basic open -/

/-- The canonical additive map from the degree-zero homogeneous localization away from `f` to
sections of `M̃` on `D₊(f)`.  At a point `x`, it enlarges the denominator submonoid from the
powers of `f` to the complement of the corresponding homogeneous prime. -/
noncomputable def moduleAwayToSection (f : A) :
    DegreeZeroLocalization 𝒜 𝓜 (.powers f) →+
      (associatedSheafInType 𝒜 𝓜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) where
  toFun z := by
    refine ⟨fun x => DegreeZeroLocalization.mapOfLE
      (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr x.2) z, ?_⟩
    obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
    intro x
    refine ⟨ProjectiveSpectrum.basicOpen 𝒜 f, x.2, 𝟙 _, c.deg, c.num, c.den,
      fun y => ?_, fun y => ?_⟩
    · show (c.den : A) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl
      exact (Submonoid.powers_le.mpr y.2) c.den_mem
    exact DegreeZeroLocalization.mapOfLE_mk
      (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr y.2) c
  map_zero' := by
    apply section_ext
    funext x
    exact (DegreeZeroLocalization.mapOfLE
      (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr x.2)).map_zero
  map_add' z w := by
    apply section_ext
    funext x
    exact (DegreeZeroLocalization.mapOfLE
      (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr x.2)).map_add z w

@[simp]
theorem moduleAwayToSection_apply (f : A)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f))
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    (moduleAwayToSection 𝒜 𝓜 f z).1 x =
      DegreeZeroLocalization.mapOfLE
        (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr x.2) z :=
  rfl

@[simp]
theorem moduleAwayToSection_mk (f : A)
    (c : NumDenSameDeg 𝒜 𝓜 (.powers f)) :
    moduleAwayToSection 𝒜 𝓜 f (DegreeZeroLocalization.mk c) =
      ⟨fun x => DegreeZeroLocalization.mk
          { deg := c.deg
            num := c.num
            den := c.den
            den_mem := (Submonoid.powers_le.mpr x.2) c.den_mem },
        fun x => ⟨ProjectiveSpectrum.basicOpen 𝒜 f, x.2, 𝟙 _, c.deg, c.num, c.den,
          fun y => by
            show (c.den : A) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl
            exact (Submonoid.powers_le.mpr y.2) c.den_mem,
          fun _ => rfl⟩⟩ := by
  apply section_ext
  funext x
  exact DegreeZeroLocalization.mapOfLE_mk
    (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr x.2) c

/-- Universal characterization of the basic-open comparison: an additive map out of the
degree-zero localization is the canonical comparison as soon as it has the canonical value on
every homogeneous fraction. -/
theorem moduleAwayToSection_unique (f : A)
    (g : DegreeZeroLocalization 𝒜 𝓜 (.powers f) →+
      (associatedSheafInType 𝒜 𝓜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (hg : ∀ c : NumDenSameDeg 𝒜 𝓜 (.powers f),
      g (DegreeZeroLocalization.mk c) =
        moduleAwayToSection 𝒜 𝓜 f (DegreeZeroLocalization.mk c)) :
    g = moduleAwayToSection 𝒜 𝓜 f := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  exact hg c

/-! ### Faces and restriction

The Čech differential restricts a section from an intersection to a smaller one, and on the
algebraic side that is `DegreeZeroLocalization.faceMap`. These two results say the basic-open
comparison intertwines them, which is what lets the differential be transported. -/

/-- Enlarging the denominators past both face denominators absorbs the face map.

Once `f` and `g = f * h` are both inverted in `T`, the fraction `hⁿ m / gⁿ` produced by the face
map is the same element as `m / fⁿ`: the two differ by the unit `hⁿ`. -/
theorem mapOfLE_faceMap {f g h : A} {e : ℕ} (hh : h ∈ 𝒜 e)
    (hgh : f * h ∈ Submonoid.powers g) (hg : f * h = g)
    {T : Submonoid A} (hfT : Submonoid.powers f ≤ T) (hgT : Submonoid.powers g ≤ T)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    DegreeZeroLocalization.mapOfLE (𝒜 := 𝒜) (𝓜 := 𝓜) hgT
        (DegreeZeroLocalization.faceMap hh hgh hg z) =
      DegreeZeroLocalization.mapOfLE (𝒜 := 𝒜) (𝓜 := 𝓜) hfT z := by
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  obtain ⟨n, hn⟩ := c.den_mem
  have hn' : f ^ n = (c.den : A) := hn
  rw [DegreeZeroLocalization.faceMap_mk hh hgh hg c n hn',
    DegreeZeroLocalization.mapOfLE_mk, DegreeZeroLocalization.mapOfLE_mk,
    DegreeZeroLocalization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  have hgn : g ^ n = (c.den : A) * h ^ n := by
    rw [← hg, mul_pow, hn']
  -- Reduce the structure projections first: `rw` cannot see through `den := ⟨g ^ n, _⟩`.
  dsimp only
  rw [hgn, mul_smul]

/-- The basic-open comparison commutes with restriction along a face.

This is the sheaf-level form of `mapOfLE_faceMap`. It holds pointwise and for a cheap reason:
`moduleAwayToSection` is defined by enlarging denominators at each point, and restriction only
reindexes the point, so nothing has to be pushed through a constructed equivalence. -/
theorem moduleAwayToSection_res_faceMap {f g h : A} {e : ℕ} (hh : h ∈ 𝒜 e)
    (hgh : f * h ∈ Submonoid.powers g) (hg : f * h = g)
    (i : (op (ProjectiveSpectrum.basicOpen 𝒜 f) : (Opens X)ᵒᵖ) ⟶
      op (ProjectiveSpectrum.basicOpen 𝒜 g))
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f)) :
    (associatedSheafInType 𝒜 𝓜).1.map i (moduleAwayToSection 𝒜 𝓜 f z) =
      moduleAwayToSection 𝒜 𝓜 g (DegreeZeroLocalization.faceMap hh hgh hg z) := by
  apply section_ext
  funext x
  rw [associatedPresheaf_res_apply, moduleAwayToSection_apply, moduleAwayToSection_apply]
  exact (mapOfLE_faceMap 𝒜 𝓜 hh hgh hg (Submonoid.powers_le.mpr (i.unop x).2)
    (Submonoid.powers_le.mpr x.2) z).symm

/-- Germ evaluation of the basic-open comparison is the canonical enlargement-of-denominators
map into the homogeneous localization at the point. -/
@[simp]
theorem stalkEquiv_germ_moduleAwayToSection (f : A)
    (z : DegreeZeroLocalization 𝒜 𝓜 (.powers f))
    (x : X) (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f) :
    stalkEquiv 𝒜 𝓜 x
        ((associatedSheafInType 𝒜 𝓜).presheaf.germ
          (ProjectiveSpectrum.basicOpen 𝒜 f) x hx (moduleAwayToSection 𝒜 𝓜 f z)) =
      DegreeZeroLocalization.mapOfLE
        (𝒜 := 𝒜) (𝓜 := 𝓜) (Submonoid.powers_le.mpr hx) z := by
  rw [stalkEquiv_germ]
  rfl

/-! ## Functoriality in the graded module -/

section Functoriality

variable {N σN : Type u} [AddCommGroup N] [Module A N]
variable [SetLike σN N] [AddSubgroupClass σN N]
variable (𝓝 : ℕ → σN) [SetLike.GradedSMul 𝒜 𝓝]

/-- Apply a grading-preserving linear map pointwise to a locally fractional section. -/
noncomputable def mapSection (f : GradedLinearMap (A := A) 𝓜 𝓝)
    {U : (Opens X)ᵒᵖ} (s : (associatedSheafInType 𝒜 𝓜).1.obj U) :
    (associatedSheafInType 𝒜 𝓝).1.obj U := by
  refine ⟨fun x => GradedLinearMap.map
    (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
      (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, d, r, t, ht, e⟩ := s.2 x
  refine ⟨V, hxV, i, d,
    ⟨f.toLinearMap r, f.map_mem d r r.2⟩, t, ht, fun y => ?_⟩
  change GradedLinearMap.map
      (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
        (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) f (s.1 (i y)) = _
  exact (congrArg (GradedLinearMap.map
    (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
      (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) f) (e y)).trans
        (GradedLinearMap.map_mk
          (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
            (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) f _)

@[simp]
theorem mapSection_apply (f : GradedLinearMap (A := A) 𝓜 𝓝)
    {U : (Opens X)ᵒᵖ} (s : (associatedSheafInType 𝒜 𝓜).1.obj U) (x : U.unop) :
    (mapSection (𝓜 := 𝓜) 𝒜 𝓝 f s).1 x = GradedLinearMap.map
      (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
        (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f (s.1 x) :=
  rfl

/-- The pointwise map on sections, bundled as a linear map over the sections of `𝒪`. -/
noncomputable def mapSectionLinear (f : GradedLinearMap (A := A) 𝓜 𝓝)
    (U : (Opens X)ᵒᵖ) :
    (associatedSheafInType 𝒜 𝓜).1.obj U →ₗ[𝒪.1.obj U]
      (associatedSheafInType 𝒜 𝓝).1.obj U where
  toFun := mapSection (𝓜 := 𝓜) 𝒜 𝓝 f
  map_add' := fun s t => by
    apply section_ext
    funext x
    exact (GradedLinearMap.map
      (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
        (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f).map_add (s.1 x) (t.1 x)
  map_smul' := fun r s => by
    apply section_ext
    funext x
    exact (GradedLinearMap.map
      (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
        (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f).map_smul
          (AlgebraicGeometry.openToLocalization 𝒜 U.unop x.1 x.2 r) (s.1 x)

/-- A grading-preserving map induces a morphism of the associated presheaves of modules. -/
noncomputable def associatedMapPresheaf (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    associatedPresheaf 𝒜 𝓜 ⟶ associatedPresheaf 𝒜 𝓝 where
  app U := ModuleCat.homMk
    (AddCommGrpCat.ofHom
      { toFun := fun s => mapSection (𝓜 := 𝓜) 𝒜 𝓝 f s
        map_zero' := by
          apply section_ext
          funext x
          exact (GradedLinearMap.map
            (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
              (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f).map_zero
        map_add' := fun s t => by
          apply section_ext
          funext x
          exact (GradedLinearMap.map
            (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
              (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f).map_add (s.1 x) (t.1 x) })
    (fun r => by
      ext s
      apply section_ext
      funext x
      exact (GradedLinearMap.map
        (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
          (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f).map_smul
            (AlgebraicGeometry.openToLocalization 𝒜 U.unop x.1 x.2 r) (s.1 x) |>.symm)
  naturality := by
    intro U V i
    ext s
    apply section_ext
    funext x
    rfl

/-- A grading-preserving linear map `M → N` induces the sheaf morphism `M̃ → Ñ`. -/
noncomputable def associatedMap (f : GradedLinearMap (A := A) 𝓜 𝓝) :
    associatedSheaf 𝒜 𝓜 ⟶ associatedSheaf 𝒜 𝓝 :=
  (AlgebraicGeometry.Scheme.Modules.toPresheafOfModules
    (AlgebraicGeometry.Proj 𝒜)).preimage
      (associatedMapPresheaf (𝓜 := 𝓜) 𝒜 𝓝 f)

@[simp]
theorem associatedMap_app_apply (f : GradedLinearMap (A := A) 𝓜 𝓝)
    (U : Opens X) (s : (associatedSheafInType 𝒜 𝓜).1.obj (op U)) (x : U) :
    ((associatedMap (𝓜 := 𝓜) 𝒜 𝓝 f).app U s :
      (associatedSheafInType 𝒜 𝓝).1.obj (op U)).1 x =
      GradedLinearMap.map (𝒜 := 𝒜) (𝓜 := 𝓜) (𝓝 := 𝓝)
        (S := x.1.asHomogeneousIdeal.toIdeal.primeCompl) f (s.1 x) := by
  change ((((AlgebraicGeometry.Scheme.Modules.toPresheafOfModules
    (AlgebraicGeometry.Proj 𝒜)).map
      (associatedMap (𝓜 := 𝓜) 𝒜 𝓝 f)).app (op U)) s :
        (associatedSheafInType 𝒜 𝓝).1.obj (op U)).1 x = _
  rw [associatedMap, CategoryTheory.Functor.map_preimage]
  rfl

end Functoriality

/-! ### Isomorphisms induced by equal graded-piece memberships -/

section IdentityIso

variable {σN : Type u} [SetLike σN M] [AddSubgroupClass σN M]
variable (𝓝 : ℕ → σN) [SetLike.GradedSMul 𝒜 𝓝]

/-- The identity linear map bundled as a graded map when every source piece is contained in the
corresponding target piece. -/
def identityGradedMap
    (h : ∀ i (m : M), m ∈ 𝓜 i → m ∈ 𝓝 i) : GradedLinearMap (A := A) 𝓜 𝓝 where
  toLinearMap := LinearMap.id
  map_mem := h

set_option backward.isDefEq.respectTransparency false in
/-- Associated sheaves only depend on the membership predicates of the graded pieces.  This
packages the identity on the underlying module as an isomorphism whenever those predicates agree.
-/
noncomputable def associatedIsoOfPiecewiseIff
    (h : ∀ i (m : M), m ∈ 𝓜 i ↔ m ∈ 𝓝 i) :
    associatedSheaf 𝒜 𝓜 ≅ associatedSheaf 𝒜 𝓝 where
  hom := associatedMap (𝓜 := 𝓜) 𝒜 𝓝
    (identityGradedMap (𝓜 := 𝓜) 𝓝 fun i m hm => (h i m).mp hm)
  inv := associatedMap (𝓜 := 𝓝) 𝒜 𝓜
    (identityGradedMap (𝓜 := 𝓝) 𝓜 fun i m hm => (h i m).mpr hm)
  hom_inv_id := by
    apply AlgebraicGeometry.Scheme.Modules.hom_ext
    intro U
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
      AlgebraicGeometry.Scheme.Modules.Hom.id_app]
    ext s
    change (associatedMap (𝓜 := 𝓝) 𝒜 𝓜
      (identityGradedMap (𝓜 := 𝓝) 𝓜 fun i m hm => (h i m).mpr hm)).app U
        ((associatedMap (𝓜 := 𝓜) 𝒜 𝓝
          (identityGradedMap (𝓜 := 𝓜) 𝓝 fun i m hm => (h i m).mp hm)).app U s) = s
    apply section_ext
    funext x
    rw [associatedMap_app_apply, associatedMap_app_apply]
    obtain ⟨c, hc⟩ := DegreeZeroLocalization.mk_surjective (s.1 x)
    rw [← hc, GradedLinearMap.map_mk, GradedLinearMap.map_mk]
    apply DegreeZeroLocalization.ext
    rfl
  inv_hom_id := by
    apply AlgebraicGeometry.Scheme.Modules.hom_ext
    intro U
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
      AlgebraicGeometry.Scheme.Modules.Hom.id_app]
    ext s
    change (associatedMap (𝓜 := 𝓜) 𝒜 𝓝
      (identityGradedMap (𝓜 := 𝓜) 𝓝 fun i m hm => (h i m).mp hm)).app U
        ((associatedMap (𝓜 := 𝓝) 𝒜 𝓜
          (identityGradedMap (𝓜 := 𝓝) 𝓜 fun i m hm => (h i m).mpr hm)).app U s) = s
    apply section_ext
    funext x
    rw [associatedMap_app_apply, associatedMap_app_apply]
    obtain ⟨c, hc⟩ := DegreeZeroLocalization.mk_surjective (s.1 x)
    rw [← hc, GradedLinearMap.map_mk, GradedLinearMap.map_mk]
    apply DegreeZeroLocalization.ext
    rfl

end IdentityIso

end AlgebraicGeometry.Proj
