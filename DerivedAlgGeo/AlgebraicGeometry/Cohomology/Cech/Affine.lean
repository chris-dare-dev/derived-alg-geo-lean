/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.LocalizedRadical
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Contractible
import DerivedAlgGeo.Topology.Opens.Limits
import DerivedAlgGeo.Topology.PrimeSpectrum.BasicOpen
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Positive-degree exactness of affine Cech complexes

This file proves that the Cech complex of the sheaf associated to an `R`-module is exact in
positive degrees for a finite distinguished-open cover of `Spec R`.

The proof restricts the cover to each member `D(f_i)`. There that member is terminal, so the
Cech nerve has an extra degeneracy and its alternating coface complex is exact. The
restriction maps on sections are localizations away from `f_i`; exactness therefore descends
from the distinguished cover because its defining elements span the unit ideal.

This is a statement about the explicit Cech complex. It does not assert a comparison between
Cech cohomology and derived-functor sheaf cohomology.
-/

universe w v u

open CategoryTheory Limits

namespace IsLocalizedModule

variable {R M M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M] [Module R M₁] [Module R M₂]

private lemma relativeAway (g f : R) (a : M →ₗ[R] M₁) (b : M →ₗ[R] M₂)
    [IsLocalizedModule (.powers g) a]
    [IsLocalizedModule (.powers (g * f)) b]
    (h : M₁ →ₗ[R] M₂) (comp : h ∘ₗ a = b) :
    IsLocalizedModule (.powers f) h := by
  let factorUnits (n : ℕ) :
      IsUnit (algebraMap R (Module.End R M₂) (g ^ n)) ∧
        IsUnit (algebraMap R (Module.End R M₂) (f ^ n)) := by
    have hu := IsLocalizedModule.map_units b
      (⟨(g * f) ^ n, n, rfl⟩ : Submonoid.powers (g * f))
    change IsUnit (algebraMap R (Module.End R M₂) ((g * f) ^ n)) at hu
    rw [mul_pow, map_mul,
      (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at hu
    exact hu
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, n, rfl⟩
    exact (factorUnits n).2
  · intro y
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (.powers (g * f)) b y
    refine ⟨⟨mk' a m (⟨g ^ n, n, rfl⟩ : Submonoid.powers g),
      (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)⟩, ?_⟩
    have cancel : g ^ n • mk' a m (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) = a m :=
      mk'_cancel' a m (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    apply ((Module.End.isUnit_iff _).mp (factorUnits n).1).injective
    change g ^ n • (f ^ n • y) =
      g ^ n • h (mk' a m (⟨g ^ n, n, rfl⟩ : Submonoid.powers g))
    rw [← h.map_smul, cancel]
    rw [← LinearMap.comp_apply, comp]
    simpa [mul_pow, mul_smul] using hy
  · intro x₁ x₂ hx
    obtain ⟨⟨m₁, ⟨_, p, rfl⟩⟩, rfl⟩ := mk'_surjective (.powers g) a x₁
    obtain ⟨⟨m₂, ⟨_, q, rfl⟩⟩, rfl⟩ := mk'_surjective (.powers g) a x₂
    have cancel₁ : g ^ p • mk' a m₁ (⟨g ^ p, p, rfl⟩ : Submonoid.powers g) = a m₁ :=
      mk'_cancel' a m₁ (⟨g ^ p, p, rfl⟩ : Submonoid.powers g)
    have cancel₂ : g ^ q • mk' a m₂ (⟨g ^ q, q, rfl⟩ : Submonoid.powers g) = a m₂ :=
      mk'_cancel' a m₂ (⟨g ^ q, q, rfl⟩ : Submonoid.powers g)
    have hx' := congrArg (fun z : M₂ ↦ g ^ q • z)
      (congrArg (fun z : M₂ ↦ g ^ p • z) hx)
    have hb : b (g ^ q • m₁) = b (g ^ p • m₂) := by
      have hleft :
          g ^ q • (g ^ p • h (mk' a m₁ (⟨g ^ p, p, rfl⟩ : Submonoid.powers g))) =
            b (g ^ q • m₁) := by
        calc
          _ = g ^ q • h (g ^ p • mk' a m₁
              (⟨g ^ p, p, rfl⟩ : Submonoid.powers g)) := by rw [h.map_smul]
          _ = h (g ^ q • (g ^ p • mk' a m₁
              (⟨g ^ p, p, rfl⟩ : Submonoid.powers g))) :=
                (h.map_smul (g ^ q) _).symm
          _ = h (g ^ q • a m₁) := by rw [cancel₁]
          _ = h (a (g ^ q • m₁)) := by rw [a.map_smul]
          _ = b (g ^ q • m₁) := by rw [← LinearMap.comp_apply, comp]
      have hright :
          g ^ q • (g ^ p • h (mk' a m₂ (⟨g ^ q, q, rfl⟩ : Submonoid.powers g))) =
            b (g ^ p • m₂) := by
        calc
          _ = g ^ p • (g ^ q • h (mk' a m₂
              (⟨g ^ q, q, rfl⟩ : Submonoid.powers g))) := by
                rw [smul_smul, smul_smul, mul_comm]
          _ = g ^ p • h (g ^ q • mk' a m₂
              (⟨g ^ q, q, rfl⟩ : Submonoid.powers g)) := by rw [h.map_smul]
          _ = h (g ^ p • (g ^ q • mk' a m₂
              (⟨g ^ q, q, rfl⟩ : Submonoid.powers g))) :=
                (h.map_smul (g ^ p) _).symm
          _ = h (g ^ p • a m₂) := by rw [cancel₂]
          _ = h (a (g ^ p • m₂)) := by rw [a.map_smul]
          _ = b (g ^ p • m₂) := by rw [← LinearMap.comp_apply, comp]
      exact hleft.symm.trans (hx'.trans hright)
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      IsLocalizedModule.exists_of_eq (S := .powers (g * f)) (f := b) hb
    change (g * f) ^ k • (g ^ q • m₁) = (g * f) ^ k • (g ^ p • m₂) at hk
    refine ⟨⟨f ^ k, k, rfl⟩, ?_⟩
    change f ^ k • mk' a m₁ (⟨g ^ p, p, rfl⟩ : Submonoid.powers g) =
      f ^ k • mk' a m₂ (⟨g ^ q, q, rfl⟩ : Submonoid.powers g)
    rw [← mk'_smul, ← mk'_smul, mk'_eq_mk'_iff]
    refine ⟨⟨g ^ k, k, rfl⟩, ?_⟩
    change g ^ k • g ^ p • f ^ k • m₂ = g ^ k • g ^ q • f ^ k • m₁
    calc
      _ = g ^ k • f ^ k • g ^ p • m₂ := by
        simp only [← mul_smul]
        congr 1
        ac_rfl
      _ = g ^ k • f ^ k • g ^ q • m₁ := by
        simpa only [mul_pow, mul_smul] using hk.symm
      _ = g ^ k • g ^ q • f ^ k • m₁ := by
        simp only [← mul_smul]
        congr 1
        ac_rfl

end IsLocalizedModule

/-- Exactness descends from localizations at a family whose span contains `d` up to radical,
provided multiplication by `d` is invertible on the source and middle modules. -/
private lemma exact_of_isLocalized_span_radical
    {R M N L : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid L] [Module R L]
    (s : Set R) (d : R) (hd : d ∈ (Ideal.span s).radical)
    (hdM : IsUnit (algebraMap R (Module.End R M) d))
    (hdN : IsUnit (algebraMap R (Module.End R N) d))
    (Mₚ : ∀ _ : s, Type*) [∀ r : s, AddCommMonoid (Mₚ r)]
    [∀ r : s, Module R (Mₚ r)] (f : ∀ r : s, M →ₗ[R] Mₚ r)
    [∀ r : s, IsLocalizedModule.Away r.1 (f r)]
    (Nₚ : ∀ _ : s, Type*) [∀ r : s, AddCommMonoid (Nₚ r)]
    [∀ r : s, Module R (Nₚ r)] (g : ∀ r : s, N →ₗ[R] Nₚ r)
    [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
    (Lₚ : ∀ _ : s, Type*) [∀ r : s, AddCommMonoid (Lₚ r)]
    [∀ r : s, Module R (Lₚ r)] (h : ∀ r : s, L →ₗ[R] Lₚ r)
    [∀ r : s, IsLocalizedModule.Away r.1 (h r)]
    (F : M →ₗ[R] N) (G : N →ₗ[R] L) (hcomp : G ∘ₗ F = 0)
    (H : ∀ r : s, Function.Exact
      (IsLocalizedModule.map (.powers r.1) (f r) (g r) F)
      (IsLocalizedModule.map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · rintro x hx
    have hxloc (r : s) :
        g r x ∈ (LinearMap.range F).localized₀ (.powers r.1) (g r) := by
      rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
      rw [← (LinearMap.exact_iff.mp (H r))]
      rw [LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
      exact ⟨x, hx, 1, by simp⟩
    obtain ⟨k, hk⟩ := Submodule.exists_pow_smul_mem_of_isLocalized_radical
      s hd Nₚ g hxloc
    obtain ⟨y, hy⟩ := hk
    let y' : M := (hdM.pow k).unit.inv y
    refine ⟨y', ?_⟩
    apply ((Module.End.isUnit_iff _).mp (hdN.pow k)).injective
    rw [← map_pow, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply]
    rw [← F.map_smul]
    have hey : d ^ k • y' = y := by
      simpa only [y', ← map_pow, Module.algebraMap_end_apply] using
        Module.End.isUnit_apply_inv_apply_of_isUnit (hdM.pow k) y
    rw [hey]
    exact hy
  · rintro _ ⟨x, rfl⟩
    change G (F x) = 0
    rw [← LinearMap.comp_apply, hcomp]
    rfl

namespace TopologicalSpace.Opens

open CategoryTheory Limits

variable {X : Type*} [TopologicalSpace X]

local instance iicHasTerminal (V : Opens X) : HasTerminal (Set.Iic V) :=
  (IsTerminal.ofUniqueHom (Y := (⟨V, by exact le_refl V⟩ : Set.Iic V))
    (fun (U : Set.Iic V) ↦ homOfLE (show U ≤ (⟨V, by exact le_refl V⟩ : Set.Iic V)
      from U.2)) (fun _ _ ↦ Subsingleton.elim _ _)).hasTerminal

local instance iicHasLimitPair (V : Opens X) {U W : Set.Iic V} : HasLimit (pair U W) := by
  let P : Set.Iic V := ⟨U.1 ⊓ W.1, by
    show U.1 ⊓ W.1 ≤ V
    exact inf_le_left.trans U.2⟩
  let c : BinaryFan U W := BinaryFan.mk (P := P)
    (homOfLE (by change U.1 ⊓ W.1 ≤ U.1; exact inf_le_left))
    (homOfLE (by change U.1 ⊓ W.1 ≤ W.1; exact inf_le_right))
  exact HasLimit.mk ⟨c, BinaryFan.isLimitMk
    (fun s ↦ homOfLE (by
      change s.pt.1 ≤ U.1 ⊓ W.1
      exact le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ ↦ Subsingleton.elim _ _) (fun _ ↦ Subsingleton.elim _ _)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)⟩

local instance iicHasBinaryProducts (V : Opens X) : HasBinaryProducts (Set.Iic V) :=
  hasBinaryProducts_of_hasLimit_pair (Set.Iic V)

local instance iicHasFiniteProducts (V : Opens X) : HasFiniteProducts (Set.Iic V) :=
  hasFiniteProducts_of_has_binary_and_terminal

private lemma iic_product_val (V : Opens X) {α : Type*} [Finite α] [Nonempty α]
    (U : α → Set.Iic V) :
    (∏ᶜ U).1 = ∏ᶜ (fun a ↦ (U a).1) := by
  apply le_antisymm
  · apply leOfHom
    apply Pi.lift
    intro a
    exact homOfLE (leOfHom (Pi.π U a))
  · let a : α := Classical.choice inferInstance
    let P : Opens X := ∏ᶜ (fun a ↦ (U a).1)
    have hPV : P ≤ V := (leOfHom (Pi.π (fun a ↦ (U a).1) a)).trans (U a).2
    let P' : Set.Iic V := ⟨P, hPV⟩
    have m : P' ⟶ ∏ᶜ U := Pi.lift fun a ↦
      homOfLE (leOfHom (Pi.π (fun a ↦ (U a).1) a))
    exact leOfHom m

private lemma iic_basicOpen_product {R : CommRingCat} {α : Type*}
    [Fintype α] [Nonempty α] (g : α → R) (d : R) :
    (∏ᶜ fun a ↦ (⟨_root_.PrimeSpectrum.basicOpen (g a) ⊓
      _root_.PrimeSpectrum.basicOpen d,
        (inf_le_right : _root_.PrimeSpectrum.basicOpen (g a) ⊓
          _root_.PrimeSpectrum.basicOpen d ≤ _root_.PrimeSpectrum.basicOpen d)⟩ :
        Set.Iic (_root_.PrimeSpectrum.basicOpen d))).1 =
      _root_.PrimeSpectrum.basicOpen ((∏ a, g a) * d) := by
  rw [iic_product_val]
  simp_rw [_root_.PrimeSpectrum.basicOpen_mul]
  rw [_root_.PrimeSpectrum.basicOpen_prod_eq_pi]
  apply le_antisymm
  · apply le_inf
    · apply leOfHom
      apply Pi.lift
      intro a
      exact homOfLE ((leOfHom (Pi.π (fun a ↦
        _root_.PrimeSpectrum.basicOpen (g a) ⊓
          _root_.PrimeSpectrum.basicOpen d) a)).trans inf_le_left)
    · let a : α := Classical.choice inferInstance
      exact (leOfHom (Pi.π (fun a ↦
        _root_.PrimeSpectrum.basicOpen (g a) ⊓
          _root_.PrimeSpectrum.basicOpen d) a)).trans inf_le_right
  · apply leOfHom
    apply Pi.lift
    intro a
    apply homOfLE
    exact le_inf (inf_le_left.trans (leOfHom (Pi.π (fun a ↦
      _root_.PrimeSpectrum.basicOpen (g a)) a))) inf_le_right

end TopologicalSpace.Opens

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type*} [Category C] {D : Type*} [Category D]

private def mapFunctor (F : C ⥤ D) : FormalCoproduct C ⥤ FormalCoproduct D where
  obj X := ⟨X.I, fun i ↦ F.obj (X.obj i)⟩
  map f := ⟨f.f, fun i ↦ F.map (f.φ i)⟩
  map_id X := by
    rw [hom_ext_iff]
    refine ⟨rfl, fun i ↦ ?_⟩
    dsimp
    rw [Category.comp_id]
    exact F.map_id (X.obj i)
  map_comp f g := by
    rw [hom_ext_iff]
    refine ⟨rfl, fun i ↦ ?_⟩
    dsimp
    rw [Category.comp_id]
    exact F.map_comp (f.φ i) (g.φ (f.f i))

end CategoryTheory.Limits.FormalCoproduct

namespace AlgebraicGeometry

open CategoryTheory Limits Opposite Simplicial TopologicalSpace
open _root_.PrimeSpectrum

private def iicIncl {X : Type*} [TopologicalSpace X] (V : Opens X) :
    Set.Iic V ⥤ Opens X where
  obj U := U.1
  map f := homOfLE (leOfHom f)

private noncomputable def tildeCechComplex {R : CommRingCat.{u}} {ι : Type u}
    [Fintype ι] (f : ι → R) (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat R) ℕ :=
  (CategoryTheory.cechComplexFunctor fun i ↦
    _root_.PrimeSpectrum.basicOpen (f i)).obj
      (modulesSpecToSheaf.obj (tilde M)).presheaf

private lemma tildeCechComplex_isUnit_of_le_basicOpen
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (d : R)
    (hfd : ∀ i, _root_.PrimeSpectrum.basicOpen (f i) ≤
      _root_.PrimeSpectrum.basicOpen d)
    (M : ModuleCat.{u} R) (n : ℕ) :
    IsUnit (algebraMap R (Module.End R ((tildeCechComplex f M).X n)) d) := by
  let Q := Fin (n + 1) → ι
  let A : Q → ModuleCat R := fun q ↦
    (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
      (op (∏ᶜ fun a : Fin (n + 1) ↦
        _root_.PrimeSpectrum.basicOpen (f (q a))))
  change IsUnit (algebraMap R (Module.End R (↑(∏ᶜ A : ModuleCat R))) d)
  have hdA (q : Q) :
      IsUnit (algebraMap R (Module.End R (A q)) d) := by
    apply (tilde M).isUnit_algebraMap_end_of_le_basicOpen
    exact (leOfHom (Limits.Pi.π (fun a : Fin (n + 1) ↦
      _root_.PrimeSpectrum.basicOpen (f (q a))) 0)).trans (hfd (q 0))
  have hdPi : IsUnit (algebraMap R (Module.End R (∀ q, A q)) d) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      funext q
      exact ((Module.End.isUnit_iff _).mp (hdA q)).injective (congrFun hxy q)
    · intro y
      choose x hx using fun q ↦ ((Module.End.isUnit_iff _).mp (hdA q)).surjective (y q)
      exact ⟨x, funext fun q ↦ hx q⟩
  let e := (ModuleCat.piIsoPi A).toLinearEquiv
  rw [Module.End.isUnit_iff] at hdPi ⊢
  constructor
  · intro x y hxy
    apply e.injective
    apply hdPi.injective
    simpa only [Module.algebraMap_end_apply, map_smul] using congrArg e hxy
  · intro y
    obtain ⟨z, hz⟩ := hdPi.surjective (e y)
    refine ⟨e.symm z, ?_⟩
    apply e.injective
    simpa only [Module.algebraMap_end_apply, map_smul, e.apply_symm_apply] using hz

private structure AffineCechLocalizationData {R : CommRingCat.{u}} {ι : Type u}
    [Fintype ι] (f : ι → R) (j : ι) (M : ModuleCat.{u} R) where
  Kloc : CochainComplex (ModuleCat R) ℕ
  comparison : tildeCechComplex f M ⟶ Kloc
  exactAt_succ (n : ℕ) : Kloc.ExactAt (n + 1)
  isLocalized (n : ℕ) :
    IsLocalizedModule (.powers (f j)) (comparison.f n).hom

private instance AffineCechLocalizationData.instIsLocalized
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    {f : ι → R} {j : ι} {M : ModuleCat.{u} R}
    (D : AffineCechLocalizationData f j M) (n : ℕ) :
    IsLocalizedModule (.powers (f j)) (D.comparison.f n).hom :=
  D.isLocalized n

private noncomputable def affineCechLocalizationData
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (j : ι) (M : ModuleCat.{u} R) :
    AffineCechLocalizationData f j M := by
  let U : ι → Opens (PrimeSpectrum R) := fun i ↦ _root_.PrimeSpectrum.basicOpen (f i)
  let D : Opens (PrimeSpectrum R) := _root_.PrimeSpectrum.basicOpen (f j)
  let Uj : ι → Set.Iic D := fun i ↦ ⟨U i ⊓ D, by
    show U i ⊓ D ≤ D
    exact inf_le_right⟩
  letI : HasTerminal (Set.Iic D) := TopologicalSpace.Opens.iicHasTerminal D
  letI : HasBinaryProducts (Set.Iic D) := TopologicalSpace.Opens.iicHasBinaryProducts D
  letI : HasFiniteProducts (Set.Iic D) := TopologicalSpace.Opens.iicHasFiniteProducts D
  let T : Set.Iic D := ⟨D, by exact le_refl D⟩
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun V ↦ homOfLE V.2) (fun _ _ ↦ Subsingleton.elim _ _)
  let d : T ⟶ Uj j := homOfLE (by
    change D ≤ D ⊓ D
    exact le_inf le_rfl le_rfl)
  let V := FormalCoproduct.mk ι U
  let Vj := FormalCoproduct.mk ι Uj
  let Xj := Vj.cech.augmentOfIsTerminal (FormalCoproduct.isTerminalIncl T hT)
  let edj : Xj.ExtraDegeneracy := Vj.extraDegeneracyCech hT d
  let F := iicIncl D
  let MF := FormalCoproduct.mapFunctor F
  let Xloc := ((SimplicialObject.Augmented.whiskering _ _).obj MF).obj Xj
  let edloc : Xloc.ExtraDegeneracy := edj.map MF
  let Z := SimplicialObject.Augmented.drop.obj Xloc
  let zToV : Z ⟶ V.cech :=
    { app := fun n ↦
        { f := id
          φ := fun x ↦ Pi.lift fun a ↦
            F.map (Pi.π (Uj ∘ x) a) ≫ homOfLE inf_le_left }
      naturality := by
        intro n m θ
        apply FormalCoproduct.hom_ext
        · intro x
          subsingleton
        · rfl }
  let P := (modulesSpecToSheaf.obj (tilde M)).presheaf
  let G := (FormalCoproduct.evalOp (Opens (PrimeSpectrum R)) (ModuleCat R)).obj P
  let Y := V.cech.rightOp ⋙ G
  let Yloc := Z.rightOp ⋙ G
  let α : Y ⟶ Yloc := CategoryTheory.Functor.whiskerRight zToV.rightOp G
  let K := (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj Y
  let Kloc := (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj Yloc
  let κ : K ⟶ Kloc := (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map α
  change tildeCechComplex f M ⟶ Kloc at κ
  have hκ (m : ℕ) : IsLocalizedModule (.powers (f j)) (κ.f m).hom := by
    change IsLocalizedModule (.powers (f j))
      (G.map (zToV.app (op ⦋m⦌)).op).hom
    let I := Fin (m + 1) → ι
    let A : I → ModuleCat R := fun x ↦
      P.obj (op ((V.cech.obj (op ⦋m⦌)).obj x))
    let B : I → ModuleCat R := fun x ↦
      P.obj (op ((Z.obj (op ⦋m⦌)).obj x))
    let q (x : I) : A x ⟶ B x :=
      P.map ((zToV.app (op ⦋m⦌)).φ x).op
    have hq (x : I) : IsLocalizedModule (.powers (f j)) (q x).hom := by
      let g : R := ∏ a, f (x a)
      let O := (V.cech.obj (op ⦋m⦌)).obj x
      let L := (Z.obj (op ⦋m⦌)).obj x
      let r : L ⟶ O := (zToV.app (op ⦋m⦌)).φ x
      have eO : O = _root_.PrimeSpectrum.basicOpen g := by
        change ∏ᶜ (U ∘ x) = _
        simpa [U, g, Function.comp_def] using
          (_root_.PrimeSpectrum.basicOpen_prod_eq_pi (fun a ↦ f (x a))).symm
      have eL : L = _root_.PrimeSpectrum.basicOpen (g * f j) := by
        change (∏ᶜ (Uj ∘ x)).1 = _
        simpa [Uj, U, D, g, Function.comp_def] using
          (TopologicalSpace.Opens.iic_basicOpen_product
            (fun a ↦ f (x a)) (f j))
      haveI : IsLocalizedModule (.powers g) (tilde.toOpen M O).hom := by
        rw [eO]
        infer_instance
      haveI : IsLocalizedModule (.powers (g * f j)) (tilde.toOpen M L).hom := by
        rw [eL]
        infer_instance
      apply IsLocalizedModule.relativeAway g (f j)
        (tilde.toOpen M O).hom (tilde.toOpen M L).hom (q x).hom
      exact congrArg ModuleCat.Hom.hom (tilde.toOpen_res M O L r)
    change IsLocalizedModule (.powers (f j))
      (Pi.lift (fun x ↦ Pi.π A x ≫ q x)).hom
    let eA := (ModuleCat.piIsoPi A).toLinearEquiv
    let eB := (ModuleCat.piIsoPi B).toLinearEquiv
    let qπ : (∀ x, A x) →ₗ[R] (∀ x, B x) :=
      LinearMap.pi fun x ↦ (q x).hom ∘ₗ LinearMap.proj x
    letI (x : I) : IsLocalizedModule (.powers (f j)) (q x).hom := hq x
    have hqπ : IsLocalizedModule (.powers (f j)) qπ := by infer_instance
    have hpre : IsLocalizedModule (.powers (f j)) (qπ ∘ₗ eA.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right (.powers (f j)) qπ eA
    have hconj : IsLocalizedModule (.powers (f j))
        (eB.symm.toLinearMap ∘ₗ qπ ∘ₗ eA.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv (.powers (f j))
        (qπ ∘ₗ eA.toLinearMap) eB.symm
    convert hconj using 1
    ext s
    apply eB.injective
    funext x
    simp [eA, eB, qπ]
    change (ConcreteCategory.hom (ModuleCat.piIsoPi B).hom)
        ((ConcreteCategory.hom (Pi.lift fun x ↦ Pi.π A x ≫ q x)) s) x =
      (ConcreteCategory.hom (q x))
        ((ConcreteCategory.hom (ModuleCat.piIsoPi A).hom) s x)
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply,
      ModuleCat.piIsoPi_hom_ker_subtype_apply]
    change ((Pi.lift (fun x ↦ Pi.π A x ≫ q x) ≫ Pi.π B x).hom) s =
      ((Pi.π A x ≫ q x).hom) s
    rw [Pi.lift_π]
  have hloc (n : ℕ) : Kloc.ExactAt (n + 1) := by
    apply AlgebraicTopology.exactAt_succ_of_extraDegeneracy_map edloc G
      (Y := Yloc) (n := n)
    exact Iso.refl _
  exact
    { Kloc := Kloc
      comparison := κ
      exactAt_succ := hloc
      isLocalized := hκ }

private lemma AffineCechLocalizationData.localizedExact
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    {f : ι → R} {j : ι} {M : ModuleCat.{u} R}
    (D : AffineCechLocalizationData f j M) (n : ℕ) :
    Function.Exact
      (IsLocalizedModule.map (.powers (f j)) (D.comparison.f n).hom
        (D.comparison.f (n + 1)).hom
        ((tildeCechComplex f M).d n (n + 1)).hom)
      (IsLocalizedModule.map (.powers (f j)) (D.comparison.f (n + 1)).hom
        (D.comparison.f (n + 2)).hom
        ((tildeCechComplex f M).d (n + 1) (n + 2)).hom) := by
  letI (m : ℕ) : IsLocalizedModule (.powers (f j))
      (D.comparison.f m).hom := D.isLocalized m
  have hmap (m : ℕ) :
      IsLocalizedModule.map (.powers (f j)) (D.comparison.f m).hom
          (D.comparison.f (m + 1)).hom
          ((tildeCechComplex f M).d m (m + 1)).hom =
        (D.Kloc.d m (m + 1)).hom := by
    apply IsLocalizedModule.ext (.powers (f j)) (D.comparison.f m).hom
      (IsLocalizedModule.map_units (D.comparison.f (m + 1)).hom)
    rw [IsLocalizedModule.map_comp]
    exact congrArg ModuleCat.Hom.hom
      (D.comparison.comm m (m + 1)).symm
  have hlocfun : Function.Exact
      (D.Kloc.d n (n + 1)).hom (D.Kloc.d (n + 1) (n + 2)).hom := by
    apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (D.Kloc.sc' n (n + 1) (n + 2))).mp
    apply (D.Kloc.exactAt_iff' n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (by
        simp [CochainComplex.next, Nat.add_assoc])).mp
    exact D.exactAt_succ n
  rw [hmap n, hmap (n + 1)]
  simpa [Nat.add_assoc] using hlocfun

/-- The Cech complex of a module sheaf on a finite distinguished-open cover of `Spec R` is
exact in every positive degree.

The hypothesis says that the elements defining the cover span the unit ideal. -/
theorem tilde_cechComplex_exactAt_succ
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor fun i ↦
      _root_.PrimeSpectrum.basicOpen (f i)).obj
        (modulesSpecToSheaf.obj (tilde M)).presheaf).ExactAt (n + 1) := by
  change (tildeCechComplex f M).ExactAt (n + 1)
  let K := tildeCechComplex f M
  apply (K.exactAt_iff' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (by
      simp [CochainComplex.next, Nat.add_assoc])).mpr
  apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (K.sc' n (n + 1) (n + 2))).mpr
  let s : Set R := Set.range f
  let index (r : s) : ι := Classical.choose r.property
  have hindex (r : s) : f (index r) = r.1 := Classical.choose_spec r.property
  let data (r : s) := affineCechLocalizationData f (index r) M
  let Mloc (r : s) : Type u := (data r).Kloc.X n
  let Nloc (r : s) : Type u := (data r).Kloc.X (n + 1)
  let Lloc (r : s) : Type u := (data r).Kloc.X (n + 2)
  let localizeM (r : s) : K.X n →ₗ[R] Mloc r :=
    ((data r).comparison.f n).hom
  let localizeN (r : s) : K.X (n + 1) →ₗ[R] Nloc r :=
    ((data r).comparison.f (n + 1)).hom
  let localizeL (r : s) : K.X (n + 2) →ₗ[R] Lloc r :=
    ((data r).comparison.f (n + 2)).hom
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeM r) := by
    rw [← hindex r]
    exact (data r).isLocalized n
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeN r) := by
    rw [← hindex r]
    exact (data r).isLocalized (n + 1)
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeL r) := by
    rw [← hindex r]
    exact (data r).isLocalized (n + 2)
  apply exact_of_isLocalized_span s hf Mloc localizeM Nloc localizeN Lloc localizeL
  intro r
  dsimp only [Mloc, Nloc, Lloc, localizeM, localizeN, localizeL, K]
  rw [LinearMap.exact_iff]
  change
    (IsLocalizedModule.map (.powers r.1) ((data r).comparison.f (n + 1)).hom
      ((data r).comparison.f (n + 2)).hom
      ((tildeCechComplex f M).d (n + 1) (n + 2)).hom).ker =
    (IsLocalizedModule.map (.powers r.1) ((data r).comparison.f n).hom
      ((data r).comparison.f (n + 1)).hom
      ((tildeCechComplex f M).d n (n + 1)).hom).range
  have h := (data r).localizedExact n
  rw [LinearMap.exact_iff] at h
  simpa only [← hindex r] using h

/-- The Cech complex of a module sheaf is exact in positive degrees on a finite
distinguished-open cover of an arbitrary distinguished open `D(d)`. -/
theorem tilde_cechComplex_exactAt_succ_of_eq_iSup
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (d : R)
    (hcover : _root_.PrimeSpectrum.basicOpen d =
      ⨆ i, _root_.PrimeSpectrum.basicOpen (f i))
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor fun i ↦
      _root_.PrimeSpectrum.basicOpen (f i)).obj
        (modulesSpecToSheaf.obj (tilde M)).presheaf).ExactAt (n + 1) := by
  change (tildeCechComplex f M).ExactAt (n + 1)
  let K := tildeCechComplex f M
  apply (K.exactAt_iff' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (by
      simp [CochainComplex.next, Nat.add_assoc])).mpr
  apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (K.sc' n (n + 1) (n + 2))).mpr
  let s : Set R := Set.range f
  have hfd (i : ι) : _root_.PrimeSpectrum.basicOpen (f i) ≤
      _root_.PrimeSpectrum.basicOpen d := by
    rw [hcover]
    exact le_iSup (fun j ↦ _root_.PrimeSpectrum.basicOpen (f j)) i
  have hd : d ∈ (Ideal.span s).radical := by
    have hz : _root_.PrimeSpectrum.zeroLocus s ⊆
        _root_.PrimeSpectrum.zeroLocus {d} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← _root_.PrimeSpectrum.zeroLocus_iUnion, s] using hcover.le
    rw [← _root_.PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      _root_.PrimeSpectrum.zeroLocus_span,
      _root_.PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx ↦ by simpa using hz hx
  let index (r : s) : ι := Classical.choose r.property
  have hindex (r : s) : f (index r) = r.1 := Classical.choose_spec r.property
  let data (r : s) := affineCechLocalizationData f (index r) M
  let Mloc (r : s) : Type u := (data r).Kloc.X n
  let Nloc (r : s) : Type u := (data r).Kloc.X (n + 1)
  let Lloc (r : s) : Type u := (data r).Kloc.X (n + 2)
  let localizeM (r : s) : K.X n →ₗ[R] Mloc r :=
    ((data r).comparison.f n).hom
  let localizeN (r : s) : K.X (n + 1) →ₗ[R] Nloc r :=
    ((data r).comparison.f (n + 1)).hom
  let localizeL (r : s) : K.X (n + 2) →ₗ[R] Lloc r :=
    ((data r).comparison.f (n + 2)).hom
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeM r) := by
    rw [← hindex r]
    exact (data r).isLocalized n
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeN r) := by
    rw [← hindex r]
    exact (data r).isLocalized (n + 1)
  letI (r : s) : IsLocalizedModule (.powers r.1) (localizeL r) := by
    rw [← hindex r]
    exact (data r).isLocalized (n + 2)
  have hcomp :
      (K.d (n + 1) (n + 2)).hom ∘ₗ (K.d n (n + 1)).hom = 0 := by
    change (K.d n (n + 1) ≫ K.d (n + 1) (n + 2)).hom = 0
    rw [K.d_comp_d]
    rfl
  apply exact_of_isLocalized_span_radical s d hd
    (tildeCechComplex_isUnit_of_le_basicOpen f d hfd M n)
    (tildeCechComplex_isUnit_of_le_basicOpen f d hfd M (n + 1))
    Mloc localizeM Nloc localizeN Lloc localizeL
    (K.d n (n + 1)).hom (K.d (n + 1) (n + 2)).hom hcomp
  intro r
  dsimp only [Mloc, Nloc, Lloc, localizeM, localizeN, localizeL, K]
  rw [LinearMap.exact_iff]
  change
    (IsLocalizedModule.map (.powers r.1) ((data r).comparison.f (n + 1)).hom
      ((data r).comparison.f (n + 2)).hom
      ((tildeCechComplex f M).d (n + 1) (n + 2)).hom).ker =
    (IsLocalizedModule.map (.powers r.1) ((data r).comparison.f n).hom
      ((data r).comparison.f (n + 1)).hom
      ((tildeCechComplex f M).d n (n + 1)).hom).range
  have h := (data r).localizedExact n
  rw [LinearMap.exact_iff] at h
  simpa only [← hindex r] using h

/-- Positive-degree form of `tilde_cechComplex_exactAt_succ`. -/
theorem tilde_cechComplex_exactAt_of_pos
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k) :
    ((CategoryTheory.cechComplexFunctor fun i ↦
      _root_.PrimeSpectrum.basicOpen (f i)).obj
        (modulesSpecToSheaf.obj (tilde M)).presheaf).ExactAt k := by
  cases k with
  | zero => exact (Nat.not_lt_zero 0 hk).elim
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        tilde_cechComplex_exactAt_succ f hf M n

end AlgebraicGeometry
