/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Grading
import DerivedAlgGeo.AlgebraicGeometry.Modules.Ample
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Functor
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.FracSection
import DerivedAlgGeo.Topology.Sheaves.PushforwardStalks

/-!
# Hyperplane sections of `Proj`

Let `x ∈ 𝒜₁` and let `ψ : 𝒜 →+*ᵍ ℬ` be a surjective graded ring map with kernel `(x)`, so that
`i = Proj.map ψ : Proj ℬ ⟶ Proj 𝒜` is the closed immersion of the hyperplane `V₊(x)`
(`isClosedImmersion_map`). A module sheaf `G` on `Proj 𝒜` on which multiplication by `x`,
`twistBy 𝒜 1 hx G : G ⟶ G ⊗ 𝒪(1)`, vanishes is pushed forward from `V₊(x)`: the unit
`G ⟶ i_* i^* G` is an isomorphism (Stacks 01QY for this ideal sheaf).

For polynomial rings this gives the coordinate hyperplane `Proj R[ι] ⟶ Proj R[Option ι]`,
`X none ↦ 0`.

## Main definitions

* `AlgebraicGeometry.Proj.twistingSheafMul`: multiplication by a homogeneous `c` of degree `j`,
  as a map `𝒪(d) ⟶ 𝒪(d + j)`.
* `AlgebraicGeometry.Proj.coordinateHyperplaneHom`: the graded surjection `R[Option ι] → R[ι]`
  sending `X none` to `0`.
* `AlgebraicGeometry.Proj.coordinateHyperplane`: `Proj` of it, the coordinate hyperplane.

## Main results

* `AlgebraicGeometry.Proj.twistBy_mul`: multiplying by `x c` is multiplying by `x` and then by `c`.
* `AlgebraicGeometry.Proj.isLocalBasis_sectionOfMem`: a homogeneous `s` of degree `k` freely
  generates `𝒪(k)` over `D₊(s)`.
* `AlgebraicGeometry.Proj.fracSection_smul_eq_zero`: if `twistBy x` vanishes on `G`, every
  fraction `x c / s` of degree zero kills the sections of `G` over opens inside `D₊(s)`.
* `AlgebraicGeometry.Proj.smul_eq_zero_of_stalkMap_eq_zero`: the kernel of the stalk map of the
  hyperplane section kills the stalks of such a `G`.
* `AlgebraicGeometry.Proj.isIso_unit_of_twistBy_eq_zero`: the unit `G ⟶ i_* i^* G` is an
  isomorphism.
* `AlgebraicGeometry.Proj.ker_coordinateHyperplaneHom`: the kernel of the coordinate map is
  `(X none)`.

## Implementation notes

### The unit is checked on stalks

The module stalk functors jointly reflect isomorphisms. Off `V₊(x)` both stalks vanish: the stalk
of `i_*` by `DerivedAlgGeo.Topology.subsingleton_stalk_pushforward`, and that of `G` because
`x / x = 1` kills it. At `p = i q` the stalk of `i_*` is the stalk at `q`
(`stalkPushforward_iso_of_isInducing`), the stalk of `i^* G` is `𝒪_{Z,q} ⊗ G_p`
(`Scheme.Modules.pullbackStalkIso`), and the unit becomes `m ↦ 1 ⊗ m`. That map is bijective as
soon as the surjection `𝒪_{X,p} → 𝒪_{Z,q}` has a kernel killing `G_p`.

### Why the kernel kills the stalk

Through `Proj.stalkIso` the stalk map is `HomogeneousLocalization.localRingHom ψ`, whose kernel
consists of fractions `x c / s` with `s ∉ p`. Multiplying a section `t` of `G` by `x c` is
`twistBy (x c) t = (x c / s) • twistBy s t` (`twistBy_app_eq_smul'`), and `twistBy (x c)` factors
through `twistBy x = 0` (`twistBy_mul`). Since `s` freely generates `𝒪(k)` near `p`
(`isLocalBasis_sectionOfMem`), `twistBy s` is injective on stalks
(`Scheme.Modules.fixedLeftTensorStalkIso`), so `(x c / s) • t = 0`.

Nothing here needs `G` quasi-coherent, nor `𝒜` generated in degree one: the cancellation uses
the chart `D₊(s)` of the denominator, of whatever degree.

### Stacks 01N1

The comparison `θ : (Proj.map ψ)^* 𝒪(d) ≅ 𝒪(d)` of Stacks 01N1 is
`mapPullbackTwistingSheafIso` in `ProjectiveSpectrum/Modules/MapPullback.lean`, stated for every
`ψ` with `ℬ₊ ≤ 𝒜₊.map ψ` once `𝒜` is generated in degree one; for a surjection it applies with
`irrelevant_le_map_of_surjective`.

## References

* [Stacks, Lemma 27.11.3 (Tag 01N0)](https://stacks.math.columbia.edu/tag/01N0).
* [Stacks, Lemma 29.4.1 (Tag 01QY)](https://stacks.math.columbia.edu/tag/01QY).
* EGA II 2.9.2.

## Tags

Proj, hyperplane section, closed immersion, twisting sheaf, pushforward
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace GradedModule HomogeneousIdeal
open scoped ChangeOfRings TensorProduct

/-- If a surjective ring map `φ : R → S` has a kernel killing `M`, then `m ↦ 1 ⊗ m` identifies
`M` with `S ⊗[R] M`. -/
private theorem bijective_extendRestrictScalarsAdj_unit_app {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat.{u} R)
    (hM : ∀ r, φ r = 0 → ∀ m : M, r • m = 0) :
    Function.Bijective ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) := by
  let : Module R S := Module.compHom S φ
  have key (r r' : R) (h : φ r = φ r') (m : M) : r • m = r' • m := by
    rw [← sub_eq_zero, ← sub_smul]
    exact hM _ (by rw [map_sub, h, sub_self]) m
  obtain ⟨pre, hpre⟩ := hφ.hasRightInverse
  let B : S →ₗ[R] M →ₗ[R] M :=
    { toFun := fun s ↦ pre s • LinearMap.id
      map_add' := fun s s' ↦ by
        ext m
        simp only [LinearMap.smul_apply, LinearMap.id_apply, ← add_smul]
        exact key _ _ (by rw [map_add, hpre, hpre, hpre]) m
      map_smul' := fun r s ↦ by
        ext m
        simp only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply, smul_smul]
        exact key _ _ (by rw [map_mul, hpre, hpre]; rfl) m }
  let L := TensorProduct.lift B
  have hL (m : M) : L ((1 : S) ⊗ₜ m) = m := by
    simp only [L, TensorProduct.lift.tmul, B, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, LinearMap.id_apply]
    rw [key (pre 1) 1 (by rw [hpre, map_one]), one_smul]
  constructor
  · intro m m' h
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
      ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at h
    rw [← hL m, ← hL m']
    exact congrArg L h
  · intro z
    change TensorProduct R S M at z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      refine ⟨pre s • m, ?_⟩
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      change (1 : S) ⊗ₜ[R] (pre s • m) = s ⊗ₜ[R] m
      rw [← TensorProduct.smul_tmul]
      congr 1
      change φ (pre s) * 1 = s
      rw [mul_one, hpre]
    | add z z' hz hz' =>
      obtain ⟨m, hm⟩ := hz
      obtain ⟨m', hm'⟩ := hz'
      exact ⟨m + m', (map_add _ m m').trans (by rw [hm, hm']; rfl)⟩

/-- A pure tensor against a free generator vanishes only when its other factor does. -/
private theorem eq_zero_of_tmul_eq_zero {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {e : N}
    (he : Function.Bijective (LinearMap.toSpanSingleton R N e)) {m : M}
    (h : m ⊗ₜ[R] e = 0) : m = 0 := by
  let E := LinearEquiv.ofBijective _ he
  have hE : E.symm e = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [E]
  have key : TensorProduct.rid R M (LinearMap.lTensor M E.symm.toLinearMap (m ⊗ₜ e)) = m := by
    rw [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, hE, TensorProduct.rid_tmul, one_smul]
  rw [← key, h, map_zero, map_zero]

namespace AlgebraicGeometry.Proj

section Twist

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

/-! ### Multiplication between twisting sheaves -/

/-- Multiplication by a homogeneous `c` of degree `j`, as a graded map `A(d) → A(e)` for
`e = d + j`. -/
def mulGradedMap {c : A} {j : ℕ} (hc : c ∈ 𝒜 j) {d e : ℤ} (he : e = d + j) :
    GradedLinearMap (A := A) (intShift 𝒜 d) (intShift 𝒜 e) where
  toLinearMap := LinearMap.mulRight A c
  map_mem i a ha := by
    rcases (mem_intShiftPiece 𝒜).mp ha with rfl | ⟨k, hk, ha⟩
    · exact (mem_intShiftPiece 𝒜).mpr (Or.inl (zero_mul c))
    · refine (mem_intShiftPiece 𝒜).mpr (Or.inr ⟨k + j, by push_cast; omega, ?_⟩)
      exact SetLike.mul_mem_graded ha hc

/-- Multiplication by a homogeneous `c` of degree `j`, as a map `𝒪(d) ⟶ 𝒪(e)` for
`e = d + j`. -/
def twistingSheafMul {c : A} {j : ℕ} (hc : c ∈ 𝒜 j) {d e : ℤ} (he : e = d + j) :
    twistingSheaf 𝒜 d ⟶ twistingSheaf 𝒜 e :=
  associatedMap (𝓜 := intShift 𝒜 d) 𝒜 (intShift 𝒜 e) (mulGradedMap 𝒜 hc he)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Multiplying by `x` and then by `c` is multiplying by `x c`, as maps out of the structure
sheaf: both send `1` to `x c / 1`. -/
theorem unitToTwist_comp_twistingSheafMul {x c : A} {i j : ℕ} (hx : x ∈ 𝒜 i) (hc : c ∈ 𝒜 j) :
    unitToTwist 𝒜 𝒜 i hx ≫ twistingSheafMul 𝒜 hc (by push_cast; ring) =
      unitToTwist 𝒜 𝒜 (i + j) (SetLike.mul_mem_graded hx hc) := by
  rw [unitToTwist, unitToTwist, SheafOfModules.unitHomEquiv_symm_comp]
  refine congrArg (SheafOfModules.unitHomEquiv _).symm ?_
  refine Subtype.ext (funext fun U ↦ ?_)
  apply section_ext
  funext y
  change ((twistingSheafMul 𝒜 hc _).app U.unop (sectionOfMem 𝒜 𝒜 U.unop i hx) :
    (associatedSheafInType 𝒜 (intShift 𝒜 ((i + j : ℕ) : ℤ))).1.obj U).1 y =
      (sectionOfMem 𝒜 𝒜 U.unop (i + j) (SetLike.mul_mem_graded hx hc)).1 y
  refine (associatedMap_app_apply (𝓜 := intShift 𝒜 (i : ℤ)) 𝒜 (intShift 𝒜 ((i + j : ℕ) : ℤ))
    (mulGradedMap 𝒜 hc _) U.unop (sectionOfMem 𝒜 𝒜 U.unop i hx) y).trans ?_
  rw [sectionOfMem_apply, sectionOfMem_apply, GradedLinearMap.map_mk]
  rfl

/-- **Multiplying by `x c` is multiplying by `x` and then by `c`**, on an arbitrary module sheaf.
So `twistBy (x c)` vanishes wherever `twistBy x` does. -/
theorem twistBy_mul {x c : A} {i j : ℕ} (hx : x ∈ 𝒜 i) (hc : c ∈ 𝒜 j) (F : (Proj 𝒜).Modules) :
    twistBy 𝒜 (i + j) (SetLike.mul_mem_graded hx hc) F =
      twistBy 𝒜 i hx F ≫
        Scheme.Modules.tensorHom (𝟙 F) (twistingSheafMul 𝒜 hc (by push_cast; ring)) := by
  rw [twistBy, twistBy, Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  refine (congrArg (Scheme.Modules.tensorHom (𝟙 F))
    (unitToTwist_comp_twistingSheafMul 𝒜 hx hc).symm).trans ?_
  exact Scheme.Modules.tensorHom_id_comp F _ _

/-! ### A homogeneous element freely generates the twist on its chart -/

section Fiber

variable {S : Submonoid A} {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (hsS : s ∈ S)

/-- The degree-zero fraction `s / 1` in the twist `A(k)`, for `s` of degree `k`. -/
private def twistFiberGenerator : DegreeZeroLocalization 𝒜 (intShift 𝒜 (k : ℤ)) S :=
  DegreeZeroLocalization.mk
    { deg := 0
      num := ⟨s, (mem_intShift_ofNat_iff 𝒜 k 0 s).mpr (by simpa [natShift] using hs)⟩
      den := ⟨1, SetLike.one_mem_graded 𝒜⟩
      den_mem := S.one_mem }

include hsS in
private theorem twistFiberGenerator_smul_injective :
    Function.Injective (LinearMap.toSpanSingleton (HomogeneousLocalization 𝒜 S) _
      (twistFiberGenerator 𝒜 (S := S) hs)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨c, rfl⟩ := a.mk_surjective
  rw [LinearMap.toSpanSingleton_apply, twistFiberGenerator, DegreeZeroLocalization.mk_smul_mk]
    at ha
  have h := congrArg Subtype.val ha
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding,
    DegreeZeroLocalization.coe_zero] at h
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  refine ⟨u * ⟨s, hsS⟩, ?_⟩
  simp only [smul_zero, Submonoid.smul_def, one_smul, smul_eq_mul] at hu
  simpa [mul_comm, mul_left_comm, mul_assoc] using hu

include hsS in
private theorem twistFiberGenerator_smul_surjective :
    Function.Surjective (LinearMap.toSpanSingleton (HomogeneousLocalization 𝒜 S) _
      (twistFiberGenerator 𝒜 (S := S) hs)) := by
  intro w
  obtain ⟨⟨i, ⟨m, hm⟩, ⟨t, ht⟩, htS⟩, rfl⟩ := DegreeZeroLocalization.mk_surjective w
  have hm' : m ∈ 𝒜 (i + k) := by
    simpa [natShift] using (mem_intShift_ofNat_iff 𝒜 k i m).mp hm
  refine ⟨HomogeneousLocalization.mk ⟨i + k, ⟨m, hm'⟩, ⟨t * s, SetLike.mul_mem_graded ht hs⟩,
    S.mul_mem htS hsS⟩, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, twistFiberGenerator, DegreeZeroLocalization.mk_smul_mk,
    DegreeZeroLocalization.mk_eq_mk_iff]
  exact ⟨1, by simp [mul_comm, mul_left_comm]⟩

private theorem mk_smul_twistFiberGenerator {i : ℕ} {m t : A} (hm : m ∈ 𝒜 (i + k))
    (ht : t ∈ 𝒜 i) (hm' : m ∈ intShift 𝒜 (k : ℤ) i) (htS : t ∈ S) :
    HomogeneousLocalization.mk ⟨i + k, ⟨m, hm⟩, ⟨t * s, SetLike.mul_mem_graded ht hs⟩,
      S.mul_mem htS hsS⟩ • twistFiberGenerator 𝒜 (S := S) hs =
        DegreeZeroLocalization.mk ⟨i, ⟨m, hm'⟩, ⟨t, ht⟩, htS⟩ := by
  rw [twistFiberGenerator, DegreeZeroLocalization.mk_smul_mk, DegreeZeroLocalization.mk_eq_mk_iff]
  exact ⟨1, by simp [mul_comm, mul_left_comm]⟩

/-- `a ↦ a • (s / 1)`, from the degree-zero localization of `A` onto that of the twist `A(k)`. -/
private def twistFiberEquiv : HomogeneousLocalization 𝒜 S ≃ₗ[HomogeneousLocalization 𝒜 S]
    DegreeZeroLocalization 𝒜 (intShift 𝒜 (k : ℤ)) S :=
  LinearEquiv.ofBijective _ ⟨twistFiberGenerator_smul_injective 𝒜 hs hsS,
    twistFiberGenerator_smul_surjective 𝒜 hs hsS⟩

end Fiber

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **A homogeneous `s` of degree `k` freely generates `𝒪(k)` over `D₊(s)`**: over every open
inside `D₊(s)`, each section of `𝒪(k)` is uniquely a function times `s / 1`. -/
theorem isLocalBasis_sectionOfMem {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    Scheme.Modules.IsLocalBasis (twistingSheaf 𝒜 (k : ℤ)) (ProjectiveSpectrum.basicOpen 𝒜 s)
      (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) k hs) := by
  intro V hV
  have hres : (twistingSheaf 𝒜 (k : ℤ)).presheaf.map (homOfLE hV).op
      (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) k hs) = sectionOfMem 𝒜 𝒜 V k hs :=
    res_sectionOfMem 𝒜 𝒜 hV k hs
  rw [hres]
  have hval (r : Γ(Proj 𝒜, V)) (y : V) :
      ((LinearMap.toSpanSingleton Γ(Proj 𝒜, V) Γ(twistingSheaf 𝒜 (k : ℤ), V)
        (sectionOfMem 𝒜 𝒜 V k hs) r :
          (associatedSheafInType 𝒜 (intShift 𝒜 (k : ℤ))).1.obj (op V)).1 y) =
        (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op V)).1 y •
          twistFiberGenerator 𝒜 (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) hs :=
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    refine Subtype.ext (funext fun y ↦ ?_)
    apply twistFiberGenerator_smul_injective 𝒜 hs (hV y.2)
    have h1 : (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op V)).1 y •
        twistFiberGenerator 𝒜 (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) hs = 0 :=
      (hval r y).symm.trans (congrArg
        (fun t : (associatedSheafInType 𝒜 (intShift 𝒜 (k : ℤ))).1.obj (op V) ↦ t.1 y) hr)
    rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply, h1]
    exact (zero_smul _ _).symm
  · intro w
    let w' : (associatedSheafInType 𝒜 (intShift 𝒜 (k : ℤ))).1.obj (op V) := w
    let e (y : V) :=
      twistFiberEquiv 𝒜 (S := y.1.asHomogeneousIdeal.toIdeal.primeCompl) hs (hV y.2)
    refine ⟨⟨fun y ↦ (e y).symm (w'.1 y), fun y ↦ ?_⟩, ?_⟩
    · obtain ⟨W, hyW, iW, i, ⟨m, hm⟩, ⟨t, ht⟩, htW, hw⟩ := w'.2 y
      have hm' : m ∈ 𝒜 (i + k) := by
        simpa [natShift] using (mem_intShift_ofNat_iff 𝒜 k i m).mp hm
      refine ⟨W, hyW, iW, i + k, ⟨m, hm'⟩, ⟨t * s, SetLike.mul_mem_graded ht hs⟩,
        fun z ↦ ?_, fun z ↦ ?_⟩
      · have := (iW z).1.isPrime
        exact (iW z).1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (htW z) (hV (iW z).2)
      · change (e (iW z)).symm (w'.1 (iW z)) = _
        rw [LinearEquiv.symm_apply_eq]
        exact (hw z).trans
          (mk_smul_twistFiberGenerator 𝒜 hs (hV (iW z).2) hm' ht hm (htW z)).symm
    · refine Subtype.ext (funext fun y ↦ ?_)
      exact (hval _ y).trans ((e y).apply_symm_apply (w'.1 y))

/-! ### The ideal of the hyperplane kills `G` -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **If multiplication by `x` vanishes on `G`, the fractions `x c / s` of degree zero kill the
sections of `G`** over every open inside `D₊(s)`, whatever the degree of `s`. These fractions
generate the ideal of `V₊(x)` there.

`twistBy (x c) t = (x c / s) • twistBy s t`, the left side vanishes by `twistBy_mul`, and
`twistBy s` is injective on stalks because `s` freely generates `𝒪(1 + D)` near every point of
`D₊(s)`. -/
theorem fracSection_smul_eq_zero {x c s : A} {D : ℕ} (hx : x ∈ 𝒜 1) (hc : c ∈ 𝒜 D)
    (hs : s ∈ 𝒜 (1 + D)) (G : (Proj 𝒜).Modules) (hG : twistBy 𝒜 1 hx G = 0)
    {V : (Proj 𝒜).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒜 s) (t : Γ(G, V)) :
    (show Γ(Proj 𝒜, V) from fracSection 𝒜 (SetLike.mul_mem_graded hx hc) hs hV) • t = 0 := by
  set a : Γ(Proj 𝒜, V) := fracSection 𝒜 (SetLike.mul_mem_graded hx hc) hs hV
  have hzero : twistBy 𝒜 (1 + D) (SetLike.mul_mem_graded hx hc) G = 0 := by
    rw [twistBy_mul 𝒜 hx hc, hG, Limits.zero_comp]
  have htmul : Scheme.Modules.tmulSection G (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ)) (op V) (a • t)
      (sectionOfMem 𝒜 𝒜 V (1 + D) hs) = 0 := by
    rw [← Scheme.Modules.smul_tmulSection_left, ← twistBy_app, ← twistBy_app_eq_smul', hzero]
    rfl
  apply Scheme.Modules.section_ext G
  intro p hp
  rw [Scheme.Modules.germ_zero]
  have hgerm := Scheme.Modules.fixedLeftTensorStalkIso_hom_app_germ_tmul G
    (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ)) p hp (a • t) (sectionOfMem 𝒜 𝒜 V (1 + D) hs)
  rw [htmul, Scheme.Modules.germ_zero] at hgerm
  have h0 : Scheme.Modules.germ G p hp (a • t) ⊗ₜ[(Proj 𝒜).presheaf.stalk p]
      Scheme.Modules.germ (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ)) p hp
        (sectionOfMem 𝒜 𝒜 V (1 + D) hs) = 0 := by
    have := congrArg ((Scheme.Modules.fixedLeftTensorStalkIso (Proj 𝒜) p G).inv.app
      (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ))) hgerm
    rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply,
      map_zero] at this
  have hres : Scheme.Modules.germ (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ)) p hp
      (sectionOfMem 𝒜 𝒜 V (1 + D) hs) =
        Scheme.Modules.germ (twistingSheaf 𝒜 ((1 + D : ℕ) : ℤ)) p (hV hp)
          (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) (1 + D) hs) := by
    rw [← Scheme.Modules.germ_res _ hV p hp]
    exact congrArg _ (res_sectionOfMem 𝒜 𝒜 hV (1 + D) hs).symm
  rw [hres] at h0
  exact eq_zero_of_tmul_eq_zero
    ((isLocalBasis_sectionOfMem 𝒜 hs).bijective_stalk (hV hp)) h0

end Twist

/-! ### The hyperplane section -/

section Hyperplane

open HomogeneousLocalization

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [CommRing B]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ)

include hψ in
/-- An element of degree zero in the kernel of `localRingHom ψ`, for `ψ` the quotient by a
degree-one `x`, is zero or a fraction `x c / s` with `s` outside the prime. -/
private theorem localRingHom_eq_zero {x : A} (hx : x ∈ 𝒜 1)
    (hker : RingHom.ker (ψ : A →+* B) = Ideal.span {x}) (I : Ideal A) [I.IsPrime]
    (hI : I.IsHomogeneous 𝒜) (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap ψ)
    (a : AtPrime 𝒜 I) (ha : localRingHom ψ I J hIJ a = 0) :
    a = 0 ∨ ∃ (D : ℕ) (c s : A) (hc : c ∈ 𝒜 D) (hs : s ∈ 𝒜 (1 + D)) (hsI : s ∈ I.primeCompl),
      a = .mk ⟨1 + D, ⟨x * c, SetLike.mul_mem_graded hx hc⟩, ⟨s, hs⟩, hsI⟩ := by
  classical
  obtain ⟨⟨k, ⟨α, hα⟩, ⟨β, hβ⟩, hβI⟩, rfl⟩ := a.mk_surjective
  have ha' := congrArg val ha
  rw [val_localRingHom, val_mk, val_zero] at ha'
  erw [Localization.localRingHom_mk] at ha'
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at ha'
  obtain ⟨⟨u, hu⟩, hu0⟩ := ha'
  obtain ⟨u', rfl⟩ := hψ u
  have hu' : u' ∉ I := by
    rw [hIJ]
    exact hu
  obtain ⟨j, hj⟩ : ∃ j, (DirectSum.decompose 𝒜 u' j : A) ∉ I := by
    by_contra! h
    exact hu' ((hI.mem_iff).mpr h)
  set v := (DirectSum.decompose 𝒜 u' j : A) with hv
  have hvj : v ∈ 𝒜 j := SetLike.coe_mem _
  have hvα : ψ (v * α) = 0 := by
    have h := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := ℬ) (a := ψ u') (b := ψ α)
      (n := j + k) (ψ.map_mem hα) (Nat.le_add_left k j)
    have hu0' : ψ u' * ψ α = 0 := hu0
    rw [Nat.add_sub_cancel, hu0'] at h
    rw [map_mul, hv, map_directSumDecompose 𝒜 ℬ, ← h]
    simp
  have hvαker : v * α ∈ RingHom.ker (ψ : A →+* B) := hvα
  rw [hker, Ideal.mem_span_singleton'] at hvαker
  obtain ⟨c₀, hc₀⟩ := hvαker
  have hvαdeg : v * α ∈ 𝒜 (j + k) := SetLike.mul_mem_graded hvj hα
  have hvI : v ∈ I.primeCompl := hj
  rcases Nat.eq_zero_or_pos (j + k) with h0 | hpos
  · left
    have hzero : v * α = 0 := by
      have h := DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := 𝒜) (b := c₀) (n := 0) hx
        (by omega)
      rw [mul_comm x c₀, hc₀, DirectSum.decompose_of_mem_same 𝒜 (h0 ▸ hvαdeg)] at h
      exact h
    apply val_injective
    rw [val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨v, hvI⟩, hzero⟩
  · right
    obtain ⟨D, hD⟩ : ∃ D, j + k = 1 + D := ⟨j + k - 1, by omega⟩
    refine ⟨D, DirectSum.decompose 𝒜 c₀ D, v * β, SetLike.coe_mem _,
      hD ▸ SetLike.mul_mem_graded hvj hβ, I.primeCompl.mul_mem hvI hβI, ?_⟩
    have hxc : x * (DirectSum.decompose 𝒜 c₀ D : A) = v * α := by
      have h := DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := 𝒜) (b := c₀) (n := 1 + D) hx
        (Nat.le_add_right 1 D)
      rw [Nat.add_sub_cancel_left, mul_comm x c₀, hc₀, ← hD,
        DirectSum.decompose_of_mem_same 𝒜 hvαdeg] at h
      exact h.symm
    apply val_injective
    simp only [val_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; rw [hxc]; ring⟩

include hψ in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **The kernel of the stalk map of the hyperplane section kills the stalks of `G`**, when
multiplication by `x` vanishes on `G`. Through `Proj.stalkIso` the stalk map is
`localRingHom ψ`, whose kernel consists of fractions `x c / s`; those kill `G` by
`fracSection_smul_eq_zero`. -/
theorem smul_eq_zero_of_stalkMap_eq_zero {x : A} (hx : x ∈ 𝒜 1)
    (hker : RingHom.ker (ψ : A →+* B) = Ideal.span {x}) (h : ℬ₊ ≤ 𝒜₊.map ψ)
    (G : (Proj 𝒜).Modules) (hG : twistBy 𝒜 1 hx G = 0) (q : Proj ℬ)
    (r : (Proj 𝒜).presheaf.stalk ((map ψ h).base q)) (hr : (map ψ h).stalkMap q r = 0)
    (g : (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) ((map ψ h).base q)).obj G) :
    r • g = 0 := by
  have hloc : localRingHom ψ _ _ rfl ((stalkIso 𝒜 ((map ψ h).base q)).hom r) = 0 := by
    have h1 := localRingHom_comp_stalkIso_apply ψ h q r
    have h2 : (map ψ h).stalkMap q r = (sheafedSpaceMap ψ h).hom.stalkMap q r := rfl
    have h3 := congrArg (stalkIso ℬ q).hom (h1.trans (h2.symm.trans hr))
    rwa [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply, map_zero]
      at h3
  rcases localRingHom_eq_zero ψ hψ hx hker _ ((map ψ h).base q).asHomogeneousIdeal.isHomogeneous
    _ rfl _ hloc with ha | ⟨D, c, s, hc, hs, hsp, ha⟩
  · have hr0 : r = 0 := by
      have := congrArg (stalkIso 𝒜 ((map ψ h).base q)).inv ha
      rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply, map_zero]
        at this
    rw [hr0, zero_smul]
  · have hr : r = (Proj 𝒜).presheaf.germ (ProjectiveSpectrum.basicOpen 𝒜 s)
        ((map ψ h).base q) hsp (AlgebraicGeometry.sectionInBasicOpen 𝒜 ((map ψ h).base q)
          ⟨1 + D, ⟨x * c, SetLike.mul_mem_graded hx hc⟩, ⟨s, hs⟩, hsp⟩) := by
      have := congrArg (stalkIso 𝒜 ((map ψ h).base q)).inv ha
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at this
      rw [this]
      exact Proj.stalkIso'_symm_mk 𝒜 _ _
    obtain ⟨W, hpW, t, rfl⟩ := Scheme.Modules.exists_germ_eq G ((map ψ h).base q) g
    have hpV : (map ψ h).base q ∈ ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W := ⟨hsp, hpW⟩
    rw [hr, ← TopCat.Presheaf.germ_res_apply (Proj 𝒜).presheaf
      (homOfLE (inf_le_left : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ _)) ((map ψ h).base q) hpV,
      ← Scheme.Modules.germ_res G (inf_le_right : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ W)
        ((map ψ h).base q) hpV,
      ← Scheme.Modules.germ_smul]
    have hsec : (Proj 𝒜).presheaf.map
        (homOfLE (inf_le_left : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ _)).op
        (AlgebraicGeometry.sectionInBasicOpen 𝒜 ((map ψ h).base q)
          ⟨1 + D, ⟨x * c, SetLike.mul_mem_graded hx hc⟩, ⟨s, hs⟩, hsp⟩) =
        fracSection 𝒜 (SetLike.mul_mem_graded hx hc) hs inf_le_left :=
      rfl
    rw [hsec, fracSection_smul_eq_zero 𝒜 hx hc hs G hG, Scheme.Modules.germ_zero]

include hψ in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Stacks 01QY for a hyperplane**: if multiplication by a degree-one `x` vanishes on `G`, then
`G` is pushed forward from the hyperplane `V₊(x)`, i.e. the unit `G ⟶ i_* i^* G` of the
pullback/pushforward adjunction along `i = Proj.map ψ` is an isomorphism. Here `ψ` is a surjective
graded ring map with kernel `(x)`.

The quasi-coherence of `G` is not needed: the proof is stalkwise and holds for every module sheaf
`G`. Nor is `𝒜` assumed generated in degree one. -/
theorem isIso_unit_of_twistBy_eq_zero {x : A} (hx : x ∈ 𝒜 1)
    (hker : RingHom.ker (ψ : A →+* B) = Ideal.span {x}) (G : (Proj 𝒜).Modules)
    (hG : twistBy 𝒜 1 hx G = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (map ψ (irrelevant_le_map_of_surjective ψ hψ))).unit.app G) := by
  have := isClosedImmersion_map ψ hψ
  suffices H : ∀ p, Function.Bijective ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (map ψ (irrelevant_le_map_of_surjective ψ hψ))).unit.app G)) by
    have (p : Proj 𝒜) := (ConcreteCategory.isIso_iff_bijective _).mpr (H p)
    exact (Scheme.Modules.moduleStalkFunctors_jointlyReflectIsomorphisms (Proj 𝒜)).isIso _
  intro p
  by_cases hp : p ∈ Set.range (map ψ (irrelevant_le_map_of_surjective ψ hψ)).base
  · obtain ⟨q, rfl⟩ := hp
    let i := map ψ (irrelevant_le_map_of_surjective ψ hψ)
    let F := (Scheme.Modules.pullback i).obj G
    let T := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base F.presheaf q
    have hT : IsIso T := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing F.presheaf q
    let P := (Scheme.Modules.pullbackStalkIso i q).hom.app G
    let U := (ModuleCat.extendRestrictScalarsAdj (i.stalkMap q).hom).unit.app
      ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).obj G)
    let η := (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G)
    have key (g : (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).obj G) :
        P (T (η g)) = U g := by
      obtain ⟨V, hV, s, rfl⟩ := Scheme.Modules.exists_germ_eq G _ g
      have h1 := (Scheme.Modules.germ_app
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) _ hV s).symm
      have h2 := ConcreteCategory.congr_hom
        (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat i.base F.presheaf V q hV)
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G).app V s)
      rw [ConcreteCategory.comp_apply] at h2
      refine (congrArg (fun z ↦ P (T z)) h1).trans ?_
      refine (congrArg P h2).trans ?_
      exact Scheme.Modules.pullbackStalkIso_hom_app_germ_unit i q G V hV s
    have hU : Function.Bijective U :=
      bijective_extendRestrictScalarsAdj_unit_app _ (i.stalkMap_surjective q) _
        fun r hr g ↦ smul_eq_zero_of_stalkMap_eq_zero ψ hψ hx hker _ G hG q r hr g
    have hTb : Function.Bijective T := ConcreteCategory.bijective_of_isIso T
    have hPb : Function.Bijective P := ConcreteCategory.bijective_of_isIso P
    refine ⟨fun a b hab ↦ hU.1 ?_, fun y ↦ ?_⟩
    · rw [← key a, ← key b]
      exact congrArg (fun z ↦ P (T z)) hab
    · obtain ⟨g, hg⟩ := hU.2 (P (T y))
      exact ⟨g, hTb.1 (hPb.1 ((key g).trans hg))⟩
  · have hxp : x ∉ p.asHomogeneousIdeal := by
      intro hxp
      obtain ⟨q, hq⟩ := exists_comap_eq_of_ker_le ψ hψ (irrelevant_le_map_of_surjective ψ hψ) p
        (by rw [hker, Ideal.span_le, Set.singleton_subset_iff]; exact hxp)
      exact hp ⟨q, hq⟩
    have hzero (g : (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj G) : g = 0 := by
      obtain ⟨W, hpW, t, rfl⟩ := Scheme.Modules.exists_germ_eq G p g
      have hpV : p ∈ W ⊓ ProjectiveSpectrum.basicOpen 𝒜 x := ⟨hpW, hxp⟩
      rw [← Scheme.Modules.germ_res G (inf_le_left : W ⊓ ProjectiveSpectrum.basicOpen 𝒜 x ≤ W) p
        hpV]
      have h1 := fracSection_smul_eq_zero 𝒜 hx (SetLike.one_mem_graded 𝒜) (D := 0)
        (by simpa using hx) G hG (inf_le_right : W ⊓ ProjectiveSpectrum.basicOpen 𝒜 x ≤ _)
        (G.presheaf.map (homOfLE inf_le_left).op t)
      have hone : (show Γ(Proj 𝒜, W ⊓ ProjectiveSpectrum.basicOpen 𝒜 x) from
          fracSection 𝒜 (SetLike.mul_mem_graded hx (SetLike.one_mem_graded 𝒜))
            (by simpa using hx) inf_le_right) = 1 := by
        refine Subtype.ext (funext fun y ↦ ?_)
        change frac 𝒜 _ _ _ = 1
        apply HomogeneousLocalization.val_injective
        rw [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one,
          ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp⟩
      rw [hone, one_smul] at h1
      rw [h1, Scheme.Modules.germ_zero]
    have htgt : Subsingleton ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj
        ((Scheme.Modules.pushforward (map ψ (irrelevant_le_map_of_surjective ψ hψ))).obj
          ((Scheme.Modules.pullback (map ψ (irrelevant_le_map_of_surjective ψ hψ))).obj G))) :=
      DerivedAlgGeo.Topology.subsingleton_stalk_pushforward _
        ⟨_, ((Scheme.Modules.pullback (map ψ (irrelevant_le_map_of_surjective ψ hψ))).obj
          G).isSheaf⟩
        (map ψ (irrelevant_le_map_of_surjective ψ hψ)).isClosedEmbedding.isClosed_range p hp
    exact ⟨fun a b _ ↦ (hzero a).trans (hzero b).symm,
      fun _ ↦ ⟨0, @Subsingleton.elim _ htgt _ _⟩⟩

end Hyperplane

/-! ### The coordinate hyperplane -/

section Coordinate

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι R : Type u) [CommRing R]

/-- The graded surjection `R[Option ι] → R[ι]` sending `X none` to `0` and `X (some i)` to
`X i`. -/
def coordinateHyperplaneHom :
    polynomialGrading (Option ι) R →+*ᵍ polynomialGrading ι R where
  toRingHom := (aeval fun o : Option ι ↦ o.elim (0 : MvPolynomial ι R) X).toRingHom
  map_mem {n p} hp := by
    have h := hp.aeval (fun o : Option ι ↦ o.elim (0 : MvPolynomial ι R) X) (n := 1) fun o ↦ by
      cases o
      · exact isHomogeneous_zero _ _ _
      · exact isHomogeneous_X _ _
    simpa using h

/-- `coordinateHyperplaneHom` is evaluation at `X none = 0`, `X (some i) = X i`. -/
@[simp]
theorem coordinateHyperplaneHom_apply (p : MvPolynomial (Option ι) R) :
    coordinateHyperplaneHom ι R p = aeval (fun o : Option ι ↦ o.elim 0 X) p :=
  rfl

/-- `coordinateHyperplaneHom` is surjective: `rename some` is a section of it. -/
theorem coordinateHyperplaneHom_surjective :
    Function.Surjective (coordinateHyperplaneHom ι R) := by
  intro p
  refine ⟨rename some p, ?_⟩
  rw [coordinateHyperplaneHom_apply, aeval_rename]
  exact aeval_X_left_apply p

/-- **The kernel of `coordinateHyperplaneHom` is the ideal `(X none)`**: under
`optionEquivLeft` the map is evaluation of the variable `X none` at `0`. -/
theorem ker_coordinateHyperplaneHom :
    RingHom.ker (coordinateHyperplaneHom ι R : MvPolynomial (Option ι) R →+* MvPolynomial ι R) =
      Ideal.span {X none} := by
  have h : (coordinateHyperplaneHom ι R : MvPolynomial (Option ι) R →+* MvPolynomial ι R) =
      (Polynomial.evalRingHom 0).comp (optionEquivLeft R ι).toRingEquiv.toRingHom := by
    refine ringHom_ext (fun r ↦ ?_) fun o ↦ ?_
    · simp [optionEquivLeft_C]
    · cases o <;> simp [optionEquivLeft_X_none, optionEquivLeft_X_some]
  rw [h, ← RingHom.comap_ker, Polynomial.ker_evalRingHom, map_zero, sub_zero]
  change Ideal.comap (optionEquivLeft R ι).toRingEquiv (Ideal.span {Polynomial.X}) = _
  rw [← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  rw [RingEquiv.symm_apply_eq]
  simp [optionEquivLeft_X_none]

/-- **The coordinate hyperplane `X none = 0`**, as a morphism `Proj R[ι] ⟶ Proj R[Option ι]`. -/
def coordinateHyperplane :
    Proj (polynomialGrading ι R) ⟶ Proj (polynomialGrading (Option ι) R) :=
  map (coordinateHyperplaneHom ι R)
    (irrelevant_le_map_of_surjective _ (coordinateHyperplaneHom_surjective ι R))

/-- The coordinate hyperplane is a closed immersion. -/
instance : IsClosedImmersion (coordinateHyperplane ι R) :=
  isClosedImmersion_map _ (coordinateHyperplaneHom_surjective ι R)

end Coordinate

end AlgebraicGeometry.Proj
