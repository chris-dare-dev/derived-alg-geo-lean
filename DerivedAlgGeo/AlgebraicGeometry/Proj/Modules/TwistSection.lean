/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistComparison

/-!
# Homogeneous elements as sections of the twist, and multiplication `F ⟶ F(n)`

`#585` asks that `fⁿ · s` extend to a global section of `F(n)`, for `F` quasi-coherent on
`Proj 𝒜` and `s` a section over a degree-one chart. **That statement cannot be written against the
tree as it stands**: multiplying a section of an arbitrary `F` by a homogeneous element needs a map
`F ⟶ F(n)`, and no such map exists. `#584` supplied the twist itself; this file supplies the
multiplication into it.

## The observation that makes it short

A degree-`n` element `m` of `𝓜` is a **global** section of `M(n)~`, not merely a section over a
basic open. The fraction is `m / 1`: a local fraction asks for numerator and denominator in the
same degree, `1` has degree `0`, and `mem_intShift_zero_of_mem` says a degree-`n` element of `𝓜`
lies in degree `0` of the shifted grading. Nothing is inverted, so the same fraction is valid at
every point of every open and restriction does not move it — which is why `sectionsOfMem`'s
compatibility is `rfl`, and why no `basicOpen_one` transport is needed anywhere.

## From there to an arbitrary `F`

`unitToTwist` is that compatible family read through `SheafOfModules.unitHomEquiv` — a global
section *is* a map out of the unit. `twistBy` then tensors it with `F` and cancels the unit:

    F ≅ F ⊗ 𝟙 --(𝟙 ⊗ ·fⁿ)--> F ⊗ O(n) = F(n)

`F` is an arbitrary module sheaf. It is **not** assumed to be an associated sheaf, which is the
point: `#584`'s comparison stops at associated sheaves, and `#585` may not inherit that limit —
its acceptance criteria forbid exactly that hypothesis. Nothing here needs the comparison.

The same two maps are what `#570` step 1 asks for to build `Γ_*(F)` as a graded module, "with the
`A`-action from the twist multiplication maps".

## Why `unitToTwist_app_one` is not decoration

`unitHomEquiv.symm` is an equivalence's inverse, so the morphism it produces is opaque at every use
site: a wrong `sectionsOfMem` would typecheck and nothing downstream would notice. That lemma pins
the content — `1 ↦ m / 1` — and is the only thing standing between this API and a map that asserts
nothing.

Its `1` is ascribed at the ring, `(1 : ringCatSheaf.obj.obj (op U))`, rather than written bare. The
unit sheaf's sections are the ring's sections by a `def` that does not unfold at reducible
transparency, so `OfNat` is not found on the bare numeral. `references/instance-transparency.md`
is the general case; Mathlib's own `unitHomEquiv_apply_coe` ascribes it for the same reason.

## Scope

The maps, and what they do to `1`. **The extension theorem of `#585` is not here** — it needs the
degree-one chart cover, quasi-coherence to make each chart a module, and an affine clearing lemma
for the denominator. With this API its statement elaborates, which is what it was blocked on; it is
proved in `Proj/Modules/Glue.lean` as `exists_globalSection_twistBy`.
-/
noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace MonoidalCategory

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

/-- A degree-`n` element of `𝓜` sits in degree `0` of the shifted grading.

Which is what makes it a *global* section of `M(n)~` rather than one over a basic open: the
fraction `m / 1` needs its numerator one degree-step below its denominator's degree, and `1` has
degree `0`. -/
theorem mem_intShift_zero_of_mem (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) :
    m ∈ intShift 𝓜 (n : ℤ) 0 :=
  Or.inr ⟨n, by simp, hm⟩

/-- **A degree-`n` element of `𝓜` is the section `m / 1` of `M(n)~`, over any open.**

Nothing is inverted, so the same fraction is valid at every point of every open, and restriction
between opens does not move it. -/
def sectionOfMem (U : Opens X) (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) :
    (associatedSheafInType 𝒜 (intShift 𝓜 (n : ℤ))).1.obj (op U) :=
  ⟨fun x => DegreeZeroLocalization.mk
      { deg := 0
        num := ⟨m, mem_intShift_zero_of_mem 𝓜 n hm⟩
        den := ⟨1, SetLike.one_mem_graded 𝒜⟩
        den_mem := Ideal.IsPrime.one_notMem inferInstance },
    fun x =>
      ⟨U, x.2, 𝟙 _, 0, ⟨m, mem_intShift_zero_of_mem 𝓜 n hm⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩,
        fun _ => Ideal.IsPrime.one_notMem inferInstance, fun _ => rfl⟩⟩

@[simp]
theorem sectionOfMem_apply (U : Opens X) (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) (x : U) :
    (sectionOfMem 𝒜 𝓜 U n hm).1 x = DegreeZeroLocalization.mk
      { deg := 0
        num := ⟨m, mem_intShift_zero_of_mem 𝓜 n hm⟩
        den := ⟨1, SetLike.one_mem_graded 𝒜⟩
        den_mem := Ideal.IsPrime.one_notMem inferInstance } := rfl

/-- **The compatible family the fractions `m / 1` form**, which is what a map out of the unit
consumes. -/
def sectionsOfMem (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) :
    (show SheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf from
      sheafTwist 𝒜 𝓜 (n : ℤ)).sections :=
  PresheafOfModules.sectionsMk (fun U => sectionOfMem 𝒜 𝓜 U.unop n hm)
    (fun U V i => by
      apply section_ext
      funext x
      rfl)

/-- **Multiplication by a degree-`n` element of `𝒜`, as a map out of the structure sheaf.**

`#584` gave the twist; this gives the *sections* of it that a homogeneous element supplies, which
is what `#585` multiplies by. -/
def unitToTwist (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) :
    SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⟶
      (show SheafOfModules (AlgebraicGeometry.Proj 𝒜).ringCatSheaf from
        sheafTwist 𝒜 𝓜 (n : ℤ)) :=
  (SheafOfModules.unitHomEquiv _).symm (sectionsOfMem 𝒜 𝓜 n hm)

/-- **What `unitToTwist` does: it sends `1` to `m / 1`.**

Without this the map is opaque — `unitHomEquiv.symm` is an equivalence's inverse, so nothing about
the resulting morphism is visible at a use site, and a wrong `sectionsOfMem` would go unnoticed. -/
@[simp]
theorem unitToTwist_app_one (n : ℕ) {m : M} (hm : m ∈ 𝓜 n) (U : Opens X) :
    (unitToTwist 𝒜 𝓜 n hm).val.app (op U)
        (1 : (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.obj (op U)) =
      sectionOfMem 𝒜 𝓜 U n hm :=
  congrArg (fun s => PresheafOfModules.sections.eval s (op U))
    ((SheafOfModules.unitHomEquiv _).apply_symm_apply (sectionsOfMem 𝒜 𝓜 n hm))

/-- **Multiplication by a degree-`n` element of `𝒜`, on an arbitrary module sheaf: `F ⟶ F(n)`.**

`F` is not assumed to be an associated sheaf, which is the whole point — `#585` multiplies a
section of an arbitrary quasi-coherent `F`, and until this map exists the statement cannot even be
written. It is the map out of the unit, tensored with `F` and read through the right unitor. -/
def twistBy (n : ℕ) {f : A} (hf : f ∈ 𝒜 n) (F : (AlgebraicGeometry.Proj 𝒜).Modules) :
    F ⟶ AlgebraicGeometry.Scheme.Modules.tensorObj F (twistingSheaf 𝒜 (n : ℤ)) :=
  (AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso F).inv ≫
    AlgebraicGeometry.Scheme.Modules.tensorHom (𝟙 F) (unitToTwist 𝒜 𝒜 n hf)

end AlgebraicGeometry.Proj
