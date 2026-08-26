/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.OpenImmersion
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistBridge

/-!
# The two charts' multiplications differ by a morphism, not a scalar

`#585`'s glue has to compare `fⁿ` and `gⁿ` as multiplications into `O(n)`. They differ by the
function `fⁿ/gⁿ`, which exists only on `D₊(g)`, so the comparison is a statement about the
restriction of `unitToTwist` to that open — and this file proves it.

## Why the scalar form is unreachable, and this one is not

The statement one first writes is `c • unitToTwist gⁿ = unitToTwist fⁿ`. That needs the scalar to
cross `tensorHom` at the next step, and it cannot: `Linear Γ(X, ⊤) X.PresheafOfModules` does not
synthesize, and supplying it would mean a `Γ`-linear structure on presheaves of modules, linearity
of `toPresheafOfModules` and of `associatedSheaf`, and a `MonoidalLinear` instance. None exists.

So the scalar is carried as a **morphism** instead. `chartFracPowMul` is multiplication by `fⁿ/gⁿ`
as an endomorphism of the unit on `D₊(g)`, and `chartUnitToTwist_eq` is a factorisation through it.
`tensorHom (𝟙 F) −` then only has to be *functorial* (`Scheme.Modules.tensorHom_id_comp`), which it
is, rather than linear, which it is not.

## The open subscheme, not the affine chart

`D₊(g)` is used here as an open subscheme of `Proj 𝒜`, not through `degreeOneChart`. The reason is
`Scheme.Opens.ι_image_top`: sections of the subscheme over `⊤` are *definitionally* sections of
`𝒪_Proj` over `D₊(g)`, so `fracPowSection` is already a global function there and no `ΓSpecIso` and
no degree-zero away ring appear anywhere in this file.

## What has to be named, and why

Two values are named at explicit result types rather than written inline, per
`references/instance-transparency.md` technique 5.

* `chartFracPowAt` — inline, the value elaborates at the `⋙ forget Ab` type of the unit's sections,
  where the scalar action does not synthesize at all.
* `chartUnitToTwist_app_one` — the same role `unitToTwist_app_one` plays one level down. Without it
  the restricted map is opaque, because `restrictUnitIso` and the restriction functor are both
  crossed before anything is applied.

`chartFracPowSections` is built openwise on the `Proj` side rather than by restricting one global
function down from `⊤`. Restricting downward puts its values at points of the *subscheme*, which
then do not compare with `fracPow` at points of `Proj`; built openwise the compatibility is `rfl`
and the comparison is `fracPow_smul_sectionOfMem` unchanged.

## Scope

The factorisation on the unit. Tensoring it up to `F` and gluing the charts are not here.
-/

noncomputable section

open CategoryTheory Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜

/-- **The function `fⁿ / gⁿ`, as a section of the structure sheaf over an open inside `D₊(g)`.**

Pointwise `fracPow`, which is a fixed fraction, so the `IsFraction` witness is the open itself and
restriction does not move it. -/
def fracPowSection {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 g) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U) :=
  ⟨fun x => fracPow 𝒜 hf hg n (hU x.2),
   fun x => ⟨U, x.2, 𝟙 _, n, ⟨f ^ n, by simpa using SetLike.pow_mem_graded n hf⟩,
     ⟨g ^ n, by simpa using SetLike.pow_mem_graded n hg⟩,
     fun y => by
       show (g ^ n : A) ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl
       exact Submonoid.pow_mem _ (hU y.2) n,
     fun _ => rfl⟩⟩

/-- A degree-one element raised to `n` has degree `n`. -/
theorem pow_mem_deg {a : A} (ha : a ∈ 𝒜 1) (m : ℕ) : a ^ m ∈ 𝒜 m := by
  simpa using SetLike.pow_mem_graded m ha

section Chart

variable {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (n : ℕ)

/-- **The basic open `D₊(g)`, as an open subscheme of `Proj 𝒜`.** -/
abbrev chartOpen : (Proj 𝒜).Opens := ProjectiveSpectrum.basicOpen 𝒜 g

/-- Restriction of module sheaves from `Proj 𝒜` to the open subscheme `D₊(g)`. -/
abbrev chartRestrictFunctor :
    (Proj 𝒜).Modules ⥤ (↑(chartOpen 𝒜 (g := g)) : Scheme).Modules :=
  Scheme.Modules.restrictFunctor (chartOpen 𝒜 (g := g)).ι

/-- **`unitToTwist`, restricted to `D₊(g)` and read as a map out of that subscheme's unit.** -/
def chartUnitToTwist (m : ℕ) {a : A} (ha : a ∈ 𝒜 m) :
    SheafOfModules.unit (↑(chartOpen 𝒜 (g := g)) : Scheme).ringCatSheaf ⟶
      (chartRestrictFunctor 𝒜 (g := g)).obj
        (show (Proj 𝒜).Modules from sheafTwist 𝒜 𝒜 (m : ℤ)) :=
  (Scheme.Modules.restrictUnitIso (chartOpen 𝒜 (g := g)).ι).inv ≫
    (chartRestrictFunctor 𝒜 (g := g)).map (unitToTwist 𝒜 𝒜 m ha)

/-- Every open of the subscheme `D₊(g)` has image inside `D₊(g)`. -/
theorem chartOpen_image_le (U : (↑(chartOpen 𝒜 (g := g)) : Scheme).Opens) :
    ((chartOpen 𝒜 (g := g)).ι ''ᵁ U) ≤ ProjectiveSpectrum.basicOpen 𝒜 g :=
  le_trans (Scheme.Hom.image_mono _ le_top)
    (le_of_eq (chartOpen 𝒜 (g := g)).ι_image_top)

/-- `fⁿ/gⁿ` over one open of `D₊(g)`, named at the subscheme's own section type.

Written inline the value elaborates at the `⋙ forget Ab` type of the unit's sections, where the
scalar action does not synthesize. -/
def chartFracPowAt (U : (↑(chartOpen 𝒜 (g := g)) : Scheme).Opensᵒᵖ) :
    Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) :=
  fracPowSection 𝒜 hf hg n (chartOpen_image_le 𝒜 U.unop)

/-- **`fⁿ/gⁿ` as a global section of the unit sheaf on `D₊(g)`.**

Built openwise on the `Proj` side; the compatibility is then `rfl`. -/
def chartFracPowSections :
    (SheafOfModules.unit (↑(chartOpen 𝒜 (g := g)) : Scheme).ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (fun U => chartFracPowAt 𝒜 hf hg n U) (fun _ _ _ => rfl)

/-- **What the restricted map does to `1`: it is still `aᵐ / 1`.**

`unitToTwist_app_one`'s role, one level down. Both `restrictUnitIso` and the restriction functor
are crossed before anything is applied, so without this the restricted map asserts nothing. -/
theorem chartUnitToTwist_app_one (m : ℕ) {a : A} (ha : a ∈ 𝒜 m)
    (U : (↑(chartOpen 𝒜 (g := g)) : Scheme).Opensᵒᵖ) :
    ((chartUnitToTwist 𝒜 (g := g) m ha).val.app U).hom
        (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop))
      = sectionOfMem 𝒜 𝒜 ((chartOpen 𝒜 (g := g)).ι ''ᵁ U.unop) m ha := by
  simp only [chartUnitToTwist, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  have h1 : ((Scheme.Modules.restrictUnitIso (chartOpen 𝒜 (g := g)).ι).inv.val.app U).hom
      (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop))
      = (1 : Γ(Proj 𝒜, (chartOpen 𝒜 (g := g)).ι ''ᵁ U.unop)) :=
    map_one (Scheme.Hom.appIso (chartOpen 𝒜 (g := g)).ι U.unop).inv.hom
  rw [h1]
  exact unitToTwist_app_one 𝒜 𝒜 m ha _

/-- **Multiplication by `fⁿ/gⁿ`, as an endomorphism of the unit on `D₊(g)`.**

A morphism, not a scalar — which is the whole point: a scalar cannot cross `tensorHom`, and a
morphism can. -/
def chartFracPowMul :
    SheafOfModules.unit (↑(chartOpen 𝒜 (g := g)) : Scheme).ringCatSheaf ⟶
      SheafOfModules.unit (↑(chartOpen 𝒜 (g := g)) : Scheme).ringCatSheaf :=
  (SheafOfModules.unitHomEquiv _).symm (chartFracPowSections 𝒜 hf hg n)

/-- **Over `D₊(g)`, multiplying by `fⁿ` is multiplying by `fⁿ/gⁿ` and then by `gⁿ`.**

The comparison `#585` needs between two charts, with the correction carried as a morphism out of
the unit rather than as a scalar. Applying `tensorHom (𝟙 F) −` to it — which preserves composition
by `Scheme.Modules.tensorHom_id_comp` — is what carries it to `F(n)`.

The proof is step A (`fracPow_smul_sectionOfMem`) read through `unitHomEquiv`, plus one bridge:
the restricted sheaf's scalar action is the `Proj` one transported along `appIso`
(`Scheme.Modules.restrict_smul_eq`), and for the inclusion of an open subscheme that transport is
`Iso.refl` but *not* `rfl`. -/
theorem chartUnitToTwist_eq :
    chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hf n)
      = chartFracPowMul 𝒜 hf hg n ≫ chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hg n) := by
  rw [chartFracPowMul, SheafOfModules.unitHomEquiv_symm_comp, Equiv.eq_symm_apply]
  ext U
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  show ((chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hf n)).val.app U).hom
      (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop))
    = ((chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hg n)).val.app U).hom
      (show Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) from
        (chartFracPowSections 𝒜 hf hg n).val U)
  have hone : (show Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) from
        (chartFracPowSections 𝒜 hf hg n).val U)
      = (show Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) from
        (chartFracPowSections 𝒜 hf hg n).val U) •
        (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop)) := by
    simp
  have hlin : ((chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hg n)).val.app U).hom
      ((show Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) from
          (chartFracPowSections 𝒜 hf hg n).val U) •
        (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop)))
      = (show Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop) from
          (chartFracPowSections 𝒜 hf hg n).val U) •
        ((chartUnitToTwist 𝒜 (g := g) n (pow_mem_deg 𝒜 hg n)).val.app U).hom
          (1 : Γ((↑(chartOpen 𝒜 (g := g)) : Scheme), U.unop)) :=
    LinearMap.map_smul _ _ _
  rw [hone, hlin, chartUnitToTwist_app_one, chartUnitToTwist_app_one]
  have hbridge := Scheme.Modules.restrict_smul_eq (chartOpen 𝒜 (g := g)).ι
    (show (Proj 𝒜).Modules from sheafTwist 𝒜 𝒜 (n : ℤ)) U.unop
    (chartFracPowAt 𝒜 hf hg n U)
    (sectionOfMem 𝒜 𝒜 ((chartOpen 𝒜 (g := g)).ι ''ᵁ U.unop) n (pow_mem_deg 𝒜 hg n))
  rw [Scheme.Opens.ι_appIso] at hbridge
  refine (hbridge.trans ?_).symm
  apply section_ext
  funext x
  exact fracPow_smul_sectionOfMem 𝒜 hf hg n (chartOpen_image_le 𝒜 (g := g) U.unop) x

end Chart

end AlgebraicGeometry.Proj
