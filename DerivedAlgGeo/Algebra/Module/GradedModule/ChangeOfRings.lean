/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Localization

/-!
# Degree-zero localizations along a graded ring map

Let `ψ : 𝒜 →+*ᵍ ℬ` be a graded ring map and `g : M →ₛₗ[ψ] N` a semilinear map of graded modules
preserving the gradings. If a submonoid `P` of `A` maps into a submonoid `Q` of `B`, the fraction
`m / s ↦ g m / ψ s` is a map of degree-zero homogeneous localizations

    DegreeZeroLocalization 𝒜 𝓜 P → DegreeZeroLocalization ℬ 𝓝 Q,

semilinear over Mathlib's `HomogeneousLocalization.map ψ`. At a point `y` of `Proj ℬ` and its image
`p = ψ⁻¹ y` in `Proj 𝒜` it is the map of fibres underlying the functoriality of associated sheaves
along `Proj.map ψ`.

## Main definitions

* `GradedModule.localizedMapOfRingHom`: `m / s ↦ g m / ψ s` on ordinary localized modules.
* `GradedModule.DegreeZeroLocalization.mapOfRingHom`: its restriction to degree zero.

## Main results

* `GradedModule.DegreeZeroLocalization.mapOfRingHom_mk`: the formula on homogeneous fractions.
* `GradedModule.DegreeZeroLocalization.mapOfRingHom_smul`: semilinearity over
  `HomogeneousLocalization.map ψ`.

## Implementation notes

The semilinear map is Mathlib's `M →ₛₗ[ψ.toRingHom] N`; preservation of the gradings is a separate
hypothesis rather than a new bundled structure. The same-ring case is `GradedLinearMap.map`.

## References

* [Stacks, Lemma 27.11.1 (Tag 01MY)](https://stacks.math.columbia.edu/tag/01MY), the map `θ` on
  standard opens.

## Tags

graded module, homogeneous localization, change of rings, semilinear map
-/

noncomputable section

open DirectSum SetLike

namespace GradedModule

variable {ι A B M N σA σB σM σN : Type*} [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [CommRing B] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [SetLike σA A] [AddSubgroupClass σA A] [SetLike σB B] [AddSubgroupClass σB B]
variable [SetLike σM M] [AddSubgroupClass σM M] [SetLike σN N] [AddSubgroupClass σN N]
variable {𝒜 : ι → σA} {ℬ : ι → σB} {𝓜 : ι → σM} {𝓝 : ι → σN}
variable [GradedRing 𝒜] [GradedRing ℬ] [SetLike.GradedSMul 𝒜 𝓜] [SetLike.GradedSMul ℬ 𝓝]
variable (ψ : 𝒜 →+*ᵍ ℬ) (g : M →ₛₗ[ψ.toRingHom] N)
variable {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap ψ)

/-- `m / s ↦ g m / ψ s` on ordinary localized modules. -/
def localizedMapOfRingHom : LocalizedModule P M →+ LocalizedModule Q N where
  toFun x := x.liftOn (fun p ↦ LocalizedModule.mk (g p.1) ⟨ψ p.2, hPQ p.2.2⟩) <| by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.2 ⟨⟨ψ u, hPQ u.2⟩, ?_⟩
    have h := congrArg g hu
    simpa only [Submonoid.smul_def, map_smulₛₗ, GradedRingHom.coe_toRingHom] using h
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : P), LocalizedModule.liftOn_mk, map_zero,
      LocalizedModule.zero_mk]
  map_add' x y := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction y using LocalizedModule.induction_on with
    | h m' s' =>
    simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, map_add, map_smulₛₗ,
      Submonoid.smul_def, Submonoid.coe_mul, map_mul, GradedRingHom.coe_toRingHom]
    rfl

omit [AddCommMonoid ι] [DecidableEq ι] [AddSubgroupClass σA A] [AddSubgroupClass σB B]
  [GradedRing 𝒜] [GradedRing ℬ] in
@[simp]
theorem localizedMapOfRingHom_mk (m : M) (s : P) :
    localizedMapOfRingHom ψ g hPQ (LocalizedModule.mk m s) =
      LocalizedModule.mk (g m) ⟨ψ s, hPQ s.2⟩ :=
  rfl

variable (hg : ∀ i (m : M), m ∈ 𝓜 i → g m ∈ 𝓝 i)

/-- A homogeneous fraction `m / s` mapped to `g m / ψ s`. -/
def NumDenSameDeg.mapOfRingHom (c : NumDenSameDeg 𝒜 𝓜 P) : NumDenSameDeg ℬ 𝓝 Q where
  deg := c.deg
  num := ⟨g c.num, hg _ _ c.num.2⟩
  den := ⟨ψ c.den, ψ.map_mem c.den.2⟩
  den_mem := hPQ c.den_mem

namespace DegreeZeroLocalization

/-- The map of degree-zero localizations `m / s ↦ g m / ψ s` along a graded ring map. -/
def mapOfRingHom : DegreeZeroLocalization 𝒜 𝓜 P →+ DegreeZeroLocalization ℬ 𝓝 Q where
  toFun z := ⟨localizedMapOfRingHom ψ g hPQ (z : LocalizedModule P M), by
    obtain ⟨c, hc⟩ := z.property
    exact ⟨NumDenSameDeg.mapOfRingHom ψ g hPQ hg c, by
      rw [← hc]
      exact (localizedMapOfRingHom_mk ψ g hPQ (c.num : M) ⟨c.den, c.den_mem⟩).symm⟩⟩
  map_zero' := Subtype.ext (map_zero (localizedMapOfRingHom ψ g hPQ))
  map_add' x y :=
    Subtype.ext (map_add (localizedMapOfRingHom ψ g hPQ) (x : LocalizedModule P M) y)

@[simp]
theorem coe_mapOfRingHom (z : DegreeZeroLocalization 𝒜 𝓜 P) :
    (mapOfRingHom ψ g hPQ hg z : LocalizedModule Q N) =
      localizedMapOfRingHom ψ g hPQ (z : LocalizedModule P M) :=
  rfl

theorem mapOfRingHom_mk (c : NumDenSameDeg 𝒜 𝓜 P) :
    mapOfRingHom ψ g hPQ hg (mk c) = mk (NumDenSameDeg.mapOfRingHom ψ g hPQ hg c) :=
  Subtype.ext (localizedMapOfRingHom_mk ψ g hPQ (c.num : M) ⟨c.den, c.den_mem⟩)

/-- The map of degree-zero localizations is semilinear over `HomogeneousLocalization.map ψ`. -/
theorem mapOfRingHom_smul (a : HomogeneousLocalization 𝒜 P)
    (z : DegreeZeroLocalization 𝒜 𝓜 P) :
    mapOfRingHom ψ g hPQ hg (a • z) =
      HomogeneousLocalization.map ψ hPQ a • mapOfRingHom ψ g hPQ hg z := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  obtain ⟨b, rfl⟩ := HomogeneousLocalization.mk_surjective a
  apply Subtype.ext
  change localizedMapOfRingHom ψ g hPQ
      ((algebraMap (HomogeneousLocalization 𝒜 P) (Localization P) (.mk b)) • c.embedding) =
    (algebraMap (HomogeneousLocalization ℬ Q) (Localization Q)
      (HomogeneousLocalization.map ψ hPQ (.mk b))) •
      localizedMapOfRingHom ψ g hPQ c.embedding
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, NumDenSameDeg.embedding, LocalizedModule.mk_smul_mk,
    localizedMapOfRingHom_mk, localizedMapOfRingHom_mk, LocalizedModule.mk_smul_mk]
  simp only [map_smulₛₗ, Submonoid.coe_mul, map_mul, GradedRingHom.coe_toRingHom]
  rfl

end DegreeZeroLocalization

end GradedModule
