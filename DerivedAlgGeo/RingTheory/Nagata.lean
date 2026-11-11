/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.NoetherNormalization

/-!
# Japanese, universally Japanese and Nagata rings

A domain is *Japanese* (N-2) if its integral closure in every finite extension of its fraction
field is finite. A ring is *universally Japanese* if every domain of finite type over it is
Japanese, and *Nagata* if it is Noetherian and every quotient by a prime is Japanese.

## Main definitions

* `IsJapanese R`: Stacks 032F (2).
* `IsUniversallyJapanese R`: Stacks 032R (1).
* `IsNagataRing R`: Stacks 032R (2).

## Main results

* `IsJapanese.of_isLocalization`: N-2 passes to localizations (Stacks 032G).
* `IsJapanese.of_span_eq_top`: N-2 is local on the ring (Stacks 032H).
* `IsUniversallyJapanese.of_essFiniteType`: universally Japanese ascends along essentially
  finite type algebras (Stacks 032S).
* `IsNagataRing.localization`: Nagata passes to localizations (Stacks 032U).
* `IsUniversallyJapanese.of_span_eq_top`, `IsNagataRing.of_span_eq_top`: both properties are
  local on the ring (Stacks 032V).
* `IsNagataRing.of_isUniversallyJapanese`: the easy half of Nagata's theorem (Stacks 0334).
* `IsUniversallyJapanese.of_charZero`: fields of characteristic zero are universally Japanese.

## Implementation notes

Nagata's theorem in the hard direction, that a Nagata ring is universally Japanese (Stacks 0334),
is not proved here. Statements that need a Nagata hypothesis therefore take the pair
`[IsNoetherianRing R] [IsUniversallyJapanese R]`, which BLMNPS Lemma 11.13
(arXiv:1902.08184v4, §11.4) shows to be equivalent to being Nagata.

`IsJapanese R` quantifies over extensions in the universe of `R`. Every finite extension of the
fraction field has a copy there, so nothing is lost, and the class gains no universe parameter.

BLMNPS Lemma 11.15 is proved without a transcendence basis: a valuation ring of `L` dominating `A`
selects finitely many generators of `L` lying in it, Stacks 00P8 cuts the resulting local ring
down to dimension one, and the normalization of that ring is a Dedekind domain whose localization
at a maximal ideal is the required discrete valuation ring.

## References

* [Stacks: Japanese rings](https://stacks.math.columbia.edu/tag/032E)
* [Stacks: Nagata rings](https://stacks.math.columbia.edu/tag/032R)
* [Stacks: Tag 0334](https://stacks.math.columbia.edu/tag/0334)
* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in families*,
  arXiv:1902.08184v4, §11.4

## Tags

Nagata ring, Japanese ring, N-2, universally Japanese, integral closure, discrete valuation ring
-/

universe u

open scoped nonZeroDivisors

/-- A domain is **Japanese** (N-2) if its integral closure in every finite extension of its
fraction field is a finite module. -/
@[stacks 032F "(2)"]
class IsJapanese (R : Type u) [CommRing R] [IsDomain R] : Prop where
  /-- The integral closure in a finite extension of the fraction field is finite. -/
  finite_integralClosure (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L)

/-- A ring is **universally Japanese** if every domain of finite type over it is Japanese. -/
@[stacks 032R "(1)"]
class IsUniversallyJapanese (R : Type u) [CommRing R] : Prop where
  /-- Every domain of finite type over the ring is Japanese. -/
  isJapanese (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S] :
    IsJapanese S

/-- A ring is **Nagata** if it is Noetherian and its quotient by every prime is Japanese.

Nagata's theorem (Stacks 0334) says that this is equivalent to being Noetherian and universally
Japanese. Only the easy direction, `IsNagataRing.of_isUniversallyJapanese`, is proved here, so
theorems that need the stronger property assume the pair
`[IsNoetherianRing R] [IsUniversallyJapanese R]` instead. -/
@[stacks 032R "(2)"]
class IsNagataRing (R : Type u) [CommRing R] : Prop where
  /-- A Nagata ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- The quotient of a Nagata ring by a prime is Japanese. -/
  isJapanese (p : Ideal R) [p.IsPrime] : IsJapanese (R ⧸ p)

section IntegralClosureLocalization

variable (R : Type*) [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
  (L : Type*) [CommRing L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

/-- For a tower `R → S → L`, the inclusion of the integral closure of `R` in `L` into that of
`S`, as an `R`-linear map. -/
private def integralClosureInclusion :
    integralClosure R L →ₗ[R] integralClosure S L where
  toFun x := ⟨x, x.2.tower_top⟩
  map_add' _ _ := rfl
  map_smul' r x := Subtype.ext <| by simp [Algebra.smul_def, IsScalarTower.algebraMap_apply R S L]

/-- Integral closure commutes with localization: the integral closure of a localization `S` of `R`
is the localization of the integral closure of `R`. -/
private theorem isLocalizedModule_integralClosureInclusion [IsLocalization M S] :
    IsLocalizedModule M (integralClosureInclusion R S L) where
  map_units m := by
    have := (IsLocalization.map_units S m).map (algebraMap S (Module.End S (integralClosure S L)))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    funext x
    simp [algebraMap_smul]
  surj y := by
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (y : L) y.2
    refine ⟨(⟨m • (y : L), hm⟩, m), Subtype.ext ?_⟩
    rfl
  exists_of_eq {x₁ x₂} h :=
    ⟨1, by
      rw [one_smul, one_smul]
      exact Subtype.ext (congr_arg (fun z : integralClosure S L ↦ (z : L)) h)⟩

end IntegralClosureLocalization

/-- A fraction field of a localization of a domain is a fraction field of the domain. -/
private theorem isFractionRing_of_isLocalization_of_isFractionRing {R : Type*} [CommRing R]
    [IsDomain R] (M : Submonoid R) (hM : M ≤ R⁰) (S T : Type*) [CommRing S] [IsDomain S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization M S] [IsFractionRing S T] : IsFractionRing R T := by
  have := IsLocalization.localization_localization_isLocalization_of_has_all_units M S⁰ T
    (fun x hx ↦ hx.mem_nonZeroDivisors)
  have hcomap : S⁰.comap (algebraMap R S) = R⁰ := by
    ext r
    simp [mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ (IsLocalization.injective S hM)]
  rw [hcomap] at this
  exact this

namespace IsJapanese

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The integral closure of a Japanese domain in a finite extension of any of its fraction fields
is finite. -/
theorem finite_integralClosure_of_isFractionRing [IsJapanese R] (K : Type*) (L : Type u) [Field K]
    [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] : Module.Finite R (integralClosure R L) := by
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let : Algebra (FractionRing R) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have : IsScalarTower R (FractionRing R) L := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R K L]
  have : FiniteDimensional (FractionRing R) L :=
    .of_equiv_equiv (A₁ := K) (B₁ := L) e.symm.toRingEquiv (RingEquiv.refl L) <| by
      ext x
      simp [RingHom.algebraMap_toAlgebra]
  exact IsJapanese.finite_integralClosure L

/-- N-2 passes to localizations. -/
@[stacks 032G]
theorem of_isLocalization [IsJapanese R] (M : Submonoid R) (S : Type u) [CommRing S] [IsDomain S]
    [Algebra R S] [IsLocalization M S] : IsJapanese S := by
  constructor
  intro L _ _ _ _ _
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S L := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (FractionRing S) L := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R S (FractionRing S),
      ← IsScalarTower.algebraMap_apply S (FractionRing S) L]
    rfl
  have hM : M ≤ R⁰ := by
    intro m hm
    exact mem_nonZeroDivisors_of_ne_zero fun h ↦
      (IsLocalization.map_units S ⟨m, hm⟩).ne_zero (by simp [h])
  have : IsFractionRing R (FractionRing S) :=
    isFractionRing_of_isLocalization_of_isFractionRing M hM S (FractionRing S)
  have := finite_integralClosure_of_isFractionRing (FractionRing S) L (R := R)
  have := isLocalizedModule_integralClosureInclusion R M S L
  exact Module.Finite.of_isLocalizedModule M (integralClosureInclusion R S L)

/-- N-2 is invariant under ring isomorphisms. -/
theorem of_ringEquiv [IsJapanese R] {S : Type u} [CommRing S] [IsDomain S] (e : R ≃+* S) :
    IsJapanese S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have : IsLocalization (⊥ : Submonoid R) S :=
    { map_units := fun ⟨m, hm⟩ ↦ by simp [Submonoid.mem_bot.mp hm]
      surj := fun z ↦ ⟨(e.symm z, 1), by simp [RingHom.algebraMap_toAlgebra]⟩
      exists_of_eq := fun h ↦ ⟨1, by simpa using e.injective h⟩ }
  exact of_isLocalization (⊥ : Submonoid R) S

/-- N-2 is local on the ring: a domain is Japanese if its localizations away from the members of a
family generating the unit ideal are. Localizations away from zero are not domains, so the
hypothesis is vacuous for them. -/
@[stacks 032H]
theorem of_span_eq_top (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g ∈ s, ∀ (Rg : Type u) [CommRing Rg] [IsDomain Rg] [Algebra R Rg]
      [IsLocalization.Away g Rg], IsJapanese Rg) :
    IsJapanese R := by
  classical
  constructor
  intro L _ _ _ _ _
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  let t' : Finset R := t.filter (· ≠ 0)
  have ht' : Ideal.span (t' : Set R) = ⊤ := by
    rw [eq_top_iff, ← ht, Ideal.span_le]
    intro g hg
    by_cases hg0 : g = 0
    · simp [hg0]
    · exact Ideal.subset_span (by simpa [t', hg0] using hg)
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) L]
    exact (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective _ _)
  have hne : ∀ g : t', (g : R) ≠ 0 := fun g ↦ (Finset.mem_filter.mp g.2).2
  have hunitL : ∀ g : t', IsUnit (algebraMap R L g) := fun g ↦
    ((map_ne_zero_iff _ hinj).mpr (hne g)).isUnit
  have hunitK : ∀ g : t', IsUnit (algebraMap R (FractionRing R) g) := fun g ↦
    ((map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr (hne g)).isUnit
  let Rg : t' → Type u := fun g ↦ Localization.Away (g : R)
  have : ∀ g : t', IsDomain (Rg g) := fun g ↦
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (hne g))
  let : ∀ g : t', Algebra (Rg g) L := fun g ↦
    (IsLocalization.Away.lift (S := Rg g) (g : R) (hunitL g)).toAlgebra
  have : ∀ g : t', IsScalarTower R (Rg g) L := fun g ↦ .of_algebraMap_eq fun r ↦
    (RingHom.congr_fun (IsLocalization.Away.lift_comp (S := Rg g) (g : R) (hunitL g)) r).symm
  let : ∀ g : t', Algebra (Rg g) (FractionRing R) := fun g ↦
    (IsLocalization.Away.lift (S := Rg g) (g : R) (hunitK g)).toAlgebra
  have : ∀ g : t', IsScalarTower R (Rg g) (FractionRing R) := fun g ↦
    .of_algebraMap_eq fun r ↦
    (RingHom.congr_fun (IsLocalization.Away.lift_comp (S := Rg g) (g : R) (hunitK g)) r).symm
  have : ∀ g : t', IsScalarTower (Rg g) (FractionRing R) L := fun g ↦ .of_algebraMap_eq <|
    RingHom.congr_fun <| show algebraMap (Rg g) L =
        (algebraMap (FractionRing R) L).comp (algebraMap (Rg g) (FractionRing R)) from
      IsLocalization.ringHom_ext (Submonoid.powers (g : R)) <| by
        ext r
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply R (Rg g) L,
          ← IsScalarTower.algebraMap_apply R (Rg g) (FractionRing R),
          ← IsScalarTower.algebraMap_apply R (FractionRing R) L]
  have : ∀ g : t', IsFractionRing (Rg g) (FractionRing R) := fun g ↦
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (g : R)) _ _
  have : ∀ g : t', IsJapanese (Rg g) := fun g ↦ h g (hts (Finset.mem_filter.mp g.2).1) (Rg g)
  have : ∀ g : t', IsLocalizedModule.Away (g : R) (integralClosureInclusion R (Rg g) L) :=
    fun g ↦ isLocalizedModule_integralClosureInclusion R _ (Rg g) L
  exact Module.Finite.of_localizationSpan_finite' t' ht'
    (fun g ↦ integralClosureInclusion R (Rg g) L)
    (fun g ↦ finite_integralClosure_of_isFractionRing (FractionRing R) L)

end IsJapanese

/-- A field is Japanese. -/
instance Field.isJapanese (K : Type u) [Field K] : IsJapanese K := by
  constructor
  intro L _ _ _ _ _
  have : Module.Finite K (FractionRing K) := .equiv (FractionRing.algEquiv K K).symm.toLinearEquiv
  have : Module.Finite K L := .trans (FractionRing K) L
  exact Module.Finite.of_injective (integralClosure K L).val.toLinearMap Subtype.val_injective

namespace IsUniversallyJapanese

variable {R : Type u} [CommRing R]

/-- A universally Japanese domain is Japanese. -/
instance isJapanese_self [IsUniversallyJapanese R] [IsDomain R] : IsJapanese R :=
  isJapanese (R := R) R

/-- Universally Japanese ascends along essentially finite type algebras. This is not an instance:
the conclusion does not determine `R`. -/
@[stacks 032S]
theorem of_essFiniteType (R : Type u) [CommRing R] [IsUniversallyJapanese R] (S : Type u)
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] : IsUniversallyJapanese S := by
  constructor
  intro T _ _ _ _
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.EssFiniteType R T := .comp R S T
  have : IsJapanese (Algebra.EssFiniteType.subalgebra R T) := isJapanese (R := R) _
  have := Algebra.EssFiniteType.isLocalization R T
  exact IsJapanese.of_isLocalization (Algebra.EssFiniteType.submonoid R T) T

/-- A domain essentially of finite type over a universally Japanese ring is Japanese. -/
theorem isJapanese_of_essFiniteType (R : Type u) [CommRing R] [IsUniversallyJapanese R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.EssFiniteType R S] :
    IsJapanese S :=
  have := of_essFiniteType R S
  inferInstance

/-- Universally Japanese is local on the ring. -/
@[stacks 032V "(1)"]
theorem of_span_eq_top (s : Set R) (hs : Ideal.span s = ⊤) (Rₚ : s → Type u)
    [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.1 (Rₚ g)]
    [∀ g, IsUniversallyJapanese (Rₚ g)] : IsUniversallyJapanese R := by
  constructor
  intro S _ _ _ _
  refine IsJapanese.of_span_eq_top (algebraMap R S '' s)
    (by rw [← Ideal.map_span, hs, Ideal.map_top]) ?_
  rintro _ ⟨g, hg, rfl⟩ Sg _ _ _ _
  have : IsLocalization.Away g (Rₚ ⟨g, hg⟩) :=
    inferInstanceAs (IsLocalization.Away (⟨g, hg⟩ : s).1 _)
  let : Algebra R Sg := ((algebraMap S Sg).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S Sg := .of_algebraMap_eq fun _ ↦ rfl
  have hu : IsUnit (algebraMap R Sg g) := IsLocalization.Away.algebraMap_isUnit (algebraMap R S g)
  let : Algebra (Rₚ ⟨g, hg⟩) Sg := (IsLocalization.Away.lift g hu).toAlgebra
  have : IsScalarTower R (Rₚ ⟨g, hg⟩) Sg := .of_algebraMap_eq fun r ↦
    (RingHom.congr_fun (IsLocalization.Away.lift_comp (S := Rₚ ⟨g, hg⟩) g hu) r).symm
  have : Algebra.EssFiniteType S Sg := .of_isLocalization Sg (Submonoid.powers (algebraMap R S g))
  have : Algebra.EssFiniteType R Sg := .comp R S Sg
  have : Algebra.EssFiniteType (Rₚ ⟨g, hg⟩) Sg := .of_comp R _ Sg
  exact isJapanese_of_essFiniteType (Rₚ ⟨g, hg⟩) Sg

end IsUniversallyJapanese

namespace IsNagataRing

variable {R : Type u} [CommRing R]

/-- The easy half of Nagata's theorem: a Noetherian universally Japanese ring is Nagata. The
converse is not proved here. -/
@[stacks 0334 "(3) ⇒ (1)"]
instance of_isUniversallyJapanese [IsNoetherianRing R] [IsUniversallyJapanese R] :
    IsNagataRing R :=
  ⟨inferInstance, fun p _ ↦ IsUniversallyJapanese.isJapanese (R := R) (R ⧸ p)⟩

/-- A localization of a Nagata ring is Nagata. -/
theorem of_isLocalization [IsNagataRing R] (M : Submonoid R) (S : Type u) [CommRing S]
    [Algebra R S] [IsLocalization M S] : IsNagataRing S := by
  have := isNoetherianRing (R := R)
  refine ⟨IsLocalization.isNoetherianRing M S this, fun q _ ↦ ?_⟩
  let p := q.comap (algebraMap R S)
  have hq : p.map (algebraMap R S) = q := IsLocalization.map_under M S q
  have : (p.map (algebraMap R S)).IsPrime := hq ▸ inferInstance
  have := isJapanese p
  have : IsJapanese (S ⧸ p.map (algebraMap R S)) :=
    IsJapanese.of_isLocalization (Algebra.algebraMapSubmonoid (R ⧸ p) M) _
  exact IsJapanese.of_ringEquiv (Ideal.quotEquivOfEq hq)

/-- A localization of a Nagata ring is Nagata. -/
@[stacks 032U]
instance localization [IsNagataRing R] (M : Submonoid R) : IsNagataRing (Localization M) :=
  of_isLocalization M _

/-- Being Nagata is local on the ring. -/
@[stacks 032V "(2)"]
theorem of_span_eq_top (s : Set R) (hs : Ideal.span s = ⊤) (Rₚ : s → Type u)
    [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.1 (Rₚ g)]
    [∀ g, IsNagataRing (Rₚ g)] : IsNagataRing R := by
  refine ⟨(isNoetherianRing_iff_ideal_fg R).mpr fun I ↦ Ideal.fg_of_localizationSpan s hs
    fun g ↦ ?_, fun p _ ↦ ?_⟩
  · have := isNoetherianRing (R := Rₚ g)
    have : IsNoetherianRing (Localization.Away g.1) := isNoetherianRing_of_ringEquiv (Rₚ g)
      (IsLocalization.algEquiv (Submonoid.powers g.1) (Rₚ g) (Localization.Away g.1)).toRingEquiv
    exact IsNoetherian.noetherian _
  refine IsJapanese.of_span_eq_top (Ideal.Quotient.mk p '' s)
    (by rw [← Ideal.map_span, hs, Ideal.map_top]) ?_
  rintro _ ⟨g, hg, rfl⟩ Dg _ _ _ _
  have : IsLocalization.Away g (Rₚ ⟨g, hg⟩) :=
    inferInstanceAs (IsLocalization.Away (⟨g, hg⟩ : s).1 _)
  have hgp : g ∉ p := by
    intro hgp
    have hz : Ideal.Quotient.mk p g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hgp
    have := IsLocalization.Away.algebraMap_isUnit (S := Dg) (Ideal.Quotient.mk p g)
    rw [hz, map_zero] at this
    exact not_isUnit_zero this
  have hdisj : Disjoint (Submonoid.powers g : Set R) p := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgp ((inferInstance : p.IsPrime).mem_of_pow_mem n hn)
  have : (p.map (algebraMap R (Rₚ ⟨g, hg⟩))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ p inferInstance hdisj
  have := isJapanese (R := Rₚ ⟨g, hg⟩) (p.map (algebraMap R (Rₚ ⟨g, hg⟩)))
  have hM : Algebra.algebraMapSubmonoid (R ⧸ p) (Submonoid.powers g) =
      Submonoid.powers (Ideal.Quotient.mk p g) :=
    Submonoid.map_powers _ g
  have : IsLocalization (Submonoid.powers (Ideal.Quotient.mk p g))
      (Rₚ ⟨g, hg⟩ ⧸ p.map (algebraMap R (Rₚ ⟨g, hg⟩))) := hM ▸ inferInstance
  exact IsJapanese.of_ringEquiv (IsLocalization.algEquiv
    (Submonoid.powers (Ideal.Quotient.mk p g))
    (Rₚ ⟨g, hg⟩ ⧸ p.map (algebraMap R (Rₚ ⟨g, hg⟩))) Dg).toRingEquiv

end IsNagataRing

namespace IsUniversallyJapanese

/-- A field of characteristic zero is universally Japanese. The proof uses Noether normalization
and the finiteness of integral closures in separable extensions, so it does not cover fields of
positive characteristic (Stacks 0335 (1)). -/
instance of_charZero (k : Type u) [Field k] [CharZero k] : IsUniversallyJapanese k := by
  constructor
  intro S _ _ _ _
  constructor
  intro L _ _ _ _ _
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k S
  let P := MvPolynomial (Fin n) k
  let : Algebra P S := g.toRingHom.toAlgebra
  have : Module.Finite P S := hfin
  have : FaithfulSMul P S := (faithfulSMul_iff_algebraMap_injective P S).mpr hg
  let E := FractionRing S
  let K := FractionRing P
  let : Algebra K E := FractionRing.liftAlgebra P E
  have : FiniteDimensional K E := .of_isLocalization P S P⁰
  let : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
  have : IsScalarTower K E L := .of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional K L := Module.Finite.trans E L
  let : Algebra P L := ((algebraMap S L).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S L := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower P K L := .of_algebraMap_eq fun x ↦ by
    change _ = algebraMap E L (algebraMap K E (algebraMap P K x))
    rw [← IsScalarTower.algebraMap_apply P K E, IsScalarTower.algebraMap_apply P S E,
      ← IsScalarTower.algebraMap_apply S E L]
    rfl
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have := IsIntegralClosure.finite P K L (integralClosure P L)
  have : Module.Finite P (integralClosure S L) :=
    Module.Finite.of_surjective (integralClosureInclusion P S L) fun y ↦
      ⟨⟨y, isIntegral_trans (R := P) (y : L) y.2⟩, rfl⟩
  exact Module.Finite.of_restrictScalars_finite P S _

end IsUniversallyJapanese

section Domination

open IsLocalRing

variable {L : Type u} [Field L]

/-- A subring of a field that contains a subring with fraction field `L` has fraction field `L`. -/
private theorem isFractionRing_of_subring_le {D B : Subring L} (h : D ≤ B)
    [IsFractionRing D L] : IsFractionRing B L where
  map_units b := IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  surj z := by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj D⁰ z
    refine ⟨⟨Subring.inclusion h x,
      ⟨Subring.inclusion h y, mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_⟩⟩, hxy⟩
    exact nonZeroDivisors.coe_ne_zero y (Subtype.ext (congr_arg (fun b : B ↦ (b : L)) h0))
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-- A subring of a field that generates it as a field has the field as fraction field. -/
private theorem isFractionRing_of_closure_eq_top (D : Subring L)
    (hD : Subfield.closure (D : Set L) = ⊤) : IsFractionRing D L where
  map_units b := IsUnit.mk0 _ fun h0 ↦ nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  surj z := by
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Subfield.mem_closure_iff.mp (by rw [hD]; exact Subfield.mem_top z)
    rw [Subring.closure_eq] at hx hy
    by_cases hy0 : y = 0
    · exact ⟨⟨0, 1⟩, by simp [hy0]⟩
    · refine ⟨⟨⟨x, hx⟩, ⟨⟨y, hy⟩, mem_nonZeroDivisors_of_ne_zero fun h ↦
        hy0 (congr_arg Subtype.val h)⟩⟩, ?_⟩
      show x / y * y = x
      exact div_mul_cancel₀ x hy0
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-- A subfield of a finitely generated field extension of `K` that contains `K` and the chosen
generators is everything. -/
private theorem eq_top_of_essFiniteType (K : Type*) [Field K] [Algebra K L]
    [Algebra.EssFiniteType K L] (F : Subfield L) (hK : ∀ k, algebraMap K L k ∈ F)
    (hs : (Algebra.EssFiniteType.finset K L : Set L) ⊆ F) : F = ⊤ := by
  have hsub : Algebra.EssFiniteType.subalgebra K L ≤ (F.toIntermediateField hK).toSubalgebra :=
    Algebra.adjoin_le hs
  rw [eq_top_iff]
  intro l _
  obtain ⟨⟨x, y⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.EssFiniteType.submonoid K L) l
  have h1 := IsLocalization.mk'_spec L x y
  rw [← eq_div_iff (IsLocalization.map_units L y).ne_zero] at h1
  change IsLocalization.mk' L x y ∈ F
  rw [h1]
  exact div_mem (hsub x.2) (hsub (y : Algebra.EssFiniteType.subalgebra K L).2)

/-- BLMNPS Lemma 11.15 for local subrings: a Noetherian, universally Japanese local subring of `L`
that is not a field, and that together with finitely many elements generates `L` as a field, is
dominated by a discrete valuation ring with fraction field `L`, essentially of finite type over
it. -/
private theorem exists_dvr_le_of_closure_eq_top (A : LocalSubring L)
    [IsNoetherianRing A.toSubring] [IsUniversallyJapanese A.toSubring]
    (hA : ¬ IsField A.toSubring) (s : Finset L)
    (hs : Subfield.closure ((A.toSubring : Set L) ∪ s) = ⊤) :
    ∃ (R : LocalSubring L) (h : A ≤ R), IsDiscreteValuationRing R.toSubring ∧
      IsFractionRing R.toSubring L ∧
        (Subring.inclusion (LocalSubring.toSubring_mono h)).EssFiniteType := by
  classical
  obtain ⟨V, hAW⟩ := A.exists_le_valuationSubring
  set W := V.toLocalSubring
  -- A finitely generated `A`-subalgebra `D ⊆ V` with fraction field `L`.
  let zs : Finset L := s.image fun z ↦ if z ∈ V then z else z⁻¹
  let D : Subalgebra A.toSubring L := Algebra.adjoin A.toSubring (zs : Set L)
  have hAD : A.toSubring ≤ D.toSubring := fun a ha ↦
    D.algebraMap_mem (⟨a, ha⟩ : A.toSubring)
  have hDW : D.toSubring ≤ W.toSubring := by
    rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | hz)
    · exact LocalSubring.toSubring_mono hAW a.2
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hz
      split_ifs with h
      · exact h
      · exact (V.mem_or_inv_mem z).resolve_left h
  have hD : Subfield.closure (D.toSubring : Set L) = ⊤ := by
    rw [eq_top_iff, ← hs, Subfield.closure_le]
    rintro z (hz | hz)
    · exact Subfield.subset_closure (hAD hz)
    · by_cases hzV : z ∈ V
      · exact Subfield.subset_closure
          (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨z, hz, ite_eq_left hzV⟩))
      · have : z⁻¹ ∈ Subfield.closure (D.toSubring : Set L) := Subfield.subset_closure
          (Algebra.subset_adjoin (Finset.mem_image.mpr ⟨z, hz, ite_eq_right hzV⟩))
        simpa using inv_mem this
  have : IsFractionRing D.toSubring L := isFractionRing_of_closure_eq_top _ hD
  have : Algebra.FiniteType A.toSubring D :=
    (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_adjoin_finset zs)
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A.toSubring D
  have : IsNoetherianRing D.toSubring := ‹IsNoetherianRing D›
  -- Its localization `Dp` at the centre of `V`.
  let p : Ideal D.toSubring := (maximalIdeal W.toSubring).comap (Subring.inclusion hDW)
  let Dp := LocalSubring.ofPrime D.toSubring p
  have hDDp : D.toSubring ≤ Dp.toSubring := LocalSubring.le_ofPrime _ _
  have : IsNoetherianRing Dp.toSubring := IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  obtain ⟨hAW', hAWloc⟩ := hAW
  have hADp : A ≤ Dp := by
    refine ⟨hAD.trans hDDp, ⟨fun a ha ↦ ?_⟩⟩
    by_contra hna
    have hp : Subring.inclusion hAD a ∈ p :=
      (mem_maximalIdeal _).mpr fun h ↦ hna (isUnit_of_map_unit (Subring.inclusion hAW') a h)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Dp.toSubring p _).mp ha hp
  have hDpf : ¬ IsField Dp.toSubring := by
    intro hF
    let := hF.toField
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp ((isField_iff_maximalIdeal_eq).not.mp hA)
    obtain ⟨hADp', hADploc⟩ := hADp
    have : IsUnit (Subring.inclusion hADp' a) :=
      isUnit_iff_ne_zero.mpr fun h ↦
        ha0 (Subtype.ext (congr_arg (fun x : Dp.toSubring ↦ (x : L)) h))
    exact (mem_maximalIdeal a).mp ha (isUnit_of_map_unit _ a this)
  -- Stacks 00P8 gives a one-dimensional Noetherian local `B` dominating `Dp`.
  obtain ⟨B, hDpB, hBN, hBdim, hBeft⟩ := Dp.exists_le_ringKrullDim_eq_one hDpf
  have hAB : A.toSubring ≤ B.toSubring :=
    (hAD.trans hDDp).trans (LocalSubring.toSubring_mono hDpB)
  have hADeft : (Subring.inclusion hAD).EssFiniteType :=
    (RingHom.finiteType_algebraMap.mpr ‹Algebra.FiniteType A.toSubring D›).essFiniteType
  have hDDpeft : (Subring.inclusion hDDp).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (.of_isLocalization _ p.primeCompl)
  have hABeft : (Subring.inclusion hAB).EssFiniteType := (hADeft.comp hDDpeft).comp hBeft
  let : Algebra A.toSubring B.toSubring := (Subring.inclusion hAB).toAlgebra
  have : Algebra.EssFiniteType A.toSubring B.toSubring := hABeft
  have : IsUniversallyJapanese B.toSubring := .of_essFiniteType A.toSubring B.toSubring
  -- The normalization `C` of `B` is a Dedekind domain, finite over `B`.
  have : IsFractionRing B.toSubring L :=
    isFractionRing_of_subring_le (hDDp.trans (LocalSubring.toSubring_mono hDpB))
  let C := integralClosure B.toSubring L
  have hC : Module.Finite B.toSubring C :=
    IsJapanese.finite_integralClosure_of_isFractionRing L L
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing B.toSubring C
  have : Ring.DimensionLEOne B.toSubring := ⟨fun {q} hq hqp ↦
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
      (Ring.krullDimLE_iff.mpr (by rw [hBdim]; rfl)) q hq hqp⟩
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension L
  have : IsFractionRing C L :=
    integralClosure.isFractionRing_of_finite_extension (A := B.toSubring) L L
  have : IsDedekindDomain C := (isDedekindDomain_iff C L).mpr ⟨inferInstance, inferInstance,
    inferInstance, fun hx ↦ (isIntegrallyClosed_iff L).mp inferInstance hx⟩
  have hmB : maximalIdeal B.toSubring ≠ ⊥ := fun h ↦ by
    have := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h)
    rw [hBdim] at this
    exact one_ne_zero this
  have hBCinj : Function.Injective (algebraMap B.toSubring C) := fun x y h ↦
    Subtype.ext (congr_arg (fun c : C ↦ (c : L)) h)
  obtain ⟨n, hn, hnB⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (maximalIdeal B.toSubring)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hBCinj]; exact bot_le)
  have hn0 : n ≠ ⊥ := by
    rintro rfl
    apply hmB
    rw [← hnB, Ideal.under, Ideal.comap_bot_of_injective _ hBCinj]
  -- The localization of `C` at a maximal ideal over that of `B`.
  let C₀ : Subring L := C.toSubring
  let n₀ : Ideal C₀ := n
  have : n₀.IsPrime := hn.isPrime
  have hn₀ : n₀ ≠ ⊥ := hn0
  let R := LocalSubring.ofPrime C₀ n₀
  have : IsDedekindDomain C₀ := inferInstanceAs (IsDedekindDomain C)
  have : IsFractionRing C₀ L := inferInstanceAs (IsFractionRing C L)
  have hdvr : IsDiscreteValuationRing R.toSubring :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (A := C₀) hn₀ R.toSubring
  have hfr : IsFractionRing R.toSubring L :=
    isFractionRing_of_subring_le (LocalSubring.le_ofPrime C₀ n₀)
  have hBC : B.toSubring ≤ C₀ := fun b hb ↦ C.algebraMap_mem (⟨b, hb⟩ : B.toSubring)
  have hC₀R : C₀ ≤ R.toSubring := LocalSubring.le_ofPrime C₀ n₀
  have hBR : B ≤ R := by
    refine ⟨hBC.trans hC₀R, ⟨fun b hb ↦ ?_⟩⟩
    by_contra hnb
    have hbn : Subring.inclusion hBC b ∈ n₀ := by
      have : b ∈ n.under B.toSubring := hnB ▸ (mem_maximalIdeal b).mpr hnb
      exact this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff R.toSubring n₀ _).mp hb hbn
  have hBCeft : (Subring.inclusion hBC).EssFiniteType :=
    (RingHom.finite_algebraMap.mpr hC).finiteType.essFiniteType
  have hC₀Reft : (Subring.inclusion hC₀R).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (.of_isLocalization _ n₀.primeCompl)
  exact ⟨R, hADp.trans (hDpB.trans hBR), hdvr, hfr, hABeft.comp (hBCeft.comp hC₀Reft)⟩

/-- **BLMNPS Lemma 11.15**, universally Japanese form. Let `A` be a Noetherian, universally
Japanese local domain that is not a field, with fraction field `K`, and let `L` be a finitely
generated field extension of `K`. Then a discrete valuation ring with fraction field `L` dominates
`A` and is essentially of finite type over it.

BLMNPS (arXiv:1902.08184v4, §11.4) assume `A` Nagata, which by their Lemma 11.13 (Stacks 0334)
is equivalent to `A` being Noetherian and universally Japanese. Only the easy direction is proved
here, so the latter is assumed. -/
theorem exists_dvr_dominating_essFiniteType {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsUniversallyJapanese A] (hA : ¬ IsField A)
    (K : Type*) (L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.EssFiniteType K L] :
    ∃ (R : LocalSubring L) (h : LocalSubring.range (algebraMap A L) ≤ R),
      IsDiscreteValuationRing R.toSubring ∧ IsFractionRing R.toSubring L ∧
        ((algebraMap A L).codRestrict R.toSubring
          fun a ↦ LocalSubring.toSubring_mono h ⟨a, rfl⟩).EssFiniteType := by
  have hf : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let A' := LocalSubring.range (algebraMap A L)
  let e : A ≃+* A'.toSubring := RingEquiv.ofBijective
    ((algebraMap A L).codRestrict A'.toSubring fun a ↦ ⟨a, rfl⟩)
    ⟨fun a b h ↦ hf (congr_arg Subtype.val h), fun ⟨_, a, rfl⟩ ↦ ⟨a, rfl⟩⟩
  have : IsNoetherianRing A'.toSubring := isNoetherianRing_of_ringEquiv A e
  let : Algebra A A'.toSubring := e.toRingHom.toAlgebra
  have he : e.toRingHom.FiniteType := .of_surjective _ e.surjective
  have : Algebra.EssFiniteType A A'.toSubring := he.essFiniteType
  have : IsUniversallyJapanese A'.toSubring := .of_essFiniteType A _
  have hA' : ¬ IsField A'.toSubring := fun h ↦ hA (MulEquiv.isField h e.toMulEquiv)
  have hs :
      Subfield.closure ((A'.toSubring : Set L) ∪ Algebra.EssFiniteType.finset K L) = ⊤ := by
    refine eq_top_of_essFiniteType K _ (fun k ↦ ?_)
      (Set.subset_union_right.trans Subfield.subset_closure)
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  obtain ⟨R, hR, hdvr, hfr, heft⟩ := exists_dvr_le_of_closure_eq_top A' hA' _ hs
  refine ⟨R, hR, hdvr, hfr, ?_⟩
  exact he.essFiniteType.comp heft

end Domination
