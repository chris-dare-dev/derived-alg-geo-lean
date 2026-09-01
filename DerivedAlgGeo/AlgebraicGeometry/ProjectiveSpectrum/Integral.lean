/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.HomogeneousLocalizationDomain
import DerivedAlgGeo.Topology.IrreducibleCover
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Properties

/-!
# `Proj` of a graded domain is integral

A scheme is integral when it is irreducible and reduced, and both halves of that for `Proj 𝒜`
come from the standard affine charts `D₊(f) ≅ Spec (A_f)₀`:

* every `(A_f)₀` is reduced -- a domain away from a nonzero `f`, and the zero ring away from
  `0` -- so `Proj 𝒜` is reduced on an affine cover;
* away from a nonzero `f` the chart is the spectrum of a domain, hence irreducible, and two
  charts meet because `D₊(f) ⊓ D₊(g) = D₊(fg)` with `fg ≠ 0`.

Mathlib proves `Spec` of a domain is integral and provides the affine charts of `Proj`, but does
not record integrality of `Proj` itself.
-/

universe u

open CategoryTheory TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsDomain A]

/-- Every standard affine chart of `Proj` of a graded domain is reduced. -/
instance isReduced_spec_away (f : A) :
    IsReduced (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) := by
  haveI : _root_.IsReduced (HomogeneousLocalization.Away 𝒜 f) :=
    HomogeneousLocalization.Away.isReduced 𝒜 f
  infer_instance

/-- `Proj` of a graded domain is reduced. -/
instance isReduced : IsReduced (Proj 𝒜) := by
  haveI : ∀ i, IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := fun i ↦
    isReduced_spec_away 𝒜 _
  exact IsReduced.of_openCover (X := Proj 𝒜) (Proj.affineOpenCover 𝒜).openCover

/-- The chart at a nonzero homogeneous element of positive degree is the spectrum of a domain. -/
lemma isDomain_away {f : A} (hf : f ≠ 0) :
    IsDomain (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)) := by
  haveI := HomogeneousLocalization.Away.nontrivial 𝒜 hf
  exact HomogeneousLocalization.Away.isDomain 𝒜 hf

/-- A basic open of `Proj` at a nonzero homogeneous element of positive degree is the range of
the corresponding chart, hence preirreducible. -/
lemma isPreirreducible_basicOpen {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : f ≠ 0) :
    IsPreirreducible (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)) := by
  haveI := isDomain_away 𝒜 hf
  have h : IsPreirreducible
      (Set.range (Proj.awayι 𝒜 f f_deg hm).base) := by
    have := (IrreducibleSpace.isIrreducible_univ
      (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)))).isPreirreducible.image
        (Proj.awayι 𝒜 f f_deg hm).base
        (Proj.awayι 𝒜 f f_deg hm).continuous.continuousOn
    rwa [Set.image_univ] at this
  have hrange : Set.range (Proj.awayι 𝒜 f f_deg hm).base =
      (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)) :=
    congrArg (fun V : (Proj 𝒜).Opens ↦ (V : Set (Proj 𝒜)))
      (Proj.opensRange_awayι 𝒜 f f_deg hm)
  rwa [hrange] at h

/-- A basic open of `Proj` at a nonzero homogeneous element of positive degree is nonempty.

This is what makes two charts meet, and it is where the domain hypothesis is used a second time:
the chart ring is nontrivial exactly because the element is not nilpotent. -/
lemma basicOpen_nonempty {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (hf : f ≠ 0) :
    (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)).Nonempty := by
  haveI := HomogeneousLocalization.Away.nontrivial 𝒜 hf
  haveI : Nonempty (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 f)))
  obtain ⟨y⟩ := ‹Nonempty (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)))›
  refine ⟨(Proj.awayι 𝒜 f f_deg hm).base y, ?_⟩
  have hrange : Set.range (Proj.awayι 𝒜 f f_deg hm).base =
      (Proj.basicOpen 𝒜 f : Set (Proj 𝒜)) :=
    congrArg (fun V : (Proj 𝒜).Opens ↦ (V : Set (Proj 𝒜)))
      (Proj.opensRange_awayι 𝒜 f f_deg hm)
  exact hrange ▸ Set.mem_range_self y

/-- `Proj` of a graded domain is irreducible, as soon as it is nonempty.

The charts at nonzero homogeneous elements of positive degree are irreducible, they still cover
-- a chart at zero is empty, so it can be discarded -- and any two of them meet, because
`D₊(f) ⊓ D₊(g) = D₊(fg)` and a product of nonzero elements of a domain is nonzero. -/
theorem irreducibleSpace [Nonempty (Proj 𝒜)] : IrreducibleSpace (Proj 𝒜) := by
  refine TopologicalSpace.irreducibleSpace_of_cover
    (ind := { fm : Σ m : ℕ+, 𝒜 (m : ℕ) // ((fm.2 : A) ≠ 0) })
    (fun i ↦ (Proj.basicOpen 𝒜 (i.1.2 : A) : Set (Proj 𝒜)))
    (fun i ↦ (Proj.basicOpen 𝒜 (i.1.2 : A)).isOpen) (fun x ↦ ?_)
    (fun i ↦ isPreirreducible_basicOpen 𝒜 (i.1.2).2 i.1.1.2 i.2) (fun i j ↦ ?_)
  · -- the charts at nonzero elements still cover
    obtain ⟨i, hi⟩ : ∃ i, x ∈ Set.range ((Proj.affineOpenCover 𝒜).f i).base :=
      ⟨_, (Proj.affineOpenCover 𝒜).covers x⟩
    have hmem : x ∈ (Proj.basicOpen 𝒜 (i.2 : A) : Set (Proj 𝒜)) := by
      have hrange : Set.range ((Proj.affineOpenCover 𝒜).f i).base =
          (Proj.basicOpen 𝒜 (i.2 : A) : Set (Proj 𝒜)) :=
        congrArg (fun V : (Proj 𝒜).Opens ↦ (V : Set (Proj 𝒜)))
          (Proj.opensRange_awayι 𝒜 (i.2 : A) (i.2).2 i.1.2)
      exact hrange ▸ hi
    have hne : (i.2 : A) ≠ 0 := by
      rintro h
      rw [h] at hmem
      simp only [Proj.basicOpen_zero] at hmem
      exact hmem
    exact ⟨⟨i, hne⟩, hmem⟩
  · -- two such charts meet
    have hdeg : ((i.1.2 : A) * (j.1.2 : A)) ∈ 𝒜 ((i.1.1 : ℕ) + (j.1.1 : ℕ)) :=
      SetLike.mul_mem_graded (i.1.2).2 (j.1.2).2
    have hne : ((i.1.2 : A) * (j.1.2 : A)) ≠ 0 := mul_ne_zero i.2 j.2
    have hpos : 0 < (i.1.1 : ℕ) + (j.1.1 : ℕ) := Nat.add_pos_left i.1.1.2 _
    have h := basicOpen_nonempty 𝒜 hdeg hpos hne
    rwa [Proj.basicOpen_mul] at h

/-- **`Proj` of a graded domain is an integral scheme**, as soon as it is nonempty. -/
theorem isIntegral [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) := by
  haveI := irreducibleSpace 𝒜
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Proj
