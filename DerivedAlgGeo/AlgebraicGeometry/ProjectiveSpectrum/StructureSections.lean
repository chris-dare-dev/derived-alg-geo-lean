/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpaceVariety

/-!
# The global function attached to a degree-zero element

`Proj.toSpecZero` makes `Proj 𝒜` a scheme over `Spec (𝒜 0)`, so every degree-zero element of the
graded ring becomes a global function. This file computes that function: **it is the constant.**
At every point its value is `a / 1` in the homogeneous localization there, which is
`HomogeneousLocalization.fromZeroRingHom`.

## Why it is not immediate

`toSpecZero` is not defined pointwise. It is built from `basicOpenToSpec 𝒜 1` through three
transports — `Scheme.topIso`, `Scheme.isoOfEq` along `basicOpen 𝒜 1 = ⊤`, and
`Scheme.Opens.topIso` — none of which is the identity on the nose, and the whole thing is stated
against `Spec (𝒜 0)` rather than against sections. So the computation has three steps:

* `toSpecZero_appTop_eq` peels the `Spec` side. `ΓSpecIso_inv_naturality` cancels the spectrum
  against the ring map and `basicOpenToSpec_app_top` exposes `awayToSection`, which *is* pointwise
  by construction;
* `toSpecZero_transport_eq` collapses the three transports into a single presheaf restriction. The
  three composed scheme morphisms are the identity of `Proj 𝒜` — the same observation Mathlib's own
  `awayι_toSpecZero` proof makes — and cancelling the resulting restriction against its inverse
  leaves the `eqToHom` for `basicOpen 𝒜 1 = ⊤`;
* `openToLocalization_toSpecZero_appTop` then evaluates, and by that point everything is
  definitional: `openToLocalization` is literally `s.1 ⟨x, hx⟩`, presheaf restriction is
  restriction of the function, and `awayToSection` was pointwise all along.

## What it is for

The base-field action on cohomology (`varietyScalarAction`) is multiplication by the global
function attached to a scalar, and it acts on the sections of an associated sheaf *pointwise* on
fibers. So identifying that action with scalar multiplication on the graded localizations comes
down to exactly this lemma. It is the bridge #666 needs between the `k`-action the Čech lane can
compute with and the one `module_finite_linearCoherentH_of_cech` consumes.

`Fintype ι` and the polynomial grading play no part: this is a statement about an arbitrary
`ℕ`-graded ring.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace AlgebraicGeometry.Proj

/-- **The `Spec` side, peeled.** The ring map `𝒜 0 → Γ(Proj 𝒜, ⊤)` induced by the structure
morphism is `fromZeroRingHom` followed by `awayToSection` at `f = 1`, transported back to `⊤`.
`awayToSection` is pointwise by construction, which is the whole point of getting here. -/
theorem toSpecZero_appTop_eq :
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appTop) =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers 1)) ≫
        Proj.awayToSection 𝒜 1 ≫ (Proj.basicOpen 𝒜 1).topIso.inv ≫
        ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv.appTop ≫ (Proj 𝒜).topIso.inv.appTop := by
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc, Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]

/-- **The three transports collapse to one restriction.** `Scheme.topIso`, the `isoOfEq` along
`basicOpen 𝒜 1 = ⊤` and `Scheme.Opens.topIso` compose to the identity of `Proj 𝒜`, so on sections
they compose to the presheaf restriction that equality induces. -/
theorem toSpecZero_transport_eq :
    ((Proj.basicOpen 𝒜 1).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv.appTop ≫ (Proj 𝒜).topIso.inv.appTop) =
      (Proj 𝒜).presheaf.map (eqToHom (Proj.basicOpen_one 𝒜).symm).op := by
  have hid : (Proj 𝒜).topIso.inv ≫ ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ≫
      (Proj.basicOpen 𝒜 1).ι = 𝟙 (Proj 𝒜) := by
    have h : ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ≫ (Proj.basicOpen 𝒜 1).ι
        = (⊤ : (Proj 𝒜).Opens).ι := by simp
    rw [h]; exact Scheme.toIso_inv_ι _
  have happ := congrArg Scheme.Hom.appTop hid
  simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at happ
  have hι : (Proj.basicOpen 𝒜 1).ι.appTop =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 1 ≤ ⊤)).op ≫
        (Proj.basicOpen 𝒜 1).topIso.inv := rfl
  rw [hι, Category.assoc, Category.assoc] at happ
  have hsub : (Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 1 ≤ ⊤)).op =
      (Proj 𝒜).presheaf.map (eqToHom (Proj.basicOpen_one 𝒜)).op :=
    congrArg (fun m => (Proj 𝒜).presheaf.map (Quiver.Hom.op m)) (Subsingleton.elim _ _)
  rw [hsub] at happ
  have hinv : (Proj 𝒜).presheaf.map (eqToHom (Proj.basicOpen_one 𝒜)).op ≫
      (Proj 𝒜).presheaf.map (eqToHom (Proj.basicOpen_one 𝒜).symm).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
    exact (Proj 𝒜).presheaf.map_id _
  haveI : IsIso ((Proj 𝒜).presheaf.map (eqToHom (Proj.basicOpen_one 𝒜)).op) := inferInstance
  exact (cancel_epi _).mp (happ.trans hinv.symm)

/-- Evaluating a section at a point commutes with restriction: both are `s.1 ⟨x, _⟩`. -/
theorem openToLocalization_presheaf_map (U V : Opens (ProjectiveSpectrum.top 𝒜)) (i : U ⟶ V)
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (Proj 𝒜).presheaf.obj (op V)) :
    (openToLocalization 𝒜 U x hx).hom ((Proj 𝒜).presheaf.map i.op s) =
      (openToLocalization 𝒜 V x (i.le hx)).hom s := rfl

/-- **A degree-zero element becomes the constant function.** The global function the structure
morphism attaches to `a : 𝒜 0` has value `a / 1` at every point.

This is what makes the base-field action on cohomology computable: `varietyScalarAction` is
multiplication by such a function, and it acts on sections of an associated sheaf pointwise. -/
theorem openToLocalization_toSpecZero_appTop (a : 𝒜 0) (x : ProjectiveSpectrum.top 𝒜) :
    (openToLocalization 𝒜 ⊤ x trivial).hom
        (((Scheme.ΓSpecIso (CommRingCat.of ↥(𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appTop).hom a) =
      HomogeneousLocalization.fromZeroRingHom 𝒜 _ a := by
  rw [toSpecZero_appTop_eq, toSpecZero_transport_eq]
  rfl

end AlgebraicGeometry.Proj
