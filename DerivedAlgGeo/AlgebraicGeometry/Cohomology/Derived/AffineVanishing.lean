/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Equivalence
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.AffineBasisComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.GlobalComparison

/-!
# The affine derived-vanishing comparison

The explicit affine calculation proves that the module-valued Čech complex of `M~` on a finite
standard distinguished-open cover is exact in every positive degree. This file transfers that
calculation to Mathlib's derived cohomology `Sheaf.H` and transports the result across the affine
module-sheaf comparison.

The comparison is obtained non-circularly from the compact distinguished-open basis and the
basis/cofinal-cover criterion of Stacks Project, Lemma 20.11.9 (Tag 01EW). In particular, the
positive comparison witness below does not assume that the same cover is already Leray-acyclic.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Cohomology

/-- The underlying abelian sheaf of the module sheaf associated to an affine module. This is the
object to which Mathlib's `Sheaf.H` applies. -/
noncomputable abbrev underlyingTildeSheaf {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :=
  (Scheme.Modules.toSheaf (Spec R)).obj (tilde M)

/-- The explicit module-valued Čech complex used by the affine localization calculation. -/
noncomputable abbrev affineTildeCechComplex
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R) :=
  (cechComplexFunctor fun i ↦ _root_.PrimeSpectrum.basicOpen (f i)).obj
    (modulesSpecToSheaf.obj (tilde M)).presheaf

/-- A degreewise comparison between the explicit module-valued affine Cech complex and derived
cohomology. -/
def AffineTildeCechDerivedComparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R) (k : ℕ)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] : Prop :=
  Nonempty (((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) ≃+
    (underlyingTildeSheaf M).H k)

/-- Degreewise comparison between the explicit affine Čech complex and derived cohomology. -/
def AffineTildeCechDerivedComparison
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (M : ModuleCat.{u} R)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] : Prop :=
  ∀ k, AffineTildeCechDerivedComparisonAt f M k

set_option maxHeartbeats 200000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The compact distinguished-open basis supplies the positive-degree affine comparison witness
without assuming derived acyclicity of the chosen cover. -/
theorem affineTildeCechDerivedComparisonAt_of_pos
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    [hExt : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] :
    AffineTildeCechDerivedComparisonAt f M k := by
  have hexact : (affineTildeCechComplex f M).ExactAt k :=
    tilde_cechComplex_exactAt_of_pos f hf M k hk
  have hzero : IsZero ((affineTildeCechComplex f M).homology k) :=
    hexact.isZero_homology
  letI : Subsingleton
      ((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((underlyingTildeSheaf M).H k) :=
    @CategoryTheory.Sheaf.H_subsingleton_of_isCechAcyclicOnCompactBasis
      (Spec R)
      (affineBasicOpenBasis R) (underlyingTildeSheaf M)
      (underlyingTilde_isCechAcyclicOnCompactBasis M) hExt
      (top_mem_affineBasicOpenBasis R) k hk
  letI : Inhabited
      ((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) := ⟨0⟩
  letI : Inhabited ((underlyingTildeSheaf M).H k) := ⟨0⟩
  letI : Unique
      ((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) :=
    Unique.mk' _
  letI : Unique ((underlyingTildeSheaf M).H k) := Unique.mk' _
  exact ⟨AddEquiv.ofUnique⟩

/-- Positive exactness of the standard affine Čech complex kills `Sheaf.H` once the comparison
with that explicit complex is available. -/
theorem tilde_H_subsingleton_of_comparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton ((underlyingTildeSheaf M).H k) := by
  have hexact : (affineTildeCechComplex f M).ExactAt k :=
    tilde_cechComplex_exactAt_of_pos f hf M k hk
  have hzero : IsZero ((affineTildeCechComplex f M).homology k) :=
    hexact.isZero_homology
  letI : Subsingleton
      ((affineTildeCechComplex f M).homology k : ModuleCat.{u} R) :=
    ModuleCat.subsingleton_of_isZero hzero
  let e := hcomparison.some
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

/-- All-degree comparison gives affine derived vanishing in every positive degree. -/
theorem tilde_H_subsingleton_of_comparison
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparison f M)
    (k : ℕ) (hk : 0 < k) : Subsingleton ((underlyingTildeSheaf M).H k) :=
  tilde_H_subsingleton_of_comparisonAt f hf M k hk (hcomparison k)

/-- The lower-level comparison-dependent form of transport across an isomorphism of underlying
abelian sheaves. -/
theorem H_subsingleton_of_iso_tilde_of_comparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R)
    (F : Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})
    (e : F ≅ underlyingTildeSheaf M) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton (F.H k) := by
  have hsub : Subsingleton ((underlyingTildeSheaf M).H k) :=
    tilde_H_subsingleton_of_comparisonAt f hf M k hk hcomparison
  let eH := (Sheaf.functorH (Opens.grothendieckTopology (Spec R)) k).mapIso e
  let eA := eH.addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ eA.injective (hsub.elim _ _)⟩

/-- The lower-level comparison-dependent form of transport for module sheaves identified with
`M~`. -/
theorem modules_H_subsingleton_of_iso_tilde_of_comparisonAt
    {R : CommRingCat.{u}} {ι : Type u} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : ModuleCat.{u} R) (G : (Spec R).Modules) (e : G ≅ tilde M)
    (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})]
    (hcomparison : AffineTildeCechDerivedComparisonAt f M k) :
    Subsingleton (((Scheme.Modules.toSheaf (Spec R)).obj G).H k) :=
  H_subsingleton_of_iso_tilde_of_comparisonAt f hf M _
    ((Scheme.Modules.toSheaf (Spec R)).mapIso e) k hk hcomparison

set_option maxHeartbeats 200000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Affine vanishing for a module sheaf associated to a module.**

For every positive degree, the derived cohomology of `M~` on `Spec R` is trivial. No
noetherian hypothesis is needed. -/
theorem tilde_H_subsingleton
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    [hExt : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] :
    Subsingleton ((underlyingTildeSheaf M).H k) :=
  @CategoryTheory.Sheaf.H_subsingleton_of_isCechAcyclicOnCompactBasis
    (Spec R)
    (affineBasicOpenBasis R) (underlyingTildeSheaf M)
    (underlyingTilde_isCechAcyclicOnCompactBasis M) hExt
    (top_mem_affineBasicOpenBasis R) k hk

/-- Affine derived vanishing transports across an isomorphism of underlying abelian sheaves. -/
theorem H_subsingleton_of_iso_tilde
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (F : Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})
    (e : F ≅ underlyingTildeSheaf M) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] :
    Subsingleton (F.H k) := by
  have hsub : Subsingleton ((underlyingTildeSheaf M).H k) :=
    tilde_H_subsingleton M k hk
  let eH := (Sheaf.functorH (Opens.grothendieckTopology (Spec R)) k).mapIso e
  let eA := eH.addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ eA.injective (hsub.elim _ _)⟩

/-- Module sheaves identified with `M~` inherit unconditional affine derived vanishing. -/
theorem modules_H_subsingleton_of_iso_tilde
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (G : (Spec R).Modules) (e : G ≅ tilde M) (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] :
    Subsingleton (((Scheme.Modules.toSheaf (Spec R)).obj G).H k) :=
  H_subsingleton_of_iso_tilde M _
    ((Scheme.Modules.toSheaf (Spec R)).mapIso e) k hk

/-- **Affine vanishing for quasi-coherent module sheaves.**

Every quasi-coherent module sheaf on `Spec R` has trivial positive derived cohomology. The
affine comparison identifies it with the tilde sheaf of its global sections, so neither a
chosen presentation nor a noetherian hypothesis is required. -/
theorem modules_H_subsingleton_of_isQuasicoherent
    {R : CommRingCat.{u}} (G : (Spec R).Modules) [G.IsQuasicoherent]
    (k : ℕ) (hk : 0 < k)
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u})] :
    Subsingleton (((Scheme.Modules.toSheaf (Spec R)).obj G).H k) := by
  letI : IsIso G.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  exact modules_H_subsingleton_of_iso_tilde
    (moduleSpecΓFunctor.obj G) G (asIso G.fromTildeΓ).symm k hk

end AlgebraicGeometry.Cohomology
