/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Basic
import DerivedAlgGeo.Topology.Sheaves.Cech.Boundedness
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Cohomological boundedness from a finite affine cover

The generic finite-cover boundedness theorem is applied to a compact scheme
using affine vanishing and affine intersections.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Cohomology

variable {X : Scheme.{u}}

private lemma image_pi_of_isOpenImmersion {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] {I : Type*} [Fintype I] [Nonempty I] (V : I → Y.Opens) :
    f ''ᵁ (∏ᶜ V) = ∏ᶜ (fun i ↦ f ''ᵁ V i) := by
  apply le_antisymm
  · apply leOfHom
    apply Pi.lift
    intro i
    exact homOfLE (f.image_mono (leOfHom (Pi.π V i)))
  · let i₀ : I := Classical.choice inferInstance
    have hRange : (∏ᶜ fun i ↦ f ''ᵁ V i) ≤ f.opensRange :=
      (leOfHom (Pi.π (fun i ↦ f ''ᵁ V i) i₀)).trans
        (f.image_le_opensRange (V i₀))
    rw [← inf_eq_right.mpr hRange, ← f.image_preimage_eq_opensRange_inf]
    apply f.image_mono
    apply leOfHom
    apply Pi.lift
    intro i
    apply homOfLE
    rw [← f.preimage_image_eq (V i)]
    exact f.preimage_mono (leOfHom (Pi.π (fun i ↦ f ''ᵁ V i) i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private noncomputable def cechCosimplicialOpenImmersionIso
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {I : Type u} (W : I → Y.Opens)
    (P : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (Limits.FormalCoproduct.cosimplicialObjectFunctor
      (Limits.FormalCoproduct.mk I W).cech).obj (f.opensFunctor.op ⋙ P) ≅
    (Limits.FormalCoproduct.cosimplicialObjectFunctor
      (Limits.FormalCoproduct.mk I (fun i ↦ f ''ᵁ W i)).cech).obj P := by
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · change (∏ᶜ fun q : Fin (n.len + 1) → I ↦
        P.obj (op (f ''ᵁ (∏ᶜ fun k : Fin (n.len + 1) ↦ W (q k))))) ≅
      (∏ᶜ fun q : Fin (n.len + 1) → I ↦
        P.obj (op (∏ᶜ fun k : Fin (n.len + 1) ↦ f ''ᵁ W (q k))))
    exact Limits.Pi.mapIso (fun q ↦
      (P.mapIso (eqToIso (image_pi_of_isOpenImmersion f
        (fun k : Fin (n.len + 1) ↦ W (q k)))).op).symm)
  · intro n m g
    dsimp [Limits.FormalCoproduct.cosimplicialObjectFunctor,
      Limits.FormalCoproduct.evalOp, Limits.FormalCoproduct.cech,
      Limits.FormalCoproduct.power, Limits.FormalCoproduct.mapPower]
    apply Limits.Pi.hom_ext
    intro q
    slice_lhs 2 3 => erw [Limits.Pi.mapIso_hom_π]
    slice_lhs 1 2 => erw [Limits.Pi.lift_π]
    slice_rhs 2 3 => erw [Limits.Pi.lift_π]
    slice_rhs 1 2 => erw [Limits.Pi.mapIso_hom_π]
    simp only [Category.assoc]
    congr 1
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1

private noncomputable def cechComplexOpenImmersionIso
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {I : Type u} (W : I → Y.Opens)
    (P : (Opens Z)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (cechComplexFunctor W).obj (f.opensFunctor.op ⋙ P) ≅
      (cechComplexFunctor (fun i ↦ f ''ᵁ W i)).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
    (cechCosimplicialOpenImmersionIso f W P)

/-- The compact distinguished-open basis lying below one fixed affine open of a scheme. -/
noncomputable def affineBasicOpenBasisAt (U : X.Opens) (hU : IsAffineOpen U) :
    CategoryTheory.Sheaf.CompactOpenBasis X where
  carrier := Set.range (X.basicOpen : Γ(X, U) → X.Opens)
  isCompact := by
    rintro V ⟨f, rfl⟩
    exact (hU.basicOpen f).isCompact
  finite_refinement := by
    rintro V ⟨d, rfl⟩ I W hVW
    let A : Set (X.Opens) :=
      { T | T ∈ Set.range (X.basicOpen : Γ(X, U) → X.Opens) ∧
        T ≤ X.basicOpen d ∧ ∃ i, T ≤ W i }
    have hcover : X.basicOpen d ≤ sSup A := by
      intro x hxd
      have hxW : x ∈ ⨆ i, W i := hVW hxd
      rw [Opens.mem_iSup] at hxW
      obtain ⟨i, hxi⟩ := hxW
      let x' : (W i ⊓ X.basicOpen d : X.Opens) := ⟨x, hxi, hxd⟩
      have hxU : (x' : X) ∈ U := X.basicOpen_le d hxd
      obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le x' hxU
      have hfA : X.basicOpen f ∈ A :=
        ⟨⟨f, rfl⟩, hf.trans inf_le_right, i, hf.trans inf_le_left⟩
      exact (le_sSup hfA) hxf
    obtain ⟨s, hs⟩ := (hU.basicOpen d).isCompact.elim_finite_subcover
      (fun T : A ↦ (T.1 : Set X)) (fun T ↦ T.1.2) (by
        intro x hxd
        have hx : x ∈ sSup A := hcover hxd
        rw [Opens.mem_sSup] at hx
        obtain ⟨T, hTA, hxT⟩ := hx
        exact Set.mem_iUnion.2 ⟨⟨T, hTA⟩, hxT⟩)
    let J := s
    let T : J → X.Opens := fun j ↦ j.1.1
    let a : J → I := fun j ↦ Classical.choose j.1.2.2.2
    refine ⟨J, inferInstance, T, a, fun j ↦ j.1.2.1,
      fun j ↦ Classical.choose_spec j.1.2.2.2, ?_⟩
    apply le_antisymm
    · intro x hxd
      have hx : x ∈ ⋃ j ∈ s, (j.1 : Set X) := hs hxd
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hj, hxj⟩ := hx
      rw [Opens.mem_iSup]
      exact ⟨⟨j, hj⟩, hxj⟩
    · rw [iSup_le_iff]
      intro j
      exact j.1.2.2.1
  inf_mem := by
    rintro V W ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, Scheme.basicOpen_mul X f g⟩

/-- The target affine open belongs to its own distinguished-open basis as `D(1)`. -/
lemma mem_affineBasicOpenBasisAt (U : X.Opens) (hU : IsAffineOpen U) :
    U ∈ (affineBasicOpenBasisAt U hU).carrier :=
  ⟨1, Scheme.basicOpen_one X⟩

/-- Quasi-coherent module sheaves on an affine spectrum are Cech-acyclic on its distinguished
open basis. -/
theorem modulesSpec_isCechAcyclicOnCompactBasis
    {R : CommRingCat.{u}} (G : (Spec R).Modules) [G.IsQuasicoherent] :
    CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis (affineBasicOpenBasis R)
      ((Scheme.Modules.toSheaf (Spec R)).obj G) := by
  letI : IsIso G.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  let e := (Scheme.Modules.toSheaf (Spec R)).mapIso (asIso G.fromTildeΓ)
  intro I _ V hV W hW hcover n hn
  exact (underlyingTilde_isCechAcyclicOnCompactBasis
    (moduleSpecΓFunctor.obj G) V hV W hW hcover n hn).of_iso
      ((cechComplexFunctor W).mapIso
        ((sheafToPresheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).mapIso e))

set_option maxHeartbeats 1000000 in
/-- The underlying abelian sheaf of a quasi-coherent module is Cech-acyclic on the local
distinguished-open basis below an affine open. -/
theorem modules_isCechAcyclicOn_affineBasicOpenBasisAt
    (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis (affineBasicOpenBasisAt U hU)
      ((Scheme.Modules.toSheaf X).obj G) := by
  let G' : (Spec Γ(X, U)).Modules := G.restrict hU.fromSpec
  have hG' : CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis
      (affineBasicOpenBasis Γ(X, U)) ((Scheme.Modules.toSheaf (Spec Γ(X, U))).obj G') :=
    modulesSpec_isCechAcyclicOnCompactBasis G'
  intro I _ V hV W hW hcover n hn
  obtain ⟨d, rfl⟩ := hV
  choose f hf using hW
  have hWeq : W = fun i ↦ X.basicOpen (f i) := funext fun i ↦ (hf i).symm
  subst W
  have hcover' : _root_.PrimeSpectrum.basicOpen d =
      ⨆ i, _root_.PrimeSpectrum.basicOpen (f i) := by
    apply hU.fromSpec.image_injective
    change (hU.fromSpec ''ᵁ _root_.PrimeSpectrum.basicOpen d) =
      hU.fromSpec ''ᵁ (⨆ i, _root_.PrimeSpectrum.basicOpen (f i))
    rw [hU.fromSpec.image_iSup]
    simpa only [hU.fromSpec_image_basicOpen] using hcover
  have h := hG' (_root_.PrimeSpectrum.basicOpen d)
    ⟨d, rfl⟩ (fun i ↦ _root_.PrimeSpectrum.basicOpen (f i))
    (fun i ↦ ⟨f i, rfl⟩) hcover' n hn
  change ((cechComplexFunctor (fun i ↦ _root_.PrimeSpectrum.basicOpen (f i))).obj
    (hU.fromSpec.opensFunctor.op ⋙ ((Scheme.Modules.toSheaf X).obj G).obj)).ExactAt n at h
  have h' := h.of_iso (cechComplexOpenImmersionIso hU.fromSpec
    (fun i ↦ _root_.PrimeSpectrum.basicOpen (f i))
    ((Scheme.Modules.toSheaf X).obj G).obj)
  simpa only [hU.fromSpec_image_basicOpen] using h'

/-- Positive local cohomology of a quasi-coherent module vanishes on an affine open.  The
cohomology group here is the actual ambient `Sheaf.H'`, not cohomology of an unrelated sheaf on
an abstract affine model. -/
theorem modules_HPrime_subsingleton_of_isAffineOpen
    (G : X.Modules) [G.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (n : ℕ) (hn : 0 < n)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)] :
    Subsingleton (@Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _ hExt
      ((Scheme.Modules.toSheaf X).obj G) n U) :=
  CategoryTheory.Sheaf.HPrime_subsingleton_of_isCechAcyclicOnCompactBasis
    (affineBasicOpenBasisAt U hU) ((Scheme.Modules.toSheaf X).obj G)
    (modules_isCechAcyclicOn_affineBasicOpenBasisAt G U hU) U
    (mem_affineBasicOpenBasisAt U hU) n hn (hExt := hExt)

/-- If every member of a finite list of opens is affine and the diagonal is affine, then a
quasi-coherent module is acyclic on every nonempty intersection generated by the list. -/
theorem modules_intersectionAcyclic_of_forall_isAffineOpen
    (G : X.Modules) [G.IsQuasicoherent]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (L : List X.Opens) (hL : ∀ V ∈ L, IsAffineOpen V) :
    @CategoryTheory.Sheaf.IntersectionAcyclic X ((Scheme.Modules.toSheaf X).obj G) hExt L := by
  cases L with
  | nil => exact .nil
  | cons U L =>
      refine .cons U L (fun n hn ↦
        modules_HPrime_subsingleton_of_isAffineOpen G U (hL U (by simp)) n hn
          (hExt := hExt))
        (modules_intersectionAcyclic_of_forall_isAffineOpen G L
          (fun V hV ↦ hL V (by simp [hV])) (hExt := hExt)) ?_
      apply modules_intersectionAcyclic_of_forall_isAffineOpen G (hExt := hExt)
      intro V hV
      obtain ⟨W, hWL, rfl⟩ := List.mem_map.mp hV
      exact IsAffineOpen.inf (hL U (by simp)) (hL W (by simp [hWL]))
termination_by L.length
decreasing_by all_goals simp_all only [List.length_cons, List.length_map]; omega

/-- A fixed nonempty finite affine cover used to state an explicit cohomological bound.  The
empty affine open is prepended so the list remains nonempty even for the empty scheme. -/
noncomputable def finiteAffineCoverOpens (X : Scheme.{u}) [CompactSpace X] : List X.Opens :=
  ⊥ :: Finset.univ.toList.map
    (fun i : X.affineCover.finiteSubcover.I₀ ↦
      (X.affineCover.finiteSubcover.f i).opensRange)

@[simp] lemma finiteAffineCoverOpens_ne_nil (X : Scheme.{u}) [CompactSpace X] :
    finiteAffineCoverOpens X ≠ [] := by
  simp [finiteAffineCoverOpens]

private lemma le_opensUnion_of_mem {L : List X.Opens} {U : X.Opens} (hU : U ∈ L) :
    U ≤ CategoryTheory.Sheaf.opensUnion L := by
  induction L with
  | nil => simp at hU
  | cons V L ih =>
      simp only [List.mem_cons] at hU
      rcases hU with rfl | hU
      · exact le_sup_left
      · exact ih hU |>.trans le_sup_right

/-- The chosen finite list really covers the scheme. -/
lemma opensUnion_finiteAffineCoverOpens (X : Scheme.{u}) [CompactSpace X] :
    CategoryTheory.Sheaf.opensUnion (finiteAffineCoverOpens X) = ⊤ := by
  apply top_unique
  rw [← X.affineCover.finiteSubcover.iSup_opensRange]
  apply iSup_le
  intro i
  apply le_opensUnion_of_mem
  simp [finiteAffineCoverOpens]

/-- Every member of the chosen finite cover is affine. -/
lemma isAffineOpen_of_mem_finiteAffineCoverOpens
    (X : Scheme.{u}) [CompactSpace X] (U : X.Opens)
    (hU : U ∈ finiteAffineCoverOpens X) : IsAffineOpen U := by
  simp only [finiteAffineCoverOpens, List.mem_cons, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and] at hU
  rcases hU with rfl | ⟨i, rfl⟩
  · exact isAffineOpen_bot X
  · exact isAffineOpen_opensRange _

/-- The explicit finite-affine-cover bound. -/
noncomputable def cohomologicalBound (X : Scheme.{u}) [CompactSpace X] : ℕ :=
  (finiteAffineCoverOpens X).length

set_option maxHeartbeats 400000 in
/-- Cohomology of a quasi-coherent module vanishes strictly above the explicit finite affine
cover bound.  Only quasi-compactness and an affine diagonal are used. -/
theorem modules_H_subsingleton_of_cohomologicalBound
    (G : X.Modules) [G.IsQuasicoherent] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (n : ℕ) (hn : cohomologicalBound X < n) :
    Subsingleton (@Sheaf.H (Opens X) _ (Opens.grothendieckTopology X)
      ((Scheme.Modules.toSheaf X).obj G) inferInstance hExt n) := by
  let L := finiteAffineCoverOpens X
  have hA : @CategoryTheory.Sheaf.IntersectionAcyclic X
      ((Scheme.Modules.toSheaf X).obj G) hExt L :=
    modules_intersectionAcyclic_of_forall_isAffineOpen G L (hExt := hExt)
      (fun U hU ↦ isAffineOpen_of_mem_finiteAffineCoverOpens X U hU)
  have hH' := CategoryTheory.Sheaf.HPrime_subsingleton_opensUnion_of_intersectionAcyclic
    ((Scheme.Modules.toSheaf X).obj G) hA (finiteAffineCoverOpens_ne_nil X) n (by
      dsimp [cohomologicalBound, L] at hn ⊢
      omega) (hExt := hExt)
  rw [opensUnion_finiteAffineCoverOpens X] at hH'
  exact (@CategoryTheory.Sheaf.subsingleton_HPrime_iff_H (Opens X) _
    (Opens.grothendieckTopology X) _ hExt ⊤ Limits.isTerminalTop _ n).mp hH'

/-- Coherent sheaves inherit the same explicit finite-affine-cover bound. -/
theorem coherent_H_subsingleton_of_cohomologicalBound
    (F : Coh X) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (n : ℕ) (hn : cohomologicalBound X < n) :
    Subsingleton ((coherentH X n).obj F) := by
  letI hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _
  letI : ((Coh.ι X).obj F).IsFinitePresentation := F.property
  change Subsingleton
    (@Sheaf.H (Opens X) _ (Opens.grothendieckTopology X)
      ((Scheme.Modules.toSheaf X).obj ((Coh.ι X).obj F)) inferInstance hExt n)
  exact modules_H_subsingleton_of_cohomologicalBound ((Coh.ι X).obj F) n hn
    (hExt := hExt)

namespace FiniteDimensionalCohomology

variable {k : Type u} [Field k] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))] [IsVariety k Y]

/-- Add the independent finite-affine-cover vanishing theorem to degreewise finite-dimensional
cohomology.  This is the constructor which turns the output of #29 into the `FiniteCohomology`
package consumed by Euler characteristics. -/
noncomputable def toFiniteCohomology (D : FiniteDimensionalCohomology k Y)
    [IsNoetherian Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] : FiniteCohomology k Y where
  toFiniteDimensionalCohomology := D
  bound := fun _ ↦ cohomologicalBound Y
  vanishesAbove := by
    intro F i hi
    have hH : Subsingleton ((coherentH Y i).obj F) :=
      coherent_H_subsingleton_of_cohomologicalBound F i hi
    let e := (D.comparison i).app F
    exact ⟨fun x y ↦
      (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance (hH.elim (e.hom x) (e.hom y))⟩

end FiniteDimensionalCohomology

end AlgebraicGeometry.Cohomology
