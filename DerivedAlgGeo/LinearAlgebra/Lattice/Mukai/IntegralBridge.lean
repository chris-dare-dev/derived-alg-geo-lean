/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.WallRegion

/-!
# The integral Mukai lattice inside the real extension

The wall-finiteness results take the lattice as the `ℤ`-span of an `ℝ`-basis of
an abstract quadratic space. The Mukai lattice of a K3 is `ℤ ⊕ NS(X) ⊕ ℤ` with
the integral pairing, which is what `Lattice/Mukai/Basic.lean` builds. This file
connects them, so that "finitely many spherical walls" is a statement about
integral classes rather than about an abstract `ZSpan`.

## Three steps

* `extendBasis` — a basis of `V` induces one of `ℝ × V × ℝ`, namely `(1,0,0)`,
  `(0, vᵢ, 0)`, `(0,0,1)`. The finiteness theorems want a basis of the whole
  space; this is it.
* `span_range_extendBasis` — its `ℤ`-span **is** the integral Mukai extension:
  integer rank and corank, lattice middle. This is what turns those theorems
  into statements about integral classes.
* `realPairing_extendMap` — for a lattice map `f` respecting the two forms, the
  induced map on Mukai extensions carries `Mukai.pairing` to `Mukai.realPairing`.
  This is the literal statement that the two files describe the same pairing,
  and it is where a factor or a sign error would surface.

## The lattice is presented by a basis, not by a tensor product

`N ⊗ ℝ` would be the textbook construction and is not used: a basis gives
everything below with no tensor-product plumbing, and the geometric input — that
`N(X)` is free of finite rank and spans `N(X) ⊗ ℝ` — is exactly what a basis is.

`V` remains an arbitrary real bilinear space; no geometry is asserted.
-/

open QuadraticMap

namespace Mukai

section Basis

variable {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The basis of the real Mukai extension induced by a basis of `V`. -/
noncomputable def extendBasis (v : Module.Basis ι ℝ V) :
    Module.Basis (Unit ⊕ (ι ⊕ Unit)) ℝ (RealExtension V) :=
  (Module.Basis.singleton Unit ℝ).prod (v.prod (Module.Basis.singleton Unit ℝ))

/-- The **integral Mukai extension** of a lattice in `V`: integral rank and
corank, lattice middle. -/
def integralExtension (Λ : Submodule ℤ V) : Submodule ℤ (RealExtension V) :=
  (Submodule.span ℤ ({1} : Set ℝ)).prod (Λ.prod (Submodule.span ℤ ({1} : Set ℝ)))

/-- The `ℤ`-span of a product basis is the product of the `ℤ`-spans. -/
private theorem span_int_range_prod {M M' : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup M'] [Module ℝ M'] {κ κ' : Type*}
    (c : Module.Basis κ ℝ M) (c' : Module.Basis κ' ℝ M') :
    Submodule.span ℤ (Set.range (c.prod c'))
      = (Submodule.span ℤ (Set.range c)).prod (Submodule.span ℤ (Set.range c')) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    cases k with
    | inl i =>
        refine ⟨?_, ?_⟩
        · rw [Module.Basis.prod_apply_inl_fst]
          exact Submodule.subset_span ⟨i, rfl⟩
        · rw [Module.Basis.prod_apply_inl_snd]
          exact Submodule.zero_mem _
    | inr j =>
        refine ⟨?_, ?_⟩
        · rw [Module.Basis.prod_apply_inr_fst]
          exact Submodule.zero_mem _
        · rw [Module.Basis.prod_apply_inr_snd]
          exact Submodule.subset_span ⟨j, rfl⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hsplit : ((x, y) : M × M') = (x, 0) + (0, y) := by simp
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · have hmap : (Submodule.span ℤ (Set.range c)).map (LinearMap.inl ℤ M M')
          ≤ Submodule.span ℤ (Set.range (c.prod c')) := by
        rw [Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
        simp
      exact hmap ⟨x, hx, rfl⟩
    · have hmap : (Submodule.span ℤ (Set.range c')).map (LinearMap.inr ℤ M M')
          ≤ Submodule.span ℤ (Set.range (c.prod c')) := by
        rw [Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        refine Submodule.subset_span ⟨Sum.inr j, ?_⟩
        simp
      exact hmap ⟨y, hy, rfl⟩

/-- **The `ℤ`-span of the extended basis is the integral Mukai extension.** -/
theorem span_range_extendBasis (v : Module.Basis ι ℝ V) :
    Submodule.span ℤ (Set.range (extendBasis v))
      = integralExtension (Submodule.span ℤ (Set.range v)) := by
  rw [extendBasis, span_int_range_prod, span_int_range_prod, integralExtension]
  congr 1 <;> [skip; congr 1] <;>
    simp [Module.Basis.singleton, Set.range_unique]

end Basis

section Comparison

variable {N : Type*} [AddCommGroup N] {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The map of Mukai extensions induced by a map of the middle summands. -/
def extendMap (f : N →ₗ[ℤ] V) (u : MukaiLattice N) : RealExtension V :=
  ((u.1 : ℝ), f u.2.1, (u.2.2 : ℝ))

omit [Module ℝ V] in
/-- The induced map is additive: `MukaiLattice` addition is componentwise and
each coordinate map is. -/
theorem extendMap_add (f : N →ₗ[ℤ] V) (u w : MukaiLattice N) :
    extendMap f (u + w) = extendMap f u + extendMap f w := by
  simp only [extendMap, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
  push_cast
  rfl

/-- **`extendMap` as a bundled hom.**  It was proved additive and left as a bare
function, which is what forces every consumer to re-prove additivity of whatever
composite it sits in. -/
noncomputable def extendMapHom (f : N →ₗ[ℤ] V) : MukaiLattice N →+ RealExtension V :=
  AddMonoidHom.mk' (extendMap f) (extendMap_add f)

/-- **The two pairings agree.** For a map of middles that respects the forms, the
integral Mukai pairing is the real one, cast. -/
theorem realPairing_extendMap (bZ : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (bR : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (f : N →ₗ[ℤ] V) (hf : ∀ x y : N, bR (f x) (f y) = (bZ x y : ℝ))
    (u w : MukaiLattice N) :
    realPairing bR (extendMap f u) (extendMap f w) = (pairing bZ u w : ℝ) := by
  simp only [realPairing, extendMap, pairing, hf]
  push_cast
  ring

/-- A class of self-pairing `-2` in the integral lattice is a spherical class of
the real form. The `-2` reads the same on both sides, which is the point of the
halving convention in `Mukai/RealForm.lean`. -/
theorem isSphericalClass_extendMap (bZ : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (bR : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (f : N →ₗ[ℤ] V) (hf : ∀ x y : N, bR (f x) (f y) = (bZ x y : ℝ))
    (hb : ∀ x y : V, bR x y = bR y x) {δ : MukaiLattice N} (hδ : IsSpherical bZ δ) :
    PeriodDomain.IsSphericalClass (realForm bR) (extendMap f δ) := by
  rw [PeriodDomain.IsSphericalClass, polar_realForm bR hb,
    realPairing_extendMap bZ bR f hf]
  rw [IsSpherical, selfPairing] at hδ
  rw [hδ]
  norm_num

end Comparison

section Finiteness

variable {ι : Type*} [Finite ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- **Finitely many integral spherical classes are orthogonal to a positive
plane**, stated over the integral Mukai extension of the lattice rather than over
an abstract `ZSpan`. -/
theorem finite_sphericalOrthogonal_integralExtension
    (hsig : PeriodDomain.HasSignatureTwo (realForm b)) {W : Submodule ℝ (RealExtension V)}
    (hW : PeriodDomain.IsPositivePlane (realForm b) W) (v : Module.Basis ι ℝ V) :
    (PeriodDomain.sphericalOrthogonal (realForm b) W ∩
      (integralExtension (Submodule.span ℤ (Set.range v)) : Set (RealExtension V))).Finite := by
  rw [← span_range_extendBasis v]
  exact PeriodDomain.finite_sphericalOrthogonal_inter hsig hW (extendBasis v)

/-- The region-wise form of the same statement. -/
theorem finite_wallClasses_integralExtension (R : PeriodDomain.PlaneRegion (realForm b))
    (v : Module.Basis ι ℝ V) :
    (R.wallClasses ∩
      (integralExtension (Submodule.span ℤ (Set.range v)) : Set (RealExtension V))).Finite := by
  rw [← span_range_extendBasis v]
  exact R.finite_wallClasses_inter (extendBasis v)

end Finiteness

end Mukai
