/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Opens.Limits
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite products of basic opens in a prime spectrum

The basic open defined by a finite product of ring elements is the categorical product of their
basic opens in the lattice of open subsets of the prime spectrum.

This is topological prime-spectrum infrastructure: its signature uses a commutative ring together
with the opens of its prime spectrum and their categorical finite products, but no scheme.
-/

open CategoryTheory Limits

namespace PrimeSpectrum

open TopologicalSpace

variable {R : CommRingCat} {α : Type*} [Fintype α]

/-- The basic open of a finite product is the product of the corresponding basic opens. -/
lemma basicOpen_prod_eq_pi (g : α → R) :
    basicOpen (∏ a, g a) = ∏ᶜ (basicOpen ∘ g) := by
  apply le_antisymm
  · apply leOfHom
    apply Pi.lift
    intro a
    apply homOfLE
    intro p hp
    rw [mem_basicOpen] at hp
    change g a ∉ p.asIdeal
    intro ha
    apply hp
    rw [Ideal.IsPrime.prod_mem_iff]
    exact ⟨a, Finset.mem_univ _, ha⟩
  · intro p hp
    rw [mem_basicOpen]
    intro hprod
    rw [Ideal.IsPrime.prod_mem_iff] at hprod
    obtain ⟨a, _, ha⟩ := hprod
    have hga := leOfHom (Pi.π (basicOpen ∘ g) a) hp
    change g a ∉ p.asIdeal at hga
    exact hga ha

end PrimeSpectrum
