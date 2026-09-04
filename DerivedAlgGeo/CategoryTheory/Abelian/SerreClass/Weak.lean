/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Weak Serre subcategories are closed in the middle of a five-term exact sequence

Mathlib's `ObjectProperty.IsSerreClass` bundles closure under subobjects,
quotients and extensions, and `ObjectProperty.prop_X₂_of_exact` uses it to put
the middle of a *three*-term exact sequence in the class. Many naturally
occurring classes are not Serre classes: quasi-coherent sheaves on a general
scheme are closed under kernels, cokernels and extensions, but a subsheaf of a
quasi-coherent sheaf need not be quasi-coherent. Such a class is a **weak Serre
subcategory**, and the three-term statement is false for it.

The correct statement one degree weaker is the five-term one proved here: if

`A ⟶ B ⟶ C ⟶ D ⟶ E`

is exact at `B`, `C` and `D`, and all four of `A`, `B`, `D`, `E` lie in `P`,
then so does `C`. Mathlib has the three closure classes
(`IsClosedUnderKernels`, `IsClosedUnderCokernels`, `IsClosedUnderExtensions`)
but not this consequence of holding all three at once.

## Why five terms and not three

With `A ⟶ B ⟶ C ⟶ D ⟶ E` write `K` for the cycles of `C` and `Q` for its
opcycles, so that `0 ⟶ K ⟶ C ⟶ Q ⟶ 0` is short exact. Exactness at `B` makes
`B ⟶ K` a cokernel of `A ⟶ B`, and exactness at `D` makes `Q ⟶ D` a kernel of
`D ⟶ E`. So `K` is reached by *cokernel* closure from `A` and `B`, and `Q` by
*kernel* closure from `D` and `E`, and extension closure then delivers `C`.

The outer two terms are exactly what pays for the missing subobject and
quotient closure: a three-term sequence gives `K` only as a quotient of `B` and
`Q` only as a subobject of `D`, neither of which a weak Serre subcategory sees.

## Main results

* `ObjectProperty.prop_of_exact_of_epi` — the middle-to-right half: an exact
  `A ⟶ B ⟶ K` with `B ⟶ K` epi puts `K` in `P`, by cokernel closure.
* `ObjectProperty.prop_of_exact_of_mono` — dually, by kernel closure.
* `ObjectProperty.prop_X₃_of_exact₅` — the five-term statement.

This is generic abelian-category mathematics stated in Mathlib's namespace, and
is an upstream candidate.
-/

universe v u

namespace CategoryTheory

open Category Limits ShortComplex

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

section

variable [P.IsClosedUnderCokernels]

/-- **A quotient reached by an exact sequence, not by quotient closure.** If
`A ⟶ B ⟶ K` is exact and `B ⟶ K` is an epimorphism, then `K` is a cokernel of
`A ⟶ B`, so cokernel closure puts it in `P`.

This is the step that a weak Serre subcategory can take and
`IsClosedUnderQuotients` would take for free: the hypothesis `P A` is what
replaces knowing that `P` sees the kernel of `B ⟶ K`. -/
lemma prop_of_exact_of_epi {S : ShortComplex C} (hS : S.Exact) [Epi S.g]
    (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃ :=
  P.prop_of_isColimit_cokernelCofork hS.gIsCokernel h₁ h₂

end

section

variable [P.IsClosedUnderKernels]

/-- **A subobject reached by an exact sequence, not by subobject closure.** If
`Q ⟶ D ⟶ E` is exact and `Q ⟶ D` is a monomorphism, then `Q` is a kernel of
`D ⟶ E`, so kernel closure puts it in `P`.

Dual to `prop_of_exact_of_epi`; the hypothesis `P E` replaces knowing that `P`
sees the cokernel of `Q ⟶ D`. -/
lemma prop_of_exact_of_mono {S : ShortComplex C} (hS : S.Exact) [Mono S.f]
    (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁ :=
  P.prop_of_isLimit_kernelFork hS.fIsKernel h₂ h₃

end

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
  [P.IsClosedUnderExtensions]

/-- **The middle of a five-term exact sequence lies in a weak Serre
subcategory.**

Given `A ⟶ B ⟶ C ⟶ D ⟶ E` exact at `B`, `C` and `D`, membership of the four
outer objects forces membership of `C`.

The proof is the one the module docstring describes. Taking `d` to be a
homology data for `B ⟶ C ⟶ D`, exactness at `C` gives the short exact sequence
`0 ⟶ d.left.K ⟶ C ⟶ d.right.Q ⟶ 0`. Exactness at `B` says `d.left.f'` is epi,
and `A ⟶ B ⟶ d.left.K` is exact because postcomposing with the mono `d.left.i`
returns `A ⟶ B ⟶ C`; so `d.left.K` is a cokernel of `f`. Dually `d.right.Q` is a
kernel of `i`. Extension closure finishes.

No hypothesis is placed on the composites beyond the three `ShortComplex`
zero-conditions, and in particular `P` is *not* assumed closed under subobjects
or quotients — that is the whole point. -/
theorem prop_X₃_of_exact₅ {A B D E : C} {X : C} {f : A ⟶ B} {g : B ⟶ X}
    {h : X ⟶ D} {i : D ⟶ E} {w₁ : f ≫ g = 0} {w₂ : g ≫ h = 0} {w₃ : h ≫ i = 0}
    (h₁ : (ShortComplex.mk f g w₁).Exact)
    (h₂ : (ShortComplex.mk g h w₂).Exact)
    (h₃ : (ShortComplex.mk h i w₃).Exact)
    (hA : P A) (hB : P B) (hD : P D) (hE : P E) : P X := by
  let S : ShortComplex C := ShortComplex.mk g h w₂
  let d : S.HomologyData := S.homologyData
  haveI : Epi d.left.f' := h₂.epi_f' d.left
  haveI : Mono d.right.g' := h₂.mono_g' d.right
  -- The cycles of `X`, as a cokernel of `f`.
  have hfK : f ≫ d.left.f' = 0 := by
    rw [← cancel_mono d.left.i, assoc, d.left.f'_i, zero_comp]
    exact w₁
  have hK : P d.left.K := by
    refine P.prop_of_exact_of_epi (S := ShortComplex.mk f d.left.f' hfK) ?_ hA hB
    let b : ShortComplex.mk f d.left.f' hfK ⟶ ShortComplex.mk f g w₁ :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := d.left.i }
    haveI : Epi b.τ₁ := show Epi (𝟙 A) from inferInstance
    haveI : IsIso b.τ₂ := show IsIso (𝟙 B) from inferInstance
    haveI : Mono b.τ₃ := show Mono d.left.i from inferInstance
    rwa [ShortComplex.exact_iff_of_epi_of_isIso_of_mono b]
  -- The opcycles of `X`, as a kernel of `i`.
  have hQi : d.right.g' ≫ i = 0 := by
    rw [← cancel_epi d.right.p, ← assoc, d.right.p_g', comp_zero]
    exact w₃
  have hQ : P d.right.Q := by
    refine P.prop_of_exact_of_mono (S := ShortComplex.mk d.right.g' i hQi) ?_ hD hE
    let a : ShortComplex.mk h i w₃ ⟶ ShortComplex.mk d.right.g' i hQi :=
      { τ₁ := d.right.p, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
    haveI : Epi a.τ₁ := show Epi d.right.p from inferInstance
    haveI : IsIso a.τ₂ := show IsIso (𝟙 D) from inferInstance
    haveI : Mono a.τ₃ := show Mono (𝟙 E) from inferInstance
    rwa [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]
  exact P.prop_X₂_of_shortExact (h₂.shortExact d) hK hQ

end ObjectProperty

end CategoryTheory
