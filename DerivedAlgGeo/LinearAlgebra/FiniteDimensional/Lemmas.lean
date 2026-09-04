/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank--nullity at an exact middle term

`LinearMap.finrank_range_add_finrank_ker` splits the dimension of the source of a linear map
into rank and nullity. At the middle term of an exact pair `A → B → C` the kernel of the
second map is the range of the first, so the dimension of `B` is the sum of the two ranks
around it. Both alternating-sum arguments, the bounded one in `Algebra/Exact/Sequence.lean`
and the `ℤ`-indexed one in `Algebra/Homology/EulerCharacteristic.lean`, consume this.

`k` is a division ring, not a field: that is what `LinearMap.finrank_range_add_finrank_ker`
asks for, and commutativity is used nowhere.
-/

namespace Function.Exact

variable {k : Type*} [DivisionRing k] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module k A] [Module k B] [Module k C] [Module.Finite k B]

/-- Rank--nullity at an exact middle term: an exact `A → B → C` splits `dim B` into the two
ranks around it. -/
theorem finrank_eq_finrank_range_add_finrank_range {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) :
    Module.finrank k B =
      Module.finrank k (LinearMap.range f) + Module.finrank k (LinearMap.range g) := by
  have hr := g.finrank_range_add_finrank_ker
  rw [h.linearMap_ker_eq] at hr
  omega

end Function.Exact
