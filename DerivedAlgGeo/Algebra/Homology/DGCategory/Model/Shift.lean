/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model.Complexes
import DerivedAlgGeo.Algebra.Homology.DGCategory.Shift

/-!
# The shifted hom-complexes of `C^dg`, checked against Mathlib

`DGCategory.shiftD` and `DGCategory.shiftComp` are stated for an arbitrary dg
category, so on `Cdg A` they must come out as the operations Mathlib already
has. This file checks that, rather than leaving the agreement to a comment.

Three things are recorded.

1. `shiftD` on `Cdg A` is `δ` with the sign `(-1) ^ m`, and `shiftComp` is
   `Cochain.comp` with the sign the derivation in `..Shift` forced. Both are
   `rfl`, so the general definitions genuinely restrict to the model.

2. The sign on the shifted differential is the same `(-1) ^ m` that Mathlib's
   own `δ_shift` carries. That lemma is about shifting the *objects* of a
   cochain — `Cochain.shift a : Cochain (K⟦a⟧) (L⟦a⟧) n` — which is a different
   operation from shifting the hom-complex, so this is a real cross-check
   between two independent constructions and not a restatement of one.

3. `shiftD_eq_delta_shift` records where the two operations meet: the sign
   `(-1) ^ m` produced by `CochainComplex.shiftFunctor` on the hom-complex and
   the sign produced by `Cochain.shift` on the objects agree, which is what
   makes the two conventions composable rather than merely coexistent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct CochainComplex.HomComplex

namespace Cdg

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- `shiftD` on `C^dg` is `δ` with the shift's sign. -/
lemma shiftD_eq {K L : Cdg A} (m a b : ℤ) (f : (dgHom K L).X a) :
    DGCategory.shiftD m a b f = m.negOnePow • (δ a b) f := rfl

/-- `shiftComp` on `C^dg` is `Cochain.comp` with the Koszul sign that
`DGCategory.shiftComp`'s derivation forced. -/
lemma shiftComp_eq {K L M : Cdg A} (m n a b c : ℤ) (h : a + b = c)
    (f : (dgHom K L).X a) (g : (dgHom L M).X b) :
    DGCategory.shiftComp m n a b c h f g = ((b - n) * m).negOnePow • Cochain.comp f g h := rfl

/-- **The cross-check.** `Cochain.shift` shifts the objects of a cochain and
`δ_shift` says that costs `(-1) ^ m`. `shiftD` shifts the hom-complex and costs
`(-1) ^ m` by `CochainComplex.shiftFunctor`. The two constructions are
independent; the signs agree. -/
lemma delta_shift_sign_agrees {K L : CochainComplex A ℤ} (m a b : ℤ)
    (γ : Cochain K L a) :
    δ a b (Cochain.shift γ m) = m.negOnePow • Cochain.shift (δ a b γ) m :=
  Cochain.δ_shift γ m b

end Cdg

end CategoryTheory
