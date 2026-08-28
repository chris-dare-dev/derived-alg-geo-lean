# Semiorthogonal-decomposition surface at the pinned Mathlib — 2026-08-28

For `projective-families-e3` (chris-dare-dev/derived-alg-geo-lean#852).  This note records the
surface used by the generic root and the gaps left for later geometric consumers.

**Environment.** The checkout pins
`mathlib_rev = 520045ab14e26149ee970e2e617ca04b09bde5d6` in `pins.json`, with
`leanprover/lean4:v4.32.1`.  The elaboration probes used that exact built dependency.  The probe
file lived under `/tmp` and is not merged.

## Result

Mathlib already owns all of the closure and generation operations needed for the common root.  It
does not own a semiorthogonal-decomposition carrier, an exceptional-collection carrier, or the
componentwise categorical structures needed to make a product of triangulated categories
triangulated.  The implementation therefore adds only an ordered family of `ObjectProperty C`
with Hom-vanishing, and reuses Mathlib predicates for every refinement.

| Need | Pinned declaration or measured result |
|---|---|
| Object properties | `CategoryTheory.ObjectProperty` and its complete lattice |
| Right/left orthogonals | `ObjectProperty.rightOrthogonal`, `leftOrthogonal` |
| Shift closure | `ObjectProperty.shiftClosure` |
| Extension closure step | `ObjectProperty.extensionProduct` |
| Thick triangulated envelope | `ObjectProperty.triangEnvelope` |
| Classical fullness | `ObjectProperty.IsClassicalTriangulatedGenerator` |
| Strong fullness | `ObjectProperty.IsStrongTriangulatedGenerator` |
| Essential image under a functor | `ObjectProperty.map` |
| Semiorthogonal/exceptional declarations | no Mathlib match |
| Product zero/preadditive/zero-object/pretriangulated instances | none synthesize |

## 1. Orthogonality and generation are already canonical

`Mathlib/CategoryTheory/ObjectProperty/Orthogonal.lean` defines

```lean
P.rightOrthogonal Y := ∀ ⦃X⦄ (f : X ⟶ Y), P X → f = 0
```

and proves closure under isomorphism.  In the triangulated setting,
`Mathlib/CategoryTheory/Triangulated/Orthogonal.lean` supplies triangulated-closure instances for
orthogonals of shift-stable properties.

`Mathlib/CategoryTheory/Triangulated/Generators.lean` builds `triangEnvelope` from shift closure,
binary products, retracts, and iterated extension products.  Its
`IsClassicalTriangulatedGenerator` is exactly the reusable fullness predicate, while
`IsStrongTriangulatedGenerator` records a uniform extension bound and proves
`isClassicalTriangulatedGenerator`.

Consequently the repository's `Triangulated.ExtensionClosure` is not used for fullness.  That
owner closure deliberately proves neither shift stability nor retract closure and explicitly does
not compare itself with Mathlib's thick triangulated envelope.  Reusing it here would create two
meanings of generation.

The generator declarations require

```lean
[HasZeroObject C] [HasShift C ℤ] [Preadditive C]
[∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
```

The carrier itself needs only `[Category.{v} C] [HasZeroMorphisms C]`; its index is an independent
`Type w` with a `Preorder`.  This is why an ungenerated semiorthogonal sequence can be used before
a geometric category has all triangulated instances assembled.

## 2. Essential-image transport is present, preservation is not automatic

`ObjectProperty.map P F` is the essential image

```lean
fun Y ↦ ∃ X, P X ∧ Nonempty (F.obj X ≅ Y)
```

There is no mathematically valid theorem saying an arbitrary functor preserves semiorthogonality.
The root therefore exposes a `SemiorthogonalSequence.map` constructor whose separate hypothesis
states orthogonality of the mapped components.  A later derived-pullback or base-change theorem
must prove that hypothesis.  Pullback, mutation, and geometric preservation are not record fields.

## 3. The product-category boundary

`Mathlib/CategoryTheory/Products/Basic.lean` supplies the category on `C × D`, componentwise
morphisms, the projections, and the section functors.  At this pin, each of the following probes
fails even when both factors carry the corresponding instance:

```lean
#synth HasZeroMorphisms (C × D)
#synth Preadditive (C × D)
#synth HasZeroObject (C × D)
```

A source search also finds no componentwise `Pretriangulated (C × D)` construction.  The examples
module adds the elementary componentwise zero-morphism instance only.  This is enough to exhibit
the two factor properties as a semiorthogonal sequence and does not pretend that a product is
already a triangulated category.  Product fullness should be added only after the missing
componentwise pretriangulated structure is constructed or supplied upstream.

Universe-wise, Mathlib's product category has morphism universe `max v₁ v₂` on
`C : Type u₁` and `D : Type u₂`; the componentwise zero-morphism instance follows that existing
category without adding a universe equality.

## 4. Root decision and statement-layer exceptions

The public carrier is `CategoryTheory.Triangulated.SemiorthogonalSequence C ι`.  It contains only
`component` and ordered Hom-vanishing.  The predicates `HasTriangulatedComponents`, `IsFull`, and
`IsStronglyFull` are independent, and strong fullness implies classical fullness by Mathlib's
theorem.  The one-block sequence and the product-factor sequence are independent inhabitants of
the carrier; the one-block sequence also inhabits both fullness predicates.

No exceptional-sequence or mutation carrier is added in this slice.  There is no present theorem
in the repository consuming exceptionality, scalar endomorphism identification, or mutation, and
issue #852 requires those notions to be added only when a theorem consumes each property.  These
are documented statement-layer exceptions to the two-inhabitant rule, not empty structures kept
in anticipation of `(P¹)^n`.  The first projective-family consumer should add the smallest
exceptionality predicates it actually uses and prove that its shifted object properties instantiate
this same semiorthogonal root.

## Commands

```sh
git -C .lake/packages/mathlib rev-parse HEAD
rg -n "Semiorthogonal|semiorthogonal|ExceptionalCollection|IsExceptional" \
  .lake/packages/mathlib/Mathlib -g '*.lean'
rg -n "Pretriangulated.*prod|HasZeroMorphisms.*×|Preadditive.*×|HasZeroObject.*×" \
  .lake/packages/mathlib/Mathlib/CategoryTheory -g '*.lean'
lake env lean /tmp/SemiProbe.lean
lake build DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition
```
