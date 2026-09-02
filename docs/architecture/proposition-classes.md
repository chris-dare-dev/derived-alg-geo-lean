# When a proposition-valued class is justified

This document records the contract for `Prop`-valued typeclasses in the
stability-condition subsystem. It exists because
`Slicing.HasPhaseTruncations` was a class that distinguished no objects: an
unconditional global instance derived it for every slicing from the
`hn_exists` field already present in `Slicing`, so the class carried no
information and served only as a second instance-search path to a theorem.

## Rule

A `Prop`-valued class is justified only when all three hold.

1. **It can fail.** Some inhabitant of the base structure does not satisfy it.
   If a single unconditional global instance discharges the class for every
   inhabitant, the content belongs in the base structure or in a theorem.
2. **It is selected.** At least one declaration is stated or proved only under
   the hypothesis, and at least one consumer supplies it from something other
   than the universal instance.
3. **Instance search is the right carrier.** The hypothesis propagates through
   enough call sites that threading it explicitly would dominate the API. A
   hypothesis used by one or two declarations should be an explicit argument.

Failing any of the three, prefer, in order: a field on the base structure, a
theorem, or an explicit hypothesis.

## Applying the rule

`Slicing` already carries `hn_exists`. Phase truncation at the boundary `0` is
therefore a theorem of every slicing, not a property of some slicings:

```lean
theorem Slicing.exists_phase_truncation_zero (s : Slicing C) (A : C) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C
```

`Slicing.toTStructure` consumes that theorem directly and takes no instance
parameter. `Slicing.toDualTStructure` in
`Foundation/Slicing/TwoHeartEmbedding.lean` was already written this way and is
the pattern to follow for further boundary constructions.

## Genuine classes in this subsystem

Classes that do discriminate — for example finiteness, boundedness, or
support hypotheses that hold for some triangulated categories and fail for
others — remain classes. The test is the first rule above: exhibit, or be able
to exhibit, an inhabitant that fails the class. A class whose only instance is
unconditional and global is a theorem wearing a class's clothes.

## Audit, 2026-08

Every `Prop`-valued class in the library was checked against rule 1. The
fifteen classes outside `HasPhaseTruncations` all pass: their instances are
either conditional on the same class (transport along a construction, as in
`IsExactPullback` and `IsTriangleAdditive`) or specialized to a single named
object (`𝟭 C` for the t-exactness classes, `free PUnit` and `unit R` for
`IsInvertible`, `Cdg A` for `IsPretriangulated`, `P.of` for `IsAdditive`,
`Proj (polynomialGrading ι k)` for `Variety.IsProjective`). None is discharged
unconditionally for every inhabitant of its base type. `HasPhaseTruncations`
was the only instance of the pattern.

The variety classes introduced when the bundled `Variety k` was retired
(2026-09-02) follow the same rule. `IsVariety k X`, `IsSmoothProperVariety k X`,
`Variety.IsProjective k X`, `SmoothProperVariety.IsK3Surface k X C`, and
`SmoothProperVariety.IsEnriquesSurface k X C` are `Prop` classes on
`X : Scheme` with `[X.Over (Spec (CommRingCat.of k))]`; their unconditional
instances are for named objects only, `Proj (polynomialGrading ι k)` and the
point `Spec (CommRingCat.of k)`, and every other instance is a parent
projection or is conditional on a class of the same family. The base field is
an `outParam` so that a conclusion mentioning no `k`, such as
`IsLocallyNoetherian X`, can still be found from the variety instance in scope.

## Promoting a private helper to enable a module split

Splitting an oversized module can require making a `private` helper public,
because `private` is scoped to the module and a helper cannot be referenced
across a file boundary. That promotion is a real cost: `private` marks
scaffolding that supports a construction without being part of its interface,
and every promotion turns scaffolding into a supported name that the axiom
audit records and that downstream code may come to depend on.

The rule is that a split does not by itself justify a promotion.

1. **Promote only what is actually referenced across the new boundary.** Do not
   promote a block wholesale. In particular, instances usually do not need
   promoting: a structure found by generic instance search — for example the
   `Pi` instances on a reducible `abbrev` — resolves without the named local
   instance being exported. Check by re-privatising and rebuilding, not by
   inspection.
2. **The promoted name must be worth supporting on its own terms.** If the
   helper only makes sense as a step in one proof, prefer keeping the module
   larger and reverting that cut.
3. **The name must read correctly at its new visibility**, and its docstring
   must state the supported meaning rather than what the proof needed.

Applying this in `#642` returned five of the seventeen helpers promoted by the
`#607` splits to `private`: the four rational-sections instances and
`nonemptyOfLE`, none of which is referenced outside its own module. The
remaining twelve are genuinely used across a boundary. `WeakUpperClosed` and
`cross` also pass rule 2 — the closed weak upper half plane and the planar
cross product are named concepts of the theory, not proof steps — as does the
rational-sections presheaf, which is a self-contained account of rational
functions on an integral scheme.

`AssociatedSheaf.RationalSections` stays under `Divisors/` despite not
mentioning divisors. Its only consumer is the divisor construction, and
`functionField` appears nowhere else outside `Divisors/`, so a general home
would be a subject boundary invented for one module. Move it when a second
consumer appears.
