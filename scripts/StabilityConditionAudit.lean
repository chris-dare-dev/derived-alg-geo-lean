/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this project's declarations.

Run: `lake build StabilityConditionAudit` -- that elaborates every slice and
prints every record. Running this file alone prints nothing: records do not
replay across an import boundary, and since 2026-08-22 it imports no slices.

Part of the library build since 2026-08-04: a `lean_lib` with
`srcDir = "scripts"`. Removed from `defaultTargets` on 2026-08-06 -- this file
does `import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition`, so it sits downstream of every module and was
making every edit anywhere re-elaborate all 497 records before `lake build`
returned. It is still a `lean_lib` and CI's axiom-gate step still runs it, so
nothing it guarded is lost; you just have to name it. Its output backs the
`fidelity` block of `formalization.yaml`; re-run it before editing that block,
and paste what it actually prints.

Being in the build is not the same as being a gate. `#print axioms` prints
`[sorryAx]` and exits 0, so a sorry-backed declaration builds green here. What
the build catches is this file falling behind the source tree in one direction
only -- see below.

Reading the output: a declaration is clean iff its axiom list is a subset of
[propext, Classical.choice, Quot.sound]. Any other name -- above all
`sorryAx` -- is a failure, not a note.

## What this file covers, and what it does not

CORRECTED 2026-08-06. The first line of this comment used to read "over every
declaration this project introduces". It is not, and cannot be.

RE-MEASURED 2026-08-08 after the #88 HN-polygon port on main at b0b90ed. The
figures below are no longer a source-text estimate and are no longer maintained
by arithmetic. They come from a sweep of the built environment, so they count
what Lean actually has rather than what a regex can find at column 0:

```bash
lake build && lake env lean scripts/StabilityConditionCensus.lean
```

**REVISED AGAIN 2026-08-07 (later), and the correction is the useful part.**
The revision below reported a real gap of **59**. The true figure was **29**.
The other 30 were compiler-generated names the sweep did not recognise --
`<Struct>.ctorIdx`, `<Struct>.mk.inj`, `<def>.congr_simp`, and generated
`ext_iff`/`ext'_iff` companions of `@[ext]` theorems. Each family was then grepped for in
`DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/` and occurs there **zero** times, so none is a declaration
anyone wrote or could list. A later census correction added the likewise
source-absent `hcongr_*` family; `scripts/StabilityConditionCensus.lean` now filters all six.

The lesson is not that a number moved. It is that **a filter is itself a claim
about what Lean emits, and it needs the same check as any other claim here.**
The projection bullet below was written immediately after this exact mistake
was caught once. Catching it a second time, in the same file, on generated
names of a different shape, means the check has to be *grep the source for the
family* -- not *remember which families exist*.

Earlier revisions said **497 / 569 / 72 / 42 / 29 / 167** (2026-08-06), then
**670 / 814 / 144 / 44 / 59 / 189** (2026-08-07). PR #97 moved the first two of
those to **677 / 821** and nothing else; PR #104 corrected the theorem figure
to **488**. Both were right against the filter of the day, and both are
superseded here -- the 821 in particular counted the 30 generated names
described above. **Re-run the command; do not adjust the numbers.**

**THE GAP IS NOW ZERO, re-measured after the finite-type openness and
relative-HN consequences on 2026-08-16.** Every
public declaration in this library that is not a structure field projection is
named below. Be precise about what that does and does not mean -- three of the
four qualifications in this comment are unaffected by it:

* it does NOT cover the **166 private** declarations, which remain structurally
  unlistable;
* it does NOT make this file a gate by itself -- `#print axioms` still exits 0
  on `[sorryAx]`; CI's output checker and environment emitter supply the gate;
* it does NOT make the zero figure self-explanatory. The broader completeness
  ratchet now rejects an unlisted public declaration, but zero in the narrower
  authored/non-projection census is still a measurement that must be rerun.

* It issues **2885** audit commands. The environment holds **3214** authored
  declarations under the stability-condition modules under `DerivedAlgGeo`; the declarations outside the
  substantive hand audit are precisely the private declarations and structure
  projections. Selected generated declarations are additionally listed because the newer
  repository-wide completeness ratchet deliberately uses a broader census.
  ("Authored" excludes constructors,
  recursors, `casesOn`, matchers, equation lemmas, internal names, and the six
  generated families named above -- none of which anybody writes or could
  list.)
* **166 are `private`** -- 128 of them theorems -- and are *structurally*
  unlistable: Lean mangles a private name to `_private.<Module>.<n>.<Name>`,
  which cannot be written as a short name from an importing module. The
  instruction below cannot be followed for them, and no amount of diligence
  changes that.
* **242 are ungated structure field projections** emitted by the `structure` command.
  These are not a coverage gap in any useful sense; listing them would be noise.
  Some projections and generated constructor lemmas are nevertheless named below
  to keep the broader CI completeness ratchet from worsening. They are
  called out because a census that does not
  separate them reports a shortfall five times the real one.
* That leaves **0**. The literal-independence audit found 194 public names that
  had accumulated outside this list; all 194 were added on 2026-08-14.
* **The residue was dominated by one syntactic shape.** Five of the first 20
  and **seven of the last 10** are `@[simp] theorem` on ONE line, which a regex
  anchored on `^theorem` cannot see. That is 12 of the 30, and it is why the
  count is taken from the environment rather than from source text: the names
  hardest to notice by eye were, systematically, the ones left out.
* `scripts/check_audit.py` still checks only that this file's commanded output
  is complete and untruncated. The complementary CI gate
  `scripts/check_audit_complete.py` now enumerates public declarations and
  rejects growth beyond its recorded legacy ceiling. It is a ratchet rather
  than a zero-gap assertion because its intentionally broader census includes
  generated projections; `scripts/StabilityConditionCensus.lean` remains the precise measurement
  for the authored, non-projection claim above.
* **825 of the distinct gated declarations are not theorems** (103 `structure`, 722 other
  constructions).
  For a `def`, `#print axioms` reports the axiom closure of a CONSTRUCTION and
  asserts nothing about any proposition. In particular
  `CategoryTheory.Triangulated.StabilityMassTriangleInequality` appears below
formatted identically to the **1981** real theorems, but it is a `def ... :
  Prop` -- its clean line means the definition is axiom-clean, NOT that the
  proposition holds.

The environment-wide emitter (`exe/Emit.lean`) sweeps `Environment.constants`
and therefore does see the private and unlisted names. That, not this file, is
the gate that closes the hole.

**On Windows the emitter cannot be linked at all** -- `supportInterpreter`
pushes the PE export table past 65535 symbols, as `exe/Emit.lean` records -- so
on that platform this file is the only axiom check available. That is *not* a
reason to believe the environment is unswept there: `scripts/StabilityConditionCensus.lean` reads
the same module data through `lake env lean`, which links nothing, and so runs
where the executable cannot. Use it to size the gap; use the emitter, in CI, to
gate it.

Adding a declaration to the library means adding it here. This file is not
derived from the source tree, so it can silently fall behind; `#print axioms`
on a name that no longer exists is a hard error, but a name never added is
invisible.

Since #480 the records live in the per-area submodules under
`scripts/StabilityConditionAudit/`, and this file carries only the contract prose. It does NOT
import them: the `lean_lib` in `lakefile.toml` globs `StabilityConditionAudit.+`, so
`lake build StabilityConditionAudit` elaborates every slice in the directory whether
or not anything imports it. Adding a slice therefore needs no edit here.

That glob replaced a hand-maintained import list on 2026-08-22. The list had
silently fallen behind -- two slices were missing from it, so `lake build`
under-reported against the gates, which have always globbed the directory
themselves. Keeping the list complete also meant editing a trust-surface file
on every pull request that added a slice, which fired the trust guard on
routine work; see the note in `.github/workflows/trust-guard.yml` about why
that is how a gate stops being read.

`#print axioms` output does NOT replay across the import boundary, which is why
the gates run each area file directly rather than running this one; adding a
declaration means adding it to the area file its module belongs to.
-/

