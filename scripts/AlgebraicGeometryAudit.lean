/-
Axiom audit. First build the optional specialization and development modules listed in
`README.md`, then run: `lake build AlgebraicGeometryAudit` -- that elaborates every
slice and prints every record. Running this file alone prints nothing.

Every line must print either "does not depend on any axioms" or exactly
`[propext, Classical.choice, Quot.sound]`. Any occurrence of `sorryAx` is a
failure: this library has no `sorry`, and the trust boundary is carried by explicit
data and proposition witnesses, which are visible in theorem types rather than holes.

Since #480 the records live in the per-area submodules under
`scripts/AlgebraicGeometryAudit/`, and this file carries only the contract prose. It does NOT
import them: the `lean_lib` in `lakefile.toml` globs `AlgebraicGeometryAudit.+`, so
`lake build AlgebraicGeometryAudit` elaborates every slice in the directory whether
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

