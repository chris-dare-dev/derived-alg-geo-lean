# Agent observations

## Baseline: 2026-09-19/20 UTC

- Issue #570 remained open with `blocked` and `research` labels even though
  #584, #585, #586, #833, and the #806-shaped follow-up #1143 had landed. The
  issue comments explicitly call the `blocked` label stale. Treat these labels
  as tracker residue, not as evidence that the theorem is still blocked; remove
  them before controller preflight and record the repair in the issue handoff.
- The original issue body still describes the `Γ_*`/Serre-correspondence route.
  The landed proof instead follows chart generation, one uniform twist,
  local-combination global generation, and the explicit tensor inverse of
  `O(N)`. Future reconnaissance should check the current declarations before
  reopening the original route.
- `TwistSection.lean` says its multiplication maps are what #570 step 1 asks
  for. That is historically true but operationally misleading after the
  direct route landed: the maps are consumed by `GlobalGeneration.lean`, not
  by a new graded-module correspondence. `Glue.lean` similarly points at the
  global-generation half without naming the final `TwistInverse.lean` step.
- The repository distinguishes UTC dates under `.claude/` from local dates in
  top-level notes. Do not normalize those timestamps while recording loop
  evidence.

## Loop/controller practices worth preserving

- Remote comments, pushes, PR creation, approval, merge, and issue closure
  must go through `scripts/loop_engine.py action ...`; read-only `gh` queries
  remain useful for live verification.
- The controller's frozen-path check historically used `.lstrip("./")`, which
  can misclassify `.claude/...` as outside a frozen list. If encountered,
  record it and use a temporary, exactly-restored controller repair rather than
  weakening the manifest.
- Required-check lookup may expose workflow names differently from check-run
  names (for example `CI` versus `ci`). Treat the latest provider status as
  authoritative only after checking this mapping; do not bypass a required
  check or use administrator merge to hide it.
- A long CI run can make `origin/main` advance. Verify PR base/head and the
  reviewed commit before any merge, and keep any base-only synchronization
  outside the frozen mathematical diff. Never start a fourth adversarial round
  just because the provider moved the base.
- Do not run `scripts/gates.sh` or an umbrella `lake build` locally. Use named
  targets and `scripts/precheck.sh`; the remote required checks are the CI
  verdict.
- The named `DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInverse`
  build stalled for roughly two minutes in this fresh worktree without starting
  a Lean child or printing a diagnostic while other shared runner processes were
  active. It was stopped and is locally inconclusive; the no-build precheck was
  green (with `SKIP_ACTIONLINT=1` because the binary is absent), and remote CI
  remains the authoritative build evidence.
- After the closeout commit, controller preflight still reports the two
  bootstrap failures `HEAD ... is not exactly origin/main` and `current branch
  already uses planned issue branch agent/aut1-570-serre-closeout`. This is a
  controller sequencing mismatch for a newly created manifest: the manifest
  and frozen files must be committed before the controller can digest them, but
  preflight requires the pre-implementation base checkout. Keep the failure in
  the record and preserve the exact base/head guards for later PR actions.

## Adversarial correction and fresh frozen chunk: 2026-09-19 UTC

- Round 1 mathematics review found a real boundary mismatch: the public
  `exists_shortExact_coproduct_twist` declaration was nested under a namespace
  context requiring `[Nontrivial ι]`, while the OpenSpec scenario correctly
  describes finite nonempty `ι` and therefore includes the singleton-index
  presentation of `P⁰`. The correction moves the `[Nontrivial ι]` requirement
  back onto the cohomology-finiteness declarations and gives the presentation
  theorem only `[Nonempty ι]`.
- This source correction is a material frozen-scope change discovered by the
  first review, so it is carried by a fresh manifest/chunk rather than being
  silently appended to the original ledger. The superseded round-1 ledger is
  retained under `.loop-runs/` as audit evidence; the new ledger starts the
  bounded review count for the corrected chunk.
- The named target
  `DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Projective` completed
  successfully after the correction. The local no-build precheck was also
  green with `SKIP_ACTIONLINT=1`, because `actionlint` is not installed; that
  local result is not a substitute for remote CI.

## Terminal review evidence and fresh documentation-hygiene chunk: 2026-09-20 UTC

- The corrected scope-correction chunk used all three permitted review rounds.
  Round 3 was adjudicated `blocked` by the controller, as required, after the
  mathematics reviewer found two additional stale claims in `Glue.lean`: the
  alternative-twist warning was ambiguous about the intermediate
  `F(e*n)(2*e*m)` comparison, and the degree-one-generation paragraph said
  that `O(n)` is not locally free rather than saying that the general
  guarantee is unavailable. No fourth review was run.
- Those two exact documentation findings are carried by a separately named
  `aut1-570-doc-hygiene` manifest/chunk with a fresh ledger. This is an
  explicit new frozen chunk, not a mutation of the blocked ledger or a hidden
  fourth round. Its scope remains issue #570 and the same existing theorem
  API; it only makes the already-frozen guidance precise before PR creation.
