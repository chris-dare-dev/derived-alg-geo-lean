# Agent observations

This is a small, append-only register for facts that caused navigation or
review friction during the DT1 loop. It is part of the OpenSpec plan so future
agents can treat it as repository context rather than private chat memory.

## Repository inconsistencies

- The live #928 and #929 issue descriptions still name `Families/` tensor files,
  but the repository's current ownership documents and imports place tensor
  code under `DerivedCategory/Tensor/` after the MO1.10 extraction.
- #928 still describes #892 as a blocker even though #892 is closed and its
  bounded monoidal restriction is present on `origin/main`.
- The main user checkout contains unrelated dirty work and is substantially
  behind `origin/main`; loop work must start from a clean dedicated worktree.

## Time sinks and confusion points

- A clean worktree does not automatically have the local `.lake` package cache;
  targeted Lean builds need the repository's existing cache/junction setup.
- The repository explicitly forbids whole-repository local builds, while older
  issue acceptance text still mentions a full build. The current AGENTS and
  CONTRIBUTING instructions are the operative local policy.
- The generic K-flat-resolution implementation already supplies localization
  machinery but does not itself expose every per-argument
  `Functor.IsLeftDerivedFunctor` witness required by #929; future agents should
  distinguish reusable construction from the missing universal-property layer.
- The current cache snapshot does not contain `MathFormalContract.olean`, so a
  direct audit-file elaboration reports a missing external module even after the
  tensor target is green. `lake build @MathFormalContract` is not a safe
  dependency-only command here: it resolved through the root package and began
  a roughly 4,000-target repository graph before it was interrupted. Future
  agents must use a verified package-specific runner/cache path rather than
  guessing Lake's `@` target syntax.
- The cold-cache focused tensor build itself traversed about 3,264 dependencies
  because the compatible cache was incomplete; it remained a single named
  target, but repeated retries are expensive. Preserve the compatible cache
  junction and prefer one quiet named build after source changes.

## Maintenance rule

Add observations here only when they are verified against checked-in files,
live issue state, or a reproducible command. Do not turn a stale issue path or
an agent's guess into a new architecture rule without reconciling it against
the canonical owner documents.
