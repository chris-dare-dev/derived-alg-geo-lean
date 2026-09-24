# Tasks

## 1. SF8.5 construction (#554)

- [x] 1.1 Inventory the existing derived pullback interfaces and freeze the independent #554 progress manifest, including the Dqc leaves, public umbrella, scheme-derived audit, task checklist, and generalization backlog; verify its structural trust-boundary and source-independence preflight
- [ ] 1.2 Construct a functorial K-flat resolution of every unbounded complex
  in X.Modules for each scheme X; for every arbitrary f : T ⟶ U in
  SchemeBaseChange S, prove pullback acyclicity and inhabit
  LeftDerivedPullback f without caller-supplied preservation assertions. Add no
  boundedness, quasicoherence, Noetherian, flatness, or exactness restriction;
  leave preservation and coherence to tasks 1.3–1.4; verify targeted Lean
  declarations and no-sorry checks.
- [ ] 1.2a Add the natural, explicitly `M.val.Elements`-indexed coproduct
  epimorphism for sheaves of modules on small ringed sites, and specialize it
  to `X.Modules`; prove the stalk formula and stalkwise flatness of the
  canonical free-Yoneda module sheaves on opens of every scheme. State the
  universe bound and verify the targeted Lean build and declaration audit.
  This prerequisite does not construct projective or K-flat resolutions and
  does not prove arbitrary pullback acyclicity.
- [ ] 1.3 Prove supported pseudo-coherence, finite-Tor, and negative-Ext preservation; verify targeted Lean tests and the relevant audit scripts
- [ ] 1.4 Add the five coherence laws, comparison/agreement result, and non-flat nonidentity example; verify targeted Lean checks and mathematical adversarial review
- [x] 1.5 Add the explicit `ℤ → ZMod 2` non-flat/nonidentity affine witness as a progress chunk; verify the supported pullback instantiation, full Lean build, and non-closing PR policy
- [x] 1.6 Compute one explicit nonzero degree-minus-one homology witness for `ℤ → ZMod 2` from a two-term free resolution; connect it to the supported affine bounded-projective representative, preserve the non-generalization boundary, and use a non-closing PR policy
- [x] 1.7 Prove a concrete comparison between the restriction of scalars of the affine witness's `H^{-1}` and `CategoryTheory.Tor (ModuleCat ℤ) 1`, using the explicit projective resolution and the chain/cochain degree correspondence; keep the theorem affine and example-specific, update the audit and tooling-friction log, and use a non-closing progress PR
- [x] 1.8 Compare the actual degreewise scheme-module pullback of the sheafified two-term free resolution along `zmodTwoSchemeMap` with the sheafification of `baseChangedResolution`; transport its nonzero `H^{-1}` to the target scheme-module derived category, audit all public declarations, and make no left-derived-pullback or general K-flat claim
- [x] 1.9 Descend the affine tilde/pullback comparison through derived localization on the full K-projective derived locus for arbitrary commutative-ring maps; apply it to the existing `ℤ → ZMod 2` representative, audit all public declarations, record only genuinely deferred generalization lifts, and make no all-scheme-module or arbitrary-scheme-morphism claim

Tasks 1.5, 1.6, and 1.7 are historical merged progress chunks: the nonflat
witness is PR #1404, the derived-effect chunk is PR #1457, and the concrete
Tor comparison is PR #1464. Issue #554 remains open; tasks 1.2–1.4 are still
outstanding. Task 1.8 was implemented by PR #1471 and is checked here in the
post-merge plan sync. Task 1.9 is a further affine progress slice and does not
complete task 1.2. Its separate manifest does not schedule #522 or #525; those
downstream tasks remain blocked on #554's eventual complete closure.

Task 1.2a is the flat-generator prerequisite tracked by issue #1495. Its
completion supplies actual flat generators and a natural epimorphism, not a
K-flat replacement of unbounded complexes; task 1.2 remains unchecked until
its own full construction and pullback-acyclicity obligations are proved.

The loop-controller digest normalizes task-checkbox state, so an active task
may be checked in its implementation PR. Task wording and the other required
OpenSpec artifacts remain frozen after ledger initialization. Task 1.7 was
synced after PR #1464 merged; task 1.8 was synced after PR #1471 merged.

## 2. SF9.2 algebraicity (#522)

- [ ] 2.1 Freeze the supported moduli root and its canonical owner; verify abstraction and import-boundary review
- [ ] 2.2 Prove the supported atlas as an actual scheme morphism; verify the atlas acceptance scenarios and targeted build
- [ ] 2.3 Prove the supported diagonal and local-finiteness morphism statements; verify the corresponding targeted build and no-sorry gate
- [ ] 2.4 Run the full repository audit surface and record the three-lens review ledger; verify self-hosted CI required checks are green

## 3. SF9.3 semistable reduction (#525)

- [ ] 3.1 Revalidate live issue dependencies and create a separate frozen chunk only after #522 and the relative-HN input are available; verify the controller rejects premature execution
- [ ] 3.2 Formalize the supported DVR/Dedekind diagrams, permitted base change, semistable replacement, and uniqueness/S-equivalence boundary; verify targeted Lean gates
- [ ] 3.3 Add the quasi-properness adapter at the actual algebraic-moduli layer; verify the OpenSpec scenarios, audits, and full gates
