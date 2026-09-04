## Outcome

<!-- What mathematical or repository result does this change deliver? -->

## Architecture

- [ ] Placement tier named for every new or moved public root: the Mathlib path it extends, or the Mathlib precedent it follows.
- [ ] Canonical root named (declaration and module).
- [ ] Root-to-consumer import direction stated; the old consumer path is not retained as a shim.
- [ ] Specialization uses an instance, projection, `extends`, `abbrev`, or a proved comparison; it does not copy the root.
- [ ] Two consumers are named, or the statement-layer exception is explained.
- [ ] Existing and transported instances have an agreement/diamond test where both paths exist.
- [ ] Generic roots do not import geometric, stability-specific, or paper-specific leaves.
- [ ] Any rejected generalization is recorded with its counterexample.
- [ ] The structural cutover ledger is updated for completed or newly confirmed lanes.

See `docs/architecture/placement.md` and `docs/architecture/abstraction-tree.md`.

## Trust and verification

- [ ] No `sorry`, `admit`, or hidden axiom was added.
- [ ] New public declarations are in the appropriate axiom audit.
- [ ] Focused build and relevant fast gates pass.
- [ ] Full verification is delegated to the repository runners before merge.
