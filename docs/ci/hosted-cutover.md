# Proposed hosted-only CI cutover for CI1.07

This is a staged plan for #1436, not a record of an applied routing change.
The public repository currently has four registered Ubuntu runners. Its
`pull_request` and `merge_group` builds are hosted, while `main` push and
manual builds use those persistent runners. A pull request can change the
workflow file used by its own run, including `runs-on`; the expression in
`ci.yml` cannot keep that PR away from the repository runners. The existing
fork approval policy and read-only default token reduce other risks but do
not enforce runner placement. The services also share one Unix account, so
their separate build directories are not a hostile-code boundary.

The proposed end state is one hosted `build` job for every `ci.yml` event,
with no self-hosted runner registered to the public repository. The required
aggregate check remains named `ci`, and strict up-to-date branch protection
remains enabled. This end state gives up persistent-main and manual-branch
builds. It does not by itself prove that the required `ci` result reflects
an unmodified gate inventory; #1434 owns candidate and gate provenance.

## Admission before rollout

The owner must explicitly select this routing and its rollback, including
the disposition of #1436's self-hosted parity, physical-host pressure and
cancellation acceptance items and its #1434/#1435 blockers. The loop may
prepare and review this patch, but its authority does not include repository
settings or runner registration changes. Do not merge the routing patch as
an unattended PR while the four registrations remain available.

Before the maintenance window, obtain four same-commit reviews of the patch.
Run the PR workflow on its updated synthetic merge commit; record the PR head,
merge commit, workflow blob, required `ci` result, and `build` runner name.
Confirm that the `build`, `roadmap`, and `ci` jobs still appear once each and
that `ci` remains the strict required context. The PR's hosted result is a
preflight of the new YAML, not an enforcement test while runners still exist.

## Coordinated rollout

1. Disable auto-merge for the cutover PR. Pause other merges and manual
   dispatches, and let current main/manual runner jobs finish. Record their
   final run IDs. An already-running job must not be killed to establish the
   boundary.
2. Stop the four runner services and verify they are offline. Remove all four
   repository runner registrations using the owner-controlled GitHub runner
   settings and host removal procedure. Check the repository runner API until
   `total_count` is zero. Stopping a service alone leaves its registration and
   can be reversed accidentally; the zero-registration check is required.
   During this short interval the old main workflow cannot obtain a build
   runner, so keep merges and dispatches paused.
3. Mark the reviewed PR ready, re-check its exact head and required `ci`, and
   merge through normal strict protection. Do not bypass a check or use an
   administrative merge. The resulting main push must run `build`, `roadmap`,
   and `ci` on hosted runners. Record the main SHA and run ID, confirm the
   workflow blob is the reviewed one, and compare the tested PR merge tree
   with the published tree.
4. Resume merges and manual dispatch only after the main `ci` succeeds.
   Confirm again that the repository runner count is zero. For a bounded
   negative test, submit a disposable PR whose only workflow change requests
   one of the old self-hosted label sets. Verify it obtains no runner, cancel
   the queued run, and close the test PR. Do not infer isolation merely from
   an offline service or a successful benign PR.

If the PR becomes stale or its content changes, get a fresh required run on
the updated head. A changed routing diff also needs a fresh four-role review.
Keep the exact run, job, runner, tree, and registration evidence with #1436.

## Rollback and failure

Keep the public repository runners deregistered. Repair or revert the hosted
workflow through a reviewed PR that still uses hosted runners and produces the
required `ci` result. Do not restore repository self-hosted registrations or
the old `runs-on` labels as a rollback: that would reopen the PR-to-runner
path. If hosted CI is unavailable, leave merges paused until a hosted repair
can pass strict protection. A future self-hosted design requires a separate
provider-enforced runner boundary and its own owner-approved rollout.

This cutover does not close #1436 until the owner has accepted the changed
routing scope and the exact PR/main and negative-path evidence exists. The
three earlier equal-tree, warm-cache hosted/self-hosted observations remain in
[`routing-parity-2026-09-27.md`](routing-parity-2026-09-27.md); they do not
substitute for the cutover checks.
