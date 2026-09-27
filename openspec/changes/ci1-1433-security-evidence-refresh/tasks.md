# Tasks

## 1. Refresh evidence

- [x] 1.1 Reconcile exact provider evidence for the four original failures, the later successful PR runs, the latest failed run, and current PR heads with no check; retain run/check URLs, full head SHAs, and observation date.
- [x] 1.2 Update `docs/ci/github-advanced-security.md` with the dated evidence, provider-failure versus successful-but-unverified versus missing classifications, and owner decision options with coverage tradeoffs.
- [x] 1.3 Verify the report contract with `openspec validate ci1-1433-security-evidence-refresh --strict --no-interactive`, `git diff --check`, and `python3 -m unittest scripts.tests.test_security_evidence`.

## 2. Publish progress

- [ ] 2.1 Run `scripts/precheck.sh` and record its local-only results; require hosted `ci` on the exact progress PR head.
- [ ] 2.2 Obtain the four independent review roles on the same exact commit, with no more than three improve/review rounds.
- [ ] 2.3 Publish and merge a progress-only PR after the review ledger and required `ci` check pass; record a non-closing progress comment on #1433 and keep the issue open for an owner disposition and current PR/main scan evidence.
