# Reproduction and verification

Use the full selected proof SHA from the submission or commit-specific report.
A concise summary can be added in a later commit that explicitly identifies
the earlier proof commit. Raw execution logs and generated run-output files
are kept local, not committed. Do not infer that an older run checked later code.

## Selected proof and completed check

Selected proof commit: `3992abb235729e5ebd0359d897470d6101acf908`, branch `main`.
The [2026-09-28 report](../verification/2026-09-28/RESULT.md) records PASS for
that exact commit: default build, direct source, frozen type, proof dependencies,
axioms, module paths, negative control and all dependency pins. It used the
existing Windows checkout and local artifacts; no fresh-clone or cache-free
claim is made. The summary was first recorded in a later evidence-only commit. The current
tree retains that historical summary without the raw logs and run-output JSON.
Removing those files and updating the comparison docs does not constitute a
new verification run.

## Pins and prerequisites

- Lean: `leanprover/lean4:v4.30.0-rc2` (`lean-toolchain`).
- Prim: `a303f6bd23bb8f29a833d1d70327528359180995`.
- mathlib: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- LeanArchitect: `f1c14e1c14290117ffcb017cf2d089a6a5e1523a`.
- All 12 dependency URLs and commits: `lake-manifest.json`.

Requires Git, elan/the pinned Lean installation, dependency network access and
adequate memory/disk for mathlib. A first build may fetch dependency caches and
take much longer than a repeated build. If the pinned ProofWidgets frontend must
be rebuilt, its package needs Node.js/npm. Keep the manifest unchanged; do not
run `lake update`.

## Fresh-checkout instructions

Substitute the selected full 40-character SHA:

```text
git clone https://github.com/huam54925-cpu/jsp-001022-lean-extension.git
cd jsp-001022-lean-extension
git checkout --detach <FULL_COMMIT_SHA_FROM_SUBMISSION>
git rev-parse HEAD
git status --porcelain
lake build
lake env lean LeanCompletion/JSP001022.lean
lake env lean LeanCompletion/Audit.lean
```

The direct source command rechecks the extension text. The audit independently
states the exact target type, inspects all 15 supplemental theorem bodies,
prints the final theorem's transitive axioms and actual module locations.
Expected axioms: `[propext, Classical.choice, Quot.sound]`. The included command
is `#print axioms LeanCompletion.jsp_001022_original_enumeration_chain`.
No dependency on `sorryAx` or an additional axiom is allowed by this check.
Text search alone is not the axiom audit.

Run the negative control separately:

```text
lake env lean verification/Negative.lean
```

It must exit nonzero because `rfl` cannot prove `0 = 1`, not because of missing
imports or tools. It is outside the default library target.

## Recording a pinned local check

Use a clean tracked tree at the selected commit and the pinned Lean/Lake
executables. Remove inherited `LEAN_*`/`LAKE_*` path overrides from the child
environment, and capture output as UTF-8 bytes under the ignored
`verification/runs/` directory. Keep these records local; do not add or force-add
them to Git. The commands are:

```text
lake --no-cache --rehash --no-ansi build
lake --no-cache --no-build env lean LeanCompletion/JSP001022.lean
lake --no-cache --no-build env lean LeanCompletion/Audit.lean
lake --no-cache --no-build env lean verification/Negative.lean
```

Before and after, record source/config hashes and each dependency's Git HEAD and
tracked cleanliness against the manifest. Inspect `EXTENSION_MODULE` paths.
The first three commands must exit 0; the fourth must reject the intended `rfl`.
`--no-cache` does not erase existing artifacts or make a build cache-free. Cache
reuse must be disclosed. This procedure alone is not external-machine/human
verification, compiler bootstrapping or independent replay of all kernel terms.

## Historical results and version binding

The 2026-09-28 local extension check recorded PASS for the then-uncommitted tree:
compilation, frozen type, proof-body dependencies, standard axioms, module paths,
12 locked dependencies and negative control. It reused checked third-party
caches while compiling Prim Main and the extension locally.

The later initial contribution commit is
`b5c329089658e9853550a0eeb27985d2cc444873`. Its extension source, audit, toolchain,
Lake configuration and manifest were compared byte-for-byte with current files
and historical input hashes on 2026-09-28; they matched. This is content binding,
not a retroactive claim of fresh-checkout execution.

B8's earlier combined-file run is separate historical evidence.
`preparation.json` retains its preparation-time status. When available, use
the commit-specific summary under `verification/`, not that old status field.
Raw logs, execution records and generated run hashes are excluded by
`.gitignore`; the frozen target specification and negative-control source remain
tracked. A normal deletion commit removes files from the current tree, not from
older Git commits.

## Review scope

[Statement correspondence](STATEMENT_CORRESPONDENCE.md) records mathematical
conventions and the historical discrepancy. Mechanical PASS does not certify
interpretation, authorship, priority, official acceptance or award eligibility.
No official `lean-verify` skill run is claimed. Maintainer review and independent
reproduction remain pending.
