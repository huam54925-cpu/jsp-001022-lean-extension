# Reproduction and verification

Use the full selected proof SHA from the submission or commit-specific report.
Evidence can be added in a later commit that explicitly identifies the earlier
proof commit. Do not infer that an older run checked later code.

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
environment, capture output as UTF-8 bytes, and record:

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
commit-specific records under `verification/`, not that old status field.

## Review scope

[Statement correspondence](STATEMENT_CORRESPONDENCE.md) records mathematical
conventions and the historical discrepancy. Mechanical PASS does not certify
interpretation, authorship, priority, official acceptance or award eligibility.
No official `lean-verify` skill run is claimed. Maintainer review and independent
reproduction remain pending.
