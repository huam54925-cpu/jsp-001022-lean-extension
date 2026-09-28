# Pinned proof verification: 2026-09-28

**PASS for proof commit `3992abb235729e5ebd0359d897470d6101acf908`**, branch `main`,
[original repository](https://github.com/huam54925-cpu/jsp-001022-lean-extension).
This is a historical summary of the selected proof version. The raw execution
logs and generated run-output files have been removed from the current tree.
This documentation and log-cleanup update did not rerun these checks.

## Executed checks

| Check | Result |
| --- | --- |
| Default `lake build` | PASS; 8327 jobs reported |
| Direct Lean check of `LeanCompletion/JSP001022.lean` | PASS |
| Independently stated frozen type | PASS |
| 15 supplemental theorem bodies and required dependencies | PASS |
| Transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Loaded module and search-path checks | PASS |
| Negative `0 = 1` control | Correctly rejected at `rfl` |
| 12 dependency Git revisions and tracked trees, before/after | PASS |
| Tracked source bytes equal selected commit, before/after | PASS |

Platform: Windows. Lean: `leanprover/lean4:v4.30.0-rc2`.
This was a clean **tracked working tree** on the existing local checkout, with
existing local build artifacts. It was not a fresh clone, a cache-free rebuild,
an external-machine run, compiler bootstrapping, or independent human review.
The source proof was directly rechecked even though dependencies were reused.
No official `lean-verify` skill execution is claimed.

## Retained evidence scope

This file records the previous run's results and limitations. Raw command output,
execution records, dependency/run snapshots and generated log hashes are not
distributed in the current repository tree. The original local run artifacts
remain local. This concise submitter summary is not an independent reproduction
or a newly executed PASS.

The selected commit, locked dependency manifest, proof source, audit module,
frozen target specification and negative control remain available for
reproduction. See [the verification instructions](../../docs/VERIFICATION.md).
The cleanup uses ordinary file deletion; older Git commits may still contain
the former run-output files.

## Semantic and attribution scope

[Statement correspondence](../../docs/STATEMENT_CORRESPONDENCE.md) supports the
current catalog's lower-density formulation and discloses the historical
lower/limsup discrepancy. It is a submitter assessment. Maintainer statement
acceptance and contribution attribution remain pending. No award or priority
claim follows from these mechanical checks.
