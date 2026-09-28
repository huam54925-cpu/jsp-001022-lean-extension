# Pinned proof verification: 2026-09-28

**PASS for proof commit `3992abb235729e5ebd0359d897470d6101acf908`**, branch `main`,
[original repository](https://github.com/huam54925-cpu/jsp-001022-lean-extension).
The files in this evidence directory are added in a later commit and describe
that selected proof version, not an unexamined later proof version.

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

## Evidence

- [Result and time bounds](result.json)
- [Command vectors, exit codes and durations](commands.json)
- [All selected-commit tracked-file hashes](source-sha256.json)
- [Checked dependency revisions](dependencies.json)
- [Build transcript](build.log), [direct source transcript](direct-source.log)
- [Axiom, frozen-type, dependency and module output](audit.log)
- [Negative-control rejection](negative.log)

Machine-local project, run, Python and toolchain paths in transcripts and command
records have been replaced by placeholders. The direct-source log is empty
because that successful command emitted no output. Published-file hashes are
in [sha256.json](sha256.json); [original log hashes](original-log-sha256.json)
identify the unredacted local originals. Hashes establish byte identities, not
independent evidence of correctness.

## Semantic and attribution scope

[Statement correspondence](../../docs/STATEMENT_CORRESPONDENCE.md) supports the
current catalog's lower-density formulation and discloses the historical
lower/limsup discrepancy. It is a submitter assessment. Maintainer statement
acceptance and contribution attribution remain pending. No award or priority
claim follows from these mechanical checks.
