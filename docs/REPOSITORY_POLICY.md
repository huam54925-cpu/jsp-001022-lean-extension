# Repository content and publication policy

This policy records what belongs in
[`huam54925-cpu/jsp-001022-lean-extension`](https://github.com/huam54925-cpu/jsp-001022-lean-extension)
and how changes may be submitted. Raw execution logs remain local.

## Content that may be committed

| Content | Allowed paths and purpose |
| --- | --- |
| Proof and audit source | `LeanCompletion.lean`, `LeanCompletion/*.lean` |
| Reproducible project configuration | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` |
| Statement and verification inputs | `verification/targets.json`, `verification/Negative.lean` |
| Curated documentation | `README.md`, `docs/*.md`, including the comparison with plby, attribution and reproduction instructions |
| Concise historical check summary | `verification/YYYY-MM-DD/RESULT.md`, identifying the exact proof commit, checks, outcomes and limitations |
| Repository rules | `.gitignore`, `AGENTS.md` and this policy |
| Historical extraction metadata | The existing `preparation.json`, explicitly identified as historical rather than current verification status |

An allowed path is not permission to change its contents outside the requested
task. New categories of tracked files should be justified in the review of that
change. A verification summary is an authored summary, not a pasted transcript.

## Content that stays local

- Raw logs, standard output/error, command transcripts and full theorem/audit
  dumps, including `*.log`, `*.log.*`, `logs/` and `verification/runs/`.
- Generated run-output JSON and log inventories: command vectors and timings,
  run results, dependency snapshots and generated run/log hash manifests.
  Dated verification directories publish only the curated `RESULT.md`.
- Downloaded API responses, discussion/chat transcripts, scratch notes and
  temporary audit inventories. Their file extension does not change this rule.
- `.lake/`, downloaded dependency source, build products, binaries and archives.
- Credentials, tokens, authentication configuration and private identity data.

The tracked `verification/targets.json` is a verification input;
`lake-manifest.json` locks dependencies. They are not generated run logs and
remain tracked. Do not force-add ignored output or rename it to bypass this
policy. Future local runs should write artifacts under `verification/runs/`.

## Preserve proof and evidence boundaries

For documentation and log-cleanup changes, leave Lean source, frozen target,
toolchain and dependency pins unchanged. Preserve the selected proof commit
`3992abb235729e5ebd0359d897470d6101acf908` as the version identified by the
historical verification summary; a later documentation commit is not a new
proof verification. Proof changes require a task that actually calls for them
and checks appropriate to those changes.

Do not relabel old results as a new build, fresh-clone replay, independent review
or official acceptance. Record reused caches and other material limitations.
Retain the original attribution of Prim and the distinction between this
extension and plby's existing formalization.

## Before committing

1. Check the branch, working tree and exact changed-file list. Preserve unrelated
   user changes.
2. Stage an explicit list of files and deletions with `git add -- <paths>`.
   Do not use blanket staging such as `git add .` or `git add -A`.
3. Inspect the staged diff and resulting tracked-file list. Confirm that no raw
   output or private material is being added and that removed logs are staged
   as deletions. `.gitignore` does not untrack files already in Git.
4. Check document links and `git diff --cached --check`. For a documentation-only
   change, verify protected proof/configuration bytes are unchanged; do not
   claim a new Lean build unless it was actually run.

## Commit, push and official PR are separate actions

Local edits are the default. Create a commit or push only when the user requests
that action; an existing explicit authorization for the current change is
sufficient and need not be requested again.

An instruction to upload to **our repository** authorizes only the named proof
repository and agreed branch, normally `origin/main`. Verify that `origin`
points to `huam54925-cpu/jsp-001022-lean-extension` before pushing. It does not
authorize opening, reopening or updating a PR in `TheJustinSunPrize/awards`,
contacting maintainers, or changing repository visibility. Those require a
separate explicit request. Preserve the user's current visibility setting.

Use an ordinary commit and non-forced push. Do not amend published commits,
rewrite history, force-push, or delete remote branches without a specific
request. Removing a log from the current tree does not erase it from older Git
commits; historical removal is a separate operation.
