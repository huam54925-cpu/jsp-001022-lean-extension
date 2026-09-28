# Repository working rules

Read [docs/REPOSITORY_POLICY.md](docs/REPOSITORY_POLICY.md) before committing or
publishing changes. It defines the allowed source/configuration/documentation
files and the output that must stay local.

- Keep raw logs, command/audit output, generated run JSON, chat/API dumps,
  credentials, downloaded dependency sources and build products out of commits.
  Keep local run
  artifacts under the ignored `verification/runs/` directory. Do not force-add
  ignored files or rename output to bypass this rule.
- Stage explicit paths and deletions, then review the staged diff. Never use
  blanket `git add .` or `git add -A`.
- For documentation or log cleanup, preserve Lean source, the frozen target,
  toolchain, dependency pins and the selected historical proof commit. Do not
  describe historical PASS results as a newly executed check.
- Default to local edits. Commit/push when the user requests it; use the
  authorization already given for that change without asking again.
- Uploading to our proof repository does not authorize an official awards PR,
  maintainer contact or a visibility change. Those need a separate explicit
  user request. Verify the destination before pushing.
- Use ordinary commits and non-forced pushes. History rewriting or historical
  log removal requires a specific request.
