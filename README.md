# JSP-001022 extension of pinned Prim

Local staging project, 2026-09-28. No public repository or contribution commit has been created here.

## Contribution boundary

`LeanCompletion/JSP001022.lean` contains only the 15 supplemental declarations extracted from the B8 file with SHA256 `5cb6b69c8f6128111a79a6063cbaeb903e188166b9c23be43dbfb3b98eac7935`. The extraction begins at `LeanCompletion.jsp_001022_eventual_lower_bound` and ends after `LeanCompletion.jsp_001022_original_enumeration_chain`.

The file imports `LeanMarathon.Main` from [Prim](https://github.com/YuanheZ/Prim) at commit `a303f6bd23bb8f29a833d1d70327528359180995`. The 14592-line upstream proof prefix is not included in this contribution's source files. The upstream chain construction remains credited to Prim/LeanMarathon and its earlier sources. The additions are the density bridge and support lemmas, explicit wrapper, cutoff/density/enumeration conversions, and final composition; they are not a new proof of the upstream chain construction.

No upstream authorization has been obtained. This layout avoids redistributing the upstream prefix in our contribution; it is not a grant of rights or a legal determination about dependency use. No blanket license is attached. Author attribution and applicable permissions must be settled before public submission.

## Entry points

- `LeanCompletion/JSP001022.lean`: the supplemental proofs.
- `LeanCompletion/Audit.lean`: frozen-type check, theorem check, transitive axiom output, proof-body dependency query and module-resolution probe.
- `verification/Negative.lean`: deliberately false equality, expected to fail at `rfl`; never include it in a default build target.
- `preparation.json`: extraction hashes and upstream-prefix comparison.
- `verification/targets.json`: exact frozen theorem type and required dependencies.

Target theorem: `LeanCompletion.jsp_001022_original_enumeration_chain`.
The toolchain remains `leanprover/lean4:v4.30.0-rc2`.
The root manifest is derived from the pinned Prim manifest, with Prim itself added as a direct dependency. It now contains 12 dependencies, including Prim and repl. Its resolution and compilation require a new check; B8's original 10-package environment is not assumed identical.

## Verification scope

B8 PASS is historical evidence for the old combined file only. It does not certify this imported-module layout. Local check results are recorded separately under `verification/runs/`; no success should be claimed without a completed `verification.json` there.

The local checker may copy matching third-party build caches from the B8 dependency directory after checking Git revisions and tracked cleanliness. It never copies the old `Aaa` proof artifact or an existing Prim Main build. Any such cache reuse is reported. This is not another clean-from-zero build and not external-machine reproduction.

Commands after dependencies are prepared:

```powershell
lake --no-cache --rehash --no-ansi build "+LeanCompletion.JSP001022:olean"
lake --no-cache --no-build env lean LeanCompletion/Audit.lean
lake --no-cache --no-build env lean verification/Negative.lean
```

The first two must exit 0; the last must reject `rfl` for `0 = 1`, not fail at an import. Capture native output as raw UTF-8 bytes. Also verify source hashes, dependency revisions, loaded module paths and the exact frozen statement. Do not run `lake update` or change pins during verification.

Once the final contribution commit exists, verify that exact commit and bind its SHA to its own results. A successful check of this uncommitted local tree is not a check of a future commit. Original-problem semantic acceptance remains separate.

## Publication exclusions

Do not publish `.lake`, dependency source checkouts, compiled artifacts, the historical combined `Reproduction.lean`/`FullProof.lean`, or an archive of the working directory. `.gitignore` is a guard, not a substitute for inspecting tracked files and the outgoing diff. Keep upstream URLs, commit pins and contribution attribution. Decide the public repository and permitted evidence files only after the local result and permissions are reviewed.
