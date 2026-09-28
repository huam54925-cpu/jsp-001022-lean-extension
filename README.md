# JSP-001022: logarithmic density and divisibility chains

Lean formalization of the positive lower logarithmic density formulation of
[JSP-001022](https://github.com/TheJustinSunPrize/awards/blob/8332eaab70094567cb3a2137e33b6ea5a2e316d8/problems/catalog-1001-1022.md#JSP-001022),
also indexed as [Erdős Problem #1217](https://www.erdosproblems.com/1217).
The contribution consists of a density bridge and statement conversions over
the existing, commit-pinned Prim chain theorem.

## Mathematical statement

Let `a₁ < a₂ < ...` be positive integers with

$$
\liminf_{x\to\infty}\frac{1}{\log x}\sum_{a_i<x}\frac{1}{a_i}>0.
$$

There are strictly increasing positive indices `k₁ < k₂ < ...` such that
`a(kᵢ)` divides `a(kᵢ₊₁)` and

$$
\limsup_{x\to\infty}\frac{\#\{i:a_{k_i}<x\}}{\log\log x}
\;\geq\;
\limsup_{x\to\infty}\frac{1}{\log\log x}
   \sum_{2\leq a_i<x}\frac{1}{a_i\log a_i}.
$$

The counting limsup is in `[0,+∞]`. The doubly harmonic weight is defined for
integers at least 2 and extended by zero at 1. The reciprocal density includes 1
normally. The precise conventions and quantifier order are explained in
[Statement correspondence](docs/STATEMENT_CORRESPONDENCE.md).

Target:
[`LeanCompletion.jsp_001022_original_enumeration_chain`](LeanCompletion/JSP001022.lean#L1136).
Its [exact type](docs/STATEMENT.md) is separately stated and checked by
[the audit module](LeanCompletion/Audit.lean). It has no extra unproved hypotheses
beyond the displayed assumptions.

## Mathematical and formalization sources

The mathematical solution is Alexeev, Barreto, Li, Lichtman, Price, Shah, Tang
and Tao, *Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond*,
[arXiv:2605.00301v1](https://arxiv.org/abs/2605.00301v1), Theorem 1.6 and Section 9.
The historical counting conjecture is [Erdős–Sárközy–Szemerédi (1966), p. 432,
equation (5)](https://www.renyi.hu/~p_erdos/1966-09.pdf#page=2).
The historical p. 431 has a prose/formula discrepancy about lower versus upper
density, explicitly recorded in the [correspondence document](docs/STATEMENT_CORRESPONDENCE.md#historical-source-discrepancy).
The target follows the current catalog's lower-density formulation.

The proof imports [`LeanMarathon.Main`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean)
from Prim at `a303f6bd23bb8f29a833d1d70327528359180995`.
Prim's 14,592-line base formalization remains credited to Prim/LeanMarathon and
its earlier sources. It is fetched as a dependency, not vendored here.

The 1,200-line extension contains 15 declarations: finite Abel and weighted
estimates, the lower-logarithmic to upper-doubly-logarithmic density implication,
an explicit upstream application, cutoff and density-type conversions, positive
enumeration and subsequence conversions, and final composition.
[Attribution](docs/ATTRIBUTION.md) identifies each declaration and separates
supplemental proofs from wrappers and engineering work. AI assistance was used.
No mathematical-discovery or first-formalization claim is made.
[Comparison with plby](docs/COMPARISON_WITH_PLBY.md) records the shared
mathematical route, distinct finite Abel implementation, plby's stronger density
comparison, and our contribution relative to Prim.
[Related submissions](docs/RELATED_WORK.md) are identified; an existing
formalization of the same problem does not by itself rule out a distinct
contribution.

## Reproduce

Requires Git and the Lean toolchain specified by `lean-toolchain` (normally
installed through elan). Substitute the full 40-character commit from the
submission or verification report and keep `lake-manifest.json` unchanged.

```text
git clone https://github.com/huam54925-cpu/jsp-001022-lean-extension.git
cd jsp-001022-lean-extension
git checkout --detach <FULL_COMMIT_SHA_FROM_SUBMISSION>
lake build
lake env lean LeanCompletion/JSP001022.lean
lake env lean LeanCompletion/Audit.lean
```

Lean is `leanprover/lean4:v4.30.0-rc2`; mathlib is pinned to
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. All 12 dependency revisions are in
`lake-manifest.json`. Do not run `lake update` or upgrade the toolchain.
See [Reproduction and verification](docs/VERIFICATION.md) for first-build setup,
the negative control, actual evidence scope and cache reuse.

The recorded local extension audit found exactly these transitive axioms:

```text
propext
Classical.choice
Quot.sound
```

It also verified the exact target type, actual proof-body dependencies,
dependency pins and module paths. It was a same-host check with declared
third-party cache reuse. Commit-specific results and their limitations are
listed in [the verification document](docs/VERIFICATION.md).

Selected proof commit: `3992abb235729e5ebd0359d897470d6101acf908` (`main`).
[The historical verification summary](verification/2026-09-28/RESULT.md)
records PASS for build, direct source, exact type, dependencies and axioms on
Windows, with existing local artifacts reused. Raw logs and generated run-output
files are kept local and excluded from the current repository tree. This
documentation update does not report a new build.

## Repository contents

| Path | Purpose |
| --- | --- |
| `LeanCompletion/JSP001022.lean` | Supplemental proof declarations |
| `LeanCompletion/Audit.lean` | Exact statement, dependency, axiom and module-path checks |
| `verification/Negative.lean` | Invalid `0 = 1` proof; must fail at `rfl` |
| `verification/targets.json` | Frozen target type and required dependency names |
| `preparation.json` | Historical extraction record, not current verification status |
| `docs/STATEMENT_CORRESPONDENCE.md` | Source and Lean correspondence |
| `docs/ATTRIBUTION.md` | Contribution boundary and license status |
| `docs/VERIFICATION.md` | Reproduction instructions and evidence limitations |
| `docs/RELATED_WORK.md` | Existing formalizations and catalog PRs |
| `docs/COMPARISON_WITH_PLBY.md` | Fixed-source comparison, contribution boundaries and submission considerations |
| `docs/REPOSITORY_POLICY.md` | Allowed commit contents, local-only outputs and publication boundaries |
| `AGENTS.md` | Working rules for coding agents |

## Repository submission rules

Follow [the repository policy](docs/REPOSITORY_POLICY.md) before committing or
pushing. Commit proof/configuration files, curated documentation and concise
verification summaries; keep raw logs and generated run artifacts local.
Upload to this proof repository only when requested. An official awards PR
requires a separate explicit request.

## Licensing

No blanket license is asserted over third-party code. A license file was not
identified in the pinned Prim tree. Prim is referenced at its original public
repository; its source and build products are excluded here. Each dependency
retains its own authorship and applicable terms. This repository does not attach
an additional license to the supplemental work. See
[Attribution](docs/ATTRIBUTION.md#licensing-and-third-party-material).
