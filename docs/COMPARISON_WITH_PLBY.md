# Comparison with the plby formalization

Source comparison dated 2026-09-28. This review reads fixed statements,
definitions, proof bodies and project imports. It does not report a new Lean
build, elaborated dependency audit or axiom-check PASS for either project.

## Scope and fixed versions

| Project | Version used in this comparison |
| --- | --- |
| This extension | Selected proof commit `3992abb235729e5ebd0359d897470d6101acf908` |
| Prim / LeanMarathon | `a303f6bd23bb8f29a833d1d70327528359180995` |
| plby/lean-proofs | `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` |

This extension imports the pinned Prim theorem. Its contribution relative to
that upstream interface is the discrete Abel density bridge and the conversions
needed for the original positive-integer enumeration statement. The comparison
and log cleanup do not change the selected proof commit or any Lean source.

The projects share the overall mathematical route: transfer positive lower
logarithmic density to positive doubly harmonic upper density, then obtain a
divisibility chain with at least that weighted upper density. Their finite Abel
implementations differ. This is a substantive implementation distinction, not
evidence by itself of historical independence, first completion or priority.

## Density transfer: plby exports the stronger comparison

The pinned [plby Density module](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Density.lean#L533)
proves `lowerLogDensity A ≤ weightedRate A`. Its
`weightedRate_pos_of_lowerLogDensity_pos` at line 540 is an immediate corollary.
The proof is implemented: finite Abel summation at line 259, a finite weighted
lower bound at line 326, and the natural-cutoff density comparison at line 464.

In mathematical notation, write

$$
\delta(A)=\liminf_{x\to\infty}
  \frac{\sum_{1\le n<x,\ n\in A}1/n}{\log x},\qquad
\Delta(A)=\limsup_{x\to\infty}
  \frac{\sum_{2\le n<x,\ n\in A}1/(n\log n)}{\log\log x}.
$$

plby exports the comparison `δ(A) ≤ Δ(A)`, without loss in the constant.
Our [`jsp_001022_density_bridge`](../LeanCompletion/JSP001022.lean#L293)
exports positivity, `δ(A) > 0 → Δ(A) > 0`, after the representation conventions
are aligned. Thus our bridge does not fill a missing bridge in plby.

This comparison concerns mathematical meaning, not identical Lean types.
plby uses `ENNReal` densities and strict cutoffs from its initial definitions;
our bridge uses Prim's real-valued densities and non-strict cutoffs. No
cross-project Lean equivalence theorem was compiled in this review.

**The final chain bound in this repository does not lose the constant.**
The bridge supplies only the positivity needed to invoke Prim. The
[final theorem](../LeanCompletion/JSP001022.lean#L1136) still bounds the chain
counting limsup below by the full weighted upper density of the original
sequence, not by a smaller auxiliary constant used inside the bridge.

## Finite Abel: different implementations of the same mathematical method

plby's `finite_abel_inv_log` calls Mathlib's
[`sum_mul_eq_sub_sub_integral_mul'`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/AbelSummation.lean#L175).
It differentiates `1 / log t`, obtains the kernel `1 / (t * (log t)^2)`,
and compares the integral against the exact primitive `log (log t)`.
It explicitly handles integrability, cutoffs and the finite initial boundary
term. Constants below the lower density approach it to obtain coefficient 1.

Our [`jsp_001022_finite_abel_lower_bound`](../LeanCompletion/JSP001022.lean#L38)
instead quantifies over an arbitrary nonnegative sequence `a : ℕ → ℝ`, assumes
prefix lower bounds only on a specified finite interval, and uses
`Nat.le_induction`. For

$$
S(t)=\sum_{k=0}^{t}a(k),\quad B_M=\sum_{k=0}^{M-1}a(k),\quad
D_M(t)=\sum_{q=M+1}^{t}\frac{\log q-\log(q-1)}{\log q},
$$

the strengthened induction invariant is

$$
cD_M(t)-\frac{B_M}{\log M}+\frac{S(t)}{\log t}
\le \sum_{n=M}^{t}\frac{a(n)}{\log n}.
$$

After specialization to `a(n) = 1_A(n)/n`, the proof reuses Prim's
[`mangoldt_log_reciprocal_main_term_bound`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L11114)
to compare the discrete logarithmic increment sum with `log log N` up to a
bounded error. That asymptotic estimate is upstream work, not a new estimate
proved by this extension.

The general nonnegative-sequence finite inequality is a useful standalone API.
This does not mean plby lacks a general Abel theorem: its Mathlib formula itself
allows general coefficients. Both implementations retain finite-prefix losses.
The distinction is discrete induction, finite hypotheses and exposed interfaces,
not a new overall mathematical method or a missing boundary argument in plby.

## The seven density and Abel lemmas

The left column abbreviates the common prefix `LeanCompletion.jsp_001022_`.
Line numbers on the right refer to the pinned plby `Density.lean`.
These are functional correspondences, not identical Lean declarations.

| Our declaration | Corresponding plby functionality | Distinction |
| --- | --- | --- |
| `eventual_lower_bound` (line 7) | `lowerLogDensityNat_le_weightedRateNat`, lines 472–485 | Fixed positive constant versus arbitrary constants approaching the lower density |
| `finite_abel_lower_bound` (38) | `finite_abel_inv_log` (259), `weightedMassNat_lower_of_harmonic` (326) | General nonnegative sequence and discrete induction versus an integral identity specialized to the set |
| `reciprocal_weight_specialization` (112) | `harmonicCoeff` (227), finite-sum identity (236), weight comparison (340–371) | Separate specialization API versus specialization inside the finite argument |
| `natural_loglog_lower_bound` (155) | `weightedMassNat_lower_of_harmonic` (326) and integral evaluation (306) | Prim's discrete bounded-error estimate versus the exact model integral |
| `eventual_to_finite_prefix` (198) | Real-to-natural liminf comparison (38), threshold extraction (473–485) | Explicit finite-support `tsum` conversion versus finite sums in the initial definitions |
| `density_to_natural_erdos_lower_bound` (246) | Combination of prefix bounds and finite weighted lower bound (478–515) | Public existential constants versus constants inside the quantitative comparison proof |
| `density_bridge` (293) | `lowerLogDensity_le_weightedRate` (533), positivity corollary (540) | Our positivity interface versus plby's stronger quantitative interface |

## Chain construction and project dependencies

The pinned [Resolution module](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Resolution.lean#L451)
implements the stronger set-valued chain theorem. Its imports lead through
`Density`, `AnalyticWeight`, `MarkovChain`, `Moments`, `OmegaBound` and `Reindex`,
with `Basic` and `ReverseFatou` as additional support. External project branches
include `Erdos164` and `Erdos697PrimeHarmonic`, the latter using
`BoundedGaps.Maynard.PrimeMertens` from pinned FormalPantheon.

Both Prim and plby use an invariant von Mangoldt weight, an upward random
divisibility chain, a visit-mass identity, a second-moment bound using the number
of prime factors, reverse Fatou and extraction of the visits lying in the set.
They organize these constructions differently in Lean. This extension directly
calls Prim's completed chain theorem; it does not claim to reprove that core.

The plby Lake project is in `src/latest`, with `lakefile.lean` and dependency
compatibility patches applied by its `post_update` hook. Its pinned toolchain
is Lean `v4.33.0`, with Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Our project uses Lean `v4.30.0-rc2` and its own locked dependencies. Source-level
import tracing is not a build or an elaborated transitive-axiom audit. This
comparison neither replays those patches nor certifies a new plby build.

## Cutoffs, types and enumeration

plby defines strict cutoffs from the start using `Finset.Ico 1 ⌈x⌉₊`, and its
density values already lie in `ENNReal`. Its
[`Reindex` module](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217/Reindex.lean#L159)
recovers strictly increasing indices in an ambient sequence.

Our conversion lemmas connect Prim's `≤ x`, real weighted density and
natural-number-indexed chains to `< x`, the required `ENNReal` comparison and
positive-integer indexing. They establish the needed endpoints, boundedness and
exact counting identities. These are real contributions relative to the chosen
Prim interface; different definitions let plby avoid the same adapters.

Another reusable interface is
[`jsp_001022_positive_enumeration_sums`](../LeanCompletion/JSP001022.lean#L1029):
it treats any weight `w : ℕ → ℝ`, identifies enumeration sums with range-set
sums, and proves finiteness of the cutoffs. Reusability does not establish that
this is the first such interface in existing formalizations.

## Contribution description and submission considerations

An accurate description of this repository is:

> This project formalizes a discrete Abel bridge from positive lower logarithmic
> density to positive doubly harmonic upper density over pinned Prim/LeanMarathon,
> and supplies strict-cutoff, density-type and positive-enumeration conversions.
> Its finite Abel implementation differs from the integral Abel implementation
> in plby's existing formalization. It claims neither a new mathematical solution
> nor the first formalization of the density-transfer conclusion.

**An existing formalization of the same problem does not automatically rule out
a submission with a distinct contribution.** A contribution to the same problem
and another registration of the same proof are different situations. The
[official contribution guidance](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#before-opening-a-pr),
checked on 2026-09-28, recommends reviewing related submissions and explaining
the differences. It also states that an earlier PR opening time alone does not
establish priority. Relevant completeness, provenance, attribution and review
requirements still apply. This is not an eligibility or award decision.

The [related submissions](RELATED_WORK.md), including #1286 and #4195 referring
to plby, should be disclosed and compared. They are not by themselves a reason
to abandon this work or treat it as ineligible. Source structure alone cannot
establish independent development or historical priority; those need separate
evidence. The present comparison gives no reason to add proof code to repair
an alleged gap in plby, and no reason to discard the supplemental work.

Self-check reports and log links are optional under the
[official verification guidance in CONTRIBUTING](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions).
This repository keeps a concise historical verification summary and reproducible
commands; raw execution logs and run-output files remain local and are excluded
from the current repository tree. No new official submission or review outcome
is implied by this documentation update.
