# Contribution and attribution

Reviewed 2026-09-28. Mathematical sources, upstream formalization, supplemental
proofs and reproduction work are distinguished below. No first-formalization
priority, independent mathematical discovery or award entitlement is asserted.

## Mathematical authors

Boris Alexeev, Kevin Barreto, Yanyang Li, Jared Duker Lichtman, Liam Price, Jibran
Iqbal Shah, Quanyu Tang and Terence Tao provide the solution used:
[*Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond*,
arXiv:2605.00301v1](https://arxiv.org/abs/2605.00301v1), Theorem 1.6 and Section 9.
The historical problem is P. Erdős, A. Sárközy and E. Szemerédi,
[*On divisibility properties of sequences of integers*](https://www.renyi.hu/~p_erdos/1966-09.pdf),
Studia Sci. Math. Hungar. 1 (1966), 431–435, p. 432, equation (5).

## Upstream formalization

[YuanheZ/Prim](https://github.com/YuanheZ/Prim), commit
`a303f6bd23bb8f29a833d1d70327528359180995`. Its
[pinned README](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/README.md)
credits [LeanMarathon](https://github.com/YuanheZ/LeanMarathon), built upon
[Erdos1196](https://github.com/YuanheZ/Erdos1196). These are project-level credits,
not a verified list of all individual authors.

[`LeanMarathon/Main.lean`](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean)
contains the base definitions and `erdos_sarkozy_szemeredi_1217`. Its 14,592
lines match the normalized prefix of the historical combined local proof.
Source SHA256: `8ca5eaef73ffacc9b6e350304a4b4c7e4ee9ec3dd3205af339df63d671ed7085`.
It is imported as a locked dependency. The upstream chain construction is not
claimed as newly authored work in this repository.

## Supplemental contribution

Original contribution repository:
[huam54925-cpu/jsp-001022-lean-extension](https://github.com/huam54925-cpu/jsp-001022-lean-extension),
branch `main`. Submitting contributor: [@huam54925-cpu](https://github.com/huam54925-cpu),
with AI assistance for proof generation, integration, auditing and documentation.
The claimed scope is the supplemental work below. No independent human verifier
is claimed.

The proof module was introduced in
[`b5c329089658e9853550a0eeb27985d2cc444873`](https://github.com/huam54925-cpu/jsp-001022-lean-extension/commit/b5c329089658e9853550a0eeb27985d2cc444873).
That commit's author label is `xialain`, whereas the submitting GitHub account
is `huam54925-cpu`. This mismatch is disclosed, not treated as a verified identity
link. Repository control and commit text alone do not prove human authorship;
contributor verification remains with maintainers. No legal-name claim or
private identity information is supplied here.

All declarations are in namespace `LeanCompletion`:

| Declaration | Line | Contribution scope |
| --- | --- | --- |
| `jsp_001022_eventual_lower_bound` | [7](../LeanCompletion/JSP001022.lean#L7) | Positive liminf to eventual reciprocal lower bound |
| `jsp_001022_finite_abel_lower_bound` | [38](../LeanCompletion/JSP001022.lean#L38) | Finite Abel estimate with endpoint control |
| `jsp_001022_reciprocal_weight_specialization` | [112](../LeanCompletion/JSP001022.lean#L112) | Specialized weighted estimate |
| `jsp_001022_natural_loglog_lower_bound` | [155](../LeanCompletion/JSP001022.lean#L155) | Natural-cutoff log-log estimate |
| `jsp_001022_eventual_to_finite_prefix` | [198](../LeanCompletion/JSP001022.lean#L198) | Finite-prefix adjustment |
| `jsp_001022_density_to_natural_erdos_lower_bound` | [246](../LeanCompletion/JSP001022.lean#L246) | Weighted lower bound from density |
| `jsp_001022_density_bridge` | [293](../LeanCompletion/JSP001022.lean#L293) | Lower-log to upper-doubly-log positivity |
| `erdos_1217_explicit` | [428](../LeanCompletion/JSP001022.lean#L428) | Upstream application/unfolding; integration wrapper |
| `jsp_001022_chain_strict_cutoff` | [447](../LeanCompletion/JSP001022.lean#L447) | Chain cutoff conversion |
| `jsp_001022_reciprocal_strict_cutoff` | [528](../LeanCompletion/JSP001022.lean#L528) | Reciprocal cutoff conversion |
| `jsp_001022_erdos_strict_cutoff` | [649](../LeanCompletion/JSP001022.lean#L649) | Weighted cutoff conversion |
| `jsp_001022_erdos_density_ennreal` | [868](../LeanCompletion/JSP001022.lean#L868) | Bounded weighted real/ENNReal limsup conversion |
| `jsp_001022_positive_enumeration_sums` | [1029](../LeanCompletion/JSP001022.lean#L1029) | Enumeration, finite cutoffs and sums |
| `jsp_001022_positive_subsequence_indices` | [1077](../LeanCompletion/JSP001022.lean#L1077) | Positive indices and exact count equality |
| `jsp_001022_original_enumeration_chain` | [1136](../LeanCompletion/JSP001022.lean#L1136) | Final composition |

The 1,200-line source SHA256 is
`d6f9e9c3be1d23d40f960cf83a4f5ec0c6e590b9f2a234df5ff9f358891fc091`.
This documentation review leaves its bytes unchanged. Line count does not
establish originality or priority. `preparation.json` is the historical extraction
record, not current release status.

## Licensing and third-party material

The complete pinned Prim Git tree was checked on 2026-09-28: no path containing
`license`, `copying`, `notice` or `authors` was found, and the tree response was
not truncated. No upstream license grant or separate authorization is asserted.
This repository fetches the original dependency and does not vendor its source.

Pinned mathlib and LeanArchitect root licenses identify Apache-2.0; they do not
establish a license for Prim or this extension. No blanket license is added and
no upstream content is relicensed. `.lake`, dependency sources/build products,
private development histories and the old combined proof are excluded. A license
choice for supplemental work is left to its responsible contributor.

## Related work and verification

[RELATED_WORK.md](RELATED_WORK.md) identifies the existing plby formalization
and catalog submissions. This repository does not import it and makes no
first-publication claim. Build and axiom checks are supporting verification
evidence, not independent authorship evidence. See [VERIFICATION.md](VERIFICATION.md).
