# Statement correspondence for JSP-001022

Reviewed 2026-09-28. Target:
`LeanCompletion.jsp_001022_original_enumeration_chain`,
[`LeanCompletion/JSP001022.lean:1136`](../LeanCompletion/JSP001022.lean#L1136).
The [exact type](STATEMENT.md) is independently stated as an `example` in
[Audit.lean](../LeanCompletion/Audit.lean#L5).

## Review conclusion and scope

Source inspection supports correspondence to the **current JSP-001022 positive
lower logarithmic density formulation**, with the endpoint and extended-real
conventions below made explicit. Existing Lean lemmas cover the cutoff,
finite-sum, density-type and enumeration changes used by the final proof.
No proof-body change was identified as necessary for that formulation.
This is the submitter's documented review, not independent human review or
maintainer approval. The historical discrepancy below is disclosed for review,
not silently replaced by a claimed equivalence.

## Sources

1. [JSP-001022 at awards commit 8332eaab70094567cb3a2137e33b6ea5a2e316d8](https://github.com/TheJustinSunPrize/awards/blob/8332eaab70094567cb3a2137e33b6ea5a2e316d8/problems/catalog-1001-1022.md#JSP-001022)
   specifies positive **lower** logarithmic density and controlled chain growth.
2. [Erdős–Sárközy–Szemerédi (1966)](https://www.renyi.hu/~p_erdos/1966-09.pdf)
   was checked from original page images: p. 431 introduces increasing sequences;
   p. 432, equation (5), gives the counting-limsup versus weighted-limsup bound.
3. [Erdős Problem #1217](https://www.erdosproblems.com/1217) gives positive
   increasing enumerations, lower density, strict cutoffs and the same inequality.
   Direct automated access returned HTTP 403; the search-index text was readable.
   We do not represent that as a fresh downloaded page snapshot.
4. [Alexeev et al., arXiv:2605.00301v1, Theorem 1.6](https://arxiv.org/html/2605.00301v1#S1.Thmtheorem6)
   and Section 9 supply the solution used by Prim. Its premise is positive upper
   doubly logarithmic density. The extension's density bridge proves the needed
   implication from the catalog's stronger lower-logarithmic premise.

### Historical source discrepancy

On p. 431 the prose says “positive lower logarithmic density”, but printed
equation (1) uses `lim sup`. This was confirmed visually, not inferred from OCR.
Equation (5) on p. 432 uses the expected two limsups in the **conclusion**.
Our hypothesis uses `liminf`, following the current catalog and #1217 wording.
Positive liminf and positive limsup are not asserted equivalent. The headline
theorem also does not claim an unconditional result for every integer sequence.
If maintainers instead select the literal historical limsup hypothesis as the
target, that is a different formal statement requiring further work.

## Mathematical reading

For strictly increasing `a : ℕ+ → ℕ+`, at sufficiently large real `x`, put

$$
H_a(x)=\sum_{a_i<x}a_i^{-1},\qquad
W_a(x)=\sum_{2\leq a_i<x}(a_i\log a_i)^{-1},\qquad
C_{a,k}(x)=\#\{i\geq1:a_{k_i}<x\}.
$$

The theorem assumes `liminf H_a(x)/log x > 0`, chooses **one fixed** strictly
increasing `k : ℕ+ → ℕ+`, proves adjacent divisibility, and proves

$$
\limsup_{x\to\infty}\frac{W_a(x)}{\log\log x}
\leq\limsup_{x\to\infty}\frac{C_{a,k}(x)}{\log\log x}.
$$

Every cutoff sum is finite; the counting limsup may be `+∞`. For finite positive
weighted density `Δ`, the conclusion means: for every `ε > 0` and real `X`, some
`x ≥ X`, `x > exp(1)`, satisfies `C_{a,k}(x)/log log x > Δ - ε`. It is not a bound
at every large scale or on every successive chain element. The strict threshold
below `Δ` matters because a limsup need not be attained.

## Correspondence table

**Exact** means literal in the target. **Lean lemma** means the conversion is
already proved. **Argument/convention** denotes an explanation here, not an
additional compiled equivalence theorem. All supplemental names are in
namespace `LeanCompletion`.

| Requirement | Lean location | Evidence |
| --- | --- | --- |
| Positive increasing enumeration | [1137](../LeanCompletion/JSP001022.lean#L1137) | **Exact:** `a : ℕ+ → ℕ+`, `StrictMono a`; no zero indices/values |
| Same underlying set and finite cutoffs | [positive_enumeration_sums, 1029](../LeanCompletion/JSP001022.lean#L1029) | **Lean lemma:** infinite range, finite cutoff sets, weighted sums preserved for every real weight |
| Positive lower logarithmic density | [1138](../LeanCompletion/JSP001022.lean#L1138) | **Exact:** positive real liminf, reciprocal sum, natural log, real `atTop` |
| Strict/non-strict reciprocal cutoff | [reciprocal_strict_cutoff, 528](../LeanCompletion/JSP001022.lean#L528) | **Lean lemma:** equal liminfs; eventual bounds and error at most `1/log x` |
| Lower-log to upper-doubly-log positivity | [density_bridge, 293](../LeanCompletion/JSP001022.lean#L293) | **Lean lemma:** implication, not equality of densities or equivalence |
| Base chain construction | [erdos_1217_explicit, 428](../LeanCompletion/JSP001022.lean#L428) | Application of pinned Prim `erdos_sarkozy_szemeredi_1217`; integration wrapper |
| Adjacent divisibility | [1142](../LeanCompletion/JSP001022.lean#L1142) | **Exact:** divisibility of `a(k i)` and `a(k(i+1))`, not of indices |
| Increasing infinite chain in the sequence | [positive_subsequence_indices, 1077](../LeanCompletion/JSP001022.lean#L1077) | **Lean lemma/argument:** `StrictMono k`; composition with `a` is strictly increasing; membership automatic |
| Index origin and exact counts | [1083](../LeanCompletion/JSP001022.lean#L1083) | **Lean lemma:** positive index 1 maps to upstream index 0 via `natPred`; counts unchanged |
| Chain strict/non-strict cutoff | [chain_strict_cutoff, 447](../LeanCompletion/JSP001022.lean#L447) | **Lean lemma:** ENNReal limsups equal; raw counts may differ by one |
| Weighted strict/non-strict cutoff | [erdos_strict_cutoff, 649](../LeanCompletion/JSP001022.lean#L649) | **Lean lemma:** strict real limsup equals upstream weighted density |
| Real weighted limsup versus ENNReal | [erdos_density_ennreal, 868](../LeanCompletion/JSP001022.lean#L868) | **Lean lemma:** eventual lower/upper bounds justify `ENNReal.ofReal_limsup` |
| Weight at 1 | [upstream definition](https://github.com/YuanheZ/Prim/blob/a303f6bd23bb8f29a833d1d70327528359180995/LeanMarathon/Main.lean#L13) | **Definition/convention:** total real division gives weight zero; omission of the singular term |
| Counting upper limit | [1147](../LeanCompletion/JSP001022.lean#L1147) | **Exact/convention:** ENNReal limsup permits infinity; no boundedness premise |
| Growth and quantifier order | [1141](../LeanCompletion/JSP001022.lean#L1141) | **Exact:** choose `k` before the inequality between the limits |

## Density convention and set coverage

We use lower logarithmic density in the conventional sense
`liminf (sum_{1≤n≤N, n∈A} 1/n)/log N`. For real `x`, set `N=floor x`: the
non-strict numerator is constant on `[N,N+1)`, bounded by `1+log N`, and
`log(N+1)/log N → 1`. Thus changing the denominator from `log N` to `log x`
changes the ratio by a quantity tending uniformly to zero on these intervals.
The strict/non-strict conversion is already proved in Lean. Replacing `log N`
by the harmonic sum likewise multiplies by a factor tending to one. The
integer-scale and harmonic-normalization arguments in this paragraph are
mathematical explanations, not additional compiled equivalence lemmas.

For the catalog's set language, finite sets have zero lower logarithmic density.
Every infinite subset of positive integers has an increasing enumeration: take
the least remaining member repeatedly; no member can be skipped forever because
only finitely many positive integers are smaller. The enumeration-to-range and
sum direction is proved in Lean. A separate Lean wrapper constructing the
enumeration from an arbitrary set is not included or claimed machine-checked.
The enumerated target itself matches the #1217 problem formulation.

## Endpoint and limit conventions

In the paper, `ℕ_{≥k}` is defined by prime-factor count; thus `ℕ_{≥1}={2,3,...}`
in weight definition (1.1). We use this weight on its stated domain and extend
it by zero at 1. That is exactly Lean's `1/(n*Real.log n)` at 1. The reciprocal
density still includes 1 with weight 1, and the chain may contain 1. Omitting
that reciprocal term or chain element changes the normalized expression by at
most `1/log x` or `1/log log x`, tending to zero. Any finite assigned weighted
term at 1 gives the same normalized limit; an infinite assignment does not.
This explicit convention avoids adding an assumption `1∉A`.

For sufficiently large `x`, both normalized expressions are nonnegative, so
pointwise `ENNReal.ofReal` preserves their values. The weighted expression is
eventually bounded; the existing lemma justifies passage through limsup. The
counting expression can be unbounded. In `[0,+∞]`, the infimum of tail suprema is
the conventional extended-real upper limit for such a nonnegative tail. A real
`Filter.limsup` without boundedness would not offer the same guarantee.

## Proof route and remaining review

```text
positive enumeration -> exact range and finite sums
positive reciprocal liminf -> cutoff conversion -> density bridge
positive upper doubly logarithmic density -> pinned Prim chain theorem
chain -> positive subsequence with identical cutoff counts
weighted cutoff + density-type conversion + chain cutoff -> final inequality
```

No missing conversion was identified in this route for the current catalog
formulation. The base chain theorem is upstream. Maintainers must independently
assess the proposed statement, including the historical discrepancy, and
reproduce the selected commit. Official acceptance is not claimed.
