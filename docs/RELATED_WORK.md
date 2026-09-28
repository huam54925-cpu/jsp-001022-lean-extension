# Related formalizations and submissions

Checked 2026-09-28 through the GitHub API, including open and closed JSP-001022
PRs. These records are not priority judgments.

| Submission | Observed state | Relationship |
| --- | --- | --- |
| [awards #4195](https://github.com/TheJustinSunPrize/awards/pull/4195) | Open, unmerged | References plby/lean-proofs #1217 |
| [awards #1286](https://github.com/TheJustinSunPrize/awards/pull/1286) | Open, unmerged | Also references plby's #1217 formalization |
| [awards #2053](https://github.com/TheJustinSunPrize/awards/pull/2053) | Open, unmerged | Description maps JSP-001022 to #1196 and primitive-set sums; current catalog instead maps it to chain question #1217 |
| [awards #1074](https://github.com/TheJustinSunPrize/awards/pull/1074) | Closed | Description also discusses #1196 under JSP-001022 |
| [awards #1723](https://github.com/TheJustinSunPrize/awards/pull/1723) | Closed | Description expressly limits its scope to component/numerical instances |
| [awards #3019](https://github.com/TheJustinSunPrize/awards/pull/3019) | Closed | Related catalog submission; no independent proof review performed here |

The inspected existing source is
[`plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1217.lean).
Its `Erdos1217.erdos_1217` addresses a positive lower logarithmic density
enumeration and weighted/counting-rate inequality, importing a separate
resolution module. Only the entry source was inspected here; that project was
not rebuilt or independently validated in this review.

Our submission is additional supplemental work over pinned Prim/LeanMarathon:
Abel estimates, a density bridge and cutoff/enumeration conversions. It does
not import or port the plby proof. No novelty over all other formalizations,
earliest priority or defect in that separate proof is asserted. Maintainers
should consider the related submissions when reviewing contribution and credit.
