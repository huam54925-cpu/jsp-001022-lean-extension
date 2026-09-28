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
enumeration and weighted/counting-rate inequality. The subsequent source review
traced Resolution and its project imports, and compared the density, chain and
reindexing proofs. It did not rebuild plby or produce a new elaborated axiom
audit. The [detailed comparison](COMPARISON_WITH_PLBY.md) records the scope.

Our work supplements pinned Prim/LeanMarathon with a discrete Abel density
bridge and cutoff/enumeration conversions. plby already proves the same density
implication and exports the stronger comparison `lowerLogDensity A ≤ weightedRate A`.
Our finite Abel implementation uses discrete induction; plby uses Mathlib's
integral Abel identity. Our project does not import plby, but import structure
and implementation differences alone do not establish development provenance
or historical independence.

An existing formalization of the same problem is not by itself a reason to
reject a distinct contribution. Re-registering the same proof and contributing
different formalization work are separate cases. The
[official guidance](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#before-opening-a-pr)
recommends comparing related submissions and explaining the differences, and
says an earlier PR opening time alone does not establish priority. No novelty
over all other formalizations, earliest priority, defect in plby or award
entitlement is asserted here. Completeness, provenance and contribution review
remain necessary.
