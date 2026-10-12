Submitted as [TheJustinSunPrize/awards #5024](https://github.com/TheJustinSunPrize/awards/issues/5024).

# [Problem] Erdős 1092: all-subgraph edge budgets

I recommend E1092 for an independent catalog identity and request confirmation
of the full original-problem scope described below.
It is not an award-eligibility or priority claim.

## Problem and original source

**Erdős problem 1092:**
[https://www.erdosproblems.com/1092](https://www.erdosproblems.com/1092).

The published mathematical reference is Vojtěch Rödl, *Nearly bipartite graphs
with large chromatic number*, Combinatorica 2, 377–383 (1982),
[DOI 10.1007/BF02579434](https://doi.org/10.1007/BF02579434).

## Statement and significance

For a fixed integer `r≥2`, call `g : ℕ → ℕ` admissible if every finite simple
graph `G` has chromatic number at most `r+1` whenever **each subgraph `H` of `G`
(not necessarily induced)** can be made `r`-colorable by deleting at most
`g(|V(H)|)` actual edges of `H`. All sizes are tested simultaneously with the
same budget function, and isolated vertices count in `|V(H)|`.

The result is that, for each fixed `r≥2`, no admissible `g` is eventually at
least linear. Equivalently, there is no admissible `g` satisfying
`(n ↦ (n : ℝ)) =O[atTop] (n ↦ (g n : ℝ))`.

The scope matters: checking only one subgraph size, using the same constant
budget at every size, or deleting vertices instead of edges proves different
statements. The result relates hereditary local edge repair to a global
chromatic bound.

Please confirm whether E1092 can receive an independent catalog entry and
whether the scope above is the appropriate original-problem scope for any
subsequent submission. I have not assigned a JSP number or reused JSP-000091.

## Known results and verification evidence

The mathematical question was already solved by Rödl's 1982 work; this
recommendation makes no claim to a new mathematical solution. The linked
repository provides a self-contained finite-construction proof and its Lean
formalization. It constructs a non-3-colorable generalized Mycielski graph with
an arbitrarily small hereditary edge-cut ratio, then uses a clique join and
small-size integrality to cover every fixed `r≥2`.

The mathematical reduction is also documented in the existing E1092
discussion:
[Quanyu Tang](https://www.erdosproblems.com/forum/thread/1092#post-1675) explains
the `r=2` consequence of Rödl's theorem, and
[Przemek Chojecki](https://www.erdosproblems.com/forum/thread/1092#post-5983)
explains the clique join for general `r`. This repository's contribution is the
Lean formalization and a self-contained exposition of that solved mathematics.

Original public proof repository:
[Wang060919/erdos1092-lean](https://github.com/Wang060919/erdos1092-lean).
Selected publicly verifiable proof version:

* Immutable proof commit: [`7649a561f6c2c8caabd60d0834beeffe89a357d5`](https://github.com/Wang060919/erdos1092-lean/commit/7649a561f6c2c8caabd60d0834beeffe89a357d5).
* Successful CI run for that exact SHA: [run 38265286397](https://github.com/Wang060919/erdos1092-lean/actions/runs/38265286397), `head_sha = 7649a561f6c2c8caabd60d0834beeffe89a357d5`, completed/success.
* Verification evidence at that commit: [clean reproduction record](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/portable-reproduction.json) and [literal statement check](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/CheckScope.lean).

The release procedure checks a clean build, an independent literal original
statement, the axioms of the public declarations, and Lean kernel replay of
the custom proof modules. The pinned Mathlib dependency remains a trusted
library rather than being independently replayed in full.

The final theorem has only `r : ℕ` and `2 ≤ r`; its finite construction and
all other mathematical suppliers are proved. The documentation does not
strengthen the conclusion to “every admissible `g` is `o(n)`.”

## Related records and conflicts

The source audit on 2026-10-12 inspected all-state proof records, relevant
claims, public GitHub Lean repositories, and batch formalizations. No earlier
complete effective Lean proof of this exact scope was confirmed among the
inspected sources. This is a bounded search conclusion; earliest priority
remains for review.

Relevant records and their actual differences include:

* [plby E1092 at `8822f7d…`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1092.lean):
  one fixed subgraph size `m`, with a vacuous `K₄` argument for `m≥5`.
* [lean-genius PR 43572](https://github.com/rjwalters/lean-genius/pull/43572):
  a fixed ambient order and a uniform integer budget, not a function evaluated
  at every subgraph's size.
* [Formal Conjectures E1092 at `34ee0e3…`](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean):
  the correct statement, with unfinished principal endpoints in the inspected
  snapshot.
* [plby E750 at `8822f7d…`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos750.lean):
  genuine generalized-Mycielski chromatic and hereditary **vertex**-deletion
  results. The deleted set may include a high-degree apex and therefore does
  not supply the required hereditary small **edge** cuts.
* [tadamcz/erdos74 at `1e7c8d7…`](https://github.com/tadamcz/erdos74/tree/1e7c8d7a5c55df54c40662cc563bb2ee2c9ffb9e):
  a different infinite-chromatic/finite-profile problem. This corresponds to
  the existing JSP-000091 relationship, rather than an E1092 identity.

The official catalog snapshot `16877004910734cecca83cc5af0fec2f5a4125b3` did not
establish an independent E1092 entry. The shared Rödl reference is insufficient
to identify it with JSP-000091/E74.

Professional relationships: **None (publisher disclosure confirmed).**

I understand that problem recommendation does not establish award eligibility,
and that acceptance, exact scope, provenance, and priority require organizer
review.
