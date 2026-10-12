# Attribution and provenance

The repository publisher is the GitHub account
[`Wang060919`](https://github.com/Wang060919). No real name or private contact
details are asserted here.

## Mathematical result

Erdős problem 1092 was already solved mathematically. The published reference is:

> Vojtěch Rödl, *Nearly bipartite graphs with large chromatic number*,
> Combinatorica 2, 377–383 (1982), DOI
> [10.1007/BF02579434](https://doi.org/10.1007/BF02579434).

The publisher's abstract records a negative answer to the nearly-bipartite
question of Erdős and Hajnal and also credits Lovász with a different
construction. This project does not claim to be the original mathematical
solver. The audit checked the publication identity and public abstract; it did
not obtain and read the complete seven-page paper.

The E1092 discussion acknowledges
[Quanyu Tang's explanation](https://www.erdosproblems.com/forum/thread/1092#post-1675)
of how Rödl's theorem answers the `r=2` question, and
[Przemek Chojecki's clique-join reduction](https://www.erdosproblems.com/forum/thread/1092#post-5983)
for general `r`. Those reductions are prior mathematical work. The discussion
also records
[Thomas Bloom's clarification](https://www.erdosproblems.com/forum/thread/1092#post-6408)
of the at-most-`r` coloring condition used in the canonical statement.

The [mathematical proof](MATHEMATICAL-PROOF.md) is the self-contained exposition
developed for this formalization. It uses a standard generalized Mycielski
odd-cycle graph, finite three-color winding identities, boundary and seam edge
cuts, and a clique join. The exposition and Lean implementation do not claim
that the graph construction, its chromatic obstruction, or the mathematical
answer is new.

## Related public formalizations

The audit inspected public formal work that provides relevant ideas and
substantive results:

* [plby/lean-proofs, E750 at `8822f7d…`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos750.lean)
  includes generalized-Mycielski definitions, chromatic-number suppliers, and
  hereditary vertex-deletion results. Those are genuine prior tools; their
  vertex-deletion model differs from the edge budget proved here.
* [tadamcz/erdos74 at `1e7c8d7…`](https://github.com/tadamcz/erdos74/tree/1e7c8d7a5c55df54c40662cc563bb2ee2c9ffb9e)
  concerns finite profiles of infinite-chromatic graphs. Its inspected
  endpoints do not supply this problem's finite hereditary edge-cut witness.
* [google-deepmind/formal-conjectures at `34ee0e3…`](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean)
  is the canonical all-subgraph function-budget statement used in the scope
  comparison.

These references acknowledge inspected prior formal work. They are not imported
as proof modules or assumed as unproved mathematical inputs to the final
theorem. The differences from other inspected E1092 claims are summarized in
[Scope](SCOPE.md). No global nonexistence or earliest-priority claim is made.

## Software dependencies and verification

The proof depends on Lean 4.33.0 and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Their authors and contributors retain
the attribution and license notices of their projects:
[Lean](https://github.com/leanprover/lean4/tree/v4.33.0) and
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d).

The custom proof consists of the seven `Erdos1092` modules listed in the
mathematical proof. The final endpoint supplies the finite construction rather
than taking it as an assumption. Verification records distinguish compilation,
axiom inspection, replay of custom modules, and the trust placed in the pinned
Mathlib dependency.

Publication history can support a later priority review; it does not settle
that review. Any award recognition remains subject to organizer assessment of
scope, provenance, prior work, and eligibility.
