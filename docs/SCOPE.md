# Scope of the E1092 formalization

The final theorem rules out an eventually linear admissible edge-budget
function for **each fixed `r ≥ 2`**. Its only parameters are `r : ℕ` and the
original hypothesis `2 ≤ r`.

The problem is [Erdős 1092](https://www.erdosproblems.com/1092). The canonical
reference checked during the statement audit is
[`FormalConjectures/ErdosProblems/1092.lean` at `34ee0e3…`](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean).

## Exact definition and endpoint

The definition in [`Outer.lean`](../Erdos1092/Outer.lean) is:

```lean
def IsAdmissible (r : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ H : G.Subgraph,
      ∃ E : Finset (Sym2 H.verts),
        E ⊆ H.coe.edgeFinset ∧ E.card ≤ g (Fintype.card H.verts) ∧
        chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
    chromaticNumber G ≤ (r + 1 : ℕ∞)
```

The endpoint in [`Main.lean`](../Erdos1092/Main.lean) is:

```lean
theorem erdos_1092 (r : ℕ) (hr : 2 ≤ r) :
    ¬∃ g : ℕ → ℕ, IsAdmissible r g ∧
      (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (g n : ℝ))
```

The source also exposes `erdos_1092_all`, the `r=2` endpoint
`f_asymptotic_2`, and `f_asymptotic_general`. The latter negates a universal
existence assertion; `erdos_1092` is the stronger statement for every fixed
parameter individually.

## Quantifiers and budgets

| Requirement | Meaning in the formalization |
|---|---|
| Every finite graph | Every `SimpleGraph (Fin n)` for every `n`; arbitrary finite vertex sets are relabeled by equivalences. |
| Every subgraph, not necessarily induced | `H : G.Subgraph` may omit arbitrary edges and vertices; induced subgraphs are included. |
| All sizes simultaneously | The same `g` is evaluated at `Fintype.card H.verts` inside `∀ H`. |
| Actual edge deletions | `E ⊆ H.coe.edgeFinset`, and the graph tested is `H.coe.deleteEdges E`. |
| Vertex count | All vertices of `H`, including isolated ones; not only incident vertices or the ambient graph's order. |
| Eventually linear | `n =O g(n)` means an eventual lower bound `g(n) ≥ cn` for some real `c>0`. |
| Small sizes | No positivity, monotonicity, or lower bound for `g` before its eventual threshold is assumed. Integrality handles those sizes. |

The complete proof constructs its finite counterexample, proves that it is
not 3-colorable, proves the hereditary edge-cut bound, and supplies every premise
of the join reduction. The final theorem has no core-existence, coloring,
number-theoretic, or probabilistic assumption.

## Boundaries

The theorem does not assert `g(n)/n → 0` for every admissible function, and does
not supply a counterexample for every arbitrarily slowly divergent budget.
Neither strengthening follows from the endpoint proved here. The case `r=1`
is outside this statement.

Here, “`r`-colorable” means chromatic number **at most** `r`, as in the canonical
Lean statement. The historical distinction between exact chromatic number `r`
and at most `r` is discussed by
[Thomas Bloom](https://www.erdosproblems.com/forum/thread/1092#post-6408).
This project does not claim a separate exact-chromatic-number variant.

## Earlier formal work and the audited differences

The prior-source audit was performed on 2026-10-12. The following distinctions
refer to the actual definitions and theorem statements inspected, rather than
repository labels or catalog flags.

| Inspected source | Actual range and difference from this theorem |
|---|---|
| [plby E1092 at `8822f7d…`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1092.lean) | Tests only subgraphs of one fixed size `m`. Its `K₄` argument when `m≥5` uses an empty family of tested subgraphs, rather than the all-size function budget. |
| [lean-genius PR 43572](https://github.com/rjwalters/lean-genius/pull/43572) | Determines a threshold for a fixed ambient order with the same integer budget on every tested subset. This is a uniform-budget model, not `g(|V(H)|)` at all sizes. |
| [Formal Conjectures at `34ee0e3…`](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean) | States the correct function-budget model; the inspected principal endpoints remain unfinished. |
| [ryantuck/erdos-ai at `378f781…`](https://github.com/ryantuck/erdos-ai/blob/378f78129a17cc2463ee66799d071aa77cad4603/conjectures-v2/1092.lean) | Uses an all-size model, but the inspected `r=2` and general endpoints have `sorry`. |
| [plby E750 at `8822f7d…`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos750.lean) | Supplies substantive generalized-Mycielski chromatic results and hereditary bipartization by **vertex** deletion. Its deletion set may include the high-degree apex; a bound on deleted vertices does not yield the required small number of deleted edges. |
| [tadamcz/erdos74 at `1e7c8d7…`](https://github.com/tadamcz/erdos74/tree/1e7c8d7a5c55df54c40662cc563bb2ee2c9ffb9e) | Resolves a different infinite-chromatic/finite-profile problem. The inspected existence and conditional suppliers do not provide the E1092 all-subgraph edge-cut construction. |

The searches included open, closed, and merged proof records, issues and claims,
semantic GitHub code queries, public proof repositories, and batch
formalizations. Closed proof PRs of interest were checked for merge status.
Numeric-only code search was too broad to exhaust, and indexed search does not
cover every public or private repository. No earlier complete effective Lean
proof of this exact scope was confirmed in the inspected sources. This is a
bounded audit conclusion, not a global absence or first-proof claim.

## Prize status

The official catalog snapshot
[`16877004910734cecca83cc5af0fec2f5a4125b3`](https://github.com/TheJustinSunPrize/awards/tree/16877004910734cecca83cc5af0fec2f5a4125b3)
did not establish an independent JSP entry for E1092. JSP-000091 concerns E74;
a shared Rödl reference does not make the two scopes identical.

The organizers must confirm the entry and scope before award eligibility can
be assessed. The official
[problem recommendation form](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/.github/ISSUE_TEMPLATE/recommend-problem.yml)
expressly states that a recommendation does not establish eligibility.
Public source, reproducible verification, and a green CI run also do not by
themselves establish priority, acceptance, authorship adjudication, or eligibility.
