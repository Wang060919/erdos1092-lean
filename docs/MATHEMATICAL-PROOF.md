# Mathematical proof of Erdős 1092

This document proves the statement formalized by
[`Erdos1092.erdos_1092`](../Erdos1092/Main.lean). The mathematical problem was
already solved: see Vojtěch Rödl, *Nearly bipartite graphs with large chromatic
number*, Combinatorica 2, 377–383 (1982),
[DOI 10.1007/BF02579434](https://doi.org/10.1007/BF02579434).
The construction and proof below are a self-contained exposition used for this
Lean development. They do not claim a new solution of the mathematical problem
or reproduce Rödl's paper. See [Attribution](ATTRIBUTION.md).

The reduction of Rödl's result to the `r=2` question was already explained by
[Quanyu Tang](https://www.erdosproblems.com/forum/thread/1092#post-1675), and the
clique-join extension to every fixed `r≥2` by
[Przemek Chojecki](https://www.erdosproblems.com/forum/thread/1092#post-5983).
This development formalizes that mathematical conclusion using the explicit
finite construction below and supplies the small-size budget argument.

## 1. Statement

Fix an integer `r ≥ 2`. A function `g : ℕ → ℕ` is **admissible** if, for every
finite simple graph `G`, the following implication holds:

* If every subgraph `H` of `G` can be made `r`-colorable by deleting at most
  `g(|V(H)|)` edges of `H`, then `G` is `(r+1)`-colorable.

Subgraphs may omit arbitrary vertices and edges; they need not be induced.
All their sizes are tested against the same function `g`. Isolated vertices
count in `|V(H)|`.

We prove that no admissible `g` is eventually at least linear: there do not
exist `c > 0` and `M ∈ ℕ` such that `g(m) ≥ c m` for every `m ≥ M`.
The formal endpoint uses the equivalent notation `n =O[atTop] g(n)`, with both
functions cast to the real numbers. The exact definition and endpoint are
recorded in [Scope](SCOPE.md).

## 2. A finite graph with a hereditary edge-cut bound

We first prove the following construction lemma.

**Lemma.** For every real `ε > 0`, there is a finite simple graph `X` that is
not 3-colorable, but every subgraph `H ⊆ X` can be made bipartite by deleting a
set `F ⊆ E(H)` satisfying `|F| ≤ ε |V(H)|`.

### 2.1. The graph

Choose an odd integer `t ≥ 3` and an integer `R ≥ 2`. The ordinary vertices are
`(j,i)`, where `0 ≤ j < R` is the layer and `i ∈ ℤ/tℤ` is the cyclic coordinate.
There is one additional vertex `z`, the apex. The edges are exactly:

1. `(0,i)—(0,i+1)` for each cyclic coordinate `i`;
2. `(j,i)—(j+1,i+1)` and `(j,i)—(j+1,i−1)` for `0 ≤ j < R−1`;
3. `z—(R−1,i)` for each `i`.

This is a generalized Mycielski graph of the odd cycle. In particular, layers
other than the base have no horizontal edges. The graph obtained by removing
all apex edges has maximum degree at most 4. This bound does not apply to the
apex in the original graph.

### 2.2. A finite winding obstruction to three colors

Suppose that the graph has a proper coloring with colors `ℤ/3ℤ`. On a proper
edge define an integer

```text
D(a,b) =  1  if b−a =  1 modulo 3,
         −1  if b−a = −1 modulo 3.
```

Thus `D(b,a) = −D(a,b)`, and `D(a,b)` is congruent to `b−a` modulo 3.

On any properly colored closed walk of length four, the sum of the four `D`
values is zero. Indeed, the sum is even, belongs to `[-4,4]`, and is divisible
by 3 because the color differences telescope. Among `−4,−2,0,2,4`, only zero
is divisible by 3. Opposite vertices of this walk may coincide.

Write `c_j(i)` for the color of `(j,i)`, and define

```text
W   = Σ_i D(c_0(i), c_0(i+1)),
F_j(i) = D(c_j(i), c_(j+1)(i+1)),
Q_j(i) = D(c_j(i), c_(j+1)(i−1)),
B_j = Σ_i (F_j(i) − Q_j(i))       (0 ≤ j < R−1).
```

The integer `W` is odd, being a sum of `t` values in `{−1,1}`. Hence `W ≠ 0`.

The base closed walk

```text
(0,i−1) → (0,i) → (0,i+1) → (1,i) → (0,i−1)
```

has zero `D` sum. Summing these identities over `i`, and shifting the cyclic
index in the sums, gives `B_0 = 2W`.

For `0 ≤ j < R−2`, use the closed walk

```text
(j,i) → (j+1,i+1) → (j+2,i) → (j+1,i−1) → (j,i).
```

Its zero-sum identity is

```text
F_j(i) + Q_(j+1)(i+1) − F_(j+1)(i−1) − Q_j(i) = 0.
```

After summing and shifting indices, this is `B_j = B_(j+1)`. Consequently
`B_(R−2) = B_0 = 2W`; for `R=2`, no middle identity is needed.

Finally, let `γ` be the apex color. The closed walk

```text
(R−2,i) → (R−1,i+1) → z → (R−1,i−1) → (R−2,i)
```

gives

```text
F_(R−2)(i) + D(c_(R−1)(i+1),γ)
  − D(c_(R−1)(i−1),γ) − Q_(R−2)(i) = 0.
```

The two apex sums cancel after cyclic reindexing, so `B_(R−2)=0`. This implies
`2W=0`, contradicting the oddness of `W`. The graph is therefore not
3-colorable. This proof only uses edges present in the graph; it does not
assume that any middle or top layer is a properly colored cycle.

### 2.3. Cuts for every subgraph

Fix an arbitrary subgraph `H`, and put `m=|V(H)|`. Let `O` be the edges of `H`
whose endpoints are both ordinary vertices. The ordinary degree bound and the
degree-sum identity give

```text
|O| ≤ 2m.
```

For each boundary `h ∈ {1,…,R−1}`, let `A_h` be the edges of `H` joining layer
`h−1` to layer `h`. Every interlayer edge belongs to exactly one such set,
while base and apex edges belong to none. Therefore

```text
Σ_h |A_h| ≤ |O| ≤ 2m.
```

Choose a boundary `h` with `|A_h| ≤ 2m/(R−1)`. Call layers below `h` the lower
part, and put all other vertices, including the apex, in the upper part.
Deleting `A_h` removes every edge between these two parts: the apex is adjacent
only to the top layer, which lies in the upper part.

For each edge `{s,s+1}` of the index cycle, let `S_s` be the ordinary edges of
`H` whose endpoints both lie in the lower part and whose cyclic coordinates
are `s` and `s+1`. These sets partition the lower-part edges. The cycle labels
are distinct for `t ≥ 3`: equality with a reversed label would force `2=0` in
`ℤ/tℤ`, which is impossible. Hence

```text
Σ_s |S_s| ≤ |O| ≤ 2m.
```

Choose `s` with `|S_s| ≤ 2m/t`, and delete this seam as well.

There is an explicit two-coloring of the remaining graph. In the lower part,
remove `{s,s+1}` from the index cycle and color by the parity of position on
the resulting path, independently of the layer. Every surviving lower edge
has consecutive path coordinates. In the upper part, color ordinary vertices
by layer parity and give the apex the color opposite to that of the top layer.
There are no base edges in the upper part, so every surviving upper edge has
different-colored endpoints. The boundary cut removes all edges between the
parts, so the two colorings combine.

The deletion set `F=A_h ∪ S_s` consists of actual edges of `H`, and

```text
|F| ≤ (2/(R−1) + 2/t) m.
```

The argument also covers the empty subgraph and isolated vertices. It never
requires a missing ambient edge to be present in `H`.

The Lean version proves a support formulation: `H` may be a spanning graph
below the ambient graph, with all edge endpoints in a finite set `S`; the bound
uses `|S|`. Vertices outside `S` are isolated and can receive arbitrary colors.
Taking `S` to be the vertex set of any original `Subgraph` recovers the stated
bound, including its isolated vertices.

### 2.4. Parameters

Given `ε>0`, choose an integer `M ≥ 2` with `M > 4/ε`. Set

```text
R = M+1,     t = 2M+1.
```

Then `t` is odd and at least 3, and

```text
2/(R−1) + 2/t = 2/M + 2/(2M+1) ≤ 4/M ≤ ε.
```

The graph is chosen from `ε` before any subgraph is considered. Sections 2.2
and 2.3 prove the construction lemma for this single graph.

## 3. Every fixed number of colors

Fix `r ≥ 2`, and suppose `g(m) ≥ c m` for all `m ≥ M`, where `c>0`. Choose

```text
ε = min(c, 1/(M+1)) > 0.
```

If a natural number `a` satisfies `a ≤ εm`, then `a ≤ g(m)` for every `m`:

* For `m ≥ M`, use `a ≤ εm ≤ cm ≤ g(m)`.
* For `m < M`, use `a ≤ εm < ε(M+1) ≤ 1`. Since `a` is a nonnegative integer,
  it must be zero, so `a ≤ g(m)` even when `g(m)=0`.

Take the graph `X` supplied by Section 2 for this `ε`, and form the join

```text
G = X ∨ K_(r−2).
```

For an arbitrary subgraph `H ⊆ G`, let `J` be its restriction to the `X`
vertices. Delete from `J` the edges supplied by the construction lemma. The
same edges are edges of `H`, and their number is at most
`ε|V(J)| ≤ ε|V(H)|`, hence at most `g(|V(H)|)`. The remaining `J` uses two
colors. Assign each of the at most `r−2` remaining clique vertices its own new
color. This gives an `r`-coloring of `H` after deletion. Arbitrary missing
edges in `H` do not obstruct this coloring.

However, `G` cannot be `(r+1)`-colorable. Its clique uses `r−2` different
colors; all cross edges of the join are present, so none of those colors can
be used on `X`. Only three colors remain for `X`, contrary to its construction.
For `r=2`, the clique is empty and the argument is simply that `X` is not
3-colorable.

Thus `G` satisfies the antecedent of admissibility and violates its conclusion.
The function `g` is not admissible.

## 4. The Big-O endpoint

For nonnegative real-valued functions `n` and `g(n)`, the assertion
`n =O[atTop] g(n)` yields a positive constant `C` and a threshold after which
`n ≤ Cg(n)`. Dividing by `C` gives `g(n) ≥ (1/C)n`, so Section 3 applies.
Conversely, an eventual lower bound `g(n) ≥ cn`, with `c>0`, gives
`n ≤ (1/c)g(n)` and therefore this Big-O relation.

We have proved, for every fixed `r≥2`,

```text
¬ ∃ g : ℕ → ℕ, IsAdmissible r g ∧ (n ↦ n) =O[atTop] (n ↦ g(n)).
```

This is not the assertion that every admissible `g` is `o(n)`: exclusion of an
eventual linear lower bound does not imply that stronger limit statement.

## 5. Correspondence with the Lean modules

| Mathematical component | Lean source |
|---|---|
| Explicit graph and support-sensitive local bound | [`Basic.lean`](../Erdos1092/Basic.lean) |
| Three-color increments and the winding contradiction | [`Winding.lean`](../Erdos1092/Winding.lean) |
| Degree counts, boundary and seam averaging, actual two-coloring | [`Cuts.lean`](../Erdos1092/Cuts.lean) |
| Join, arbitrary `Subgraph`, small-size integrality, Big-O bridge | [`Outer.lean`](../Erdos1092/Outer.lean) |
| Relabeling the finite construction onto `Fin n` | [`Transport.lean`](../Erdos1092/Transport.lean) |
| Parameter existence | [`Parameters.lean`](../Erdos1092/Parameters.lean) |
| Complete construction and final theorem | [`Main.lean`](../Erdos1092/Main.lean) |

The outer reduction is proved with an abstract construction interface, but
the final theorem supplies that interface from the explicit finite graph.
Neither Rödl's stronger constructions nor an unproved existence assertion is
a hypothesis of the final endpoint.
