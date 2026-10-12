# Erdős problem 1092: hereditary edge budgets

Lean formalization of the negative answer for every fixed `r ≥ 2`.
The theorem covers every finite graph and every subgraph, with the deletion
budget evaluated at each subgraph's own vertex count.

For `g : ℕ → ℕ`, admissibility means that whenever every subgraph `H` of a
finite graph `G` can be made at most `r`-colorable by deleting at most
`g(|V(H)|)` of its actual edges, `G` has chromatic number at most `r + 1`.
The main theorem proves that no admissible `g` has `n = O(g(n))`.
There is no monotonicity assumption on `g`, core-existence hypothesis, or
restriction to a particular graph size. This Big-O negation is the audited
scope; it does not assert the stronger statement `g(n) = o(n)`.

- [Full mathematical proof](docs/MATHEMATICAL-PROOF.md)
- [Original statement and exact Lean scope](docs/SCOPE.md)
- [Mathematical and formalization attribution](docs/ATTRIBUTION.md)
- [Independent literal statement](verification/CheckScope.lean)
- [Clean directory reproduction](verification/portable-reproduction.json)
- [Historical local verification record](verification/LOCAL-AUDIT.md)

The primary declaration is `Erdos1092.erdos_1092` in
[`Erdos1092/Main.lean`](Erdos1092/Main.lean). Its only arguments are `r : ℕ`
and `2 ≤ r`. The odd-cycle construction, three-color winding obstruction,
hereditary edge cuts, clique join, small-size integrality argument and
asymptotic bridge are all proved in this repository.

## Reproduce

Lean is pinned to `leanprover/lean4:v4.33.0` and Mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`. `lake-manifest.json` pins all nine
dependencies. On Linux, use the pinned Elan toolchain, or set
`ERDOS1092_LEAN_BIN` to the `bin` directory of the official Lean 4.33.0
release (containing `lean`, `lake` and `leanchecker`). The scripts check the
runtime version and release commit.

```sh
./scripts/cache.sh
./scripts/verify.sh
```

The verification script checks the shipped SHA256 manifest and actual
dependency revisions, runs the default Lake build with warnings as failures,
elaborates the independent original statement, audits all 68 public
declarations and four literal bridges, and kernel-replays all seven custom
proof modules. Logs are regenerated under `.lake/verification/`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the
axiom audit. Imported pinned Mathlib and dependency libraries are trusted,
rather than all independently replayed.

The [GitHub Actions workflow](.github/workflows/verify.yml) downloads the
pinned official Lean release, checks its SHA256, and repeats these checks
from the checked-out revision. A workflow definition or a local build alone
is not evidence that a particular remote commit passed CI; the public run
must identify that exact commit.

## Catalog status

E1092 does not yet have a confirmed independent JSP catalog identifier.
A problem recommendation and scope confirmation are being prepared using
the [recommendation draft](submission/RECOMMENDATION-DRAFT.md). Publication
and Lean verification do not establish award eligibility, priority or
organizer acceptance. No unrelated JSP identifier is reused.
