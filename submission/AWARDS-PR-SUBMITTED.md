Submitted as [TheJustinSunPrize/awards PR #5025](https://github.com/TheJustinSunPrize/awards/pull/5025).

E1092 has no independently confirmed entry in the current problem bank. This PR proposes one unassigned record containing complete mathematical and Lean proof evidence, and requests inclusion, numbering and scope review. It leaves the existing catalog, index, candidates and awards unchanged.

## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

## Problem

- Problem ID: **Erdős 1092; JSP identifier unassigned.** This is a proposed independent addition, with the final JSP identifier and placement requested during maintainer review.
- Original source: [Erdős problem 1092](https://www.erdosproblems.com/1092), with the at-most-r coloring convention and every fixed r >= 2.
- Proposed change: add `problems/proposals/erdos-1092.md`, an unassigned record with the original complete Lean source, exact statement, mathematical proof, reproduction and attribution evidence. No numbered entry, index/count change, candidate or award record is created. This new-problem proposal is outside the ordinary existing-entry update route in CONTRIBUTING; it implements the linked recommendation as a concrete review diff. Inclusion, placement and numbering are requested as part of this review.
- Related recommendation: https://github.com/TheJustinSunPrize/awards/issues/5024
- Known mathematical solution: Vojtěch Rödl, *Nearly bipartite graphs with large chromatic number*, Combinatorica 2, 377–383 (1982), [DOI](https://doi.org/10.1007/BF02579434). [Tang](https://www.erdosproblems.com/forum/thread/1092#post-1675) explains the r=2 consequence, [Chojecki](https://www.erdosproblems.com/forum/thread/1092#post-5983) the clique join, and [Bloom](https://www.erdosproblems.com/forum/thread/1092#post-6408) the at-most-r scope.

## Formal statement

- Complete mathematical solution supplied for review: [self-contained proof](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/MATHEMATICAL-PROOF.md), Sections 1–4; mathematical result already solved, no new solver claim.
- Mathematical review: local proof/scope audit completed; official mathematical and statement review pending. Lean compilation does not replace this review.
- Formal statement: [Main.lean](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/Erdos1092/Main.lean), declaration `Erdos1092.erdos_1092`.
- Statement origin: proposed statement requiring organizer review, matching the canonical all-subgraph function-budget model in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean).
- Exact scope: every fixed natural r >= 2, every finite graph, every subgraph (not necessarily induced), all sizes simultaneously, actual edge deletions bounded by g(card H.verts), including isolated vertices. The endpoint negates existence of an admissible g with n = O(g(n)); it does not assert g=o(n). Its only arguments are r and 2<=r. [Scope audit](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/SCOPE.md).

## Proof submission

```json
[
  {
    "repository": "https://github.com/Wang060919/erdos1092-lean",
    "branch": "main",
    "commit": "7649a561f6c2c8caabd60d0834beeffe89a357d5"
  }
]
```

- Proof: `Erdos1092/Main.lean`, `Erdos1092.erdos_1092`.
- This endpoint constructs the finite non-3-colorable graph and its hereditary edge cuts, transports to Fin n, and discharges all premises of the clique-join/Big-O argument. No core-existence assumption remains.
- Independent literal bridge: [CheckScope.lean](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/CheckScope.lean), `original_fixed_r`, `original_r_two`, `original_all_fixed`, `admissible_literal`.
- Public history / exact revision CI: https://github.com/Wang060919/erdos1092-lean/actions/runs/38265286397 (head_sha = 7649a561f6c2c8caabd60d0834beeffe89a357d5, completed/success). No earlier private completion date or commit timestamp alone is claimed as public priority evidence.

## Reproduction

- Lean: leanprover/lean4:v4.33.0; release commit d8b18978322de05a8f3dba51ef03cf5461676c17.
- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependencies fixed in lake-manifest.json.
- [Build instructions](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/README.md).
- Setup: pinned Elan toolchain, or ERDOS1092_LEAN_BIN pointing to the official Lean 4.33.0 bin directory. Run `./scripts/cache.sh`, then `./scripts/verify.sh`.
- Verification: SHA256 manifest, actual dependency HEAD/tracked-clean, default `lake --wfail build`, four literal scope checks, 68 public-declaration axiom checks, and seven custom proof-module kernel replays.
- Axiom command: [CheckAxioms.lean](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/CheckAxioms.lean). All four final endpoints (`erdos_1092`, `erdos_1092_all`, `f_asymptotic_2`, `f_asymptotic_general`) depend only on `propext`, `Classical.choice`, `Quot.sound`. Audit also rejects any nonstandard axiom in all other queried declarations.

## Pre-submission Lean verification

- Checked proof version: 7649a561f6c2c8caabd60d0834beeffe89a357d5, matching CI head_sha.
- [Clean directory reproduction](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/portable-reproduction.json).
- Actual conclusion: build, literal original-scope bridge, standard-foundation audit and all seven custom-module kernel replays passed.
- Limitations: imported exact-pinned Mathlib/dependency libraries trusted, not independently replayed in full. No separate external checker or independent human verification is claimed. Organizer review remains required.

## Attribution

- Mathematical result: Rödl (1982), with the cited Tang/Chojecki reduction and Bloom scope clarification; this submission is for the Lean role only.
- Lean development: published through Wang060919's original repository; precise proof files and history linked above. [Attribution](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/ATTRIBUTION.md). Repository ownership alone is not presented as a completed organizer authorship adjudication.
- Independent human verifier: none claimed.
- Relevant public professional relationships: none, as confirmed by the publisher.

## Submission checklist

This PR contains a new unassigned proposal, so its scope differs from the template's ordinary existing-entry update. The actual single-file diff and fixed proof references have been checked.

- [x] I changed only the unassigned E1092 proposal record and supplied its mathematical, formalization and attribution evidence. Existing catalog entries and index/eligibility/register records are unchanged.
- [x] The submitted result fully solves the original problem. Any submitted Lean proof is complete at the specified commit, with no sorry, admit or added unproved assumptions replacing proof steps.
- [x] I have linked the complete mathematical solution and its evidence and identified the mathematical solver and Lean contribution separately.
- [x] I am submitting my own contribution in the original repository, with selected commit in main and statement, reproduction and axiom evidence.
- [x] This PR contains no Lean source, archives, binaries, dependencies or private identity/contact/payment information.

## Requested maintainer decisions

Please review whether E1092 should be included as an independent problem, confirm the all-fixed-r/all-subgraph function-budget scope, review the supplied mathematics and Lean evidence, and assign an appropriate JSP identifier and catalog location if accepted. The proposal uses **Pending verification** for eligibility. No organizer acceptance, earliest-priority adjudication or award claim is asserted.
