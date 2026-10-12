# Verification records

`proof-inputs.json` identifies the exact eleven Lean source/configuration files
checked in the original local audit. Packaging changes do not change any of
those proof inputs. `result.json` is the historical result of that audit; it is
not a claim of CI for a later Git commit.

`CheckScope.lean` independently transcribes the all-size, all-subgraph condition
and elaborates four bridges to the main theorem. `CheckAxioms.lean` prints the
axioms of all 68 public declarations named in `targets.json`. The portable
verification script checks those declarations and the literal bridges against
only `propext`, `Classical.choice`, and `Quot.sound`.

Run `./scripts/verify.sh` to regenerate current build, scope, axiom, and seven
proof-module kernel replay logs under `.lake/verification/`. Imported pinned
Mathlib/dependency libraries are trusted; their complete environments are not
independently replayed. The import-only `Erdos1092.lean` wrapper is checked by
the default Lake build; the seven modules containing custom proof bodies are
the kernel replay targets.

`portable-reproduction.json` records the later clean independent-directory
run, with newly fetched exact dependency source revisions, no copied project
`.lake`, fresh custom-module builds, and the same successful checks. Its raw
logs are shipped in `evidence/portable/`. The records were added after that run;
public CI checks the final published tree at its exact Git revision.
