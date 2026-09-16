# JSP-001018: Verification Report and Axiom Audit

## English

### Verification Summary
- **Target module:** submissions/jsp-001018/Erdos1213.lean
- **Main theorem:** Erdos1213.erdos_1213
- **Helper theorem:** Erdos1213.equal_interval_sums_of_last_gt_explicitBound
- **Toolchain:** leanprover/lean4:v4.33.0
- **Library:** mathlib v4.33.0
- **Build result:** Passed (zero compile errors, exit code 0)

### Axiom Audit
Both theorems depend strictly on standard Lean 4 kernel axioms:
```text
info: Erdos1213.lean:508:0: 'Erdos1213.equal_interval_sums_of_last_gt_explicitBound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Erdos1213.lean:509:0: 'Erdos1213.erdos_1213' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- **sorryAx count:** 0 (zero unproved subgoals, clean closed proof)
- **Custom axioms:** None (no unproved assumptions)

### Reproduction Instructions
Because the package configuration (`lakefile.toml` and `lean-toolchain`) is self-contained in this directory, navigate to the package directory first:
```sh
cd submissions/jsp-001018
lake build
```
Or check the file directly within the Lake environment:
```sh
cd submissions/jsp-001018
lake env lean Erdos1213.lean
```

### Upstream Mirror Reference
This proof source is also mirrored and pinned in the external repository at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e (src/latest/ErdosProblems/Erdos1213.lean). Both copies are identical.
