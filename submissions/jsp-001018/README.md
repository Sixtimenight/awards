# JSP-001018: Formal Lean 4 Proof of Erdős Problem 1213

## English

This directory contains the self-contained Lean 4 formalization for **JSP-001018** (Erdős Problem 1213).

### Theorem
Norbert Hegyvári proved in 1986 (*Acta Math. Hungar.* 48, 193–200) that every strictly increasing sequence of positive integers with bounded gaps contains two distinct consecutive blocks with equal sums once its last element is sufficiently large.

In `Erdos1213.lean`, we formalize this result with the explicit threshold:
$$f(a, K) = 4^K \cdot a + 2K \cdot (4^K)^2$$

The proof uses a sliding-window discrete intermediate value property combined with dyadic slot pigeonhole argument.

### Package Contents
- `Erdos1213.lean`: The complete 514-line Lean 4 proof.
- `STATEMENT.md`: Mathematical and formal statement alignment.
- `VERIFICATION.md`: Axiom audit, reproduction instructions, and zero-sorry certificate.
- `evidence/`: Machine build log and kernel axiom audit log.
- `lean-toolchain`: Pinned Lean 4 toolchain version `leanprover/lean4:v4.33.0`.
- `lakefile.toml`: Lake configuration.

### Reproduction
```sh
cd submissions/jsp-001018
lake build
```