# Citation

Candidate under formal verification; review pending.

## English

Erdős Problem JSP-000298 (Erdős Problem #360) investigates the minimum number of colors $f(n)$ required to color the integers $\{1, \dots, n-1\}$ such that no monochromatic subset sums to $n$. Originally posed by Erdős and Graham (1980), bounds of order $n^{1/3 \pm o(1)}$ were established by Noga Alon and Paul Erdős (*Acta Arithmetica* 74(3), 1996, pp. 269–272), with further sharp order bounds established by Conlon, Fox, and Pham (2021).

This machine-checked Lean 4 formalization proves both the elementary cubic-root bound, the general sieve-remainder upper bound theorem from Alon–Erdős (1996, Section 2), and connects the remainder to Mathlib's Selberg sieve framework:
1. **Sieve-Remainder Bound**: For any $n \ge 2, s \ge 1$, and finite set $P$ with elements not dividing $n$, there exists an explicit monochromatic subset-sum-avoiding coloring using $s + |P| + \lceil |R| / s \rceil$ colors (`exists_coloring_sieve`, `minColors_le_sieve`), where $R = \{x \in \{1, \dots, n-1\} \mid (s+1)x < n \wedge \forall p \in P, p \nmid x\}$. Crucially, this combinatorial theorem does not require $n \le s^3$.
2. **Prime Set Specialization**: Specializing to $P = \{p \le s \mid p.\text{Prime} \wedge p \nmid n\}$ yields $f(n) \le 2s + \lceil |R| / s \rceil$ (`minColors_le_two_s_add_remainder`), with $R$ equivalent to a coprimality filter on $\{1, \dots, \lfloor(n-1)/(s+1)\rfloor\}$ (`sieve_remainder_eq_coprime_filter`).
3. **Mathlib Selberg Sieve Instantiation**: Direct connection to `Mathlib.NumberTheory.SelbergSieve.BoundingSieve` (`erdosBoundingSieve`), proving the sifted sum equals $|R|$ (`siftedSum_eq_card_remainder`), deriving the upper Moebius bound $|R| \le m \cdot \text{mainSum}(\mu^+) + \text{errSum}(\mu^+)$ (`card_remainder_le_mainSum_errSum`), and establishing the controlled error bound $|\text{rem}(d)| \le 1$ for all divisors $d \mid D$ (`erdos_rem_bound_of_mem_divisors`).
4. **Cubic-Root Baseline**: For any $n \le s^3$, an explicit $2s$-coloring avoids monochromatic subset sums (`exists_coloring_of_le_cube`, `minColors_le_two_mul_s`), yielding $f(n) \le 2\lceil n^{1/3}\rceil$.
5. **Covering Principle & Avoidance Blocks**: General covering theorem (`exists_coloring_of_avoiding_family`), interval blocks for any $k \ge 1$ (`interval_block_avoids_subset_sum`), modular divisibility avoidance (`dvd_subset_sum_free`), and small-cardinality blocks (`small_card_block_avoids_subset_sum`).
6. **Lower Bound**: $f(n) \ge 2$ for all $n \ge 3$ (`minColors_ge_two`).