# Lean 4 Formalization for Erdős Problem JSP-000298

This package provides a standalone, reproducible Lean 4 formalization of monochromatic subset-sum avoidance bounds for Erdős Problem JSP-000298 (Erdős Problem #360), based on:
> Noga Alon and Paul Erdős, *Sure monochromatic subset sums*, Acta Arithmetica 74(3), 1996, pp. 269–272.

## Reproduction Instructions

Using `elan` (Lean version manager):

```bash
# Enter this submission directory
cd submissions/jsp-000298

# Fetch mathlib cache
lake exe cache get

# Build the Erdos298 library
lake build
```

## Formalized Theorems

### 1. Sieve-Remainder Bound (Alon–Erdős 1996, Section 2)
- `Erdos298.exists_coloring_sieve`: For any $n \ge 2, s \ge 1$, and finite set $P$ of integers not dividing $n$ (such as primes $p \le s$ with $p \nmid n$), there exists a coloring with $s + |P| + \lceil |R| / s \rceil$ colors avoiding monochromatic subset sum $n$, where $R = \{x \in \{1, \dots, n-1\} \mid (s+1)x < n \wedge \forall p \in P, p \nmid x\}$. This finite combinatorial theorem does **not** require $n \le s^3$.
- `Erdos298.minColors_le_sieve`: Formal chromatic number bound $f(n) \le s + |P| + \lceil |R| / s \rceil$.
- `Erdos298.minColors_le_two_s_add_remainder`: Specialized bound $f(n) \le 2s + \lceil |R| / s \rceil$ using $P = \{p \le s \mid p.\text{Prime} \wedge p \nmid n\}$.
- `Erdos298.exists_coloring_of_avoiding_family`: General covering principle showing any family of subset-sum-avoiding sets covering $\{1, \dots, n-1\}$ induces an avoiding coloring.

### 2. Mathlib Selberg Sieve Connection & Controlled Divisor Error
- `Erdos298.sieve_remainder_eq_coprime_filter`: Representation of the remainder $R$ as the coprimality filter on $\{1, \dots, \lfloor(n-1)/(s+1)\rfloor\}$ with respect to $D = \prod_{p \in P} p$.
- `Erdos298.erdosBoundingSieve`: Direct instantiation of Mathlib's `Mathlib.NumberTheory.SelbergSieve.BoundingSieve` with unit density $\nu(d) = 1/d$.
- `Erdos298.siftedSum_eq_card_remainder`: Identification of `BoundingSieve.siftedSum` with the exact cardinality $|R|$.
- `Erdos298.card_remainder_le_mainSum_errSum`: Upper Moebius sieve bound $|R| \le m \cdot \text{mainSum}(\mu^+) + \text{errSum}(\mu^+)$ for any upper Moebius coefficients $\mu^+$.
- `Erdos298.erdos_rem_bound_of_mem_divisors`: Rigorous proof that the divisor counting error satisfies $|\text{rem}(d)| \le 1$ for all divisors $d \mid D$.

### 3. Cubic-Root Bound (Elementary Baseline)
- `Erdos298.exists_coloring_of_le_cube`: Constructive explicit coloring with $2s$ colors for any $n \le s^3$ avoiding monochromatic subset sums ($f(n) \le 2\lceil n^{1/3}\rceil$).
- `Erdos298.minColors_le_two_mul_s`: Chromatic number bound $f(n) \le 2s$ whenever $n \le s^3$.

### 4. Structural Avoidance Blocks
- `Erdos298.interval_block_avoids_subset_sum`: Interval blocks $A_k = \{x \mid n \le (k+1)x \wedge kx < n\}$ are subset-sum-free for all $k \ge 1$.
- `Erdos298.upper_half_subset_sum_free`: Special case $k = 1$ covering $[\lceil(n+1)/2\rceil, n-1]$.
- `Erdos298.dvd_subset_sum_free`: Multiples of any non-divisor $m \nmid n$ form a subset-sum-free class.
- `Erdos298.small_card_block_avoids_subset_sum`: Any block of cardinality $\le s$ with elements satisfying $(s+1)x < n$ avoids subset sum $n$.

### 5. Non-Trivial Lower Bound
- `Erdos298.no_one_coloring_of_ge_three`: No 1-coloring avoids monochromatic subset sums for $n \ge 3$ (since $\{1, n-1\}$ sums to $n$).
- `Erdos298.minColors_ge_two`: Chromatic number lower bound $f(n) \ge 2$ for all $n \ge 3$.