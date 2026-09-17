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

## Status of Results: Unconditional Theorems vs. Conditional Reductions

| Component | Formal Status | Scope & Dependencies |
| :--- | :--- | :--- |
| **Cubic-Root Upper Bound** ($f(n) \le 2\lceil n^{1/3}\rceil$) | **Unconditionally Proven** | Complete constructive Lean 4 proof (`Erdos298.exists_coloring_of_le_cube`). |
| **Sieve-Remainder Bound** ($f(n) \le s + \|P\| + \lceil \|R\|/s \rceil$) | **Unconditionally Proven** | Complete combinatorial proof (`Erdos298.exists_coloring_sieve`). |
| **Finite Selberg Sieve** ($\|R\| \le m/G + z^4$) | **Unconditionally Proven** | Complete quadratic form diagonal sum & error bound (`Erdos298.selberg_remainder_bound`). |
| **Prime Reciprocal Sum Bound** | **Unconditionally Proven** | Complete explicit prime sum bound (`Erdos298.minColors_le_of_sum_primes`). |
| **CFP 4-Layer Upper Bound** | **Unconditionally Proven** | Complete constructive 4-layer coloring (`Erdos298.exists_coloring_conlon_fox_pham`). |
| **Elementary Lower Bound** ($f(n) \ge 2$) | **Unconditionally Proven** | Machine-checked for all $n \ge 3$ (`Erdos298.minColors_ge_two`, `Erdos298.minColors_ge_two_via_cfp`). |
| **CFP Lower Bound Reduction Engine** | **Unconditionally Proven** | Monotone lifting, fiber pigeonhole, AP hitting bridge (`Erdos298.minColors_ge_of_cfp_witness`). |
| **Asymptotic Growth Equivalence** ($f(n) \asymp F(n)$) | **Conditional Reduction** | Requires external lower/upper witnesses (`Erdos298.conlon_fox_pham_bounds`, `Erdos298.erdos_problem_360_asymptotic_master`). |
| **Asymptotic Lower Bound Witness** | **Open Formalization Frontier** | Constructing the explicit witness family for $f(n) \ge c F_{cfp}(n)$ requires deep external theorems (Szemerédi–Vu, Brun–Titchmarsh prime concentration, quantitative Mertens) not currently in Mathlib. |

> [!NOTE]
> **Honest Scope Boundary**: The formalization achieves a fully verified, unconditional upper bound theory through the 2021 Conlon–Fox–Pham 4-layer construction and an unconditional lower bound of $f(n) \ge 2$. The asymptotic two-sided equivalence $f(n) \asymp F(n)$ is formalized as a conditional reduction framework; the concrete instantiation of the asymptotic lower bound witness remains open due to prerequisites beyond current Mathlib.

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

### 3. Finite Selberg Sieve Remainder Bound
- `Erdos298.selberg_remainder_bound`: Quantitative, unconditional finite Selberg sieve bound:
  $$|R| \le \frac{\lfloor(n-1)/(s+1)\rfloor}{G} + z^4$$
  for all $n \ge 2, s \ge 1, z \ge 1$, where $G = \sum_{d \in D.\text{divisors}, d \le z} \text{selbergTerms}(d) \ge 1$.
- `Erdos298.mainSum_selbergWeight_eq`: Exact evaluation of the diagonalized quadratic form on canonical Selberg weights $w(d)$: $\text{mainSum}(\lambda^2 w) = 1/G$.
- `Erdos298.errSum_selbergWeight_le`: Rigorous error sum bound $\text{errSum}(\lambda^2 w) \le (\sum_{d \mid D} |w(d)|)^2 \le z^4$.
- `Erdos298.selbergWeight_isUpperMoebius`: Proof that the normalized $\Lambda^2$ Selberg weights yield an upper Moebius sieve.
- `Erdos298.sieveG_ge_one`: Non-triviality bound $G \ge 1 > 0$.

### 4. Prime Reciprocal Sum Lower Bounds & Quantitative Chromatic Bounds
- `Erdos298.selbergTerms_prime`: Exact evaluation $\text{selbergTerms}(p) = 1 / (p - 1)$ for any prime $p \nmid n$.
- `Erdos298.sieveG_ge_one_add_sum_primes`: Prime sum lower bound $G \ge 1 + \sum_{p \in P, p \le z} \frac{1}{p - 1}$.
- `Erdos298.minColors_le_of_sieveG_lower_bound`: Chromatic number bound for any lower bound $g_0 \le G$:
  $$f(n) \le 2s + \left\lceil \frac{n - 1}{s(s+1) g_0} + \frac{z^4}{s} \right\rceil.$$
- `Erdos298.minColors_le_of_sum_primes`: Chromatic number bound via the full prime reciprocal sum:
  $$f(n) \le 2s + \left\lceil \frac{n - 1}{s(s+1)\left(1 + \sum_{p \le z, p \nmid n} \frac{1}{p - 1}\right)} + \frac{z^4}{s} \right\rceil.$$
- `Erdos298.minColors_le_of_prime_subset`: Chromatic number bound for any prime subset $Q \subseteq P$ with $\max Q \le z$:
  $$f(n) \le 2s + \left\lceil \frac{n - 1}{s(s+1)\left(1 + \sum_{p \in Q} \frac{1}{p - 1}\right)} + \frac{z^4}{s} \right\rceil.$$

### 5. Cubic-Root Bound (Elementary Baseline)
- `Erdos298.exists_coloring_of_le_cube`: Constructive explicit coloring with $2s$ colors for any $n \le s^3$ avoiding monochromatic subset sums ($f(n) \le 2\lceil n^{1/3}\rceil$).
- `Erdos298.minColors_le_two_mul_s`: Chromatic number bound $f(n) \le 2s$ whenever $n \le s^3$.

### 6. Structural Avoidance Blocks
- `Erdos298.interval_block_avoids_subset_sum`: Interval blocks $A_k = \{x \mid n \le (k+1)x \wedge kx < n\}$ are subset-sum-free for all $k \ge 1$.
- `Erdos298.upper_half_subset_sum_free`: Special case $k = 1$ covering $[\lceil(n+1)/2\rceil, n-1]$.
- `Erdos298.dvd_subset_sum_free`: Multiples of any non-divisor $m \nmid n$ form a subset-sum-free class.
- `Erdos298.small_card_block_avoids_subset_sum`: Any block of cardinality $\le s$ with elements satisfying $(s+1)x < n$ avoids subset sum $n$.

### 7. Non-Trivial Lower Bound
- `Erdos298.no_one_coloring_of_ge_three`: No 1-coloring avoids monochromatic subset sums for $n \ge 3$ (since $\{1, n-1\}$ sums to $n$).
- `Erdos298.minColors_ge_two`: Chromatic number lower bound $f(n) \ge 2$ for all $n \ge 3$.

### 8. Conlon–Fox–Pham (2021) 4-Layer Upper Bound Construction
- `Erdos298.congruence_block_high_avoids`: Proof that high congruence blocks $\{a \in [1, n-1] \mid a \equiv t \pmod d \wedge x_t a > n\}$ avoid subset sums to $n$.
- `Erdos298.congruence_block_mid_avoids`: Proof that mid congruence blocks $\{a \in [1, n-1] \mid a \equiv t \pmod d \wedge (d+x_t)a > n \wedge x_t a < n\}$ avoid subset sums to $n$.
- `Erdos298.exists_coloring_conlon_fox_pham`: Constructive 4-layer coloring (interval blocks, prime multiples, reduced congruence classes modulo $d$, and small remainder blocks) using $s_1 + |P| + 2|\text{reducedResidues } d| + \lceil |R_{cfp}| / s_{rem} \rceil$ colors avoiding monochromatic subset sums to $n$.
- `Erdos298.minColors_le_conlon_fox_pham`: Chromatic number bound:
  $$f(n) \le s_1 + |P| + 2|\text{reducedResidues } d| + \left\lceil \frac{|R_{cfp}|}{s_{rem}} \right\rceil.$$
- `Erdos298.minColors_le_conlon_fox_pham_coarse`: Coarser bound bounding $|\text{reducedResidues } d| \le d$:
  $$f(n) \le s_1 + |P| + 2d + \left\lceil \frac{|R_{cfp}|}{s_{rem}} \right\rceil.$$

### 9. Asymptotic Reductions & Conlon–Fox–Pham (2021)
- `Erdos298.HasChromaticUpperBound`: Formal witness predicate for upper bounds relative to growth scale $F(n)$.
- `Erdos298.HasChromaticLowerBound`: Formal witness predicate for lower bounds relative to growth scale $F(n)$.
- `Erdos298.conlon_fox_pham_bounds`: The Conlon–Fox–Pham two-sided asymptotic growth theorem $c F(n) \le f(n) \le C F(n)$.

### 10. Conlon–Fox–Pham (2021) Lower Bound Formulation & Combinatorial Reductions
- `Erdos298.hasValidColoring_of_le`: Monotone lifting of valid colorings ($m \le k \wedge \mathrm{HasValidColoring}(n, m) \implies \mathrm{HasValidColoring}(n, k)$).
- `Erdos298.minColors_gt_of_not_hasValidColoring`: Contrapositive chromatic lower bound: $\neg \mathrm{HasValidColoring}(n, k) \implies f(n) > k$.
- `Erdos298.minColors_ge_of_not_hasValidColoring`: Lower bound: $\neg \mathrm{HasValidColoring}(n, k) \implies f(n) \ge k + 1$.
- `Erdos298.monochromatic_fiber_sum_eq`: Exact partition identity $\sum_{i < k} |S \cap c^{-1}(i)| = |S|$ for any coloring $c$.
- `Erdos298.exists_monochromatic_fiber_strict`: Strict monochromatic pigeonhole principle: $|S| > k M \implies \exists i \in \mathrm{Fin}\; k, |S \cap c^{-1}(i)| > M$.
- `Erdos298.subsetSums`: Explicit subset sum collection $\Sigma(A) = \{\sum_{x \in B} x \mid B \subseteq A\}$.
- `Erdos298.arithProg`: Explicit arithmetic progression finset $\{a + l \cdot d \mid 0 \le l \le L\}$.
- `Erdos298.not_avoids_of_arithProg_subset`: Subset-sum hitting from arithmetic progression coverage: $\mathrm{arithProg}(a, d, L) \subseteq \Sigma(A) \wedge n \in \mathrm{arithProg}(a, d, L) \implies \neg \mathrm{AvoidsSubsetSum}(A, n)$.
- `Erdos298.denseSubsetSumHitting_of_ap`: Bridge theorem from arithmetic progression witness to dense subset sum hitting.
- `Erdos298.not_avoidsMonoSubsetSum_of_dense`: Proof that any $k$-coloring fails avoidance when $|S| > k M$ and every subset of size $M + 1$ hits $n$.
- `Erdos298.minColors_ge_of_dense`: General lower bound $f(n) \ge k + 1$ from dense subset hitting.
- `Erdos298.minColors_ge_of_cfp_witness`: Conlon–Fox–Pham lower bound theorem from structured witness `CFPLowerBoundWitness n k`.
- `Erdos298.minColors_ge_of_cfp_ap_witness`: Arithmetic progression form of the lower bound theorem from `CFPAPWitness n k`.
- `Erdos298.hasChromaticLowerBound_of_cfp_witnesses`: Formal deduction of global asymptotic lower bound $\mathrm{HasChromaticLowerBound}(F, c)$.
- `Erdos298.subsetSums_add_of_disjoint` (Lemma A): Addition of subset sums on disjoint sets: $x \in \Sigma(A) \wedge y \in \Sigma(B) \implies x + y \in \Sigma(A \cup B)$.
- `Erdos298.subsetSums_interval_extend_single` (Lemma B, single step): If $[a, b] \subseteq \Sigma(A)$ and $t \le b - a + 1$, then $[a, b + t] \subseteq \Sigma(A \cup \{t\})$.
- `Erdos298.subsetSums_interval_extend` (Lemma B, inductive): If $[a, b] \subseteq \Sigma(A)$ and $\forall t \in B, t \le b - a + 1$, then $[a, b + \sum B] \subseteq \Sigma(A \cup B)$.
- `Erdos298.subsetSums_scale` (Lemma C): Scaling lemma: $v \cdot Q \subseteq A \wedge m \in \Sigma(Q) \implies v \cdot m \in \Sigma(A)$.
- `Erdos298.mem_subsetSums_of_scaled` (Lemma C Corollary): If $v \mid n$, $v \cdot Q \subseteq A$, and $(n / v) \in \Sigma(Q)$, then $n \in \Sigma(A)$.
- `Erdos298.cfpWitness_two`: Explicit machine-checked witness for $k = 1$ using $\{1, n-1\}$ for any $n \ge 3$.
- `Erdos298.minColors_ge_two_via_cfp`: Non-trivial lower bound $f(n) \ge 2$ for $n \ge 3$ derived from the general Section 8 witness framework.
- `Erdos298.cfpScale`: Canonical Conlon–Fox–Pham asymptotic growth scale $F(n) = \frac{n^{1/3}\,(n/\varphi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}$.
- `Erdos298.cfpScale_pos_of_hyp`: Machine-checked strict positivity of $\mathrm{cfpScale}(n)$ for $\log n > 1$ and $\varphi(n) > 0$.

### 11. Final Master Theorems (Unified Synthesis)
- `Erdos298.erdos_problem_360_finite_master`:
  For any integer $n \ge 3$, any lower bound witness $w : \mathrm{CFPLowerBoundWitness}(n, k)$, and any valid Conlon–Fox–Pham 4-layer upper configuration $(s_1, P, d, s_{rem})$ with $s_{rem} \le s_1$ and $\forall p \in P, p \nmid n$:
  $$k + 1 \le f(n) \le s_1 + |P| + 2|\mathrm{reducedResidues}(d)| + \left\lceil \frac{|R_{cfp}|}{s_{rem}} \right\rceil.$$
- `Erdos298.erdos_problem_360_unconditional_master`:
  Unconditional two-sided bound for all $n \ge 3$:
  $$2 \le f(n) \le s_1 + |P| + 2|\mathrm{reducedResidues}(d)| + \left\lceil \frac{|R_{cfp}|}{s_{rem}} \right\rceil.$$
- `Erdos298.erdos_problem_360_asymptotic_master` *(Conditional Reduction)*:
  Conlon–Fox–Pham (2021) two-sided asymptotic growth equivalence:
  $$c \cdot F(n) \le f(n) \le C \cdot F(n)$$
  for all sufficiently large $n$, assuming matching asymptotic lower and upper bound witnesses with respect to $F$.
- `Erdos298.erdos_problem_360_unified_solution` *(Grand Synthesis Conjunction)*:
  The master theorem unifying all three historical generations of Erdős Problem 360:
  1. (Alon–Erdős 1996 Elementary, Unconditional): Cubic-root bound $f(n) \le 2s$ for $n \le s^3$.
  2. (Alon–Erdős 1996 Sieve, Unconditional): Quantitative Selberg prime-sieve bound on $f(n)$.
  3. (Conlon–Fox–Pham 2021 Upper, Unconditional): 4-layer chromatic upper bound.
  4. (Conlon–Fox–Pham 2021 Lower, Unconditional): Inverse additive lower bound witness theorem $f(n) \ge k + 1$.
  5. (Conlon–Fox–Pham 2021 Asymptotic, Conditional): Two-sided asymptotic growth equivalence $f(n) \asymp F(n)$ under hypothesis of matching witnesses.