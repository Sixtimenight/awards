# Lean 4 Formalization for Erdős Problem JSP-000298

This package provides a standalone, reproducible Lean 4 formalization of monochromatic subset-sum avoidance bounds for Erdős Problem JSP-000298 (Erdős Problem #360), based on:
> 1. Noga Alon and Paul Erdős, *Sure monochromatic subset sums*, Acta Arithmetica 74(3), 1996, pp. 269–272.
> 2. David Conlon, Jacob Fox, and Huy Tuan Pham, *Subset sums, completeness and colorings*, arXiv:2104.14766 [math.CO], 2021.
> 3. Matt DeVos, *On a problem of Erdős and Heilbronn*, Discrete Mathematics / DeVos–Goddyn–Mohar (2009).

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
| **Kneser Addition Theorem & Iterated Growth (Phase U1)** | **Unconditionally Proven** | Complete inductive proof via DeVos (2009) on arbitrary composite modulus (`Erdos298.iterSum_card_ge_of_zero_mem_of_generates`). |
| **CFP Lemma 5.6 Claim 1 (Growth Budget)** | **Unconditionally Proven** | Claim 1 bounded unconditionally via U1 (`Erdos298.growthSteps_card_le_p16Budget_closed`). |
| **Phase P08 Branch A AP Lifting** ($|R.H|^3 \ge R_{\mathrm{card}}$) | **Unconditionally Proven** | Complete AP lifting geometry, 0 sorry (`Erdos298.hasIntAPCoverBranchA`). |
| **Phase P08/P09 Master Branch Reductions** | **Unconditionally Proven** | Decoupled master theorems (`hasIntAPCover_of_branchA_and_branchB`, `cfp_lemma_5_6_m_eq_n_of_branches_and_sieve`). |
| **Grand Unified Master Theorem** | **Unconditionally Proven (as a conjunction)** | Conjunction of 5 statements (`Erdos298.erdos_problem_360_unified_solution`); items 1–4 are unconditional results, item 5 is the *conditional* asymptotic reduction of the row below. |
| **Unconditional Two-Sided Master Theorem** | **Unconditionally Proven** | $2 \le f(n) \le s_1 + \|P\| + 2\|\text{reducedResidues } d\| + \lceil \|R_{cfp}\| / s_{rem} \rceil$ (`Erdos298.erdos_problem_360_unconditional_master`). |
| **Asymptotic Growth Equivalence** ($f(n) \asymp F(n)$) | **Conditional Reduction** | `Erdos298.erdos_problem_360_asymptotic_master`: from matching witnesses `HasChromaticLowerBound F c` and `HasChromaticUpperBound F C` deduces $c F(n) \le f(n) \le C F(n)$ for large $n$. **Neither witness is proven for $F = \mathrm{cfpScale}$**: the lower one needs the open items below, the upper one needs an asymptotic evaluation of the 4-layer bound (Mertens-type estimates not in Mathlib). |
| **Asymptotic Lower Bound Witness** | **Open Formalization Frontier** | Constructing the explicit witness family for $f(n) \ge c F_{cfp}(n)$ requires deep external theorems (Szemerédi–Vu, Brun–Titchmarsh prime concentration, quantitative Mertens) not currently in Mathlib. |

> [!NOTE]
> **Honest Scope Boundary**: The formalization achieves a fully verified, unconditional upper bound theory through the 2021 Conlon–Fox–Pham 4-layer construction, an unconditional lower bound of $f(n) \ge 2$, and extensive formalization of the Conlon–Fox–Pham additive combinatorics machinery (DeVos/Kneser, Lev, CFP Lemma 5.4, Lemma 5.6, Phase P08 Branch A). The asymptotic two-sided equivalence $f(n) \asymp F(n)$ is formalized as a rigorous reduction framework; the concrete instantiation of the asymptotic lower bound witness remains open due to prerequisites beyond current Mathlib.

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
- `Erdos298.selbergTerms_of_squarefree`: Exact evaluation $\text{selbergTerms}(c) = 1 / \varphi(c)$ for any squarefree integer $c \ge 1$.
- `Erdos298.sieveG_ge_half_totient_ratio_mul_log`: **Master Selberg sieve $G$ lower bound**:
  $$\frac{1}{2} \frac{\varphi(n)}{n} \log z \le \mathrm{sieveG}(n, s, z)$$
  unconditionally for all $n \ge 2, s \ge 1, 2 \le z \le s$.
- `Erdos298.minColors_le_of_totient_log`: Totient-weighted sieve bound with totient-logarithm sieve $G$ lower bound:
  $$f(n) \le 2s + \left\lceil \frac{n - 1}{s(s+1) ((1/2) (\varphi(n)/n) \log z)} + \frac{z^4}{s} \right\rceil.$$

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
- `Erdos298.subsetSums_Icc_zero`: Continuous subset sum coverage $[0, m(m+1)/2] \subseteq \Sigma(\{1, \dots, m\})$.
- `Erdos298.mem_subsetSums_Icc_of_le`: $n \le m(m+1)/2 \implies n \in \Sigma(\{1, \dots, m\})$.
- `Erdos298.mem_subsetSums_scaled_Icc_of_le`: $v \mid n \wedge (n/v) \le m(m+1)/2 \implies n \in \Sigma(v \cdot \{1, \dots, m\})$.
- `Erdos298.cfpLowerBoundSet`: Canonical scaled arithmetic progression $v \cdot \{1, \dots, m\}$.
- `Erdos298.cfpLowerBoundSet_subset`, `Erdos298.cfpLowerBoundSet_card`, `Erdos298.mem_subsetSums_cfpLowerBoundSet`: Inclusion, cardinality, and divisor hitting for CFP key subsets.
- `Erdos298.cfpWitness_scaled`: Constructive scaled arithmetic progression witness instantiation of `CFPLowerBoundWitness n 1`.
- `Erdos298.minColors_ge_two_via_cfp_scaled`: Lower bound $f(n) \ge 2$ derived from any scaled arithmetic progression witness.
- `Erdos298.IsDiverse`: Conlon–Fox–Pham §5.1 $k$-diversity predicate on finite sets.
- `Erdos298.isDiverse_of_le`, `Erdos298.isDiverse_of_subset`: Diversity monotonicity under scalar parameter and subset inclusion.
- `Erdos298.quotient_scale_subset`: Re-scaling lemma $v \cdot ((A \cap v\mathbb{N}) / v) \subseteq A$.
- `Erdos298.mem_subsetSums_of_quotient_hit`: Quotient divisor hitting theorem: $v \mid n \wedge (n/v) \in \Sigma((A \cap v\mathbb{N}) / v) \implies n \in \Sigma(A)$.
- `Erdos298.mem_subsetSums_of_quotient_Icc_subset`, `Erdos298.mem_subsetSums_of_scaled_Icc_subset`: Scaled continuous interval hitting theorems.
- `Erdos298.CFPDiverseWitness`: Conlon–Fox–Pham diverse lower bound witness structure representing the core combinatorial data of Section 5.1.
- `Erdos298.CFPLowerBoundWitness.ofDiverse`: Bridge theorem from `CFPDiverseWitness` to `CFPLowerBoundWitness`.
- `Erdos298.minColors_ge_of_cfp_diverse_witness`: Chromatic lower bound theorem $k + 1 \le f(n)$ from any diverse lower bound witness.
- `Erdos298.not_isDiverse_iff`: Exact predicate characterization of non-diversity ($\neg \mathrm{IsDiverse}(A, t) \iff \exists d \ge 2, |A \setminus d\mathbb{N}| < t$).
- `Erdos298.card_le_card_filter_dvd_add`: Disjoint partition bound $|A| \le |A \cap d\mathbb{N}| + (t - 1)$ when $|A \setminus d\mathbb{N}| < t$.
- `Erdos298.card_image_div_eq_card_filter_dvd`: Strict injectivity and cardinality preservation of integer division on multiples: $|(A \cap d\mathbb{N})/d| = |A \cap d\mathbb{N}|$.
- `Erdos298.div_step_bounds`: Bound preservation under division: $A \subseteq [1, B] \implies (A \cap d\mathbb{N})/d \subseteq [1, \lfloor B/d \rfloor]$.
- `Erdos298.exists_diverse_scaled_subset`: Algorithmic Conlon–Fox–Pham (2021, §5.1) divisor-extraction iteration theorem: for any $A \subseteq [1, B]$ with $1 \le t$, $B < 2^L$, and $(t-1)L < |A|$, there exist $v > 0$ and non-empty $Q \subseteq \mathbb{N}$ such that $v \cdot Q \subseteq A$, $Q$ is $t$-diverse, and $|A| \le |Q| + (t-1)L$.
- `Erdos298.scale_factor_le_of_mem_bounds`: Upper bound on the extracted factor: $v \le B$.
- `Erdos298.subsetSumsMod`: The set of residue classes modulo $d$ formed by subset sums of $A$.
- `Erdos298.subsetSumsMod_eq_univ_of_divisor_counts` (Conlon–Fox–Pham 2021, Lemma 5.8): If for every divisor $e \mid d$, $|A \setminus e\mathbb{N}| \ge e - 1$, then subset sums of $A$ cover all residues modulo $d$.
- `Erdos298.subsetSumsMod_eq_univ_of_isDiverse`: If $A$ is $t$-diverse and $d - 1 \le t$ with $d > 0$, then $\Sigma_d(A) = \mathbb{Z}/d\mathbb{Z}$.
- `Erdos298.exists_diverse_scaled_subset_mod_coverage`: The extracted diverse scaled subset $Q$ from `exists_diverse_scaled_subset` covers all residues modulo $d$ for every modulus $1 \le d \le t + 1$.
- `Erdos298.sanity_mod_coverage_empty`: Sanity check for $d = 1, A = \emptyset$.
- `Erdos298.sanity_mod_coverage_4`: Sanity check for $d = 4, A = \{1, 5, 9\}$.
- `Erdos298.sanity_mod_coverage_6`: Sanity check for $d = 6, A = \{2, 3, 4, 8, 9\}$.

### 11. Residue Fiber Decomposition and Product Bound (Conlon–Fox–Pham 2021, Lemma 5.11)
- `Erdos298.zmodProj`: Natural projection ring homomorphism $\pi : \mathbb{Z}/N\mathbb{Z} \to \mathbb{Z}/d\mathbb{Z}$ for $d \mid N$.
- `Erdos298.residueFiber`: Residue fiber $F_r = \{s \in \Sigma_N(A) \mid \pi(s) = r\}$.
- `Erdos298.card_subsetSumsMod_dvd_le_fiber`: Machine-checked fiber lower bound:
  $$|\Sigma_N(A \cap d\mathbb{N})| \le |F_r| \quad \text{for any non-empty fiber } F_r \ne \emptyset$$
  proved by decomposing any subset $B \subseteq A$ into $U \subseteq A \setminus d\mathbb{N}$ and $V \subseteq A \cap d\mathbb{N}$, obtaining a base representative $x = \sum U \pmod N$ with $\pi(x) = r$, and constructing an injective translation $y \mapsto x + y$ from $\Sigma_N(A \cap d\mathbb{N})$ into $F_r$.
- `Erdos298.subsetSumsMod_image_zmodProj`: Projection image identity: $\pi(\Sigma_N(A)) = \Sigma_d(A)$.
- `Erdos298.card_subsetSumsMod_dvd_mul_card_le` (CFP Lemma 5.11):
  $$|\Sigma_d(A)| \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$$
  proved by partitioning $\Sigma_N(A)$ into residue fibers over $\Sigma_d(A)$ and applying the fiber lower bound to each non-empty fiber.
- `Erdos298.card_mul_card_subsetSumsMod_dvd_le_of_isDiverse`:
  $$d \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$$
  for any $t$-diverse set $A$ and modulus $d$ with $d - 1 \le t$ and $d > 0$, combining Lemma 5.8 ($|\Sigma_d(A)| = d$) with Lemma 5.11.
- `Erdos298.sanity_fiber_example_12`: Sanity check on $N=12, d=3, A=\{1, 3, 6\}$ verifying fiber sizes ($|\Sigma_{12}(D)| = 4, |F_0|=4, |F_1|=4, |F_2|=0$), illustrating the necessity of $F_r \ne \emptyset$.
- `Erdos298.sanity_fiber_example_6`: Sanity check on $N=6, d=2, A=\{1, 7, 2\}$ verifying unequal fiber sizes ($|F_0|=3, |F_1|=2$) and product bound $2 \cdot 2 \le 5$.

### 12. Translation Growth and Double Counting (Conlon–Fox–Pham 2021, Lemma 2.6 & Lemma 2.7)
- `Erdos298.translate`: Translation of a finset `S` by an element `x`: $S + x = \{s + x \mid s \in S\}$.
- `Erdos298.delta`: Incremental growth cardinality $\delta(S, x) = |(S + x) \setminus S|$.
- `Erdos298.card_translate`, `Erdos298.translate_zero`, `Erdos298.translate_add`, `Erdos298.delta_zero`, `Erdos298.card_union_translate`: Structural translation properties and union cardinality formula $|S \cup (S + x)| = |S| + \delta(S, x)$.
- `Erdos298.delta_add_le`: Subadditivity of translation growth:
  $$\delta(S, x + y) \le \delta(S, x) + \delta(S, y).$$
- `Erdos298.delta_sum_le_sum_delta`, `Erdos298.delta_sum_le_mul_of_forall_le`, `Erdos298.delta_sum_le_mul_of_forall_le_real` (CFP Lemma 2.7):
  Sumset list growth bounds: if $\forall x \in xs, \delta(S, x) \le D$, then $\delta(S, \sum xs) \le |xs| \cdot D$.
- `Erdos298.interCard`: Intersection cardinality $I(x) = |(S + x) \cap S|$, with $I(x) + \delta(S, x) = |S|$.
- `Erdos298.sum_interCard_eq_sq`: Double counting identity on any finite group $G$:
  $$\sum_{x \in G} |(S + x) \cap S| = |S|^2.$$
- `Erdos298.card_smallGrowth_mul_le` & `Erdos298.card_smallGrowth_le_div` (CFP Lemma 2.6):
  $$|G| \cdot (|S| - D) \le |S|^2 \quad \text{and} \quad |G| \le \frac{|S|^2}{|S| - D} \quad \text{for } D < |S|,$$
  along with corresponding real versions `card_smallGrowthR_mul_le` and `card_smallGrowthR_le_div`.
- `Erdos298.exists_mem_large_growth` & `Erdos298.exists_mem_large_growth_real`:
  Selection tool guaranteeing existence of an element $a \in T$ with $\delta(S, a) > D$ whenever $|T| > |G|$.
- `Erdos298.card_subsetSumsMod_insert_eq`:
  Identification of the subset sum cardinality increment upon element addition:
  $$|\Sigma_d(A \cup \{x\})| = |\Sigma_d(A)| + \delta(\Sigma_d(A), x).$$
- `Erdos298.natCast_zmod_injOn_Ico` & `Erdos298.card_image_natCast_zmod_of_Ico`:
  Modulo projection injectivity and cardinality preservation for integer candidate subsets located on intervals of length $\le d$.

### 13. Iterated Sumsets and Kneser Bridge (Conlon–Fox–Pham 2021, Lemma 2.3 Bridge)
- `Erdos298.sumset`: Sumset $A + B = \{a + b \mid a \in A, b \in B\}$.
- `Erdos298.iterSum`: $k$-fold iterated sumset $k T$, with $0 T = \{0\}$ and $(k + 1) T = k T + T$.
- `Erdos298.stab`: Stabilizer subgroup $\mathrm{Stab}(S) = \{x \in G \mid \delta(S, x) = 0\}$.
- `Erdos298.iterSum_zero`, `Erdos298.iterSum_succ`, `Erdos298.mem_sumset_iff`, `Erdos298.sumset_assoc`, `Erdos298.sumset_zero_left`, `Erdos298.sumset_zero_right`: Foundational algebraic sumset properties.
- `Erdos298.iterSum_add`: Additive decomposition of iterated sumsets:
  $$(a + b) T = a T + b T.$$
- `Erdos298.iterSum_subset_succ` & `Erdos298.iterSum_mono_of_zero_mem`: Monotonicity of iterated sumsets when $0 \in T$:
  $$k_1 \le k_2 \wedge 0 \in T \implies k_1 T \subseteq k_2 T.$$
- `Erdos298.iterSum_smallGrowth_subset`: Preservation of small translation growth under sumsets:
  $$k (G_D) \subseteq G_{k D}.$$
- `Erdos298.cochrane_ostergaard_spencer_arith_le`: Algebraic lemma of Cochrane–Ostergaard–Spencer:
  $$(k + 1) q \le 2(k(q - 1) + 1) \quad \text{for } k \ge 1, q \ge 2.$$
- `Erdos298.iterSum_growth_bound_of_kneser_data`: Bridge theorem deducing $(k + 1) |T| \le 2 |kT|$ from Kneser bounds $|kT| \ge (k(q - 1) + 1)|H|$ and $|T| \le q|H|$ for $q \ge 2$.
- `Erdos298.iterSum_card_ge_of_kneser_hyp` & `Erdos298.iterSum_card_ge_of_kneser_hyp_real`:
  Conditional growth interfaces in natural and real numbers:
  $$\min(|G|, (k + 1)|T|/2) \le |kT|.$$

### 14. Subgroup Index, Scaled Coprimality, and Fiber Coordinates (Conlon–Fox–Pham 2021, §5.1)
- `Erdos298.subgroupIndex`: Exact subgroup index $g = \gcd(t, \gcd(B))$ of the subgroup generated by $B$ modulo $t$.
- `Erdos298.subgroupIndex_pos`, `Erdos298.subgroupIndex_dvd_modulus` ($g \mid t$), `Erdos298.subgroupIndex_dvd_mem` ($\forall a \in B, g \mid a$).
- `Erdos298.subgroupIndex_mono`: $B' \subseteq B \implies g(B) \mid g(B')$.
- `Erdos298.subgroupIndex_doubles_of_lt`: $g(B) < g(B') \implies 2 g(B) \le g(B')$.
- `Erdos298.subgroupIndex_le_of_mem` ($a \in B \wedge a > 0 \implies g \le a$) and `Erdos298.subgroupIndex_le_modulus` ($t > 0 \implies g \le t$).
- `Erdos298.subgroupIndex_scaled_coprime`: Scaled coprimality theorem ensuring the scaled candidate set $B / g$ generates $\mathbb{Z}/(t/g)\mathbb{Z}$:
  $$\gcd\left(\frac{t}{g}, \gcd\left(\frac{B}{g}\right)\right) = 1 \quad \text{when } t > 0.$$
- `Erdos298.natCast_zmod_div_injOn_Ico` & `Erdos298.card_image_natCast_zmod_div_of_Ico`:
  Modulo projection injectivity and cardinality preservation for scaled candidate subsets on intervals of length $\le t/g$.
- `Erdos298.fiber`: Residue fiber $F_r = \{s \in S \mid \pi(s) = r\}$.
- `Erdos298.card_eq_sum_image_fibers`: Exact fiber partition cardinality formula $|S| = \sum_{r \in \pi(S)} |F_r|$.
- `Erdos298.translate_fiber_subset` & `Erdos298.delta_fiber_le_delta`: Single fiber growth bound $\delta(F_r, x) \le \delta(S, x)$ for elements $x$ in the kernel ($\pi(x) = 0$).
- `Erdos298.centerFiber`: Fiber centering $F_r - x_0$ around a base representative $x_0 \in F_r$.
- `Erdos298.card_centerFiber` ($|F_r - x_0| = |F_r|$), `Erdos298.centerFiber_subset_kernel` ($F_r - x_0 \subseteq \ker \pi$), and `Erdos298.delta_centerFiber_eq` ($\delta(F_r - x_0, x) = \delta(F_r, x)$).

### 15. Coset Arithmetic Progression Lifting (Conlon–Fox–Pham 2021, Lemma 5.10)
- `Erdos298.IntAP`: Integer arithmetic progression structure $\{a + j \cdot b \mid 0 \le j < k\}$ with base $a \in \mathbb{Z}$, step $b > 0$, and length $k \in \mathbb{N}$.
- `Erdos298.IntAP.toFinset` & `Erdos298.IntAP.card_toFinset`: Image set and exact cardinality formula:
  $$|P| = k.$$
- `Erdos298.cosetAPLift`: Canonical lifting of a coset of a cyclic subgroup $H \le \mathbb{Z}/N\mathbb{Z}$ of order $h$ ($h \mid N$) to an integer arithmetic progression of length $h$ and common difference $N/h$.
- `Erdos298.cosetAPLift_card`:
  $$|\mathrm{cosetAPLift}(N, h, c)| = h.$$
- `Erdos298.coset_family_length_sum_eq`: Exact length sum identity for a family of $q$ lifted coset APs each of length $h$:
  $$\sum_{i < q} |P_i| = q \cdot h.$$
- `Erdos298.coset_family_length_sum_le_three_mul`: Length sum budget bound for a coset partition of $R \subseteq \mathbb{Z}/N\mathbb{Z}$:
  $$q \cdot h \le 3 |R|.$$

### 16. Numerical Condition Interface and Greedy State Machine (Conlon–Fox–Pham 2021, §5.1)
- `Erdos298.FiniteConditions`: Purely mathematical structure isolating the 10 explicit numerical parameters and combinatorial conditions for CFP Lemma 5.6:
  - Parameters: $t > 0, A \subseteq \mathbb{N}, v > 0, K, M > 0, k_{div}, U > 0, D > 0, gMax > 0, \xi > 0, \ell > 0, B_{growth} \le K$.
  - Hypotheses: $K + M \le |A|$, $\mathrm{IsDiverse}(A, k_{div})$, subgroup index bounds $g(B) \le gMax \wedge g(B) - 1 \le k_{div}$ on all $B \subseteq A$ with $|B| \ge M$, $U < t / (2 gMax)$, $8 D < U$, and growth budget $(32 / \ell) \cdot t \le D \cdot (K - B_{growth})$.
- `Erdos298.GreedyState`: Discrete state tracking $(E, B)$ with $E \subseteq A$.
  - Invariants: `GreedyState.card_B` ($|B| = |A| - |E|$), `GreedyState.B_card_ge` ($|B| \ge M$ for $j \le K$), and `GreedyState.B_nonempty` ($B \ne \emptyset$).
- `Erdos298.isGrowthStage`, `Erdos298.isSaturatedStage`, `Erdos298.isUnsaturatedStage`: The three mutually exclusive and exhaustive stages of the CFP greedy iteration:
  - Growth: $\exists r \in \pi(S), |F_r| \le U$.
  - Saturated: $\forall r \in \pi(S), |F_r| \ge \xi \cdot t / g$.
  - Unsaturated: Neither growth nor saturated.
- `Erdos298.exists_greedy_element`: Existence of candidate $a \in B$ maximizing the modular subset sum increment $\delta(S, a)$.
- `Erdos298.nextState`: State transition $E' = E \cup \{a\}$, satisfying `nextState_card` ($|E'| = |E| + 1$), `nextState_S_mono` ($S \subseteq S'$), and divisibility `nextState_g_dvd` ($g(B) \mid g(B')$).

### 17. Saturated Branch Modular Subset Sum Density (Conlon–Fox–Pham 2021, §5.1)
- `Erdos298.subsetSumsMod_eq_of_compl_dvd`: Subset sum stabilization $\Sigma_d(E) = \Sigma_d(A)$ when all remaining candidates in $A \setminus E$ are divisible by $d$.
- `Erdos298.card_ge_of_fibers_ge`: Global lower bound $|S| \ge g \cdot \text{bound}$ when $\pi(S) = \mathbb{Z}/g\mathbb{Z}$ and all fibers have size $\ge \text{bound}$.
- `Erdos298.mul_div_cancel_of_pos`: Density cancellation:
  $$g \cdot (\xi \cdot t / g) = \xi \cdot t \quad \text{for } g > 0.$$
- `Erdos298.card_subsetSumsMod_ge_of_saturated`: CFP Lemma 5.6 Saturated Branch Theorem:
  If at any step $j \le K$, the state is saturated, then the final modular subset sums achieve the target linear density:
  $$\xi \cdot t \le |\Sigma_t(A)|.$$


### 18. Single-Step Growth Bounds for Growth Stage (Conlon–Fox–Pham 2021, Claim 1 / P15)
- `Erdos298.card_smallGrowth_half_le`: Rigorous double-counting bound on translation small-growth set with threshold $D = |S| / 2$:
  $$|G_{|S|/2}| \le 2 |S|.$$
- `Erdos298.exists_large_growth_of_two_mul_lt`: Range 1 single-step growth:
  $$2 |S| < |T| \implies \exists x \in T, \delta(S, x) > |S| / 2.$$
- `Erdos298.floor_mul_succ_gt`: Exact floor arithmetic property:
  $$\forall s, b \in \mathbb{N}, b > 0 \implies 4s < (\lfloor 4s / b \rfloor + 1) \cdot b.$$
- `Erdos298.range2_arith_contradiction`: Range 2 arithmetic contradiction:
  $$(q + 1) \cdot b \le 4s \wedge 4s < (q + 1) \cdot b \implies \text{False}.$$

### 19. Combinatorial Core F1 of CFP Lemma 5.6 (Phases P16, P17, P18)
- `Erdos298.initialGreedyState`: Base empty state with $E = \emptyset$.
- `Erdos298.greedyChoice`: Constructive choice of element in $B$ maximizing translation growth $\delta(S, \cdot)$ via `Classical.choose`.
- `Erdos298.greedyChoice_mem`, `Erdos298.greedyChoice_max`: Chosen element lies in remaining candidates $B$ and achieves maximal delta increment.
- `Erdos298.greedySeq`: Complete discrete state trajectory $(E_j, B_j)_{j \le K}$.
- `Erdos298.card_greedySeq_zero_E`, `Erdos298.card_greedySeq_E`: Exact induction proving $|E_j| = j$ for all $j \le K$.
- `Erdos298.greedySeq_S_subset`: Invariant $\Sigma_t(E_j) \subseteq \Sigma_t(A)$.
- `Erdos298.greedyDelta`: Explicit functional representation of translation growth increment $\delta_j$.
- `Erdos298.card_greedySeq_S_succ`: Inductive subset sum cardinality increment formula $|S_{j+1}| = |S_j| + \delta_j$.
- `Erdos298.sum_delta_le_card_final`: Telescopic sum lower bound $\sum_{j < K} \delta_j \le |S_K|$.
- `Erdos298.sum_delta_le_total`: Master telescopic bound $\sum_{j < K} \delta_j \le |\Sigma_t(A)|$.
- `Erdos298.growthSteps`, `Erdos298.saturatedSteps`, `Erdos298.unsaturatedSteps`: Exact step classification sets for $j < K$.
- `Erdos298.disjoint_growth_unsaturated`: Formal proof of disjointness between growth and unsaturated steps.
- `Erdos298.steps_partition`: Exhaustive 3-way partition: every step $j < K$ is either saturated, growth, or unsaturated.
- `Erdos298.card_unsaturatedSteps_ge`: Rigorous capacity bound $|U| \ge K - B_{growth}$ when saturated steps are empty.
- `Erdos298.cfp_lemma_5_6_finite_core`: **The Combinatorial Core F1 Master Theorem of CFP Lemma 5.6**, establishing:
  $$\min\left(\xi, \frac{32}{\ell}\right) \cdot t \le |\Sigma_t(A)|$$
  under the numerical and combinatorial hypotheses of `FiniteConditions`.

### 20. Parameter Instantiation, Arithmetic Adapter & Non-Vacuity (Phase P19)
- `Erdos298.concreteFiniteConditions`: Constructive realization of `FiniteConditions` with concrete numbers ($t = 20, A = \{1, 3, 7\}, v = 1, K = 2, M = 1, k_{div} = 1, U = 9, D = 1, gMax = 1, \xi = 1/128, \ell = 1024, B_{growth} = 0$).
- `Erdos298.finiteConditions_realizable`: Rigorous non-vacuity theorem proving `Nonempty FiniteConditions` with machine-checked proofs of all 10 numerical and combinatorial conditions.
- `Erdos298.concreteCFPArithParams` & `Erdos298.concreteP17Conditions`: Explicit witness for the *arithmetic* parameter layer ($n = t = 16411$ (prime), $v = W = 1$, $y = 8192$, $A = [8192, 16383]$, $K = 32$, $M = 8160$, $k_{div} = 1$, $U = 9$, $D = 1$, $gMax = 1$, $\xi = 1/128$, $\ell = 2^{20}$, $B_{growth} = 31$, $r = 8160^5$), with machine-checked proofs of all conditions of `CFPArithParams` and `P17FiniteArithConditions` including E1, E2, E3 and $\xi \le 1/20$ (helper lemmas `witness_prime`, `witness_coprime`, `witness_subgroupIndex_le_one`, `witness_isDiverse`, `witness_log2`, `witness_E1`, `witness_loglog_le`, `witness_logr_ge`, `witness_E3`).
- `Erdos298.concreteCFPArithParams_numeric`: The growth-step budget condition $h_{numeric}$ ($\text{p16TotalBudget} \le B_{growth}$) holds for the witness.
- `Erdos298.cfpArithParams_realizable`, `Erdos298.p17FiniteArithConditions_realizable`, `Erdos298.lemma_5_6_parameter_hypotheses_satisfiable`: `Nonempty CFPArithParams`, `Nonempty (P17FiniteArithConditions _)`, and joint satisfiability of all parameter-side hypotheses of the Lemma 5.6 master reductions. The witness is deliberately small (for it the conclusion $\min(\xi, 32/\ell) t \le |\Sigma_t(A)|$ is trivial); its purpose is to certify that no theorem of the chain is vacuous for lack of admissible parameters.
- `Erdos298.primorialProd`: Primorial $W(P) = \prod_{p \in P} p$.
- `Erdos298.cfpTau`: The canonical Conlon–Fox–Pham ratio $\tau(W, m) = \varphi(W \cdot m) / (W \cdot m)$.
- `Erdos298.cfpTau_pos`: Strict positivity $0 < \tau(W, m)$ when $W > 0$ and $m > 0$.
- `Erdos298.inY` & `Erdos298.inY_v`: Number-theoretic rough candidate set definitions $Y(y, m, W)$ and $Y_v(y, m, W, v)$ from CFP §5.1 / Phase P11.
- `Erdos298.mem_Y_of_mem_Y_v`: Scaling injection bridge: $a \in Y_v \implies v \cdot a \in Y$.
- `Erdos298.CFPArithParams`: Arithmetic parameter configuration bundling target $n$, scaling $v$, modulus $t$, set $A$, and the 10 numerical conditions.
- `Erdos298.CFPArithParams.toFiniteConditions`: Canonical mapping from arithmetic parameters to the combinatorial interface `FiniteConditions`.
- `Erdos298.cfp_lemma_5_6_m_eq_n`: **CFP Lemma 5.6 Specialized to $m = n$ (Phase P19 Master Theorem)**:
  $$\min\left(\xi, \frac{32}{\ell}\right) \cdot t \le |\Sigma_t(A)|.$$
- `Erdos298.chromatic_lower_bound_of_diverse_density`: Interface bridge connecting modular density to chromatic lower bound $k + 1 \le f(n)$ via `CFPDiverseWitness`.

### 21. Diverse Subset Extraction and Subsampling (Conlon–Fox–Pham 2021, Lemma 5.4 / Phase 21)
- `Erdos298.filter_not_dvd_sdiff_subset`: Difference containment of non-divisible filtered sets: $((A \setminus v\mathbb{N}) \setminus (B \setminus v\mathbb{N})) \subseteq A \setminus B$.
- `Erdos298.card_sdiff_of_subset`: Difference cardinality identity $|A \setminus B| = |A| - |B|$ for $B \subseteq A$.
- `Erdos298.card_filter_not_dvd_le_card_add_sdiff`: Strict upper bound on the loss of non-divisible elements under subset restriction:
  $$|(A \setminus v\mathbb{N})| \le |(B \setminus v\mathbb{N})| + |A \setminus B|.$$
- `Erdos298.isDiverse_subset_of_card_diff_le`: **Deterministic Diversity Preservation Theorem** (Generalizing CFP Lemma 5.4):
  $$\forall B \subseteq A,\; |A| - |B| \le k - k' \implies \mathrm{IsDiverse}(B, k').$$
- `Erdos298.isDiverse_sdiff_singleton`: Single-element removal preserves $(k - 1)$-diversity:
  $$\mathrm{IsDiverse}(A, k) \wedge x \in A \implies \mathrm{IsDiverse}(A \setminus \{x\}, k - 1).$$
- `Erdos298.isDiverse_sdiff_finset`: Finite set removal preserves $(k - |E|)$-diversity:
  $$\mathrm{IsDiverse}(A, k) \wedge E \subseteq A \wedge |E| \le k \implies \mathrm{IsDiverse}(A \setminus E, k - |E|).$$
- `Erdos298.GreedyState.isDiverse_B`: Immediate application to greedy iteration state machine: the remaining candidate set $B_j = A \setminus E_j$ retains diversity $k_{div} - |E_j|$.
- `Erdos298.exists_diverse_subset_of_card_eq`: Constructive existence of diverse subsets of any prescribed size $s$ with controlled loss.
- `Erdos298.isDiverse_gcd_le_one`: Divisor bound on diverse sets: $\gcd(A) \le 1$ for any $k$-diverse set with $k \ge 1$.
- `Erdos298.isDiverse_gcd_eq_one`: Exact gcd identity $\gcd(A) = 1$ when $A$ contains at least one positive element.
- `Erdos298.subgroupIndex_eq_one_of_isDiverse`: Subgroup index vanishing: $\mathrm{subgroupIndex}(t, B) = 1$ for diverse $B$, linking diverse sets directly to `FiniteConditions`.
- `Erdos298.exists_disjoint_diverse_subsets`: Two-stage disjoint extraction of independent diverse subsets $A_1, A_2 \subseteq A$ with controlled loss.
- `Erdos298.exists_scaled_diverse_candidate`: End-to-end algorithmic divisor extraction + subsampling pipeline combining Section 8.3 with Lemma 5.4.
- `Erdos298.diverse_candidate_satisfies_finiteConditions`: Structural adapter proving extracted diverse sets fulfill `FiniteConditions` diversity and capacity bounds.
- `Erdos298.CFPLemma54Statement`: Mathematical specification of Conlon–Fox–Pham Lemma 5.4 subsampling interface.
- `Erdos298.cfp_lemma_5_4_of_deterministic`: Unconditional realization of Lemma 5.4 under controlled cardinality loss.
- `Erdos298.CFPLemma54FullStatement`: Formal specification of CFP Lemma 5.4 with range bound $N$.
- `Erdos298.cfp_lemma_5_4_full_of_deterministic`: Realization of full Lemma 5.4 under deterministic loss budget.
- `Erdos298.CFPLemma54Subsets`: Finset of size-$s$ subsets retaining $k'$-diversity.
- `Erdos298.cfp_lemma_5_4_all_subsets_diverse`: Universal diversity theorem: 100% of size-$s$ subsets are $k'$-diverse under controlled loss.
- `Erdos298.card_CFPLemma54Subsets_eq`: Combinatorial cardinality $\binom{|A|}{s}$ of diverse subsamples.

### 22. Modulo Density to Integer Subset Sum Growth (Conlon–Fox–Pham 2021, Lemma 2.5 & Lemma 5.5 / Phase 22)
- `Erdos298.subsetSums_mono`: Subset sums monotonicity: $A \subseteq B \implies \Sigma(A) \subseteq \Sigma(B)$.
- `Erdos298.maxFiberElem`, `Erdos298.maxFiberElem_mem`, `Erdos298.le_maxFiberElem`: Canonical maximum fiber representative construction.
- `Erdos298.card_subsetSums_insert_ge`: **Conlon–Fox–Pham (2021) Lemma 2.5** (Single-element subset sum growth from modular density):
  $$|\Sigma(A)| + |\Sigma_m(A)| \le |\Sigma(A \cup \{m\})| \quad (m \notin A, m > 0).$$
- `Erdos298.card_subsetSums_union_ge_sum`: Iterated disjoint subset sum growth:
  $$|\Sigma(S)| + \sum_{b \in B} |\Sigma_b(S)| \le |\Sigma(S \cup B)|.$$
- `Erdos298.card_subsetSums_union_ge_mul_min` & `card_subsetSums_union_ge_mul_min_real`:
  $$|B| \cdot L \le |\Sigma(S \cup B)| \quad \text{when } \forall b \in B, L \le |\Sigma_b(S)|.$$
- `Erdos298.cfp_lemma_5_5`: **CFP Lemma 5.5 Master Theorem**:
  For diverse subsets $A_1, A_2 \subseteq A$ with $A_1 \cap A_2 = \emptyset$ and $\forall b \in A_2, b \ge y/v$:
  $$|\Sigma(A)| \ge |A_2| \cdot c \cdot \frac{y}{v}.$$
- `Erdos298.cfp_lemma_5_5_scale`: Scaled specialization under Lemma 5.4 extraction ($|A_2| \ge s$) and Lemma 5.6 density:
  $$s \cdot \min\left(\xi, \frac{32}{\ell}\right) \cdot \frac{y}{v} \le |\Sigma(A)|.$$

### 23. Growth Steps Budget Infrastructure (Conlon–Fox–Pham 2021, Lemma 5.6 Claim 1 / Phase P16)
- `Erdos298.selectedMultiplesSums`: Tracked fiber multiples sums: $T_g(E) = \Sigma_t(E \cap g\mathbb{N})$ with monotonicity and incremental delta formula `card_selectedMultiplesSums_insert_eq`.
- `Erdos298.card_selectedMultiplesSums_le_U`: Capacity bound $|T_{g_j}(E_j)| \le U$ at growth stage derived from Lemma 5.11 fiber bound.
- `Erdos298.greedyChoice`: Stage-aware candidate selection: maximizes small fiber growth $\delta(T_{g_j}(E_j), a)$ in growth stages (`Erdos298.growthChoice`) and total subset sum growth $\delta(S, a)$ in ordinary stages (`Erdos298.ordinaryChoice`).
- `Erdos298.injOn_scaled_of_injOn` & `Erdos298.card_image_scaled_of_injOn`: Invertible scaling into quotient coordinates $\mathbb{Z}/(t/g)\mathbb{Z}$.
- `Erdos298.exists_candidate_range1_growth`: Unconditional single-step growth in Range 1 ($2|S| < |B|$): $\exists a \in B, 3|S| \le 2(|S| + \delta(S, a))$.
- `Erdos298.exists_candidate_range2_growth_of_iterSum_growth`: Range 2 single-step growth reduction on general modulus $\mathbb{Z}_N$: under iterated sumset growth $h_{u1}$, contradiction derived via $\lfloor 4s/b \rfloor \cdot \lfloor (b-1)/8 \rfloor \le s/2$ establishing $\exists a \in Q, |Q| \le 8 \delta(S, a)$.
- `Erdos298.zmodScale`, `zmodScale_add`, `zmodScale_injective`, `zmodScale_natCast_div`: Scaled quotient embedding $x \mapsto (g \cdot x.\text{val} : \mathbb{Z}_t)$ from $\mathbb{Z}_{t/g} \to \mathbb{Z}_t$.
- `Erdos298.translate_image_zmodScale`, `Erdos298.delta_image_zmodScale`: Exact preservation of translate and delta under scaled quotient embedding: $\delta(S.\text{image}(\text{zmodScale}), \text{zmodScale } x) = \delta(S, x)$.
- `Erdos298.closure_eq_top_of_one_mem`: Subgroup generated by $1 \in \mathbb{Z}_n$ is $\top$.
- `Erdos298.greedySeq_E_mono`: Sequence of chosen subsets is monotonic along the greedy iteration: $j_1 \le j_2 \implies E_{j_1} \subseteq E_{j_2}$.
- `Erdos298.f_g`, `f_g_mono`, `one_le_f_g`, `f_g_le_t`, `f_g_succ_eq`: Real trajectory potential $f_g(j) = |T_g(E_j)|$ with exact single-step formula at growth steps.
- `Erdos298.trajectory_growth_step_range1`: Unconditional Range 1 single-step growth along the trajectory: $3 f_g(j) \le 2 f_g(j+1)$.
- `Erdos298.trajectory_growth_step_range2`: Range 2 single-step growth along the trajectory: $8 f_g(j) + M \le 8 f_g(j+1)$.
- `Erdos298.p16MultBudget`, `Erdos298.p16LinearBudget`, `Erdos298.p16BlockBudget`, `Erdos298.p16TotalBudget`: Logarithmic budget functions:
  $$\text{p16MultBudget}(t) = 2(\lfloor\log_2 t\rfloor + 1), \quad \text{p16LinearBudget}(U, M) = \lfloor 8U/M \rfloor + 1,$$
  $$\text{p16BlockBudget}(t, U, M) = \text{p16MultBudget}(t) + \text{p16LinearBudget}(U, M),$$
  $$\text{p16TotalBudget}(t, gMax, U, M) = (\lfloor\log_2 gMax\rfloor + 1) \cdot \text{p16BlockBudget}(t, U, M).$$
- `Erdos298.card_mult_growth_steps_le`: Sparse multiplicative step counting bound: any marked subset $J$ with $3 f(j) \le 2 f(j+1)$ along a bounded monotonic sequence has $|J| \le 2(\lfloor\log_2 t\rfloor + 1)$.
- `Erdos298.card_linear_growth_steps_le`: Sparse linear step counting bound: any marked subset $J$ with $8 f(j) + M \le 8 f(j+1)$ has $|J| \le \lfloor 8U/M \rfloor + 1$.
- `Erdos298.card_partition_le_p16BlockBudget`: Marked-step partition bound: $|J| \le \text{p16BlockBudget}(t, U, M)$.
- `Erdos298.growthSteps_block_card_le_p16BlockBudget`: **Per-block budget theorem eliminating $h_{fibers}$**: each subgroup index block has $|J_y| \le \text{p16BlockBudget}(t, U, M)$ via partition into $J_{mult} \cup J_{lin}$ and application of D1 and D2.
- `Erdos298.greedySeq_g_dvd` & `Erdos298.greedySeq_g_le`: Divisibility and order monotonicity of subgroup index along the greedy trajectory.
- `Erdos298.greedySeq_g_image_doubling` & `Erdos298.doubling_chain_finset_card_le`: Doubling chain cardinality bound in $\mathrm{Finset}\;\mathbb{N}$: $|Y| \le \lfloor\log_2 gMax\rfloor + 1$.
- `Erdos298.growthSteps_g_image_card_le`: Distinct subgroup blocks in `growthSteps` bounded by $\lfloor\log_2 gMax\rfloor + 1$.
- `Erdos298.growthSteps_card_le_p16Budget`: **Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Logarithmic Master Theorem without $h_{fibers}$**:
  $$(\text{growthSteps } fc).\text{card} \le \text{p16TotalBudget}(fc.t, fc.gMax, fc.U, fc.M).$$
- `Erdos298.growthSteps_card_le_budget_of_p16`: Numerical adaptation of Claim 1 to `fc.B_growth` without $h_{fibers}$.
- `Erdos298.cfp_lemma_5_6_finite_core_of_p16`: Finite core of Lemma 5.6 with growth budget derived from `p16TotalBudget` without $h_{fibers}$.
- `Erdos298.subsetSumsMod_image_zmodScale`, `Erdos298.scaledSelectedSums_image_zmodScale`, `Erdos298.card_scaledSelectedSums_eq`, `Erdos298.delta_scaledSelectedSums_eq`: Bridge 1 establishing exact subset sum and delta preservation between quotient ring $\mathbb{Z}/(t/g)\mathbb{Z}$ and full modulus $\mathbb{Z}/t\mathbb{Z}$.
- `Erdos298.nat_gcd_cast_mem_addSubgroup`, `Erdos298.finset_gcd_cast_mem_addSubgroup`, `Erdos298.closure_natCast_image_eq_top_of_gcd_eq_one`, `Erdos298.closure_scaled_candidate_eq_top`: Bridge 2 establishing unconditional subgroup generation of $\mathbb{Z}/(t/g)\mathbb{Z}$ from $\{a/g \mid a \in B\}$ via Bézout coefficients and scaled coprimality.
- `Erdos298.small_fiber_card_mul_two_lt`: Bridge 3 establishing the quotient cardinality precondition $2 |S| < t / g$ along the growth trajectory.
- `Erdos298.exists_trajectory_range2_candidate_of_iterSum_growth`: Bridge 4 deriving the real Range 2 candidate $\exists a \in B_j, |B_j| \le 8 \delta(T_{g_j}(E_j), a)$ strictly from the iterated sumset growth theorem $h_{u1}$.
- `Erdos298.trajectory_growth_step_range2_of_iterSum_growth`: Real Range 2 trajectory growth step closed under $h_{u1}$.
- `Erdos298.growthSteps_block_card_le_p16BlockBudget_of_iterSum_growth`: Per-block budget bound derived directly from $h_{u1}$.
- `Erdos298.growthSteps_card_le_p16Budget_of_iterSum_growth`: Total growth steps bounded by $\text{p16TotalBudget}$ without external $h_{fibers}$ or $h_{range2}$, derived directly from $h_{u1}$.
- `Erdos298.growthSteps_card_le_budget_of_iterSum_growth`: Growth step budget bound derived strictly from $h_{u1}$.
- `Erdos298.cfp_lemma_5_6_finite_core_of_iterSum_growth`: Finite core of CFP Lemma 5.6 strictly reduced to iterated sumset growth $h_{u1}$.
- `Erdos298.cfp_lemma_5_6_m_eq_n_of_iterSum_growth`: CFP Lemma 5.6 ($m = n$) strictly reduced to iterated sumset growth $h_{u1}$.
- `Erdos298.growthSteps_card_le_p16Budget_closed`: Conlon–Fox–Pham Lemma 5.6 Claim 1 total growth steps bounded by $\text{p16TotalBudget}$ unconditionally without $h_{fibers}$ and without $h_{u1}$.
- `Erdos298.growthSteps_card_le_budget_closed`: Growth step budget bound $B_{growth}$ closed unconditionally without $h_{fibers}$ and without $h_{u1}$.
- `Erdos298.cfp_lemma_5_6_finite_core_closed`: Combinatorial Core F1 of CFP Lemma 5.6 ($\min(\xi, 32/\ell) \cdot t \le |\Sigma_t(A)|$) closed with U1 / Claim 1 mathematical dependencies resolved, still requiring P17 (`h_unsaturated_step_growth`) and parameter conditions (`h_inj`, `h_numeric`).
- `Erdos298.cfp_lemma_5_6_m_eq_n_closed`: Master CFP Lemma 5.6 ($m = n$) closed with U1 / Claim 1 mathematical dependencies resolved, still requiring P17 (`h_unsaturated_step_growth`) and parameter conditions (`h_inj`, `h_numeric`).
- `Erdos298.aperiodic_sumset_bound` & `Erdos298.iterSum_card_ge_of_zero_mem_of_generates`: DeVos (2009) inductive proof of Kneser's addition theorem and unconditional iterated sumset growth on arbitrary composite modulus:
  $$(k C).\mathrm{card} = N \lor (k + 1) \cdot C.\mathrm{card} \le 2 \cdot (k C).\mathrm{card}$$
  for any composite modulus $N = t/g$ ($[NeZero N]$), generators $C$ with $0 \in C$ and $\mathrm{closure}(C) = \top$, and any $k \ge 1$.
- Strict Axiom Audit: The entire proof chain relies strictly on standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]` with zero `sorry`, zero `admit`, and zero custom axioms.

### 24. Phase P17: Candidate Injectivity, Fiber Pullback, and Unsaturated Step Growth (Integration Layer)
- `Erdos298.injOn_of_inY_v`: Modulo $t$ injectivity $\mathrm{InjOn}(a \mapsto (a : \mathbb{Z}_t), A)$ derived unconditionally from $A \subseteq Y_v$ and interval bounds $y \le v \cdot t$.
- `Erdos298.zmodScale_val_div`: Scale retraction theorem: every element in $\ker(\mathrm{zmodProj}\; hd)$ is in the image of `zmodScale t g`.
- `Erdos298.card_centerFiberPullback` & `Erdos298.delta_centerFiberPullback`: Exact cardinality and translation delta preservation between centered fiber $C \subseteq \mathbb{Z}/t\mathbb{Z}$ and quotient pullback $T \subseteq \mathbb{Z}/(t/g)\mathbb{Z}$.
- `Erdos298.delta_fiber_pullback_le_delta_S`: Pullback delta bounded by total state delta: $\delta(T, a/g) \le \delta(S, a)$ for all $a \in B$.
- `Erdos298.unsaturatedSteps_div_neZero`: Machine-checked proof that quotient modulus $N = t/g$ is non-zero at any unsaturated step.
- `Erdos298.unsaturated_step_medium_fiber_and_smallGrowth`: Complete reduction of any unsaturated step with $\delta_j \le D$ to smallGrowth $T \subseteq \mathbb{Z}/(t/g)\mathbb{Z}$ with $U < |T|$, $|T| < \xi \cdot (t/g)$, $Q \subseteq \mathrm{smallGrowth}(T, D)$, $M \le |Q|$, and $\mathrm{closure}(Q) = \top$.
- `Erdos298.P17FiniteArithConditions`: Clean arithmetic parameter structure bundling raw parameters $(n, r, y, W)$ and explicit numerical thresholds $(E_1, E_2, E_3)$ without any structural or sieve oracles.
- `Erdos298.P17FiniteArithConditions.injOn_A`: Automatic elimination of external injectivity hypothesis $h_{inj}$ from $P17FiniteArithConditions$.
- `Erdos298.SmallGrowthTrichotomy`: Rigorous interface for the 3-branch small growth classification (proper subgroup, small cardinality, or AP cover with Selberg sieve bound).
- `Erdos298.unsaturated_step_growth_of_arith_conditional`: Master contradiction deriving $D \le \delta_j$ for each unsaturated step under P17 arithmetic conditions and the structural trichotomy.
- `Erdos298.unsaturatedSteps_growth_of_arith_conditional`: Uniform unsaturated growth bound $\forall j \in \mathrm{unsaturatedSteps}, D \le \delta_j$.
- `Erdos298.cfp_lemma_5_6_finite_core_of_arith_conditional`: Master finite core theorem with both $h_{inj}$ and $h_{unsaturated\_step\_growth}$ eliminated under $P17FiniteArithConditions$ and the explicit structural trichotomy.
- `Erdos298.GuardedTrichotomy` & `Erdos298.GuardedAPCover`: Named interfaces for the guarded structural trichotomy and for its Branch 3 in isolation. `GuardedAPCover` carries the density window $8d < |T| < \xi N$ ($0 < \xi \le 1/20$) together with the two guards $\mathrm{closure}(\mathrm{smallGrowth}(T,d)) = \top$ and $|\mathrm{smallGrowth}(T,d)| > 20(2d)^{51/50}/|T|^{1/50}$ that exclude Branches 1 and 2.
- `Erdos298.guardedAPCover_iff_trichotomy` (with `guardedAPCover_of_trichotomy`, `trichotomy_of_guardedAPCover`): The two interfaces are equivalent.
- `Erdos298.not_unguarded_ap_cover` & `Erdos298.not_unguarded_ap_cover'`: The *unguarded* coset-AP cover statement (used by an earlier version of the `*_of_ap_cover` chain) is refuted by $T = \mathrm{univ}$ in $\mathbb{Z}/(128d+1)\mathbb{Z}$; the chain below is therefore stated on `GuardedAPCover`.
- `Erdos298.unsaturated_step_growth_of_ap_cover`, `Erdos298.unsaturatedSteps_growth_of_ap_cover`, `Erdos298.cfp_lemma_5_6_finite_core_of_ap_cover`, `Erdos298.cfp_lemma_5_6_m_eq_n_of_ap_cover`, `Erdos298.cfp_lemma_5_6_finite_core_of_rough_count`, `Erdos298.cfp_lemma_5_6_m_eq_n_of_rough_count`: The Lemma 5.6 reduction chain with the structural input isolated to `GuardedAPCover` (the two guards are discharged inside `unsaturated_step_growth_of_ap_cover` from $\mathrm{closure}(Q) = \top$ and $E_1$) and the sieve input reduced to `APCoverSieveBridge` / per-AP rough counts.
- Strict Axiom Audit: All new theorems depend strictly on standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]` with zero `sorry` and zero custom axioms.

### 25. Final Master Theorems (Unified Synthesis)
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

### 26. Analytical Number Theory Foundation (`Erdos298/Mertens.lean`)
- Dedicated independent analytical module containing 15 machine-checked, zero-sorry, standard-axiom lemmas:
  - `Erdos298.inv_sq_le_inv_sub`: Telescoping inverse square bound $1/k^2 \le 1/(k-1) - 1/k$.
  - `Erdos298.sum_Icc_sub_tele`: Telescoping sum identity $\sum_{k=2}^z (f(k-1) - f(k)) = f(1) - f(z)$.
  - `Erdos298.sum_inv_sq_le_two`: Universal bound $\sum_{k=1}^z 1/k^2 \le 2$.
  - `Erdos298.harmonic_le_two_mul_sum_squarefree_inv`: Harmonic sum domination by squarefree reciprocals $\sum_{n=1}^z 1/n \le 2 \sum_{a \le z, \text{sqfree}} 1/a$.
  - `Erdos298.log_le_harmonic`: Logarithmic lower bound $\log z \le \sum_{n=1}^z 1/n$.
  - `Erdos298.sum_squarefree_inv_ge_half_log`: Squarefree reciprocal sum lower bound $\frac{1}{2} \log z \le \sum_{a \le z, \text{sqfree}} 1/a$.
  - `Erdos298.sum_squarefree_inv_totient_ge_half_log`: Squarefree totient reciprocal sum lower bound $\frac{1}{2} \log z \le \sum_{a \le z, \text{sqfree}} 1/\varphi(a)$.
  - `Erdos298.totient_of_squarefree`: Product formula $\varphi(d) = \prod_{p \in d.\mathrm{primeFactors}} (p - 1)$ for squarefree $d$.
  - `Erdos298.primeFactors_inj_of_squarefree`: Injectivity of prime factors on squarefree integers.
  - `Erdos298.cast_totient_of_squarefree` & `Erdos298.inv_totient_of_squarefree`: Real cast and reciprocal product identities for squarefree totients.
  - `Erdos298.one_add_inv_sub_one`: Algebraic identity $1 + 1/(p-1) = p/(p-1)$.
  - `Erdos298.sum_divisors_squarefree_inv_totient_le`: Divisor totient reciprocal sum bound $\sum_{d \mid n, \text{sqfree}} 1/\varphi(d) \le n/\varphi(n)$.
  - `Erdos298.sum_squarefree_inv_totient_le_mul`: Coprime squarefree decomposition of totient sum.
  - `Erdos298.sum_coprime_squarefree_inv_totient_ge_half`: Fundamental coprime squarefree totient reciprocal lower bound:
    $$\frac{1}{2} \frac{\varphi(n)}{n} \log z \le \sum_{c \le z, \text{Squarefree } c, \gcd(c, n) = 1} \frac{1}{\varphi(c)}.$$

