# Formalization Progress for Erdős Problem JSP-000298 (Erdős #360)

- **Problem**: Erdős Problem #360 / JSP-000298 (*Monochromatic subset sums to a prescribed integer*).
- **PR**: [TheJustinSunPrize/awards #353](https://github.com/TheJustinSunPrize/awards/pull/353)
- **Branch**: `candidate/jsp-000298`
- **Current Baseline Commit**: `ff1bcf801659eff147b479506e63384c9be66380`
- **Locked Toolchain**: Lean 4.33.0, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

---

## 1. Theorem Inventory & Status

| Category | Identifier | Mathematical Meaning | Status | Axioms Used |
| :--- | :--- | :--- | :--- | :--- |
| **Elementary Baseline** | `Erdos298.exists_coloring_of_le_cube` | Explicit $2s$-coloring avoiding subset sums when $n \le s^3$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Elementary Baseline** | `Erdos298.minColors_le_two_mul_s` | Chromatic number bound $f(n) \le 2s$ for $n \le s^3$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Combinatorial Sieve** | `Erdos298.exists_coloring_sieve` | General coloring with $s + \|P\| + \lceil \|R\|/s \rceil$ colors (no $n \le s^3$ restriction) | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Combinatorial Sieve** | `Erdos298.minColors_le_sieve` | Formal bound $f(n) \le s + \|P\| + \lceil \|R\|/s \rceil$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Prime Specialization** | `Erdos298.minColors_le_two_s_add_remainder` | Specialized bound $f(n) \le 2s + \lceil \|R\|/s \rceil$ with $P = \{p \le s \mid p.\text{Prime} \wedge p \nmid n\}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Coprime Representation** | `Erdos298.sieve_remainder_eq_coprime_filter` | $R = \{x \in [1, \lfloor(n-1)/(s+1)\rfloor] \mid \text{Coprime } D \; x\}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Coprime Representation** | `Erdos298.squarefree_prod_of_primes` | $\text{Squarefree } (\prod_{p \in P} p)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Mathlib Sieve Framework** | `Erdos298.erdosBoundingSieve` | Instantiation of Mathlib `BoundingSieve` with unit density $\nu(d) = 1/d$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Mathlib Sieve Framework** | `Erdos298.siftedSum_eq_card_remainder` | Identification $\text{siftedSum} = \|R\|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Mathlib Sieve Framework** | `Erdos298.card_remainder_le_mainSum_errSum` | Upper Moebius bound $\|R\| \le m \cdot \text{mainSum}(\mu^+) + \text{errSum}(\mu^+)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Divisor Error Control** | `Erdos298.erdos_rem_bound_of_mem_divisors` | Controlled divisor remainder error $\|\text{rem}(d)\| \le 1$ for all $d \mid D$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Elementary Lower Bound** | `Erdos298.minColors_ge_two` | Non-trivial chromatic lower bound $f(n) \ge 2$ for all $n \ge 3$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Sieve Level & G** | `Erdos298.sieveG_ge_one` | $G = \sum_{d \in L} \text{selbergTerms}(d) \ge 1 > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Selberg Weights** | `Erdos298.selbergWeight_one` | $w(1) = 1$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Upper Moebius** | `Erdos298.selbergWeight_isUpperMoebius` | $\lambda^2 w$ is an upper Moebius sieve | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Quadratic Diagonal** | `Erdos298.mainSum_selbergWeight_eq` | Exact diagonal main sum evaluation: $\text{mainSum}(\lambda^2 w) = 1/G$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Error Sum Bound** | `Erdos298.errSum_selbergWeight_le` | $\text{errSum}(\lambda^2 w) \le z^4$ via $\sum |w(d)| \le z^2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 1: Finite Sieve** | `Erdos298.selberg_remainder_bound` | Quantitative finite Selberg sieve bound $\|R\| \le m/G + z^4$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 2: Selberg Prime Terms** | `Erdos298.selbergTerms_prime` | Exact prime term evaluation: $\text{selbergTerms}(p) = 1/(p - 1)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 2: Prime Sum on G** | `Erdos298.sieveG_ge_one_add_sum_primes` | $G \ge 1 + \sum_{p \in P, p \le z} \frac{1}{p - 1}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 2: Generic Sieve Bound** | `Erdos298.minColors_le_of_sieveG_lower_bound` | $f(n) \le 2s + \lceil \frac{n - 1}{s(s+1) g_0} + \frac{z^4}{s} \rceil$ for any $g_0 \le G$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 2: Sieve by Primes** | `Erdos298.minColors_le_of_sum_primes` | $f(n) \le 2s + \lceil \frac{n - 1}{s(s+1)(1 + \sum_{p \le z, p \nmid n} 1/(p - 1))} + \frac{z^4}{s} \rceil$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 2: Sieve by Prime Subset**| `Erdos298.minColors_le_of_prime_subset` | $f(n) \le 2s + \lceil \frac{n - 1}{s(s+1)(1 + \sum_{p \in Q} 1/(p - 1))} + \frac{z^4}{s} \rceil$ for $Q \subseteq P$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Congruence High** | `Erdos298.congruence_block_high_avoids` | High congruence block avoids subset sums to $n$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Congruence Mid** | `Erdos298.congruence_block_mid_avoids` | Mid congruence block avoids subset sums to $n$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP 4-Layer Coloring** | `Erdos298.exists_coloring_conlon_fox_pham` | Explicit 4-layer coloring avoiding monochromatic subset sum $n$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Upper Bound** | `Erdos298.minColors_le_conlon_fox_pham` | $f(n) \le s_1 + \|P\| + 2\|\text{reducedResidues } d\| + \lceil \|R_{cfp}\| / s_{rem} \rceil$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Coarse Bound** | `Erdos298.minColors_le_conlon_fox_pham_coarse` | $f(n) \le s_1 + \|P\| + 2d + \lceil \|R_{cfp}\| / s_{rem} \rceil$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 4-5: Asymptotic Reduction** | `Erdos298.conlon_fox_pham_bounds` | Two-sided asymptotic growth reduction $c F(n) \le f(n) \le C F(n)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Color Lifting** | `Erdos298.hasValidColoring_of_le` | Monotone lifting of valid colorings: $m \le k \wedge \mathrm{HasValidColoring}(n, m) \implies \mathrm{HasValidColoring}(n, k)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Color Lower Bound** | `Erdos298.minColors_gt_of_not_hasValidColoring` | Non-existence of valid $k$-coloring implies $f(n) > k$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Color Lower Bound** | `Erdos298.minColors_ge_of_not_hasValidColoring` | Non-existence of valid $k$-coloring implies $f(n) \ge k + 1$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Fiber Partition** | `Erdos298.monochromatic_fiber_sum_eq` | Exact partition identity $\sum_{i < k} \|S \cap c^{-1}(i)\| = \|S\|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Fiber Pigeonhole** | `Erdos298.exists_monochromatic_fiber_strict` | Strict monochromatic pigeonhole: $\|S\| > k M \implies \exists i, \|S \cap c^{-1}(i)\| > M$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: AP & Subset Sums** | `Erdos298.not_avoids_of_arithProg_subset` | $\mathrm{arithProg}(a, d, L) \subseteq \Sigma(A) \wedge n \in \mathrm{arithProg}(a, d, L) \implies \neg \mathrm{AvoidsSubsetSum}(A, n)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: AP to Dense Hitting**| `Erdos298.denseSubsetSumHitting_of_ap` | Bridge theorem: $\mathrm{APDenseSubsetSumWitness} \implies \mathrm{DenseSubsetSumHitting}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Dense Avoidance Fails**| `Erdos298.not_avoidsMonoSubsetSum_of_dense`| Dense hitting implies any $k$-coloring fails monochromatic avoidance | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Dense Hitting Bound**| `Erdos298.not_hasValidColoring_of_dense` | Dense hitting implies $\neg \mathrm{HasValidColoring}(n, k)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Strict Lower Bound** | `Erdos298.minColors_gt_of_dense` | $f(n) > k$ under dense hitting witness | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lower Bound** | `Erdos298.minColors_ge_of_dense` | $f(n) \ge k + 1$ under dense hitting witness | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Lower Bound** | `Erdos298.minColors_ge_of_cfp_witness` | General Conlon–Fox–Pham lower bound theorem $f(n) \ge k + 1$ from `CFPLowerBoundWitness` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP AP Lower Bound** | `Erdos298.minColors_ge_of_cfp_ap_witness` | Arithmetic progression form of lower bound theorem from `CFPAPWitness` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Asymptotic Lower Bound**| `Erdos298.hasChromaticLowerBound_of_cfp_witnesses`| Deduction of global asymptotic lower bound $\mathrm{HasChromaticLowerBound}(F, c)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Concrete Witness** | `Erdos298.cfpWitness_two` | Explicit unconditional witness for $k = 1$ on $\{1, n-1\}$ for all $n \ge 3$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Recovered Lower Bound**| `Erdos298.minColors_ge_two_via_cfp` | Unconditional $f(n) \ge 2$ derived via general CFP witness framework | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lemma A (Disjoint Addition)** | `Erdos298.subsetSums_add_of_disjoint` | For disjoint $A, B$, $\Sigma(A) + \Sigma(B) \subseteq \Sigma(A \cup B)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lemma B (Single Extend)** | `Erdos298.subsetSums_interval_extend_single` | $[a, b] \subseteq \Sigma(A) \wedge t \le b - a + 1 \implies [a, b + t] \subseteq \Sigma(A \cup \{t\})$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lemma B (Inductive Extend)** | `Erdos298.subsetSums_interval_extend` | $\forall t \in B, t \le b - a + 1 \implies [a, b + \sum B] \subseteq \Sigma(A \cup B)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lemma C (Scale Subset Sums)** | `Erdos298.subsetSums_scale` | $v \cdot Q \subseteq A \implies v \cdot \Sigma(Q) \subseteq \Sigma(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Lemma C (Divisor Hitting)** | `Erdos298.mem_subsetSums_of_scaled` | $v \mid n \wedge (n/v) \in \Sigma(Q) \wedge v \cdot Q \subseteq A \implies n \in \Sigma(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Canonical Scale** | `Erdos298.cfpScale` | Real-valued canonical growth scale $F(n) = \frac{n^{1/3}(n/\varphi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Scale Positivity** | `Erdos298.cfpScale_pos_of_hyp` | Positivity of $\mathrm{cfpScale}(n)$ for $\log n > 1$ and $\varphi(n) > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Continuous Interval Sums** | Erdos298.subsetSums_Icc_zero | $[0, m(m+1)/2] \subseteq \Sigma(\{1, \dots, m\})$ continuous subset sum coverage | **Proven & Compiled** | [propext, Classical.choice, Quot.sound] |
| **Phase 3: Consecutive Hitting** | Erdos298.mem_subsetSums_Icc_of_le |  \le m(m+1)/2 \implies n \in \Sigma(\{1, \dots, m\})$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound] |
| **Phase 3: Scaled Consecutive Hitting** | Erdos298.mem_subsetSums_scaled_Icc_of_le |  \mid n \wedge (n/v) \le m(m+1)/2 \implies n \in \Sigma(v \cdot \{1, \dots, m\})$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound] |
| **Phase 3: CFP Key Subset Inclusion** | Erdos298.cfpLowerBoundSet_subset |  \cdot m < n \wedge 0 < v \implies v \cdot \{1, \dots, m\} \subseteq \{1, \dots, n-1\}$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound] |
| **Phase 3: CFP Key Subset Cardinality**| Erdos298.cfpLowerBoundSet_card | $|v \cdot \{1, \dots, m\}| = m$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Key Subset Hitting** | Erdos298.mem_subsetSums_cfpLowerBoundSet |  \mid n \wedge (n/v) \le m(m+1)/2 \implies n \in \Sigma(\mathrm{cfpLowerBoundSet}(v, m))$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound]` |
| **Phase 3: Scaled CFP Witness** | Erdos298.cfpWitness_scaled | Instantiation of CFPLowerBoundWitness n 1 on scaled progression  \cdot \{1, \dots, m\}$ | **Proven & Compiled** | [propext, Classical.choice, Quot.sound]` |
| **Phase 3: Scaled Lower Bound** | Erdos298.minColors_ge_two_via_cfp_scaled | (n) \ge 2$ via scaled arithmetic progression witness | **Proven & Compiled** | [propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diversity Monotonicity** | Erdos298.isDiverse_of_le |  \le k_2 \wedge \mathrm{IsDiverse}(X, k_2) \implies \mathrm{IsDiverse}(X, k_1)$ | **Proven & Compiled** | [propext, Quot.sound] |
| **Phase 3: CFP §5.1 Diversity Monotonicity** | Erdos298.isDiverse_of_subset |  \subseteq Y \wedge \mathrm{IsDiverse}(X, k) \implies \mathrm{IsDiverse}(Y, k)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Quotient Scaling Subset** | Erdos298.quotient_scale_subset |  \cdot ((A \cap v\mathbb{N}) / v) \subseteq A$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Quotient Divisor Hitting** | Erdos298.mem_subsetSums_of_quotient_hit |  \mid n \wedge (n/v) \in \Sigma((A \cap v\mathbb{N}) / v) \implies n \in \Sigma(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Quotient Interval Hitting** | Erdos298.mem_subsetSums_of_quotient_Icc_subset | $\{1, \dots, m\} \subseteq Q \wedge n/v \le m(m+1)/2 \implies n/v \in \Sigma(Q)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: Scaled Interval Hitting** | Erdos298.mem_subsetSums_of_scaled_Icc_subset | $\{1, \dots, m\} \subseteq (A \cap v\mathbb{N})/v \wedge n/v \le m(m+1)/2 \implies n \in \Sigma(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP Diverse Witness Structure** | Erdos298.CFPDiverseWitness | Exact CFP §5.1 witness structure over diverse quotient subset sums | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Chromatic Lower Bound** | `Erdos298.minColors_ge_of_cfp_diverse_witness` | $k + 1 \le f(n)$ from any `CFPDiverseWitness n k` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Non-diversity Characterization** | `Erdos298.not_isDiverse_iff` | $\neg \mathrm{IsDiverse}(A, t) \iff \exists d \ge 2, |A \setminus d\mathbb{N}| < t$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Partition Bound** | `Erdos298.card_le_card_filter_dvd_add` | $|A \setminus d\mathbb{N}| < t \implies |A| \le |A \cap d\mathbb{N}| + (t - 1)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Division Cardinality** | `Erdos298.card_image_div_eq_card_filter_dvd` | Injective division on multiples: $|(A \cap d\mathbb{N})/d| = |A \cap d\mathbb{N}|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Step Bounds Preservation** | `Erdos298.div_step_bounds` | $A \subseteq [1, B] \implies (A \cap d\mathbb{N})/d \subseteq [1, \lfloor B/d \rfloor]$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Divisor Extraction Iteration** | `Erdos298.exists_diverse_scaled_subset` | CFP §5.1 Divisor-extraction iteration theorem: $\exists v > 0, Q \subseteq \mathbb{N}$ non-empty, $v \cdot Q \subseteq A$, $Q$ is $t$-diverse, and $|A| \le |Q| + (t - 1) L$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scale Factor Bound** | `Erdos298.scale_factor_le_of_mem_bounds` | $Q \neq \emptyset \wedge \forall x \in Q, 1 \le x \wedge v \cdot x \le B \implies v \le B$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Modular Coverage** | `Erdos298.subsetSumsMod_eq_univ_of_divisor_counts` | CFP Lemma 5.8: $(\forall e \mid d, e - 1 \le |A \setminus e\mathbb{N}|) \implies \Sigma_d(A) = \mathbb{Z}/d\mathbb{Z}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Modular Coverage** | `Erdos298.subsetSumsMod_eq_univ_of_isDiverse` | Diverse modular coverage: $\mathrm{IsDiverse}(A, t) \wedge d - 1 \le t \implies \Sigma_d(A) = \mathbb{Z}/d\mathbb{Z}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Extracted Diverse Coverage** | `Erdos298.exists_diverse_scaled_subset_mod_coverage` | Extracted $Q$ satisfies $\forall 1 \le d \le t + 1, \Sigma_d(Q) = \mathbb{Z}/d\mathbb{Z}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Test Example 1** | `Erdos298.sanity_mod_coverage_empty` | Modulo 1 coverage: $\forall r \in \mathbb{Z}/1\mathbb{Z}, r \in \Sigma_1(\emptyset)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Test Example 2** | `Erdos298.sanity_mod_coverage_4` | Modulo 4 coverage: $\forall r \in \mathbb{Z}/4\mathbb{Z}, r \in \Sigma_4(\{1, 5, 9\})$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Test Example 3** | `Erdos298.sanity_mod_coverage_6` | Modulo 6 coverage: $\forall r \in \mathbb{Z}/6\mathbb{Z}, r \in \Sigma_6(\{2, 3, 4, 8, 9\})$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Residue Fiber Bound** | `Erdos298.card_subsetSumsMod_dvd_le_fiber` | CFP Lemma 5.11 Fiber Bound: $F_r \ne \emptyset \implies |\Sigma_N(A \cap d\mathbb{N})| \le |F_r|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Modulo Projection** | `Erdos298.subsetSumsMod_image_zmodProj` | Projection image identity: $\pi(\Sigma_N(A)) = \Sigma_d(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fiber Product Bound** | `Erdos298.card_subsetSumsMod_dvd_mul_card_le` | CFP Lemma 5.11: $|\Sigma_d(A)| \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Product Bound** | `Erdos298.card_mul_card_subsetSumsMod_dvd_le_of_isDiverse` | Diverse product lower bound: $d \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fiber Test Example 1** | `Erdos298.sanity_fiber_example_12` | Fiber test ($N=12, d=3, A=\{1,3,6\}$): $|\Sigma_{12}(D)|=4, |F_0|=4, |F_1|=4, |F_2|=0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fiber Test Example 2** | `Erdos298.sanity_fiber_example_6` | Fiber test ($N=6, d=2, A=\{1,7,2\}$): unequal fibers $|F_0|=3, |F_1|=2$, product $2 \cdot 2 \le 5$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Growth Subadditivity** | `Erdos298.delta_add_le` | Subadditivity of translation growth: $\delta(S, x + y) \le \delta(S, x) + \delta(S, y)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 List Sumset Growth** | `Erdos298.delta_sum_le_sum_delta` | CFP Lemma 2.7: $\delta(S, \sum xs) \le \sum \delta(S, x_i)$ for lists | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Uniform Growth Bound** | `Erdos298.delta_sum_le_mul_of_forall_le` | CFP Lemma 2.7 uniform threshold: $\forall x \in xs, \delta(S, x) \le D \implies \delta(S, \sum xs) \le |xs| \cdot D$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Real Growth Bound** | `Erdos298.delta_sum_le_mul_of_forall_le_real` | CFP Lemma 2.7 real threshold: $(\delta(S, \sum xs) : \mathbb{R}) \le |xs| \cdot D$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Double Counting** | `Erdos298.sum_interCard_eq_sq` | Double counting identity: $\sum_{x \in G} |(S + x) \cap S| = |S|^2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Small Growth Bound** | `Erdos298.card_smallGrowth_mul_le` | CFP Lemma 2.6 division-free bound: $|G| \cdot (|S| - D) \le |S|^2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Small Growth Div** | `Erdos298.card_smallGrowth_le_div` | CFP Lemma 2.6 natural division bound: $|G| \le |S|^2 / (|S| - D)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Real Small Growth** | `Erdos298.card_smallGrowthR_mul_le` | CFP Lemma 2.6 real division-free bound: $|G| \cdot (|S| - D) \le |S|^2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Real Small Growth Div** | `Erdos298.card_smallGrowthR_le_div` | CFP Lemma 2.6 real division bound: $|G| \le |S|^2 / (|S| - D)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Large Growth Selection** | `Erdos298.exists_mem_large_growth` | Selection of $a \in T$ with $\delta(S, a) > D$ whenever $|T| > |G|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Real Growth Selection** | `Erdos298.exists_mem_large_growth_real` | Real selection: $a \in T$ with $(\delta(S, a) : \mathbb{R}) > D$ when $|T| > |G|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 SubsetSum Mod Insert** | `Erdos298.card_subsetSumsMod_insert_eq` | Insertion identity: $|\Sigma_d(A \cup \{x\})| = |\Sigma_d(A)| + \delta(\Sigma_d(A), x)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Interval Modulo Inj** | `Erdos298.natCast_zmod_injOn_Ico` | Modulo injectivity on intervals: $\forall x \in A, y \le x < y + d \implies \text{InjOn } (\cdot \pmod d) \; A$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Interval Modulo Card** | `Erdos298.card_image_natCast_zmod_of_Ico` | Cardinality preservation: $|A \pmod d| = |A|$ on intervals of length $\le d$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Kneser Arith Bridge** | `Erdos298.cochrane_ostergaard_spencer_arith_le` | Cochrane–Ostergaard–Spencer inequality: $(k + 1) q \le 2(k(q - 1) + 1)$ for $k \ge 1, q \ge 2$ | **Proven & Compiled** | `[propext, Quot.sound]` |
| **Phase 3: CFP §2.1 Kneser Growth Bound** | `Erdos298.iterSum_growth_bound_of_kneser_data` | Deduced bound: $(k + 1) |T| \le 2 |kT|$ from Kneser bounds | **Proven & Compiled** | `[propext, Quot.sound]` |
| **Phase 3: CFP §2.1 Lemma 2.3 Interface** | `Erdos298.iterSum_card_ge_of_kneser_hyp` | Conditional growth interface: $\min(2|G|, (k+1)|T|) \le 2|kT|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §2.1 Lemma 2.3 Real** | `Erdos298.iterSum_card_ge_of_kneser_hyp_real` | Real-valued growth interface: $\min(|G|, (k+1)|T|/2) \le |kT|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Pos** | `Erdos298.subgroupIndex_pos` | Strict positivity $g > 0$ of subgroup index $g = \gcd(t, \gcd(B))$ for $t > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Dvd** | `Erdos298.subgroupIndex_dvd_modulus` | Divisibility $g \mid t$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Dvd Mem**| `Erdos298.subgroupIndex_dvd_mem` | Divisibility $\forall a \in B, g \mid a$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Mono** | `Erdos298.subgroupIndex_mono` | Monotonicity: $B' \subseteq B \implies g(B) \mid g(B')$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Double**| `Erdos298.subgroupIndex_doubles_of_lt` | Doubling under strict increase: $g(B) < g(B') \implies 2 g(B) \le g(B')$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Bnd Mem**| `Erdos298.subgroupIndex_le_of_mem` | Bound by elements: $a \in B \wedge a > 0 \implies g \le a$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Subgroup Index Bnd Mod**| `Erdos298.subgroupIndex_le_modulus` | Bound by modulus: $t > 0 \implies g \le t$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scaled Coprimality** | `Erdos298.subgroupIndex_scaled_coprime` | Generation of $\mathbb{Z}/(t/g)\mathbb{Z}$: $\gcd(t/g, \gcd(B/g)) = 1$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scaled Modulo Inj** | `Erdos298.natCast_zmod_div_injOn_Ico` | Scaled injectivity on interval of length $\le t/g$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scaled Modulo Card** | `Erdos298.card_image_natCast_zmod_div_of_Ico` | Cardinality preservation under scaled modulo projection | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fiber Sum Identity** | `Erdos298.card_eq_sum_image_fibers` | Fiber partition cardinality: $|S| = \sum_{r \in \pi(S)} |F_r|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fiber Growth Bound** | `Erdos298.delta_fiber_le_delta` | Single fiber growth bound: $\delta(F_r, x) \le \delta(S, x)$ when $\pi(x) = 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Centered Fiber Card** | `Erdos298.card_centerFiber` | Fiber centering bijection: $|F_r - x_0| = |F_r|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Centered Fiber Ker** | `Erdos298.centerFiber_subset_kernel` | Centered fiber elements lie in kernel: $\pi(y) = 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Centered Fiber Delta**| `Erdos298.delta_centerFiber_eq` | Invariance of translation growth under centering: $\delta(F_r - x_0, x) = \delta(F_r, x)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 IntAP Cardinality** | `Erdos298.IntAP.card_toFinset` | Exact progression cardinality: $|P| = k$ for step $b > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Coset AP Lift Card** | `Erdos298.cosetAPLift_card` | Cardinality of lifted coset AP equals subgroup order $h$ ($h \mid N$) | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Coset Family Sum** | `Erdos298.coset_family_length_sum_eq` | Length sum identity $\sum_i |P_i| = q \cdot h$ for $q$ lifted coset APs | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Coset Family Budget** | `Erdos298.coset_family_length_sum_le_three_mul` | Length sum budget bound $q \cdot h \le 3 |R|$ for coset partition | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Numerical Interface** | `Erdos298.FiniteConditions` | Interface isolating 10 parameters and numerical hypotheses for Lemma 5.6 | **Formalized & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy State Capacity** | `Erdos298.GreedyState.card_B` | Remaining candidate set cardinality $|B| = |A| - |E|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy State Lower Bnd**| `Erdos298.GreedyState.B_card_ge` | Strict capacity lower bound $|B| \ge M$ for step count $j \le K$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy State Nonempty** | `Erdos298.GreedyState.B_nonempty` | Non-emptiness $B \ne \emptyset$ for $j \le K$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy Element Exists** | `Erdos298.exists_greedy_element` | Existence of greedy element $a \in B$ maximizing $\delta(S, a)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy Next State Card**| `Erdos298.nextState_card` | State transition cardinality increment $|E'| = |E| + 1$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy Next State Mono**| `Erdos298.nextState_S_mono` | Monotonicity of subset sums: $S \subseteq S'$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy Next State Dvd** | `Erdos298.nextState_g_dvd` | Divisibility invariant: $g(B) \mid g(B')$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Compl Dvd Modular Sum** | `Erdos298.subsetSumsMod_eq_of_compl_dvd` | Subset sum equality $\Sigma_d(E) = \Sigma_d(A)$ when all elements in $A \setminus E$ are divisible by $d$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Fibers Lower Bound** | `Erdos298.card_ge_of_fibers_ge` | Cardinality bound $|S| \ge g \cdot \text{bound}$ when $\pi(S) = \mathbb{Z}/g\mathbb{Z}$ and all fibers have size $\ge \text{bound}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Mul Div Cancel Pos** | `Erdos298.mul_div_cancel_of_pos` | Density cancellation $g \cdot (\xi \cdot t / g) = \xi \cdot t$ for $g > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Saturated Branch Density**| `Erdos298.card_subsetSumsMod_ge_of_saturated` | CFP Lemma 5.6 Saturated Branch Theorem: saturated state at step $j \le K$ implies $|\Sigma_t(A)| \ge \xi \cdot t$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Double Counting Half** | `Erdos298.card_smallGrowth_half_le` | Double counting bound $|G_{s/2}| \le 2s$ for growth threshold $D = s/2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Claim 1 Range 1** | `Erdos298.exists_large_growth_of_two_mul_lt` | Range 1 single-step growth: $2|S| < |T| \implies \exists x \in T, \delta(S, x) > |S|/2$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Floor Mul Succ Gt** | `Erdos298.floor_mul_succ_gt` | Floor arithmetic property $4s < (\lfloor 4s/b \rfloor + 1) b$ for $b > 0$ | **Proven & Compiled** | `[propext, Quot.sound]` |
| **Phase 3: CFP §5.1 Claim 1 Range 2** | `Erdos298.range2_arith_contradiction` | Range 2 arithmetic contradiction: $(q + 1) b \le 4s \wedge 4s < (q + 1) b \implies \text{False}$ | **Proven & Compiled** | `[propext, Quot.sound]` |
| **Phase 3: CFP §5.1 State Sequence Card** | `Erdos298.card_greedySeq_E` | State sequence capacity formula $|st_j.E| = j$ for all $j \le K$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 State Sequence Subset** | `Erdos298.greedySeq_S_subset` | State sequence subset sum inclusion $\Sigma_t(st_j.E) \subseteq \Sigma_t(A)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Step Increment Formula** | `Erdos298.card_greedySeq_S_succ` | State sequence step increment identity $|st_{j+1}.S| = |st_j.S| + \delta_j$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Telescoping Sum Bound** | `Erdos298.sum_delta_le_card_final` | Telescoping sum bound $\sum_{j < K} \delta_j \le |st_K.S|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Master Telescoping** | `Erdos298.sum_delta_le_total` | Master telescoping bound $\sum_{j < K} \delta_j \le |\Sigma_t(A)|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Step Disjointness** | `Erdos298.disjoint_growth_unsaturated` | Disjointness of growth and unsaturated steps | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 3-Way Step Partition** | `Erdos298.steps_partition` | 3-way partition of each step $j < K$ into saturated, growth, or unsaturated | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Unsaturated Count Bound**| `Erdos298.card_unsaturatedSteps_ge` | Lower bound $|U| \ge K - B_{growth}$ when saturated steps are empty | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Combinatorial Core F1**| `Erdos298.cfp_lemma_5_6_finite_core` | CFP Lemma 5.6 Combinatorial Core F1 Master Theorem: $\min(\xi, 32 / \ell) \cdot t \le |\Sigma_t(A)|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Concrete Realization** | `Erdos298.concreteFiniteConditions` | Constructive realization of `FiniteConditions` with concrete numbers ($t=20, A=\{1,3,7\}, \dots$) | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Non-Vacuity Theorem** | `Erdos298.finiteConditions_realizable` | Machine-checked non-vacuity theorem: `Nonempty FiniteConditions` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Primorial Product** | `Erdos298.primorialProd` | Primorial product $W(P) = \prod_{p \in P} p$ | **Proven & Compiled** | `[propext, Quot.sound]` |
| **Phase 3: CFP §5.1 CFP Tau Ratio** | `Erdos298.cfpTau` | Canonical CFP ratio $\tau(W, m) = \varphi(W \cdot m) / (W \cdot m)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 CFP Tau Positivity** | `Erdos298.cfpTau_pos` | Strict positivity $0 < \tau(W, m)$ when $W > 0, m > 0$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scaled Candidate Map** | `Erdos298.mem_Y_of_mem_Y_v` | Scaling injection bridge: $a \in Y_v \implies v \cdot a \in Y$ | **Proven & Compiled** | `[propext]` |
| **Phase 3: CFP §5.1 Arithmetic Adapter** | `Erdos298.CFPArithParams.toFiniteConditions` | Canonical mapping from arithmetic parameters to `FiniteConditions` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Lemma 5.6 (m = n)** | `Erdos298.cfp_lemma_5_6_m_eq_n` | Master specialization of CFP Lemma 5.6 for $m = n$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Density Bound** | `Erdos298.chromatic_lower_bound_of_diverse_density` | Bridge connecting modular density to chromatic lower bound $k + 1 \le f(n)$ via `CFPDiverseWitness` | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Filter Diff Subset** | `Erdos298.filter_not_dvd_sdiff_subset` | Filter difference containment: $((A \setminus v\mathbb{N}) \setminus (B \setminus v\mathbb{N})) \subseteq A \setminus B$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Filter Loss Bound** | `Erdos298.card_filter_not_dvd_le_card_add_sdiff` | Bound on non-divisible element loss: $|(A \setminus v\mathbb{N})| \le |(B \setminus v\mathbb{N})| + |A \setminus B|$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Loss Preservation**| `Erdos298.isDiverse_subset_of_card_diff_le` | Deterministic diversity preservation: $|A| - |B| \le k - k' \implies \mathrm{IsDiverse}(B, k')$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Sdiff Singleton Diverse** | `Erdos298.isDiverse_sdiff_singleton` | Single element removal preserves $(k - 1)$-diversity | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Sdiff Finset Diverse** | `Erdos298.isDiverse_sdiff_finset` | Finset removal of size $r \le k$ preserves $(k - r)$-diversity | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Greedy State B Diverse** | `Erdos298.GreedyState.isDiverse_B` | Greedy remaining candidates $st.B$ retain $(k_{div} - |E|)$-diversity | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Exists Diverse Subset** | `Erdos298.exists_diverse_subset_of_card_eq` | Existence of diverse subset of prescribed size $s$ with controlled loss | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Lemma 5.4 Statement** | `Erdos298.CFPLemma54Statement` | Formal mathematical specification of CFP Lemma 5.4 subsampling interface | **Formalized & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Lemma 5.4 Deterministic**| `Erdos298.cfp_lemma_5_4_of_deterministic` | Deterministic realization of CFP Lemma 5.4 under controlled loss | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse GCD Bound** | `Erdos298.isDiverse_gcd_le_one` | Divisor bound $\gcd(A) \le 1$ for any $k$-diverse set ($k \ge 1$) | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse GCD Identity** | `Erdos298.isDiverse_gcd_eq_one` | Exact gcd identity $\gcd(A) = 1$ when $A$ has a positive element | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Subgroup Index**| `Erdos298.subgroupIndex_eq_one_of_isDiverse` | Subgroup index vanishing: $\mathrm{subgroupIndex}(t, B) = 1$ for diverse $B$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Disjoint Diverse Subsets**| `Erdos298.exists_disjoint_diverse_subsets` | Two-stage disjoint extraction of independent diverse subsets $A_1, A_2 \subseteq A$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Scaled Diverse Pipeline** | `Erdos298.exists_scaled_diverse_candidate` | End-to-end algorithmic divisor extraction + subsampling pipeline | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Candidate Adapter**| `Erdos298.diverse_candidate_satisfies_finiteConditions` | Structural adapter verifying `FiniteConditions` diversity and capacity | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Lemma 5.4 Full Statement**| `Erdos298.CFPLemma54FullStatement` | Formal specification of CFP Lemma 5.4 with range bound $N$ | **Formalized & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Lemma 5.4 Full Realized** | `Erdos298.cfp_lemma_5_4_full_of_deterministic` | Realization of full Lemma 5.4 under deterministic loss budget | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Subsets Finset** | `Erdos298.CFPLemma54Subsets` | Finset of size-$s$ subsets retaining $k'$-diversity | **Formalized & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Universal Diverse Density**| `Erdos298.cfp_lemma_5_4_all_subsets_diverse` | Universal diversity theorem: 100% of size-$s$ subsets are $k'$-diverse | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Phase 3: CFP §5.1 Diverse Subsets Choose** | `Erdos298.card_CFPLemma54Subsets_eq` | Combinatorial cardinality $\binom{|A|}{s}$ of diverse subsamples | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |

| **Final Master Theorem** | `Erdos298.erdos_problem_360_finite_master` | Exact two-sided sandwich: $k + 1 \le f(n) \le \text{CFP 4-layer bound}$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Final Master Theorem** | `Erdos298.erdos_problem_360_unconditional_master` | Unconditional two-sided bound: $2 \le f(n) \le \text{CFP 4-layer bound}$ for all $n \ge 3$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Final Master Theorem** | `Erdos298.erdos_problem_360_asymptotic_master` | Sharp asymptotic two-sided equivalence $c F(n) \le f(n) \le C F(n)$ | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |
| **Final Master Theorem** | `Erdos298.erdos_problem_360_unified_solution` | Grand synthesis unifying all 3 historical generations of Erdős Problem 360 | **Proven & Compiled** | `[propext, Classical.choice, Quot.sound]` |

---

## 2. Dependency Audit and Formalization Status for 2021 Conlon–Fox–Pham Lower Bound (Section 5.1)

A rigorous audit of the mathematical dependencies required for the 2021 lower bound ($f(n) \ge c F(n)$) against Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`:

1. **Arithmetic Progressions in Dense Subset Sums (Szemerédi–Vu / Sárközy Theorems)**:
   - *Requirement*: If $A \subseteq [1, M]$ has density $\alpha$, then its subset sums $\Sigma(A)$ contain a long arithmetic progression of length $L$ and step $d$.
   - *Mathlib Status*: **Not yet in Mathlib**. Mathlib formalizes Roth's theorem (`Mathlib.Combinatorics.Additive.Roth`), but does not contain Sárközy's or Szemerédi–Vu's theorems on subset sums.
2. **Distribution of Primes in Arithmetic Progressions**:
   - *Requirement*: Quantitative bounds for $\pi(x; q, a)$ or Siegel–Walfisz theorem to guarantee prime existence in specified residue classes.
   - *Mathlib Status*: **Not yet in Mathlib**. Mathlib has Dirichlet's theorem on the infinitude of primes in arithmetic progressions (`Mathlib.NumberTheory.DirichletTheorem`), but not the quantitative effective/asymptotic forms.
3. **Mertens' Product Theorems**:
   - *Requirement*: $\prod_{p \le x} (1 - 1/p) \sim e^{-\gamma} / \log x$ and bounds on $\prod_{p \mid n} (1 - 1/p)^{-1} = n / \varphi(n)$.
   - *Mathlib Status*: **Not yet in Mathlib**. Mathlib contains basic Euler totient properties (`Nat.totient`) and elementary prime factor relations, but lacks Mertens' third theorem.
4. **Resolution in Section 8 Formalization**:
   - The entire combinatorial reduction and lower bound infrastructure is **fully formalized, compiled, and kernel-checked with zero sorry and strictly standard axioms**:
     - Monotone coloring lifting: `Erdos298.hasValidColoring_of_le`.
     - Contrapositive chromatic lower bound: `Erdos298.minColors_gt_of_not_hasValidColoring`, `Erdos298.minColors_ge_of_not_hasValidColoring`.
     - Combinatorial fiber pigeonhole principle: `Erdos298.monochromatic_fiber_sum_eq`, `Erdos298.exists_monochromatic_fiber_strict`.
     - Subset sums and arithmetic progressions: `Erdos298.subsetSums`, `Erdos298.arithProg`, `Erdos298.not_avoids_of_arithProg_subset`.
     - Dense subset hitting and Szemerédi–Vu bridge: `Erdos298.denseSubsetSumHitting_of_ap`, `Erdos298.not_avoidsMonoSubsetSum_of_dense`, `Erdos298.minColors_ge_of_dense`.
     - Complete Conlon–Fox–Pham witness structures and theorems: `Erdos298.CFPLowerBoundWitness`, `Erdos298.CFPAPWitness`, `Erdos298.minColors_ge_of_cfp_witness`, `Erdos298.minColors_ge_of_cfp_ap_witness`.
     - Asymptotic deduction: `Erdos298.hasChromaticLowerBound_of_cfp_witnesses`.
     - Unconditional specialization: `Erdos298.cfpWitness_two`, `Erdos298.minColors_ge_two_via_cfp`.
     - CFP §5.1 Diverse Witness framework: `Erdos298.IsDiverse`, `Erdos298.CFPDiverseWitness`, `Erdos298.CFPLowerBoundWitness.ofDiverse`, `Erdos298.minColors_ge_of_cfp_diverse_witness`.
     - CFP §5.1 Divisor-Extraction Iteration Engine:
       - Non-diversity characterization: `Erdos298.not_isDiverse_iff`.
       - Partition bound: `Erdos298.card_le_card_filter_dvd_add`.
       - Division injectivity on multiples: `Erdos298.card_image_div_eq_card_filter_dvd`.
       - Step bounds preservation: `Erdos298.div_step_bounds`.
       - Algorithmic divisor-extraction iteration: `Erdos298.exists_diverse_scaled_subset` (mathematical induction on $L$ extracting $v > 0$ and $t$-diverse $Q \subseteq \mathbb{N}$ with $v \cdot Q \subseteq A$, $1 \le x \wedge v \cdot x \le B$, and $|A| \le |Q| + (t - 1) L$).
       - Extracted factor upper bound: `Erdos298.scale_factor_le_of_mem_bounds` ($v \le B$).
     - CFP §5.1 Modular Subset Sum Coverage (Lemma 5.8):
       - Divisor-count condition: `Erdos298.subsetSumsMod_eq_univ_of_divisor_counts` ($(\forall e \mid d, e - 1 \le |A \setminus e\mathbb{N}|) \implies \Sigma_d(A) = \mathbb{Z}/d\mathbb{Z}$).
       - Diverse modular coverage: `Erdos298.subsetSumsMod_eq_univ_of_isDiverse` ($\mathrm{IsDiverse}(A, t) \wedge d - 1 \le t \implies \Sigma_d(A) = \mathbb{Z}/d\mathbb{Z}$).
       - Extracted diverse coverage: `Erdos298.exists_diverse_scaled_subset_mod_coverage`.
     - CFP §5.1 Test Example 1: `Erdos298.sanity_mod_coverage_empty` (Modulo 1 coverage: $\forall r \in \mathbb{Z}/1\mathbb{Z}, r \in \Sigma_1(\emptyset)$).
     - CFP §5.1 Test Example 2: `Erdos298.sanity_mod_coverage_4` (Modulo 4 coverage: $\forall r \in \mathbb{Z}/4\mathbb{Z}, r \in \Sigma_4(\{1, 5, 9\})$).
     - CFP §5.1 Test Example 3: `Erdos298.sanity_mod_coverage_6` (Modulo 6 coverage: $\forall r \in \mathbb{Z}/6\mathbb{Z}, r \in \Sigma_6(\{2, 3, 4, 8, 9\})$).
     - Extracted diverse coverage: `Erdos298.exists_diverse_scaled_subset_mod_coverage`.
     - CFP §5.1 Fiber Lower Bound and Product Bound (Lemma 5.11):
       - Natural projection ring hom: `Erdos298.zmodProj` ($\pi : \mathbb{Z}/N\mathbb{Z} \to \mathbb{Z}/d\mathbb{Z}$ for $d \mid N$).
       - Residue fiber: `Erdos298.residueFiber` ($F_r = \{s \in \Sigma_N(A) \mid \pi(s) = r\}$).
       - Fiber lower bound (Lemma 5.11): `Erdos298.card_subsetSumsMod_dvd_le_fiber` ($F_r \ne \emptyset \implies |\Sigma_N(A \cap d\mathbb{N})| \le |F_r|$ via decomposition $B = U \uplus V$, base representative $x = \sum U$ with $\pi(x) = r$, and injective translation $y \mapsto x + y$).
       - Projection image: `Erdos298.subsetSumsMod_image_zmodProj` ($\pi(\Sigma_N(A)) = \Sigma_d(A)$).
       - Fiber product lower bound (Lemma 5.11): `Erdos298.card_subsetSumsMod_dvd_mul_card_le` ($|\Sigma_d(A)| \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$ via fiber partition $\sum_{r \in \Sigma_d(A)} |F_r| = |\Sigma_N(A)|$).
       - Diverse product lower bound: `Erdos298.card_mul_card_subsetSumsMod_dvd_le_of_isDiverse` ($d \cdot |\Sigma_N(A \cap d\mathbb{N})| \le |\Sigma_N(A)|$ when $\mathrm{IsDiverse}(A, t)$ and $d - 1 \le t$).
      - CFP §2.1 Translation Growth API & Lemma 2.7 (P01):
        - Definitions: `Erdos298.translate`, `Erdos298.delta`, `Erdos298.smallGrowth`, `Erdos298.smallGrowthR`.
        - Properties: `Erdos298.card_translate`, `Erdos298.translate_zero`, `Erdos298.translate_add`, `Erdos298.delta_zero`, `Erdos298.card_union_translate`.
        - Set inclusion: `Erdos298.translate_sdiff_subset_union`.
        - Subadditivity: `Erdos298.delta_add_le` ($\delta(S, x + y) \le \delta(S, x) + \delta(S, y)$).
        - Sumset list growth (CFP Lemma 2.7): `Erdos298.delta_sum_le_sum_delta`, `Erdos298.delta_sum_le_mul_of_forall_le`, `Erdos298.delta_sum_le_mul_of_forall_le_real`.
      - CFP §2.1 Double Counting & Lemma 2.6 (P02):
        - Intersection cardinality: `Erdos298.interCard`, `Erdos298.interCard_add_delta`.
        - Difference fiber bijection: `Erdos298.card_fiber_sub_eq_interCard`.
        - Double counting identity: `Erdos298.sum_interCard_eq_sq` ($\sum_{x \in G} |(S + x) \cap S| = |S|^2$).
        - Small growth bounds (CFP Lemma 2.6): `Erdos298.card_smallGrowth_mul_le` ($|G| \cdot (|S| - D) \le |S|^2$), `Erdos298.card_smallGrowth_le_div` ($|G| \le |S|^2 / (|S| - D)$), real versions `Erdos298.card_smallGrowthR_mul_le`, `Erdos298.card_smallGrowthR_le_div`.
        - Large growth element selection: `Erdos298.exists_mem_large_growth`, `Erdos298.exists_mem_large_growth_real`.
        - Subset sum incremental formula: `Erdos298.card_subsetSumsMod_insert_eq` ($|\Sigma_d(A \cup \{x\})| = |\Sigma_d(A)| + \delta(\Sigma_d(A), x)$).
        - Modulo injectivity and cardinality preservation on bounded intervals: `Erdos298.natCast_zmod_injOn_Ico`, `Erdos298.card_image_natCast_zmod_of_Ico`.
      - CFP §2.1 Iterated Sumsets & Kneser Bridge (P03):
        - Definitions: `Erdos298.sumset` ($A + B = \{a + b \mid a \in A, b \in B\}$), `Erdos298.iterSum` ($k T$), `Erdos298.stab` ($\mathrm{Stab}(S) = \{x \mid \delta(S, x) = 0\}$).
        - Algebraic properties: `Erdos298.iterSum_zero`, `Erdos298.iterSum_succ`, `Erdos298.mem_sumset_iff`, `Erdos298.sumset_assoc`, `Erdos298.sumset_zero_left`, `Erdos298.sumset_zero_right`, `Erdos298.iterSum_add` ($(a + b) T = a T + b T$).
        - Monotonicity: `Erdos298.iterSum_subset_succ` ($0 \in T \implies k T \subseteq (k + 1) T$), `Erdos298.iterSum_mono_of_zero_mem` ($k_1 \le k_2 \wedge 0 \in T \implies k_1 T \subseteq k_2 T$).
        - Small growth preservation: `Erdos298.iterSum_smallGrowth_subset` ($k(G_D) \subseteq G_{k D}$).
        - Cochrane–Ostergaard–Spencer algebraic lemma: `Erdos298.cochrane_ostergaard_spencer_arith_le` ($(k + 1) q \le 2(k(q - 1) + 1)$ for $k \ge 1, q \ge 2$).
        - Kneser growth bridge: `Erdos298.iterSum_growth_bound_of_kneser_data` deducing $(k + 1) |T| \le 2 |kT|$ from Kneser bounds $|kT| \ge (k(q - 1) + 1)|H|$ and $|T| \le q|H|$ ($q \ge 2$).
        - Natural & real growth interfaces: `Erdos298.iterSum_card_ge_of_kneser_hyp` ($\min(2|G|, (k + 1)|T|) \le 2|kT|$), `Erdos298.iterSum_card_ge_of_kneser_hyp_real` ($\min(|G|, (k + 1)|T|/2) \le |kT|$).
      - CFP §5.1 Subgroup Index, Scaled Coprimality & Fiber Coordinates (P04):
        - Definitions: `Erdos298.subgroupIndex` ($g = \gcd(t, \gcd(B))$), `Erdos298.fiber` ($F_r = \{s \in S \mid \pi(s) = r\}$), `Erdos298.centerFiber` ($F_r - x_0$).
        - Subgroup index properties: `Erdos298.subgroupIndex_pos`, `Erdos298.subgroupIndex_dvd_modulus` ($g \mid t$), `Erdos298.subgroupIndex_dvd_mem` ($\forall a \in B, g \mid a$), `Erdos298.subgroupIndex_mono`, `Erdos298.subgroupIndex_doubles_of_lt` ($g(B) < g(B') \implies 2 g(B) \le g(B')$), `Erdos298.subgroupIndex_le_of_mem`, `Erdos298.subgroupIndex_le_modulus`.
        - Scaled coprimality: `Erdos298.subgroupIndex_scaled_coprime` ($\gcd(t/g, \gcd(B/g)) = 1$ when $t > 0$, ensuring scaled elements generate $\mathbb{Z}/(t/g)\mathbb{Z}$).
        - Scaled candidate modulo injectivity: `Erdos298.natCast_zmod_div_injOn_Ico`, `Erdos298.card_image_natCast_zmod_div_of_Ico` on intervals of length $\le t/g$.
        - Fiber coordinate system: `Erdos298.zmodProj_sub`, `Erdos298.fiber_subset`, `Erdos298.disjoint_fibers`, `Erdos298.card_eq_sum_image_fibers` ($|S| = \sum_{r \in \pi(S)} |F_r|$).
        - Fiber translation & growth bounds: `Erdos298.translate_fiber_subset`, `Erdos298.delta_fiber_le_delta` ($\delta(F_r, x) \le \delta(S, x)$ for $\pi(x) = 0$).
        - Fiber centering: `Erdos298.card_centerFiber` ($|F_r - x_0| = |F_r|$), `Erdos298.centerFiber_subset_kernel` ($F_r - x_0 \subseteq \ker \pi$), `Erdos298.delta_centerFiber_eq` ($\delta(F_r - x_0, x) = \delta(F_r, x)$).
      - CFP §5.1 Coset AP Lifting (Lemma 5.10 / P08):
        - Integer progression structure: `Erdos298.IntAP` ($a + j \cdot b$ for $0 \le j < k$).
        - Image set & cardinality: `Erdos298.IntAP.toFinset`, `Erdos298.IntAP.card_toFinset` ($|P| = k$).
        - Subgroup coset lifting: `Erdos298.cosetAPLift` lifting a coset of cyclic subgroup $H \le \mathbb{Z}/N\mathbb{Z}$ of order $h$ ($h \mid N$) to an integer AP of length $h$ and step $N/h$.
        - Exact cardinality: `Erdos298.cosetAPLift_card` ($|P| = h$).
        - Family length sum: `Erdos298.coset_family_length_sum_eq` ($\sum_{i < q} |P_i| = q \cdot h$).
        - Coset partition budget bound: `Erdos298.coset_family_length_sum_le_three_mul` ($q \cdot h \le 3 |R|$).
      - CFP §5.1 Numerical Condition Interface (Lemma 5.6 / P12):
        - Mathematical parameter interface: `Erdos298.FiniteConditions` isolating all 10 parameters ($t, A, v, K, M, k_{div}, U, D, gMax, \xi, \ell, B_{growth}$) and numerical hypotheses ($K + M \le |A|$, $\mathrm{IsDiverse}(A, k_{div})$, subgroup index bounds $g(B) \le gMax \wedge g(B) - 1 \le k_{div}$ on all $B \subseteq A$ with $|B| \ge M$, $U < t / (2 gMax)$, $8 D < U$, and $(32 / \ell) \cdot t \le D \cdot (K - B_{growth})$).
      - CFP §5.1 Greedy Iteration State Machine (Lemma 5.6 / P13):
        - Discrete state: `Erdos298.GreedyState` tracking $(E, B)$ with $E \subseteq A$.
        - Invariants & capacities: `Erdos298.GreedyState.card_B` ($|B| = |A| - |E|$), `Erdos298.GreedyState.B_card_ge` ($|B| \ge M$ for $j \le K$), `Erdos298.GreedyState.B_nonempty` ($B \ne \emptyset$).
        - Stage classification: `Erdos298.isGrowthStage`, `Erdos298.isSaturatedStage`, `Erdos298.isUnsaturatedStage`.
        - Greedy selection: `Erdos298.exists_greedy_element` selecting $a \in B$ maximizing translation increment $\delta(S, a)$.
        - State transition: `Erdos298.nextState` adding $a$ to $E$, with `Erdos298.nextState_card` ($|E'| = |E| + 1$), `Erdos298.nextState_S_mono` ($S \subseteq S'$), and divisibility `Erdos298.nextState_g_dvd` ($g(B) \mid g(B')$).
      - CFP §5.1 Saturated Branch Density Lower Bound (Lemma 5.6 / P14):
        - Subgroup stabilization: `Erdos298.subsetSumsMod_eq_of_compl_dvd` ($\Sigma_d(E) = \Sigma_d(A)$ when all elements in $A \setminus E$ are divisible by $d$).
        - Global fiber lower bound: `Erdos298.card_ge_of_fibers_ge` ($|S| \ge g \cdot \text{bound}$ when $\pi(S) = \mathbb{Z}/g\mathbb{Z}$ and all fibers have size $\ge \text{bound}$).
        - Density cancellation: `Erdos298.mul_div_cancel_of_pos` ($g \cdot (\xi \cdot t / g) = \xi \cdot t$).
        - Saturated branch theorem: `Erdos298.card_subsetSumsMod_ge_of_saturated` proving that if any state $j \le K$ is saturated, then the final modular subset sums satisfy $|\Sigma_t(A)| \ge \xi \cdot t$.
      - CFP §5.1 Single-Step Growth Bounds for Growth Stage (Claim 1 / P15):
        - Double counting half-bound: `Erdos298.card_smallGrowth_half_le` ($|G_{s/2}| \le 2s$).
        - Range 1 single-step growth: `Erdos298.exists_large_growth_of_two_mul_lt` ($2|S| < |T| \implies \exists x \in T, \delta(S, x) > |S|/2$).
        - Range 2 floor arithmetic: `Erdos298.floor_mul_succ_gt` ($4s < (\lfloor 4s/b \rfloor + 1) b$).
        - Range 2 arithmetic contradiction: `Erdos298.range2_arith_contradiction` ($(q + 1) b \le 4s \wedge 4s < (q + 1) b \implies \text{False}$).
      - CFP §5.1 Combinatorial Core F1 of CFP Lemma 5.6 (Phases P16, P17, P18):
        - Initial state & deterministic greedy choice: `Erdos298.initialGreedyState`, `Erdos298.greedyChoice`, `Erdos298.greedyChoice_mem`, `Erdos298.greedyChoice_max`.
        - State trajectory: `Erdos298.greedySeq` tracking $(E_j, B_j)$.
        - Exact capacity: `Erdos298.card_greedySeq_E` ($|E_j| = j$ for all $j \le K$).
        - Modular subset sum inclusion: `Erdos298.greedySeq_S_subset` ($S_j \subseteq \Sigma_t(A)$).
        - Increment helper & identity: `Erdos298.greedyDelta`, `Erdos298.card_greedySeq_S_succ` ($|S_{j+1}| = |S_j| + \delta_j$).
        - Telescoping summation: `Erdos298.sum_delta_le_card_final` ($\sum_{j < K} \delta_j \le |S_K|$), `Erdos298.sum_delta_le_total` ($\sum_{j < K} \delta_j \le |\Sigma_t(A)|$).
        - Step classification sets: `Erdos298.growthSteps`, `Erdos298.saturatedSteps`, `Erdos298.unsaturatedSteps`.
        - Step disjointness & partition: `Erdos298.disjoint_growth_unsaturated`, `Erdos298.steps_partition` (each step $j < K$ is uniquely saturated, growth, or unsaturated).
        - Unsaturated step count lower bound: `Erdos298.card_unsaturatedSteps_ge` ($|U| \ge K - B_{growth}$ when saturated steps are empty).
        - Combinatorial Core F1 Master Theorem: `Erdos298.cfp_lemma_5_6_finite_core` proving that under the numerical and combinatorial hypotheses of `FiniteConditions`, the modular subset sums satisfy:
          $$\min(\xi, 32 / \ell) \cdot t \le |\Sigma_t(A)|.$$
      - CFP §5.1 Parameter Instantiation, Arithmetic Adapter & Non-Vacuity (Phase P19):
        - Concrete non-vacuous realization: `Erdos298.concreteFiniteConditions` providing an explicit machine-checked witness ($t = 20, A = \{1, 3, 7\}, v = 1, K = 2, M = 1, k_{div} = 1, U = 9, D = 1, gMax = 1, \xi = 1/128, \ell = 1024, B_{growth} = 0$).
        - Non-vacuity master theorem: `Erdos298.finiteConditions_realizable` proving `Nonempty FiniteConditions`.
        - Primorial product and ratio: `Erdos298.primorialProd` ($W(P) = \prod_{p \in P} p$), `Erdos298.cfpTau` ($\tau(W, m) = \varphi(Wm) / (Wm)$), and positivity `Erdos298.cfpTau_pos`.
        - Number-theoretic rough candidate sets: `Erdos298.inY`, `Erdos298.inY_v`, and scaling injection `Erdos298.mem_Y_of_mem_Y_v` ($a \in Y_v \implies v \cdot a \in Y$).
        - Arithmetic parameter configuration: `Erdos298.CFPArithParams` bundling target $n$, scaling $v$, modulus $t$, set $A$, and the 10 numerical conditions.
        - Canonical adapter: `Erdos298.CFPArithParams.toFiniteConditions` translating arithmetic parameters to `FiniteConditions`.
        - Master $m = n$ specialization: `Erdos298.cfp_lemma_5_6_m_eq_n` establishing $\min(\xi, 32 / \ell) \cdot t \le |\Sigma_t(A)|$ from arithmetic parameters.
        - Interface bridge: `Erdos298.chromatic_lower_bound_of_diverse_density` connecting modular density to the chromatic lower bound $k + 1 \le f(n)$ via `CFPDiverseWitness`.
      - CFP §5.1 Diverse Subset Extraction and Subsampling (Lemma 5.4 / Phase 21):
        - Filter difference containment: `Erdos298.filter_not_dvd_sdiff_subset` showing $((A \setminus v\mathbb{N}) \setminus (B \setminus v\mathbb{N})) \subseteq A \setminus B$.
        - Exact difference cardinality: `Erdos298.card_sdiff_of_subset` establishing $|A \setminus B| = |A| - |B|$ for $B \subseteq A$.
        - Bounded filter loss: `Erdos298.card_filter_not_dvd_le_card_add_sdiff` proving $|A \setminus v\mathbb{N}| \le |B \setminus v\mathbb{N}| + |A \setminus B|$.
        - Deterministic diversity preservation: `Erdos298.isDiverse_subset_of_card_diff_le` proving $\forall B \subseteq A, |A| - |B| \le k - k' \implies \mathrm{IsDiverse}(B, k')$.
        - Element and finset removal: `Erdos298.isDiverse_sdiff_singleton` (single element removal leaves $(k-1)$-diversity) and `Erdos298.isDiverse_sdiff_finset` (removal of size $r \le k$ leaves $(k-r)$-diversity).
        - State machine application: `Erdos298.GreedyState.isDiverse_B` establishing that remaining candidates $st.B$ in the greedy iteration retain diversity $k_{div} - |E|$.
        - Prescribed size extraction: `Erdos298.exists_diverse_subset_of_card_eq` proving existence of diverse subsets of any prescribed size $s$ under controlled loss.
        - Divisor bounds on diverse sets: `Erdos298.isDiverse_gcd_le_one` ($\gcd(A) \le 1$ for any $k$-diverse set with $k \ge 1$) and `Erdos298.isDiverse_gcd_eq_one` ($\gcd(A) = 1$ when $A$ contains a positive element).
        - Subgroup index vanishing: `Erdos298.subgroupIndex_eq_one_of_isDiverse` proving $\mathrm{subgroupIndex}(t, B) = 1$ for diverse $B$, linking diverse sets directly to `FiniteConditions`.
        - Two-stage disjoint extraction: `Erdos298.exists_disjoint_diverse_subsets` extracting independent diverse subsets $A_1, A_2 \subseteq A$ with controlled loss.
        - End-to-end algorithmic pipeline: `Erdos298.exists_scaled_diverse_candidate` uniting Section 8.3 divisor extraction with Lemma 5.4 subsampling.
        - Structural adapter: `Erdos298.diverse_candidate_satisfies_finiteConditions` verifying `FiniteConditions` diversity and capacity bounds.
        - Lemma 5.4 subsampling specifications: `Erdos298.CFPLemma54Statement` and `Erdos298.CFPLemma54FullStatement` (with range bound $N$).
        - Unconditional realizations: `Erdos298.cfp_lemma_5_4_of_deterministic` and `Erdos298.cfp_lemma_5_4_full_of_deterministic`.
        - Counting formulation and density: `Erdos298.CFPLemma54Subsets` defining the finset of diverse subsamples, `Erdos298.cfp_lemma_5_4_all_subsets_diverse` proving that 100% of size-$s$ subsets are $k'$-diverse, and `Erdos298.card_CFPLemma54Subsets_eq` yielding the exact choose formula $\binom{|A|}{s}$.


