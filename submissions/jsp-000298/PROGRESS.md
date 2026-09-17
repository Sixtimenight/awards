# Formalization Progress for Erdős Problem JSP-000298 (Erdős #360)

- **Problem**: Erdős Problem #360 / JSP-000298 (*Monochromatic subset sums to a prescribed integer*).
- **PR**: [TheJustinSunPrize/awards #353](https://github.com/TheJustinSunPrize/awards/pull/353)
- **Branch**: `candidate/jsp-000298`
- **Current Baseline Commit**: `38294f4add8980d5ec3854028dd9b0d08b3d542b`
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

