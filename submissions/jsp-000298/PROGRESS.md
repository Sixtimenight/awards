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
| **Phase 2: 1996 Upper Bound** | `Erdos298.alon_erdos_upper_bound` | $f(n) \le C (n \log \log n / \log n)^{1/3}$ for large $n$ | **To be proven (Phase 2)** | - |
| **Phase 3: 2021 Upper Bound** | `Erdos298.conlon_fox_pham_upper_bound` | $f(n) \le C \cdot F(n)$ where $F(n) = \frac{n^{1/3}(n/\varphi(n))}{(\log n)^{1/3}(\log \log n)^{2/3}}$ | **To be proven (Phase 3)** | - |
| **Phase 4: 2021 Lower Bound** | `Erdos298.conlon_fox_pham_lower_bound` | $f(n) \ge c \cdot F(n)$ for large $n$ | **To be proven (Phase 4)** | Major external dependencies |
| **Phase 5: Exact Growth** | `Erdos298.conlon_fox_pham_main_theorem` | $c \cdot F(n) \le f(n) \le C \cdot F(n)$ for all $n \ge N_0$ | **To be proven (Phase 5)** | Depends on Phases 3 & 4 |

---

## 2. Dependency Audit for 2021 Conlon–Fox–Pham Lower Bound (Section 5.1)

A rigorous audit of the mathematical dependencies required for the 2021 lower bound ($f(n) \ge c F(n)$) against Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`:

1. **Arithmetic Progressions in Dense Subset Sums (Szemerédi–Vu / Sárközy Theorems)**:
   - *Requirement*: If $A \subseteq [1, M]$ has density $\alpha$, then its subset sums $\Sigma(A)$ contain a long arithmetic progression of length $L$ and step $d$.
   - *Mathlib Status*: **Not yet located**. Mathlib formalizes Roth's theorem (`Mathlib.Combinatorics.Additive.Roth`), but does not contain Sárközy's or Szemerédi–Vu's theorems on subset sums.
2. **Distribution of Primes in Arithmetic Progressions**:
   - *Requirement*: Quantitative bounds for $\pi(x; q, a)$ or Siegel–Walfisz theorem to guarantee prime existence in specified residue classes.
   - *Mathlib Status*: **Not yet located**. Mathlib has Dirichlet's theorem on the infinitude of primes in arithmetic progressions (`Mathlib.NumberTheory.DirichletTheorem`), but not the quantitative effective/asymptotic forms.
3. **Mertens' Product Theorems**:
   - *Requirement*: $\prod_{p \le x} (1 - 1/p) \sim e^{-\gamma} / \log x$ and bounds on $\prod_{p \mid n} (1 - 1/p)^{-1} = n / \varphi(n)$.
   - *Mathlib Status*: **Not yet located**. Mathlib contains basic Euler totient properties (`Nat.totient`) and elementary prime factor relations, but lacks Mertens' third theorem.
4. **Conclusion of Dependency Audit**:
   - The lower bound of Conlon–Fox–Pham (2021) relies on deep additive combinatorics and analytic prime distribution results that are not currently available in Mathlib.
   - Therefore, the lower bound will be developed by cleanly identifying and isolating these dependencies, ensuring that Phase 1 (finite Selberg sieve) and Phase 2 (1996 upper bound) provide complete, unconditioned, machine-checked theorems in core Mathlib.
