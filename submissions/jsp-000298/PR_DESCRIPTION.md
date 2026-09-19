# PR Description: Erdős Problem #360 (JSP-000298)

## Title
`feat(jsp-000298): Formalization of Erdős Problem #360 — Unifying Alon–Erdős and Conlon–Fox–Pham (Phase G6 Part 1 Mertens Analytical Package & Sieve G Closed)`

---

## Summary of Changes

This Pull Request provides a comprehensive, standalone, and reproducible Lean 4 formalization of monochromatic subset-sum avoidance bounds for **Erdős Problem JSP-000298 (Erdős Problem #360)**.

The formalization bridges and unifies all three historical generations of solutions:
1. **Generation 1 (Alon–Erdős 1996 Elementary)**: Constructive $2s$-coloring for $n \le s^3$, establishing $f(n) \le 2\lceil n^{1/3}\rceil$.
2. **Generation 2 (Alon–Erdős 1996 Sieve)**: Finite quantitative Selberg sieve remainder bound and prime reciprocal sum lower bound.
3. **Generation 3 (Conlon–Fox–Pham 2021 Upper Bound)**: Constructive 4-layer coloring using reduced residues modulo $d$.
4. **Generation 3 (Conlon–Fox–Pham 2021 Lower Bound & Additive Combinatorics Engine)**: Extensive formalization of the additive combinatorics machinery underlying the lower bound:
   - **DeVos–Goddyn–Mohar (2009) / Kneser Addition Theorem**: General finite abelian group sumset growth and stabilizer theory (`Erdos298/DeVos.lean`, `Erdos298/Kneser.lean`).
   - **Lev Continuous Interval Subset-Sum Coverage**: Interval extension and hitting theory (`Erdos298/Lev.lean`).
   - **CFP Lemma 5.4**: Diverse subset extraction, subsampling, and two-stage partition.
   - **CFP Lemma 5.6**: Combinatorial core and finite core:
     - Growth step budget bound (Claim 1 closed via iterated Kneser growth).
     - Unsaturated step expansion (Claim 2).
     - Structural input isolated to the guarded coset-AP cover interface `GuardedAPCover`, proven equivalent to the guarded trichotomy (`guardedAPCover_iff_trichotomy`). An earlier unguarded form of this hypothesis was refutable (`not_unguarded_ap_cover'`) and has been removed.
     - Explicit non-vacuity witness for the parameter layer: `concreteCFPArithParams`, `concreteP17Conditions`, `concreteCFPArithParams_numeric`, `lemma_5_6_parameter_hypotheses_satisfiable` (all conditions of `CFPArithParams` / `P17FiniteArithConditions` including E1–E3 are machine-checked on $n = t = 16411$).
   - **Phase P08 Branch A (`hasIntAPCoverBranchA`)**: Arithmetic progression lifting geometry for $|R.H|^3 \ge R_{\mathrm{card}}$ **completely closed with 0 sorry and standard Lean 4 axioms**.
   - **Phase P08/P09 Master Branch Reductions**: Decoupled master theorems (`hasIntAPCover_of_branchA_and_branchB`, `cfp_lemma_5_6_m_eq_n_of_branches_and_sieve`).
   - **Phase P09 Selberg Sieve for APs**: Real-valued divisibility bounds, monotonicity, and universal length bounds for arithmetic progression rough counts.
5. **Phase G6 Part 1 (Mertens Analytical Number Theory Foundation & Sieve G Lower Bound)**:
   - **New Independent Module `Erdos298/Mertens.lean`**: 15 machine-checked analytical and number-theoretic lemmas without circularity (harmonic sum bounds, squarefree reciprocal lower bounds $\frac{1}{2}\log z \le \sum_{a \le z, \text{sqfree}} 1/\varphi(a)$, divisor totient bounds, and coprime squarefree decomposition).
   - **Master Selberg Sieve G Lower Bound (`sieveG_ge_half_totient_ratio_mul_log`)**:
     $$\frac{1}{2} \frac{\varphi(n)}{n} \log z \le \mathrm{sieveG}(n, s, z)$$
     unconditionally for all $n \ge 2, s \ge 1, 2 \le z \le s$.
   - **Totient-weighted sieve bound (`minColors_le_of_totient_log`)**:
     $$f(n) \le 2s + \left\lceil \frac{n - 1}{s(s+1) ((1/2) (\varphi(n)/n) \log z)} + \frac{z^4}{s} \right\rceil.$$

---

## Status of Results

| Component | Formal Status | Scope & Dependencies |
| :--- | :--- | :--- |
| **Cubic-Root Upper Bound** ($f(n) \le 2\lceil n^{1/3}\rceil$) | **Unconditionally Proven** | Complete constructive proof (`Erdos298.exists_coloring_of_le_cube`, `minColors_le_two_mul_s`). |
| **Sieve-Remainder Bound** ($f(n) \le s + |P| + \lceil |R|/s \rceil$) | **Unconditionally Proven** | Complete combinatorial proof (`Erdos298.exists_coloring_sieve`, `minColors_le_sieve`). |
| **Finite Selberg Sieve** ($|R| \le m/G + z^4$) | **Unconditionally Proven** | Diagonalized quadratic form & error sum (`Erdos298.selberg_remainder_bound`). |
| **Prime Reciprocal Sum Bound** | **Unconditionally Proven** | Complete explicit prime sum bound (`Erdos298.minColors_le_of_sum_primes`). |
| **CFP 4-Layer Upper Bound** | **Unconditionally Proven** | Complete constructive 4-layer coloring (`Erdos298.exists_coloring_conlon_fox_pham`, `minColors_le_conlon_fox_pham`). |
| **Mertens Analytical Package (`Mertens.lean`)** | **Unconditionally Proven** | 15 analytical lemmas; squarefree totient reciprocal sum $\ge \frac{1}{2}\log z$ (`Erdos298.sum_coprime_squarefree_inv_totient_ge_half`). |
| **Master Selberg Sieve G Lower Bound** | **Unconditionally Proven** | $\mathrm{sieveG}(n, s, z) \ge \frac{1}{2} \frac{\varphi(n)}{n} \log z$ (`Erdos298.sieveG_ge_half_totient_ratio_mul_log`, `minColors_le_of_totient_log`). |
| **Elementary Lower Bound** ($f(n) \ge 2$) | **Unconditionally Proven** | Machine-checked for all $n \ge 3$ (`Erdos298.minColors_ge_two`). |
| **CFP Lower Bound Reduction Engine** | **Unconditionally Proven** | Monotone lifting, fiber pigeonhole, AP hitting bridge (`Erdos298.minColors_ge_of_cfp_witness`). |
| **DeVos–Goddyn–Mohar (2009) & Kneser Growth** | **Unconditionally Proven** | Complete inductive proof on arbitrary composite modulus (`Erdos298/DeVos.lean`, `Erdos298/Kneser.lean`). |
| **Lev Continuous Interval Coverage** | **Unconditionally Proven** | Complete interval extension and target hitting (`Erdos298/Lev.lean`). |
| **CFP Lemma 5.4 Diverse Subsampling** | **Unconditionally Proven** | End-to-end algorithmic divisor extraction + subsampling (`Erdos298.exists_scaled_diverse_candidate`). |
| **CFP Lemma 5.6 Claim 1 (Growth Budget)** | **Unconditionally Proven** | Unconditionally bounded via iterated Kneser growth (`Erdos298.growthSteps_card_le_p16Budget_closed`). |
| **Phase P08 Branch A AP Lifting** ($|R.H|^3 \ge R_{\mathrm{card}}$) | **Unconditionally Proven** | Complete AP lifting geometry, 0 sorry (`Erdos298.hasIntAPCoverBranchA`). |
| **Phase P08/P09 Master Branch Reductions** | **Unconditionally Proven** | Decoupled master theorems (`hasIntAPCover_of_branchA_and_branchB`, `cfp_lemma_5_6_m_eq_n_of_branches_and_sieve`). |
| **Grand Unified Master Theorem** | **Unconditionally Proven (as a conjunction)** | Conjunction of 5 statements (`Erdos298.erdos_problem_360_unified_solution`); items 1–4 unconditional, item 5 is the conditional asymptotic reduction below. |
| **Unconditional Two-Sided Master Theorem** | **Unconditionally Proven** | $2 \le f(n) \le s_1 + |P| + 2|\text{reducedResidues } d| + \lceil |R_{cfp}| / s_{rem} \rceil$ (`Erdos298.erdos_problem_360_unconditional_master`). |
| **Asymptotic Growth Equivalence** ($f(n) \asymp F(n)$) | **Conditional Reduction** | `Erdos298.erdos_problem_360_asymptotic_master`: matching witnesses `HasChromaticLowerBound F c` ∧ `HasChromaticUpperBound F C` ⟹ $c F(n) \le f(n) \le C F(n)$. (Neither witness is proven for $F = \mathrm{cfpScale}$ yet.) |

---

## Verification & Axiom Audit

- **Toolchain**: Lean 4.33.0 / Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- **Lake Build**: `lake build Erdos298` completes with **2765 jobs, Exit Code 0, 0 errors, strictly 0 warnings**.
- **Axiom Check**: All key theorems verified via `#print axioms` to depend strictly on standard Lean 4 foundational axioms:
  ```lean
  [propext, Classical.choice, Quot.sound]
  ```
- **Strict Compliance**: Strictly 0 `sorry`, 0 `admit`, 0 custom axioms.

---

## File Structure

```text
submissions/jsp-000298/
├── Erdos298.lean            # Master formalization file (11,062 lines, 0 warnings)
│                            # Contains all theorems, definitions, and unified master results
├── Erdos298/                # Modular mathematical components
│   ├── Basic.lean           # Integer arithmetic progression fundamentals and lifting structures
│   ├── DeVos.lean           # DeVos–Goddyn–Mohar (2009) small growth structure theorem (1,634 lines)
│   ├── Kneser.lean          # Kneser addition theorem and iterated sumset growth on finite abelian groups
│   ├── Lev.lean             # Lev continuous interval subset-sum coverage theory
│   └── Mertens.lean         # Analytical number theory foundation: harmonic, totient & sieve G bounds
├── HANDOVER.md              # Detailed technical documentation and action plans
├── ROADMAP_REMAINING_GAPS.md # Gap-by-gap attack plan for the remaining open items (G0–G6)
├── PROGRESS.md              # Complete progress tracking and theorem catalog
├── README.md                # Comprehensive documentation and reproduction instructions
├── lake-manifest.json       # Pinned Mathlib dependency manifest
├── lakefile.toml            # Lake build configuration
└── lean-toolchain           # Lean 4.33.0 toolchain pin
```

---

## Reproduction Instructions

```bash
cd submissions/jsp-000298
lake exe cache get
lake build Erdos298
```
