# JSP-001018: Statement Correspondence and Mathematical Alignment

## English

### Problem Statement
**JSP-001018** (Erdős Problem 1213 / Hegyvári 1986):
*Must every sufficiently long integer sequence with bounded gaps have two distinct consecutive blocks with equal sums?*

**Mathematical formulation:**
Let $a, K \ge 1$. There exists a finite bound $f(a, K)$ such that for every strictly increasing sequence of positive integers $A = (A_0, A_1, \dots, A_{s-1})$ satisfying:
1. $A_0 = a$
2. $A_{i+1} - A_i \le K$ for all $i$
3. $A_{s-1} > f(a, K)$
there exist two distinct nonempty index intervals $[u, v)$ and $[x, y)$ contained in $[0, s)$ such that:
$$\sum_{i=u}^{v-1} A_i = \sum_{j=x}^{y-1} A_j$$

### Lean 4 Formalization Correspondence
In `Erdos1213.lean`:
```lean
def intervalSum (A : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico u v, A i

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ,
    u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
      intervalSum A u v = intervalSum A x y

def explicitBound (a K : ℕ) : ℕ :=
  4 ^ K * a + 2 * K * (4 ^ K) ^ 2

theorem erdos_1213 :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ, ∀ (s : ℕ) (A : ℕ → ℕ),
      0 < s →
      A 0 = a →
      (∀ ⦃i j : ℕ⦄, i < j → j < s → A i < A j) →
      (∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) - A i ≤ K) →
      f < A (s - 1) →
      Erdos1213.HasEqualIntervalSums A s
```

### Mathematical Attribution
- **Mathematical proof:** Norbert Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. 48 (1986), 193–200.
- **Formal proof:** Lean 4 with Mathlib v4.33.0.