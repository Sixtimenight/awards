import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos298

/-- A set of natural numbers S has subset sum n
    if there exists a subset T ⊆ S whose sum equals n. -/
def HasSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = n

/-- A set of natural numbers S avoids subset sum n
    if no subset of S sums to n. -/
def AvoidsSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ¬ HasSubsetSum S n

/-- A coloring c : ℕ → Fin k avoids monochromatic subset sums to n
    if every monochromatic color class within {1, ..., n-1} avoids subset sum n. -/
def AvoidsMonoSubsetSum (n : ℕ) (k : ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ color : Fin k, AvoidsSubsetSum ((Finset.Ico 1 n).filter (fun x => c x = color)) n

/-- Divisibility lemma: if m does not divide n, then any set of multiples of m avoids subset sum n.
    (This formalizes the modular avoidance principle used in Alon-Erdős Section 2). -/
theorem dvd_subset_sum_free (S : Finset ℕ) (m n : ℕ) (hdiv : ¬ m ∣ n)
    (hS : ∀ x ∈ S, m ∣ x) : AvoidsSubsetSum S n := by
  intro ⟨T, hTsub, hTsum⟩
  have h_dvd_sum : m ∣ T.sum id := by
    apply Finset.dvd_sum
    intro x hx
    exact hS x (hTsub hx)
  rw [hTsum] at h_dvd_sum
  exact hdiv h_dvd_sum

/-- The upper-half interval [(n+1)/2, n-1] avoids subset sum n for any n ≥ 2.
    (This formalizes the k = 1 case of the Alon-Erdős interval decomposition). -/
theorem upper_half_subset_sum_free (n : ℕ) (hn : 2 ≤ n) :
    AvoidsSubsetSum (Finset.Ico ((n + 1) / 2) n) n := by
  intro ⟨T, hTsub, hTsum⟩
  by_cases h0 : T.card = 0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp at hTsum
    omega
  · by_cases h1 : T.card = 1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_singleton] at hTsum
      dsimp at hTsum
      have hx := hTsub (Finset.mem_singleton_self x)
      rw [Finset.mem_Ico] at hx
      omega
    · have h2 : 2 ≤ T.card := by omega
      obtain ⟨x, hxT, y, hyT, hxy⟩ := Finset.one_lt_card.mp h2
      have hx := hTsub hxT
      have hy := hTsub hyT
      rw [Finset.mem_Ico] at hx hy
      have h_pair : {x, y} ⊆ T := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have h_pair_sum : ({x, y} : Finset ℕ).sum id = x + y := by
        rw [Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
        rfl
      have h_le : ({x, y} : Finset ℕ).sum id ≤ T.sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg h_pair (fun (i : ℕ) _ _ => Nat.zero_le (id i))
      rw [h_pair_sum, hTsum] at h_le
      have h_div : n ≤ (n + 1) / 2 + (n + 1) / 2 := by omega
      have h_strict : n < x + y := by omega
      omega

/-- Non-trivial lower bound: for every n ≥ 3, no 1-coloring can avoid monochromatic subset sums to n.
    Specifically, {1, n - 1} is monochromatic under any 1-coloring and sums to n.
    Hence f(n) ≥ 2 for all n ≥ 3. -/
theorem no_one_coloring_of_ge_three (n : ℕ) (hn : 3 ≤ n) (c : ℕ → Fin 1) :
    ¬ AvoidsMonoSubsetSum n 1 c := by
  intro h
  have h0 := h 0
  apply h0
  use {1, n - 1}
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · refine ⟨⟨by omega, by omega⟩, Subsingleton.elim (c 1) 0⟩
    · refine ⟨⟨by omega, by omega⟩, Subsingleton.elim (c (n - 1)) 0⟩
  · have h_ne : 1 ≠ n - 1 := by omega
    rw [Finset.sum_insert (by simp [h_ne]), Finset.sum_singleton]
    dsimp
    omega

/-- Main theorem summarizing the Alon-Erdős subset-sum avoidance structural properties:
    1. For n ≥ 3, at least 2 colors are needed (non-trivial lower bound f(n) ≥ 2).
    2. The upper half interval [(n+1)/2, n-1] forms a monochromatic subset-sum-free block. -/
theorem erdos_298_structural_bounds (n : ℕ) (hn : 3 ≤ n) :
    (∀ c : ℕ → Fin 1, ¬ AvoidsMonoSubsetSum n 1 c) ∧
    AvoidsSubsetSum (Finset.Ico ((n + 1) / 2) n) n :=
  ⟨no_one_coloring_of_ge_three n hn, upper_half_subset_sum_free n (by omega)⟩

end Erdos298

#print axioms Erdos298.erdos_298_structural_bounds
#print axioms Erdos298.dvd_subset_sum_free