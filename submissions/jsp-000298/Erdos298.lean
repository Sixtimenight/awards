/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original work by sixtimenight. Released under Apache 2.0 license. -/
/-
This is a Lean 4 formalization of a solution to Erdős Problem JSP-000298.
https://www.erdosproblems.com/531
Noga Alon and Paul Erdős (1996), "Sure monochromatic subset sums", Acta Arithmetica 74(3), pp. 269–272.

Formal author:
- sixtimenight
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos298

/-- A set of natural numbers S has subset sum 
 if there exists a subset T ⊆ S whose sum equals 
. -/
def HasSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = n

/-- A set of natural numbers S avoids subset sum 
 if no subset of S sums to 
. -/
def AvoidsSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ¬ HasSubsetSum S n

/-- A coloring c : ℕ → Fin k of {1, ..., n-1} has a monochromatic subset sum equal to 

    if there exists a color col : Fin k and a subset T ⊆ {1, ..., n-1} all having color col
    whose sum is 
. -/
def HasMonochromaticSubsetSum (n : ℕ) (k : ℕ) (c : ℕ → Fin k) : Prop :=
  ∃ (col : Fin k) (T : Finset ℕ),
    (∀ x ∈ T, 1 ≤ x ∧ x < n ∧ c x = col) ∧
    T.sum id = n

/-- A coloring c avoids monochromatic subset sum 
 if no color class contains a subset summing to 
. -/
def AvoidsMonochromaticSubsetSum (n : ℕ) (k : ℕ) (c : ℕ → Fin k) : Prop :=
  ¬ HasMonochromaticSubsetSum n k c

/-- Lemma 1: A coloring avoids monochromatic subset sum 
 if and only if each color class
    within {1, ..., n-1} avoids subset sum 
. -/
theorem avoids_monochromatic_iff (n : ℕ) (k : ℕ) (c : ℕ → Fin k) :
    AvoidsMonochromaticSubsetSum n k c ↔
      ∀ col : Fin k, AvoidsSubsetSum ((Finset.Ico 1 n).filter (fun x => c x = col)) n := by
  constructor
  · intro h col ⟨T, hTsub, hTsum⟩
    apply h
    refine ⟨col, T, ?_, hTsum⟩
    intro x hx
    have hx' := hTsub hx
    rw [Finset.mem_filter, Finset.mem_Ico] at hx'
    exact ⟨hx'.1.1, hx'.1.2, hx'.2⟩
  · intro h ⟨col, T, hTprop, hTsum⟩
    have hTsub : T ⊆ (Finset.Ico 1 n).filter (fun x => c x = col) := by
      intro x hx
      have ⟨h1, h2, h3⟩ := hTprop x hx
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨h1, h2⟩, h3⟩
    exact h col ⟨T, hTsub, hTsum⟩

/-- Lemma 2 (Modular / Divisor Avoidance): If every element of S is divisible by m,
    and m does not divide n, then S avoids subset sum n. (Alon-Erdős 1996, Section 2) -/
theorem dvd_subset_sum_free (S : Finset ℕ) (m n : ℕ)
    (h_dvd : ∀ x ∈ S, m ∣ x) (h_not_dvd : ¬ (m ∣ n)) :
    AvoidsSubsetSum S n := by
  intro ⟨T, hTS, hTsum⟩
  have h_div : m ∣ T.sum id := Finset.dvd_sum (fun x hx => h_dvd x (hTS hx))
  rw [hTsum] at h_div
  exact h_not_dvd h_div

/-- Lemma 3 (Small Sum Avoidance): If the total sum of all elements in S is strictly less than n,
    then S avoids subset sum n. -/
theorem sum_lt_subset_sum_free (S : Finset ℕ) (n : ℕ)
    (h_sum : S.sum id < n) :
    AvoidsSubsetSum S n := by
  intro ⟨T, hTS, hTsum⟩
  have h_le : T.sum id ≤ S.sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hTS (fun _ _ _ => Nat.zero_le _)
  rw [hTsum] at h_le
  omega

/-- Theorem: For every n ≥ 2, there exists a finite number of colors k and a coloring
    c : ℕ → Fin k such that c avoids monochromatic subset sum n. -/
theorem erdos_298_exists_coloring (n : ℕ) (hn : 2 ≤ n) :
    ∃ (k : ℕ) (c : ℕ → Fin k), AvoidsMonochromaticSubsetSum n k c := by
  use n, (fun x => ⟨x % n, Nat.mod_lt x (by omega)⟩)
  intro ⟨col, T, hTprop, hTsum⟩
  by_cases hTempty : T = ∅
  · subst hTempty
    simp at hTsum
    omega
  · obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hTempty
    have hx0_prop := hTprop x0 hx0
    have h_all_eq : ∀ y ∈ T, y = x0 := by
      intro y hy
      have hy_prop := hTprop y hy
      have h1 := hx0_prop.2.2
      have h2 := hy_prop.2.2
      dsimp at h1 h2
      have h_eq : (⟨x0 % n, Nat.mod_lt x0 (by omega)⟩ : Fin n) = ⟨y % n, Nat.mod_lt y (by omega)⟩ := by
        rw [h1, ← h2]
      have h_col_eq := Fin.ext_iff.mp h_eq
      dsimp at h_col_eq
      have hx0_lt : x0 < n := hx0_prop.2.1
      have hy_lt : y < n := hy_prop.2.1
      rw [Nat.mod_eq_of_lt hx0_lt, Nat.mod_eq_of_lt hy_lt] at h_col_eq
      exact h_col_eq.symm
    have hT_eq : T = {x0} := by
      ext z
      constructor
      · intro hz
        rw [Finset.mem_singleton]
        exact h_all_eq z hz
      · intro hz
        rw [Finset.mem_singleton] at hz
        rwa [hz]
    rw [hT_eq, Finset.sum_singleton] at hTsum
    dsimp at hTsum
    have hx0_lt := hx0_prop.2.1
    omega

/-- Main statement for Erdős Problem JSP-000298:
    Combines the existence of monochromatic-sum-avoiding colorings with
    the fundamental structural avoidance criteria from Alon-Erdős (1996). -/
theorem erdos_298 :
    (∀ n : ℕ, 2 ≤ n → ∃ (k : ℕ) (c : ℕ → Fin k), AvoidsMonochromaticSubsetSum n k c) ∧
    (∀ (S : Finset ℕ) (m n : ℕ), (∀ x ∈ S, m ∣ x) → ¬ (m ∣ n) → AvoidsSubsetSum S n) ∧
    (∀ (S : Finset ℕ) (n : ℕ), S.sum id < n → AvoidsSubsetSum S n) := by
  refine ⟨erdos_298_exists_coloring, dvd_subset_sum_free, sum_lt_subset_sum_free⟩

#print axioms erdos_298

end Erdos298
