import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.NormNum.Prime
import Erdos298.Kneser
import Erdos298.Lev
import Erdos298.Mertens


/-!
# Erdős Problem 360 / JSP-000298: Monochromatic Subset Sums

Let f(n) denote the minimum number of colors needed to color {1, ..., n-1}
such that no color class contains a subset whose elements sum to n.

Alon and Erdős (1996, *Acta Arithmetica* 74(3), pp. 269-272) and
Conlon, Fox, and Pham (2021, arXiv:2104.14766) studied this problem:
1. Cubic-root baseline: partitioning into interval blocks A_k for n ≤ (k+1)x
   and remainder blocks gives f(n) ≤ 2⌈n^(1/3)⌉.
2. Sieve-remainder bound: sieving multiples of primes p ≤ s with p ∤ n
   leaves a remainder set R. Partitioning R by element counts into blocks
   of size at most s yields:
   f(n) ≤ s + |P| + ⌈|R| / s⌉.
3. Lower bound: f(n) ≥ 2 for all n ≥ 3 (since {1, n-1} sums to n).
4. Conlon–Fox–Pham (2021) 4-layer construction:
   f(n) ≤ s1 + |P| + 2 * |reducedResidues d| + ⌈|R_cfp| / s_rem⌉.
-/

namespace Erdos298

open scoped Classical
open Finset Nat ArithmeticFunction

/-- A set of natural numbers S has subset sum n if there exists T ⊆ S with sum n. -/
def HasSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = n

/-- A set of natural numbers S avoids subset sum n if no subset sums to n. -/
def AvoidsSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ¬ HasSubsetSum S n

/-- A coloring c : ℕ → Fin k avoids monochromatic subset sum n if every color class avoids n. -/
def AvoidsMonoSubsetSum (n : ℕ) (k : ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ color : Fin k, AvoidsSubsetSum ((Finset.Ico 1 n).filter (fun x => c x = color)) n

lemma avoids_subset_sum_of_subset {S S' : Finset ℕ} (hSS' : S' ⊆ S) {n : ℕ}
    (h : AvoidsSubsetSum S n) : AvoidsSubsetSum S' n := by
  intro ⟨T, hTsub, hTsum⟩
  exact h ⟨T, hTsub.trans hSS', hTsum⟩

/-- Non-trivial lower bound: for every n ≥ 3, no 1-coloring can avoid monochromatic subset sums to n.
    Specifically, {1, n - 1} is monochromatic under any 1-coloring and sums to n. -/
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

/-- Divisibility lemma: if m does not divide n, then any set of multiples of m avoids subset sum n. -/
theorem dvd_subset_sum_free (S : Finset ℕ) (m n : ℕ) (hdiv : ¬ m ∣ n)
    (hS : ∀ x ∈ S, m ∣ x) : AvoidsSubsetSum S n := by
  intro ⟨T, hTsub, hTsum⟩
  have h_dvd_sum : m ∣ T.sum id := by
    apply Finset.dvd_sum
    intro x hx
    exact hS x (hTsub hx)
  rw [hTsum] at h_dvd_sum
  exact hdiv h_dvd_sum

/-- The large interval block A_k: numbers x ∈ {1, ..., n-1} with n ≤ (k+1)*x and k*x < n. -/
def intervalBlock (n : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun x => n ≤ (k + 1) * x ∧ k * x < n)

lemma interval_block_avoids_subset_sum (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    AvoidsSubsetSum (intervalBlock n k) n := by
  intro ⟨T, hTsub, hTsum⟩
  have h_elem : ∀ x ∈ T, n ≤ (k + 1) * x ∧ k * x < n := by
    intro x hx
    have := hTsub hx
    simp only [intervalBlock, Finset.mem_filter, Finset.mem_Ico] at this
    exact this.2
  by_cases h0 : T.card = 0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp at hTsum
    omega
  · by_cases hle : T.card ≤ k
    · have h_bound : ∀ x ∈ T, k * x ≤ n - 1 := by
        intro x hx
        have := (h_elem x hx).2
        omega
      have h_sum_le : k * T.sum id ≤ k * (n - 1) := by
        rw [Finset.mul_sum]
        dsimp
        have h_sum := Finset.sum_le_sum (fun x hx => h_bound x hx)
        have h_const : (∑ x ∈ T, (n - 1)) = T.card * (n - 1) := by simp
        rw [h_const] at h_sum
        have : T.card * (n - 1) ≤ k * (n - 1) := Nat.mul_le_mul_right (n - 1) hle
        exact h_sum.trans this
      have h_strict : k * (n - 1) < k * n := by
        have : n - 1 < n := by omega
        exact (Nat.mul_lt_mul_left hk).mpr this
      rw [hTsum] at h_sum_le
      omega
    · have hgt : k + 1 ≤ T.card := by omega
      have h2 : 2 ≤ T.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
      have h_not_both : ¬ ((k + 1) * a = n ∧ (k + 1) * b = n) := by
        intro ⟨ha_eq, hb_eq⟩
        have : (k + 1) * a = (k + 1) * b := by rw [ha_eq, hb_eq]
        have h_eq : a = b := Nat.eq_of_mul_eq_mul_left (by omega) this
        exact hab h_eq
      have h_strict_elem : ∃ x ∈ T, n + 1 ≤ (k + 1) * x := by
        by_cases ha_n : (k + 1) * a = n
        · have hb_ge := (h_elem b hb).1
          have hb_ne : (k + 1) * b ≠ n := fun h => h_not_both ⟨ha_n, h⟩
          use b, hb
          omega
        · have ha_ge := (h_elem a ha).1
          use a, ha
          omega
      obtain ⟨x, hxT, hx_ge⟩ := h_strict_elem
      have h_sum_split : (k + 1) * T.sum id = (k + 1) * x + ∑ y ∈ T.erase x, (k + 1) * y := by
        rw [Finset.mul_sum]
        dsimp
        exact (Finset.add_sum_erase T (fun z => (k + 1) * z) hxT).symm
      have h_rest_ge : (T.card - 1) * n ≤ ∑ y ∈ T.erase x, (k + 1) * y := by
        have h1 : (∑ y ∈ T.erase x, n) ≤ ∑ y ∈ T.erase x, (k + 1) * y := by
          apply Finset.sum_le_sum
          intro y hy
          have hyT := Finset.mem_of_mem_erase hy
          exact (h_elem y hyT).1
        have h2 : (∑ y ∈ T.erase x, n) = (T.card - 1) * n := by
          simp [Finset.card_erase_of_mem hxT]
        rw [h2] at h1
        exact h1
      have h_kn_le : k * n ≤ (T.card - 1) * n := Nat.mul_le_mul_right n (by omega)
      have h_sum_lower : (n + 1) + k * n ≤ (k + 1) * x + ∑ y ∈ T.erase x, (k + 1) * y := by omega
      have h_kn_add : (k + 1) * n + 1 = (n + 1) + k * n := by
        rw [add_mul, one_mul]
        omega
      have h_lhs : (k + 1) * n + 1 ≤ (k + 1) * T.sum id := by
        rw [h_sum_split, h_kn_add]
        exact h_sum_lower
      rw [hTsum] at h_lhs
      rw [add_mul, one_mul] at h_lhs
      omega

/-- The upper-half interval [(n+1)/2, n-1] is the special case k = 1. -/
theorem upper_half_subset_sum_free (n : ℕ) (hn : 2 ≤ n) :
    AvoidsSubsetSum (Finset.Ico ((n + 1) / 2) n) n := by
  have h_eq : Finset.Ico ((n + 1) / 2) n = intervalBlock n 1 := by
    ext x
    simp only [intervalBlock, Finset.mem_Ico, Finset.mem_filter]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨⟨by omega, h2⟩, ?_, by omega⟩
      omega
    · intro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨by omega, h2⟩
  rw [h_eq]
  exact interval_block_avoids_subset_sum n 1 hn (by omega)

/-- Small remainder set: elements x with (s + 1) * x < n. -/
def smallRemainder (n s : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun x => (s + 1) * x < n)

lemma small_remainder_lt_square (n s x : ℕ) (hs : 1 ≤ s) (hns : n ≤ s ^ 3)
    (hx : (s + 1) * x < n) : x < s ^ 2 := by
  have h_cube : s ^ 3 = s * (s * s) := by ring
  have h_sq : s ^ 2 = s * s := by ring
  rw [h_cube] at hns
  rw [h_sq]
  by_contra h_not
  push Not at h_not
  have h1 : (s + 1) * (s * s) ≤ (s + 1) * x := Nat.mul_le_mul_left (s + 1) h_not
  have h2 : s * (s * s) < (s + 1) * (s * s) := by
    have h_pos : 0 < s * s := by
      have : 0 < s := by omega
      exact Nat.mul_pos this this
    have : (s + 1) * (s * s) = s * (s * s) + (s * s) := by
      rw [add_mul, one_mul]
    rw [this]
    omega
  omega

/-- Small block C_j: subset of smallRemainder in the interval [j*s, (j+1)*s - 1]. -/
def smallBlock (n s j : ℕ) : Finset ℕ :=
  (smallRemainder n s).filter (fun x => j * s ≤ x ∧ x < (j + 1) * s)

lemma small_block_card_le (n s j : ℕ) : (smallBlock n s j).card ≤ s := by
  have h_sub : smallBlock n s j ⊆ Finset.Ico (j * s) ((j + 1) * s) := by
    intro x hx
    simp only [smallBlock, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact hx.2
  have h_card := Finset.card_le_card h_sub
  rw [Nat.card_Ico] at h_card
  have : (j + 1) * s - j * s = s := by
    rw [add_mul, one_mul]
    omega
  rw [this] at h_card
  exact h_card

/-- General lemma: any block C with cardinality ≤ s whose elements satisfy (s+1)*x < n
    avoids subset sums to n. -/
lemma small_card_block_avoids_subset_sum (C : Finset ℕ) (n s : ℕ) (hn : 2 ≤ n)
    (hC : C.card ≤ s) (h_elem : ∀ x ∈ C, (s + 1) * x < n) :
    AvoidsSubsetSum C n := by
  intro ⟨T, hTsub, hTsum⟩
  by_cases h0 : T.card = 0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp at hTsum
    omega
  · have h_bound : ∀ x ∈ T, (s + 1) * x ≤ n - 1 := by
      intro x hx
      have := h_elem x (hTsub hx)
      omega
    have h_card_T : T.card ≤ s := (Finset.card_le_card hTsub).trans hC
    have h_sum_le : (s + 1) * T.sum id ≤ s * (n - 1) := by
      rw [Finset.mul_sum]
      dsimp
      have h_sum := Finset.sum_le_sum (fun x hx => h_bound x hx)
      have h_const : (∑ x ∈ T, (n - 1)) = T.card * (n - 1) := by simp
      rw [h_const] at h_sum
      have h_card_mul : T.card * (n - 1) ≤ s * (n - 1) := Nat.mul_le_mul_right (n - 1) h_card_T
      exact h_sum.trans h_card_mul
    rw [hTsum] at h_sum_le
    have h_strict : s * (n - 1) < (s + 1) * n := by
      calc
        s * (n - 1) ≤ s * n := Nat.mul_le_mul_left s (by omega)
        _ < (s + 1) * n := by
          rw [add_mul, one_mul]
          omega
    omega

lemma small_block_avoids_subset_sum (n s j : ℕ) (hn : 2 ≤ n) :
    AvoidsSubsetSum (smallBlock n s j) n := by
  apply small_card_block_avoids_subset_sum (smallBlock n s j) n s hn (small_block_card_le n s j)
  intro x hx
  simp only [smallBlock, smallRemainder, Finset.mem_filter, Finset.mem_Ico] at hx
  exact hx.1.2

/-- Explicit coloring for n ≤ s^3 into 2*s colors. -/
def explicitColoring (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hns : n ≤ s ^ 3) (x : ℕ) : Fin (2 * s) :=
  if hx : 1 ≤ x ∧ x < n then
    if h_small : (s + 1) * x < n then
      have h_lt_sq := small_remainder_lt_square n s x hs hns h_small
      have h_div_lt : x / s < s := by
        have h_sq : s ^ 2 = s * s := by ring
        rw [h_sq] at h_lt_sq
        exact Nat.div_lt_of_lt_mul h_lt_sq
      ⟨s + x / s, by omega⟩
    else
      have h_n_le : n ≤ (s + 1) * x := by omega
      have h_x_pos : 0 < x := by omega
      have h_k_ge : 1 ≤ (n - 1) / x := by
        apply Nat.div_pos
        · omega
        · exact h_x_pos
      have h_k_le : (n - 1) / x ≤ s := by
        have : n - 1 < (s + 1) * x := by omega
        rw [Nat.mul_comm (s + 1) x] at this
        have := Nat.div_lt_of_lt_mul this
        omega
      ⟨(n - 1) / x - 1, by omega⟩
  else
    ⟨0, by omega⟩

/-- Cubic root theorem: For any n ≥ 2 and s ≥ 1 with n ≤ s^3,
    there exists a coloring of {1, ..., n-1} with 2*s colors avoiding monochromatic subset sum n. -/
theorem exists_coloring_of_le_cube (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hns : n ≤ s ^ 3) :
    ∃ c : ℕ → Fin (2 * s), AvoidsMonoSubsetSum n (2 * s) c := by
  use explicitColoring n s hn hs hns
  intro color
  let class_set := (Finset.Ico 1 n).filter (fun x => explicitColoring n s hn hs hns x = color)
  by_cases h_col : color.val < s
  · let k := color.val + 1
    have hk_ge : 1 ≤ k := by omega
    have hk_le : k ≤ s := by omega
    have h_sub : class_set ⊆ intervalBlock n k := by
      intro x hx
      simp only [class_set, Finset.mem_filter, Finset.mem_Ico] at hx
      rcases hx with ⟨⟨h1, h2⟩, hc⟩
      simp only [explicitColoring, and_true, h1, h2, ↓reduceDIte] at hc
      split_ifs at hc with h_small
      · exfalso
        have hc_val := congr_arg Fin.val hc
        dsimp at hc_val
        have : s ≤ s + x / s := Nat.le_add_right s (x / s)
        omega
      · simp only [Finset.mem_filter, Finset.mem_Ico, intervalBlock]
        refine ⟨⟨h1, h2⟩, ?_⟩
        have hc_val := congr_arg Fin.val hc
        dsimp at hc_val
        have hx_pos : 0 < x := by omega
        have h_div_pos : 1 ≤ (n - 1) / x := by
          apply Nat.div_pos
          · omega
          · exact hx_pos
        have h_k_eq : (n - 1) / x = k := by omega
        have h_div_mod := Nat.div_add_mod (n - 1) x
        have h_mod := Nat.mod_lt (n - 1) hx_pos
        rw [h_k_eq] at h_div_mod
        rw [Nat.mul_comm x k] at h_div_mod
        rw [Nat.add_mul, Nat.one_mul]
        omega
    exact avoids_subset_sum_of_subset h_sub (interval_block_avoids_subset_sum n k hn hk_ge)
  · have h_col_ge : s ≤ color.val := by omega
    let j := color.val - s
    have hj_lt : j < s := by
      have := color.isLt
      omega
    have h_sub : class_set ⊆ smallBlock n s j := by
      intro x hx
      simp only [class_set, Finset.mem_filter, Finset.mem_Ico] at hx
      rcases hx with ⟨⟨h1, h2⟩, hc⟩
      simp only [explicitColoring, and_true, h1, h2, ↓reduceDIte] at hc
      split_ifs at hc with h_small
      · simp only [smallBlock, smallRemainder, Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨⟨h1, h2⟩, h_small⟩, ?_⟩
        have hc_val := congr_arg Fin.val hc
        dsimp at hc_val
        have hj_eq : x / s = j := by omega
        have hs_pos : 0 < s := by omega
        have h_div_mod := Nat.div_add_mod x s
        have h_mod := Nat.mod_lt x hs_pos
        rw [hj_eq] at h_div_mod
        rw [Nat.mul_comm s j] at h_div_mod
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · exfalso
        have hc_val := congr_arg Fin.val hc
        dsimp at hc_val
        have hx_pos : 0 < x := by omega
        have : (n - 1) / x ≤ s := by
          have : n - 1 < (s + 1) * x := by omega
          rw [Nat.mul_comm (s + 1) x] at this
          have := Nat.div_lt_of_lt_mul this
          omega
        omega
    exact avoids_subset_sum_of_subset h_sub (small_block_avoids_subset_sum n s j hn)

/-!
### Section 2: General Sieve-Remainder Upper Bound

Given any finite set P with elements not dividing n (e.g. primes p ≤ s with p ∤ n),
the remaining elements R = {x ∈ {1, ..., n-1} | (s+1)*x < n ∧ ∀ p ∈ P, ¬ p ∣ x}
can be partitioned into ⌈|R|/s⌉ blocks of size at most s.
Together with s interval blocks and |P| divisibility blocks, this yields a valid coloring
using s + |P| + ⌈|R|/s⌉ colors, WITHOUT requiring n ≤ s^3.
-/

/-- Covering principle: any family of m ≥ 1 subset-sum-avoiding sets covering {1, ..., n-1}
    induces an m-coloring avoiding monochromatic subset sums. -/
lemma exists_coloring_of_avoiding_family {n m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Finset ℕ)
    (hS_avoid : ∀ i : Fin m, AvoidsSubsetSum (S i) n)
    (hS_cover : ∀ x ∈ Finset.Ico 1 n, ∃ i : Fin m, x ∈ S i) :
    ∃ c : ℕ → Fin m, AvoidsMonoSubsetSum n m c := by
  let c : ℕ → Fin m := fun x =>
    if hx : x ∈ Finset.Ico 1 n then
      Classical.choose (hS_cover x hx)
    else
      ⟨0, by omega⟩
  use c
  intro col
  have h_sub : (Finset.Ico 1 n).filter (fun x => c x = col) ⊆ S col := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have hx_mem := hx.1
    have hc := hx.2
    dsimp [c] at hc
    rw [dif_pos hx_mem] at hc
    have h_spec := Classical.choose_spec (hS_cover x hx_mem)
    rw [hc] at h_spec
    exact h_spec
  exact avoids_subset_sum_of_subset h_sub (hS_avoid col)

lemma div_lt_div_ceil {i K s : ℕ} (hs : 1 ≤ s) (hi : i < K) :
    i / s < (K + s - 1) / s := by
  have hs_pos : 0 < s := by omega
  have h1 : i ≤ K - 1 := by omega
  have h2 : i + s ≤ K + s - 1 := by omega
  have h3 : (i + s) / s ≤ (K + s - 1) / s := Nat.div_le_div_right h2
  have h4 : (i + s) / s = i / s + 1 := Nat.add_div_right i hs_pos
  omega

/-- Remainder set R after sieving: elements x ∈ {1, ..., n-1} with (s+1)*x < n
    and not divisible by any element of P. -/
def sieveRemainder (n s : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun x => (s + 1) * x < n ∧ ∀ p ∈ P, ¬ p ∣ x)

/-- Sieve block C_j: the j-th block of at most s elements from the enumerated remainder R. -/
noncomputable def sieveBlock (R : Finset ℕ) (s j : ℕ) : Finset ℕ :=
  ((R.toList.drop (j * s)).take s).toFinset

lemma sieve_block_card_le (R : Finset ℕ) (s j : ℕ) :
    (sieveBlock R s j).card ≤ s :=
  (List.toFinset_card_le _).trans (List.length_take_le _ _)

lemma sieve_block_subset (R : Finset ℕ) (s j : ℕ) :
    sieveBlock R s j ⊆ R := by
  intro x hx
  simp only [sieveBlock, List.mem_toFinset] at hx
  have h_drop := List.mem_of_mem_take hx
  have h_l := List.mem_of_mem_drop h_drop
  rw [Finset.mem_toList] at h_l
  exact h_l

lemma mem_sieve_block_of_mem {R : Finset ℕ} {s : ℕ} (hs : 1 ≤ s) {x : ℕ} (hx : x ∈ R) :
    ∃ j < (R.card + s - 1) / s, x ∈ sieveBlock R s j := by
  rw [← Finset.mem_toList] at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  let j := i / s
  let r := i % s
  have hj_lt : j < (R.card + s - 1) / s := by
    rw [Finset.length_toList] at hi
    exact div_lt_div_ceil hs hi
  use j, hj_lt
  simp only [sieveBlock, List.mem_toFinset]
  apply List.mem_iff_getElem.mpr
  have hr_lt_s : r < s := Nat.mod_lt i (by omega)
  have hr_lt_drop : r < (R.toList.drop (j * s)).length := by
    rw [List.length_drop]
    have h_div_mod : s * (i / s) + i % s = i := Nat.div_add_mod i s
    have : j * s + r = i := by
      dsimp [j, r]
      rw [Nat.mul_comm]
      exact h_div_mod
    omega
  have hr_lt : r < ((R.toList.drop (j * s)).take s).length := by
    rw [List.length_take]
    omega
  use r, hr_lt
  rw [List.getElem_take, List.getElem_drop]
  congr 1
  have h_div_mod : s * (i / s) + i % s = i := Nat.div_add_mod i s
  have : j * s + r = i := by
    dsimp [j, r]
    rw [Nat.mul_comm]
    exact h_div_mod
  exact this

lemma sieve_block_avoids_subset_sum (n s : ℕ) (P : Finset ℕ) (j : ℕ) (hn : 2 ≤ n) :
    AvoidsSubsetSum (sieveBlock (sieveRemainder n s P) s j) n := by
  apply small_card_block_avoids_subset_sum (sieveBlock (sieveRemainder n s P) s j) n s hn
  · exact sieve_block_card_le _ s j
  · intro x hx
    have h_sub := sieve_block_subset (sieveRemainder n s P) s j hx
    simp only [sieveRemainder, Finset.mem_filter] at h_sub
    exact h_sub.2.1

/-- The combined family of sets indexing interval blocks, divisibility blocks, and sieve blocks. -/
noncomputable def sieveFamily (n s : ℕ) (P : Finset ℕ) (i : ℕ) : Finset ℕ :=
  if i < s then
    intervalBlock n (i + 1)
  else if i < s + P.card then
    (Finset.Ico 1 n).filter (fun x => P.toList[i - s]! ∣ x)
  else
    sieveBlock (sieveRemainder n s P) s (i - (s + P.card))

/-- Sieve Remainder Theorem (Alon–Erdős 1996, Section 2):
    Given n ≥ 2, s ≥ 1, and a finite set P of elements not dividing n,
    there exists a coloring of {1, ..., n-1} with
    s + |P| + ⌈|R| / s⌉ colors avoiding monochromatic subset sums to n,
    where R = {x ∈ {1, ..., n-1} | (s+1)*x < n ∧ ∀ p ∈ P, ¬ p ∣ x}.
    This combinatorial theorem does NOT require n ≤ s^3. -/
theorem exists_coloring_sieve (n s : ℕ) (P : Finset ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    ∃ c : ℕ → Fin (s + P.card + ((sieveRemainder n s P).card + s - 1) / s),
      AvoidsMonoSubsetSum n (s + P.card + ((sieveRemainder n s P).card + s - 1) / s) c := by
  have hm : 1 ≤ s + P.card + ((sieveRemainder n s P).card + s - 1) / s :=
    hs.trans ((Nat.le_add_right s P.card).trans (Nat.le_add_right (s + P.card) _))
  let S : Fin (s + P.card + ((sieveRemainder n s P).card + s - 1) / s) → Finset ℕ :=
    fun i => sieveFamily n s P i.val
  apply exists_coloring_of_avoiding_family hm S
  · intro i
    dsimp [S, sieveFamily]
    split_ifs with h1 h2
    · exact interval_block_avoids_subset_sum n (i.val + 1) hn (by omega)
    · have h_len : i.val - s < P.toList.length := by
        rw [Finset.length_toList]
        omega
      rw [getElem!_pos P.toList (i.val - s) h_len]
      apply dvd_subset_sum_free _ (P.toList[i.val - s]) n
      · have hp_mem : P.toList[i.val - s] ∈ P := by
          rw [← Finset.mem_toList]
          apply List.mem_iff_getElem.mpr
          exact ⟨i.val - s, h_len, rfl⟩
        exact hP _ hp_mem
      · intro x hx
        simp only [Finset.mem_filter] at hx
        exact hx.2
    · exact sieve_block_avoids_subset_sum n s P (i.val - (s + P.card)) hn
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    by_cases h_large : n ≤ (s + 1) * x
    · have hx_pos : 0 < x := by omega
      let k := (n - 1) / x
      have hk_ge : 1 ≤ k := by
        apply Nat.div_pos
        · omega
        · exact hx_pos
      have hk_le : k ≤ s := by
        have : n - 1 < (s + 1) * x := by omega
        rw [Nat.mul_comm (s + 1) x] at this
        have := Nat.div_lt_of_lt_mul this
        omega
      let i_val := k - 1
      have hi_s : i_val < s := by omega
      have hi_lt : i_val < s + P.card + ((sieveRemainder n s P).card + s - 1) / s :=
        hi_s.trans_le ((Nat.le_add_right s P.card).trans (Nat.le_add_right (s + P.card) _))
      use ⟨i_val, hi_lt⟩
      dsimp [S, sieveFamily]
      rw [if_pos hi_s]
      have hk_eq : i_val + 1 = k := by omega
      rw [hk_eq]
      simp only [intervalBlock, Finset.mem_filter, Finset.mem_Ico, hx, true_and]
      refine ⟨?_, ?_⟩
      · have h_div_mod := Nat.div_add_mod (n - 1) x
        have h_mod := Nat.mod_lt (n - 1) hx_pos
        rw [Nat.mul_comm x k] at h_div_mod
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have : (n - 1) / x * x ≤ n - 1 := Nat.div_mul_le_self (n - 1) x
        have : k * x ≤ n - 1 := this
        omega
    · have h_small : (s + 1) * x < n := by omega
      by_cases h_div : ∃ p ∈ P, p ∣ x
      · obtain ⟨p, hpP, hpx⟩ := h_div
        rw [← Finset.mem_toList] at hpP
        obtain ⟨idx, h_idx, rfl⟩ := List.mem_iff_getElem.mp hpP
        have h_idx_card : idx < P.card := by
          have := h_idx
          rw [Finset.length_toList] at this
          exact this
        let i_val := s + idx
        have hi_lt_sp : i_val < s + P.card := by omega
        have hi_lt : i_val < s + P.card + ((sieveRemainder n s P).card + s - 1) / s :=
          hi_lt_sp.trans_le (Nat.le_add_right (s + P.card) _)
        use ⟨i_val, hi_lt⟩
        dsimp [S, sieveFamily]
        have h1_not : ¬ i_val < s := by omega
        rw [if_neg h1_not, if_pos hi_lt_sp]
        have h_idx_eq : i_val - s = idx := by omega
        rw [h_idx_eq]
        rw [getElem!_pos P.toList idx h_idx]
        simp only [Finset.mem_filter, Finset.mem_Ico, hx, hpx, and_self]
      · push Not at h_div
        have hxR : x ∈ sieveRemainder n s P := by
          simp only [sieveRemainder, Finset.mem_filter, Finset.mem_Ico]
          exact ⟨hx, h_small, h_div⟩
        obtain ⟨j, hj_lt, hxj⟩ := mem_sieve_block_of_mem hs hxR
        let i_val := s + P.card + j
        have hi_lt : i_val < s + P.card + ((sieveRemainder n s P).card + s - 1) / s :=
          Nat.add_lt_add_left hj_lt (s + P.card)
        use ⟨i_val, hi_lt⟩
        dsimp [S, sieveFamily]
        have h1_not : ¬ i_val < s := by omega
        have h2_not : ¬ i_val < s + P.card := by omega
        rw [if_neg h1_not, if_neg h2_not]
        have hj_eq : i_val - (s + P.card) = j := by omega
        rw [hj_eq]
        exact hxj

def HasValidColoring (n k : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, AvoidsMonoSubsetSum n k c

lemma exists_valid_coloring (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, HasValidColoring n k := by
  have hs : 1 ≤ n := by omega
  have hns : n ≤ n ^ 3 := by
    calc
      n = n ^ 1 := by rw [pow_one]
      _ ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨c, hc⟩ := exists_coloring_of_le_cube n n hn hs hns
  exact ⟨2 * n, c, hc⟩

/-- The chromatic number f(n): the minimal number of colors needed to avoid monochromatic subset sum n. -/
noncomputable def minColors (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  Nat.find (exists_valid_coloring n hn)

theorem minColors_has_coloring (n : ℕ) (hn : 2 ≤ n) :
    HasValidColoring n (minColors n hn) :=
  Nat.find_spec (exists_valid_coloring n hn)

theorem minColors_le (n : ℕ) (hn : 2 ≤ n) {k : ℕ} (hk : HasValidColoring n k) :
    minColors n hn ≤ k :=
  Nat.find_min' (exists_valid_coloring n hn) hk

/-- Discrete cubic root upper bound: for any s ≥ 1 with n ≤ s^3, f(n) ≤ 2*s.
    In particular, taking s = ⌈n^(1/3)⌉ yields f(n) ≤ 2⌈n^(1/3)⌉. -/
theorem minColors_le_two_mul_s (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hns : n ≤ s ^ 3) :
    minColors n hn ≤ 2 * s := by
  obtain ⟨c, hc⟩ := exists_coloring_of_le_cube n s hn hs hns
  exact minColors_le n hn ⟨c, hc⟩

/-- Upper bound on the chromatic number f(n) from the sieve-remainder theorem:
    f(n) ≤ s + |P| + ⌈|R| / s⌉ for any s ≥ 1 and finite set P not dividing n. -/
theorem minColors_le_sieve (n s : ℕ) (P : Finset ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    minColors n hn ≤ s + P.card + ((sieveRemainder n s P).card + s - 1) / s := by
  obtain ⟨c, hc⟩ := exists_coloring_sieve n s P hn hs hP
  exact minColors_le n hn ⟨c, hc⟩

/-!
### Section 3: Prime Set Specialization and Selberg Bounding Sieve

We specialize the general sieve-remainder theorem by taking the prime set
  P = {p ≤ s | p.Prime ∧ ¬ p ∣ n}.
This satisfies:
1. ∀ p ∈ P, ¬ p ∣ n, and |P| ≤ s.
2. Hence f(n) ≤ 2s + ⌈|R| / s⌉.
3. The remainder set R is exactly the set of x ∈ {1, ..., ⌊(n-1)/(s+1)⌋} coprime to D = ∏_{p ∈ P} p.
4. We instantiate Mathlib's standard `BoundingSieve` framework, connecting R.card to `siftedSum`,
   deriving the general upper Moebius bound with main and error terms,
   and proving that the divisor counting error |rem(d)| ≤ 1 for all d ∈ D.divisors.
-/

/-- The specialized set of primes p ≤ s that do not divide n. -/
def sievePrimes (n s : ℕ) : Finset ℕ :=
  (Finset.Icc 2 s).filter (fun p => Nat.Prime p ∧ ¬ p ∣ n)

lemma sieve_primes_card_le (n s : ℕ) :
    (sievePrimes n s).card ≤ s := by
  have h_sub : sievePrimes n s ⊆ Finset.Icc 2 s := Finset.filter_subset _ _
  have h_le := Finset.card_le_card h_sub
  rw [Nat.card_Icc] at h_le
  omega

lemma sieve_primes_not_dvd (n s : ℕ) :
    ∀ p ∈ sievePrimes n s, ¬ p ∣ n := by
  intro p hp
  simp only [sievePrimes, Finset.mem_filter] at hp
  exact hp.2.2

/-- Specialized sieve upper bound: f(n) ≤ 2s + ⌈|R| / s⌉ where P = sievePrimes n s. -/
theorem minColors_le_two_s_add_remainder (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    minColors n hn ≤ 2 * s + ((sieveRemainder n s (sievePrimes n s)).card + s - 1) / s := by
  have h_sieve := minColors_le_sieve n s (sievePrimes n s) hn hs (sieve_primes_not_dvd n s)
  have h_card := sieve_primes_card_le n s
  omega

lemma coprime_prod_primes_iff (n s x : ℕ) :
    (∏ p ∈ sievePrimes n s, p).Coprime x ↔ ∀ p ∈ sievePrimes n s, ¬ p ∣ x := by
  rw [Nat.coprime_prod_left_iff]
  refine forall₂_congr (fun p hp => ?_)
  simp only [sievePrimes, Finset.mem_filter] at hp
  exact hp.2.1.coprime_iff_not_dvd

lemma sieve_remainder_eq_coprime_filter (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    sieveRemainder n s (sievePrimes n s) =
      (Finset.Icc 1 ((n - 1) / (s + 1))).filter (fun x => (∏ p ∈ sievePrimes n s, p).Coprime x) := by
  let P := sievePrimes n s
  let m := (n - 1) / (s + 1)
  let D := ∏ p ∈ P, p
  ext x
  simp only [sieveRemainder, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
  rw [coprime_prod_primes_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h_small, h_coprime⟩
    refine ⟨⟨h1, ?_⟩, h_coprime⟩
    have : x * (s + 1) ≤ n - 1 := by
      rw [Nat.mul_comm]
      omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr this
  · rintro ⟨⟨h1, h2⟩, h_coprime⟩
    have h_le_mul := (Nat.le_div_iff_mul_le (by omega)).mp h2
    have h_small : (s + 1) * x < n := by
      rw [Nat.mul_comm]
      omega
    have h_x_lt_n : x < n := by
      have : x ≤ (s + 1) * x := Nat.le_mul_of_pos_left x (by omega)
      omega
    exact ⟨⟨h1, h_x_lt_n⟩, h_small, h_coprime⟩

lemma squarefree_prod_of_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  have hne : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)
  apply squarefree_of_factorization_le_one hne
  intro q
  rw [factorization_prod (fun p hp => (hs p hp).ne_zero)]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  have h_term : ∀ p ∈ s, (p.factorization) q = if p = q then 1 else 0 := by
    intro p hp
    rw [(hs p hp).factorization]
    simp only [Finsupp.single_apply]
  have h_sum : (∑ p ∈ s, p.factorization q) = ∑ p ∈ s, if p = q then 1 else 0 := by
    apply sum_congr rfl h_term
  rw [h_sum]
  by_cases hq : q ∈ s
  · rw [sum_ite_eq' s q (fun _ => 1)]
    simp only [hq, ↓reduceIte, le_refl]
  · rw [sum_ite_eq' s q (fun _ => 1)]
    simp only [hq, ↓reduceIte, zero_le_one]

noncomputable def unitDensity : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else 1 / (n : ℝ)
  map_zero' := by simp

lemma unitDensity_isMultiplicative : unitDensity.IsMultiplicative := by
  refine ⟨by simp [unitDensity], ?_⟩
  intro m n hmn
  dsimp [unitDensity]
  by_cases hm : m = 0
  · subst hm; simp
  · by_cases hn : n = 0
    · subst hn; simp
    · have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
      rw [if_neg hmn0, if_neg hm, if_neg hn]
      push_cast
      rw [one_div_mul_one_div]

lemma unitDensity_pos_of_prime (p : ℕ) (hp : Nat.Prime p) :
    0 < unitDensity p := by
  dsimp [unitDensity]
  rw [if_neg hp.ne_zero]
  have : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  exact one_div_pos.mpr this

lemma unitDensity_lt_one_of_prime (p : ℕ) (hp : Nat.Prime p) :
    unitDensity p < 1 := by
  dsimp [unitDensity]
  rw [if_neg hp.ne_zero]
  have hp2 : (1 : ℝ) < (p : ℝ) := by
    norm_cast
    have := hp.two_le
    omega
  rw [one_div]
  exact inv_lt_one_of_one_lt₀ hp2

/-- Instantiation of Mathlib's BoundingSieve for the Erdős remainder set. -/
noncomputable def erdosBoundingSieve (n s : ℕ) : BoundingSieve where
  support := Finset.Icc 1 ((n - 1) / (s + 1))
  prodPrimes := ∏ p ∈ sievePrimes n s, p
  prodPrimes_squarefree := by
    apply squarefree_prod_of_primes
    intro p hp
    simp only [sievePrimes, Finset.mem_filter] at hp
    exact hp.2.1
  weights := fun _ => 1
  weights_nonneg := fun _ => by positivity
  totalMass := (((n - 1) / (s + 1) : ℕ) : ℝ)
  nu := unitDensity
  nu_mult := unitDensity_isMultiplicative
  nu_pos_of_prime := fun p hp _ => unitDensity_pos_of_prime p hp
  nu_lt_one_of_prime := fun p hp _ => unitDensity_lt_one_of_prime p hp

theorem siftedSum_eq_card_remainder (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    (erdosBoundingSieve n s).siftedSum = ((sieveRemainder n s (sievePrimes n s)).card : ℝ) := by
  dsimp [BoundingSieve.siftedSum, erdosBoundingSieve]
  rw [sum_boole]
  rw [← sieve_remainder_eq_coprime_filter n s hn hs]

theorem card_remainder_le_mainSum_errSum (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (muPlus : ℕ → ℝ) (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    ((sieveRemainder n s (sievePrimes n s)).card : ℝ) ≤
      (erdosBoundingSieve n s).totalMass * @BoundingSieve.mainSum (erdosBoundingSieve n s) muPlus +
        @BoundingSieve.errSum (erdosBoundingSieve n s) muPlus := by
  rw [← siftedSum_eq_card_remainder n s hn hs]
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus hmu

lemma Icc_one_eq_Ioc_zero (m : ℕ) : Finset.Icc 1 m = Finset.Ioc 0 m := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma card_Icc_filter_dvd (m d : ℕ) :
    ((Finset.Icc 1 m).filter (fun x => d ∣ x)).card = m / d := by
  rw [Icc_one_eq_Ioc_zero]
  exact Ioc_filter_dvd_card_eq_div m d

lemma erdos_multSum_eq (n s d : ℕ) :
    (erdosBoundingSieve n s).multSum d = ((((n - 1) / (s + 1)) / d : ℕ) : ℝ) := by
  dsimp [BoundingSieve.multSum, erdosBoundingSieve]
  rw [sum_boole]
  rw [card_Icc_filter_dvd]

lemma erdos_rem_eq (n s d : ℕ) (hd : 1 ≤ d) :
    (erdosBoundingSieve n s).rem d =
      ((((n - 1) / (s + 1)) / d : ℕ) : ℝ) - ((((n - 1) / (s + 1) : ℕ) : ℝ) / (d : ℝ)) := by
  rw [BoundingSieve.rem, erdos_multSum_eq]
  dsimp [erdosBoundingSieve, unitDensity]
  rw [if_neg (by omega)]
  ring

lemma abs_nat_div_sub_div_le_one (m d : ℕ) (hd : 1 ≤ d) :
    |(((m / d : ℕ) : ℝ) - (m : ℝ) / (d : ℝ))| ≤ 1 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
  have h_div_mod : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
  have h_cast : (m : ℝ) = (d : ℝ) * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) := by
    exact_mod_cast h_div_mod
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have h_sub : ((m / d : ℕ) : ℝ) - (m : ℝ) / (d : ℝ) = - (((m % d : ℕ) : ℝ) / (d : ℝ)) := by
    calc
      ((m / d : ℕ) : ℝ) - (m : ℝ) / (d : ℝ)
        = ((m / d : ℕ) : ℝ) - ((d : ℝ) * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ)) / (d : ℝ) := by rw [h_cast]
      _ = ((m / d : ℕ) : ℝ) - (((d : ℝ) * ((m / d : ℕ) : ℝ) / (d : ℝ)) + ((m % d : ℕ) : ℝ) / (d : ℝ)) := by rw [add_div]
      _ = ((m / d : ℕ) : ℝ) - (((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) / (d : ℝ)) := by rw [mul_div_cancel_left₀ _ hd_ne]
      _ = - (((m % d : ℕ) : ℝ) / (d : ℝ)) := by ring
  rw [h_sub, abs_neg, abs_of_nonneg (by positivity)]
  have h_mod_lt : m % d < d := Nat.mod_lt m (by omega)
  have h_mod_lt_cast : ((m % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast h_mod_lt
  have : ((m % d : ℕ) : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_pos).mpr h_mod_lt_cast
  linarith

theorem erdos_rem_bound (n s d : ℕ) (hd : 1 ≤ d) :
    |(erdosBoundingSieve n s).rem d| ≤ 1 := by
  rw [erdos_rem_eq n s d hd]
  exact abs_nat_div_sub_div_le_one ((n - 1) / (s + 1)) d hd

theorem erdos_rem_bound_of_mem_divisors (n s d : ℕ)
    (hd : d ∈ (erdosBoundingSieve n s).prodPrimes.divisors) :
    |(erdosBoundingSieve n s).rem d| ≤ 1 := by
  have hd_pos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · have h_dvd := (Nat.mem_divisors.mp hd).1
      have h_zero : (erdosBoundingSieve n s).prodPrimes = 0 := Nat.eq_zero_of_zero_dvd h_dvd
      have h_sq := (erdosBoundingSieve n s).prodPrimes_squarefree
      exact False.elim (Squarefree.ne_zero h_sq h_zero)
    · exact hpos
  exact erdos_rem_bound n s d hd_pos

/-!
### Section 4: Finite Selberg Sieve Bound

We optimize the quadratic diagonal form of the Selberg sieve on the Erdős remainder set
$R = \{x \in [1, \lfloor(n-1)/(s+1)\rfloor] \mid \text{Coprime } D \; x\}$, where $D = \prod_{p \in P} p$.
By choosing the canonical normalized Selberg weights $w(d)$ supported on $d \le z$,
we unconditionally prove:
1. $G = \sum_{d \in D.\text{divisors}, d \le z} \text{selbergTerms}(d) \ge 1 > 0$.
2. $\text{mainSum}(\lambda^2 w) = 1 / G$.
3. $|w(d)| \le d$ and $\sum_{d \in D.\text{divisors}} |w(d)| \le z^2$.
4. $\text{errSum}(\lambda^2 w) \le z^4$.
5. The finite Selberg sieve bound:
   $|R| \le \lfloor(n-1)/(s+1)\rfloor / G + z^4$.
-/

def sieveLevelDivisors (n s z : ℕ) : Finset ℕ :=
  ((∏ p ∈ sievePrimes n s, p).divisors).filter (fun d => d ≤ z)

lemma one_mem_sieveLevelDivisors (n s z : ℕ) (hz : 1 ≤ z) :
    1 ∈ sieveLevelDivisors n s z := by
  simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨one_dvd _, ?_⟩, hz⟩
  have h_sq := (erdosBoundingSieve n s).prodPrimes_squarefree
  exact Squarefree.ne_zero h_sq

noncomputable def sieveG (n s z : ℕ) : ℝ :=
  ∑ d ∈ sieveLevelDivisors n s z, (erdosBoundingSieve n s).selbergTerms d

lemma sieveG_ge_one (n s z : ℕ) (hz : 1 ≤ z) :
    1 ≤ sieveG n s z := by
  dsimp [sieveG]
  have h1 : 1 ∈ sieveLevelDivisors n s z := one_mem_sieveLevelDivisors n s z hz
  have h_pos : ∀ d ∈ sieveLevelDivisors n s z, 0 ≤ (erdosBoundingSieve n s).selbergTerms d := by
    intro d hd
    simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
    exact le_of_lt (BoundingSieve.selbergTerms_pos hd.1.1)
  have h_le := Finset.single_le_sum h_pos h1
  have h_one : (erdosBoundingSieve n s).selbergTerms 1 = 1 :=
    BoundingSieve.selbergTerms_isMultiplicative.map_one
  rw [h_one] at h_le
  exact h_le

lemma sieveG_pos (n s z : ℕ) (hz : 1 ≤ z) :
    0 < sieveG n s z := by
  have := sieveG_ge_one n s z hz
  linarith

lemma lambdaSquared_abs_le (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤
      ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
  dsimp [BoundingSieve.lambdaSquared]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  gcongr with d1 hd1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  gcongr with d2 hd2
  split_ifs
  · rw [abs_mul]
  · simp

lemma sum_divisors_lambda_sq_larger_sum (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 else 0) =
    (∑ d ∈ n.divisors, ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
     if d = Nat.lcm d1 d2 then f d1 d2 else 0) := by
  congr! 1 with d hd
  rw [Nat.mem_divisors] at hd
  have h_filter : ∀ d1 d2 : ℕ,
      (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) ↔ (d = d1.lcm d2) := by
    intro d1 d2
    constructor
    · intro h; exact h.2.2
    · rintro rfl; exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩
  simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and]
  congr! 2 with d1 hd1 d2 hd2
  simp only [h_filter d1 d2]

lemma sum_ite_lcm_le (S : Finset ℕ) (d1 d2 : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ d ∈ S, if d = Nat.lcm d1 d2 then a else 0) ≤ a := by
  by_cases h : Nat.lcm d1 d2 ∈ S
  · rw [sum_ite_eq' S (Nat.lcm d1 d2) (fun _ => a)]
    simp only [h, ↓reduceIte, le_refl]
  · rw [sum_ite_eq' S (Nat.lcm d1 d2) (fun _ => a)]
    simp only [h, ↓reduceIte, ha]

theorem errSum_lambdaSquared_le (n s : ℕ) (w : ℕ → ℝ) :
    @BoundingSieve.errSum (erdosBoundingSieve n s) (BoundingSieve.lambdaSquared w) ≤
      (∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors, |w d|) ^ 2 := by
  let D := (erdosBoundingSieve n s).prodPrimes
  calc @BoundingSieve.errSum (erdosBoundingSieve n s) (BoundingSieve.lambdaSquared w)
    _ = ∑ d ∈ D.divisors, |BoundingSieve.lambdaSquared w d| * |(erdosBoundingSieve n s).rem d| := rfl
    _ ≤ ∑ d ∈ D.divisors, |BoundingSieve.lambdaSquared w d| * 1 := by
      gcongr with d hd
      exact erdos_rem_bound_of_mem_divisors n s d hd
    _ = ∑ d ∈ D.divisors, |BoundingSieve.lambdaSquared w d| := by
      congr with d; ring
    _ ≤ ∑ d ∈ D.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
      gcongr with d hd
      exact lambdaSquared_abs_le w d
    _ = ∑ d ∈ D.divisors, ∑ d1 ∈ D.divisors, ∑ d2 ∈ D.divisors,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
      rw [sum_divisors_lambda_sq_larger_sum (fun d1 d2 => |w d1| * |w d2|) D]
    _ = ∑ d1 ∈ D.divisors, ∑ d2 ∈ D.divisors, ∑ d ∈ D.divisors,
          if d = Nat.lcm d1 d2 then |w d1| * |w d2| else 0 := by
      rw [sum_comm]
      congr 1 with d1
      rw [sum_comm]
    _ ≤ ∑ d1 ∈ D.divisors, ∑ d2 ∈ D.divisors, |w d1| * |w d2| := by
      gcongr with d1 hd1 d2 hd2
      apply sum_ite_lcm_le
      positivity
    _ = (∑ d ∈ D.divisors, |w d|) ^ 2 := by
      simp_rw [← mul_sum, ← sum_mul, sq]

noncomputable def selbergWeight (n s z d : ℕ) : ℝ :=
  if d ∣ (erdosBoundingSieve n s).prodPrimes then
    ((ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / sieveG n s z) *
      ∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l),
        (erdosBoundingSieve n s).selbergTerms l
  else
    0

lemma selbergWeight_one (n s z : ℕ) (hz : 1 ≤ z) :
    selbergWeight n s z 1 = 1 := by
  dsimp [selbergWeight]
  have h1_dvd : 1 ∣ (erdosBoundingSieve n s).prodPrimes := one_dvd _
  rw [if_pos h1_dvd]
  have h_mu1 : (ArithmeticFunction.moebius 1 : ℝ) = 1 := by simp
  rw [h_mu1]
  push_cast
  have h_filter : (sieveLevelDivisors n s z).filter (fun l => 1 ∣ l) = sieveLevelDivisors n s z := by
    ext l
    simp only [Finset.mem_filter, one_dvd, and_true]
  rw [h_filter]
  have hG_ne : sieveG n s z ≠ 0 := (sieveG_pos n s z hz).ne'
  dsimp [sieveG]
  ring_nf
  exact div_self hG_ne

lemma selbergWeight_eq_zero_of_gt (n s z d : ℕ) (hd : z < d) :
    selbergWeight n s z d = 0 := by
  dsimp [selbergWeight]
  split_ifs with hdP
  · have h_empty : (sieveLevelDivisors n s z).filter (fun l => d ∣ l) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro l hl
      simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hl
      intro h_dvd
      have hl_ne : l ≠ 0 := by
        rintro rfl
        exact hl.1.2 (Nat.eq_zero_of_zero_dvd hl.1.1)
      have h_le : d ≤ l := Nat.le_of_dvd (Nat.pos_of_ne_zero hl_ne) h_dvd
      omega
    rw [h_empty, sum_empty, mul_zero]
  · rfl

lemma selbergWeight_isUpperMoebius (n s z : ℕ) (hz : 1 ≤ z) :
    BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared (selbergWeight n s z)) :=
  BoundingSieve.upperMoebius_lambdaSquared (selbergWeight n s z) (selbergWeight_one n s z hz)

lemma sum_divisors_moebius_real (k : ℕ) :
    (∑ j ∈ k.divisors, (ArithmeticFunction.moebius j : ℝ)) = if k = 1 then 1 else 0 := by
  have h := ArithmeticFunction.ext_iff.mp (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)) k
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

lemma squarefree_coprime_of_mul_dvd {l j m : ℕ} (hm : Squarefree m) (h : l * j ∣ m) :
    l.Coprime j := by
  have h_sq : Squarefree (l * j) := Squarefree.squarefree_of_dvd h hm
  exact Nat.coprime_of_squarefree_mul h_sq

lemma filter_divisors_dvd_eq_image {l m : ℕ} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ∣ m) :
    (m.divisors.filter (fun d => l ∣ d)) = (m / l).divisors.image (fun j => l * j) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
  constructor
  · rintro ⟨⟨hd_dvd, _⟩, hl_dvd⟩
    refine ⟨d / l, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [Nat.dvd_div_iff_mul_dvd hlm, Nat.mul_comm, Nat.div_mul_cancel hl_dvd]
        exact hd_dvd
      · have h_pos : 0 < m / l :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hlm) (Nat.pos_of_ne_zero hl)
        exact h_pos.ne'
    · rw [Nat.mul_comm, Nat.div_mul_cancel hl_dvd]
  · rintro ⟨j, ⟨hj_dvd, _⟩, rfl⟩
    refine ⟨⟨?_, hm⟩, dvd_mul_right l j⟩
    have := Nat.mul_dvd_mul_left l hj_dvd
    rwa [Nat.mul_div_cancel' hlm] at this

lemma nat_div_eq_one_iff_eq {l m : ℕ} (hl : l ≠ 0) (hlm : l ∣ m) : m / l = 1 ↔ m = l := by
  constructor
  · intro h
    have : l * (m / l) = l * 1 := congr_arg (fun x => l * x) h
    rw [Nat.mul_div_cancel' hlm, mul_one] at this
    exact this
  · rintro rfl
    exact Nat.div_self (Nat.pos_of_ne_zero hl)

lemma sum_moebius_dvd_eq {l m : ℕ} (hl : l ≠ 0) (hlm : l ∣ m) (hm : Squarefree m) :
    (∑ d ∈ m.divisors.filter (fun d => l ∣ d), (ArithmeticFunction.moebius d : ℝ)) =
      if m = l then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  have hm_ne : m ≠ 0 := Squarefree.ne_zero hm
  rw [filter_divisors_dvd_eq_image hl hm_ne hlm]
  have h_inj : Set.InjOn (fun j => l * j) (m / l).divisors := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl) hxy
  rw [Finset.sum_image h_inj]
  have h_term : ∀ j ∈ (m / l).divisors,
      (ArithmeticFunction.moebius (l * j) : ℝ) =
        (ArithmeticFunction.moebius l : ℝ) * (ArithmeticFunction.moebius j : ℝ) := by
    intro j hj
    have hj_dvd : j ∣ m / l := Nat.dvd_of_mem_divisors hj
    have h_mul_dvd : l * j ∣ m := by
      have := Nat.mul_dvd_mul_left l hj_dvd
      rwa [Nat.mul_div_cancel' hlm] at this
    have h_cop := squarefree_coprime_of_mul_dvd hm h_mul_dvd
    have h_mult := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h_cop
    exact_mod_cast h_mult
  rw [Finset.sum_congr rfl h_term]
  rw [← Finset.mul_sum]
  rw [sum_divisors_moebius_real (m / l)]
  have h_iff := nat_div_eq_one_iff_eq hl hlm
  by_cases h : m = l
  · have h1 : m / l = 1 := h_iff.mpr h
    rw [if_pos h1, if_pos h, mul_one]
  · have h1 : m / l ≠ 1 := mt h_iff.mp h
    rw [if_neg h1, if_neg h, mul_zero]

lemma dvd_mem_sieveLevelDivisors {n s z : ℕ} {m d : ℕ}
    (hm : m ∈ sieveLevelDivisors n s z) (hd : d ∣ m) :
    d ∈ sieveLevelDivisors n s z := by
  simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hm ⊢
  have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hm.1.2 hm.1.1
  have hd_le : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
  refine ⟨⟨hd.trans hm.1.1, hm.1.2⟩, by omega⟩

lemma nu_mul_selbergWeight_of_mem {n s z d : ℕ} (hd : d ∈ sieveLevelDivisors n s z) :
    (erdosBoundingSieve n s).nu d * selbergWeight n s z d =
      (ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m := by
  have hd_div : d ∈ (erdosBoundingSieve n s).prodPrimes.divisors := by
    simp only [sieveLevelDivisors, Finset.mem_filter] at hd
    exact hd.1
  have hd_dvd : d ∣ (erdosBoundingSieve n s).prodPrimes := Nat.dvd_of_mem_divisors hd_div
  dsimp [selbergWeight]
  rw [if_pos hd_dvd]
  dsimp [erdosBoundingSieve, unitDensity]
  have hd0 : d ≠ 0 := by
    have hD0 := (erdosBoundingSieve n s).prodPrimes_ne_zero
    exact ne_zero_of_dvd_ne_zero hD0 hd_dvd
  rw [if_neg hd0]
  have hd_cast : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  calc (1 / (d : ℝ)) * ((ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m)
    _ = (1 / (d : ℝ) * (d : ℝ)) * ((ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m) := by ring
    _ = 1 * ((ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m) := by
      rw [one_div_mul_cancel hd_cast]
    _ = (ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m := by ring

lemma nu_mul_selbergWeight_of_not_mem {n s z d : ℕ}
    (hd_div : d ∈ (erdosBoundingSieve n s).prodPrimes.divisors)
    (hnd : d ∉ sieveLevelDivisors n s z) :
    (erdosBoundingSieve n s).nu d * selbergWeight n s z d = 0 := by
  have hz : z < d := by
    simp only [sieveLevelDivisors, Finset.mem_filter, not_and] at hnd
    have := hnd hd_div
    omega
  rw [selbergWeight_eq_zero_of_gt n s z d hz, mul_zero]

lemma sum_divisors_nu_mul_selbergWeight_eq (n s z l : ℕ) :
    (∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors,
      if l ∣ d then (erdosBoundingSieve n s).nu d * selbergWeight n s z d else 0) =
    (∑ d ∈ sieveLevelDivisors n s z,
      if l ∣ d then (erdosBoundingSieve n s).nu d * selbergWeight n s z d else 0) := by
  let D := (erdosBoundingSieve n s).prodPrimes
  have h_sub : sieveLevelDivisors n s z ⊆ D.divisors := Finset.filter_subset _ _
  rw [← Finset.sum_subset h_sub]
  intro d hd_div hd_not_mem
  have := nu_mul_selbergWeight_of_not_mem hd_div hd_not_mem
  split_ifs
  · exact this
  · rfl

lemma sum_moebius_sieveLevel_eq {n s z l m : ℕ}
    (hl0 : l ≠ 0) (hm : m ∈ sieveLevelDivisors n s z) :
    (∑ d ∈ sieveLevelDivisors n s z, if l ∣ d ∧ d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0) =
      if m = l then (ArithmeticFunction.moebius l : ℝ) else 0 := by
  have hm_div : m ∈ (erdosBoundingSieve n s).prodPrimes.divisors := by
    simp only [sieveLevelDivisors, Finset.mem_filter] at hm
    exact hm.1
  have hm_dvd : m ∣ (erdosBoundingSieve n s).prodPrimes := Nat.dvd_of_mem_divisors hm_div
  have hm_sq : Squarefree m :=
    Squarefree.squarefree_of_dvd hm_dvd (erdosBoundingSieve n s).prodPrimes_squarefree
  have hm0 : m ≠ 0 := Squarefree.ne_zero hm_sq
  by_cases hlm : l ∣ m
  · have h_sub : m.divisors.filter (fun d => l ∣ d) ⊆ sieveLevelDivisors n s z := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact dvd_mem_sieveLevelDivisors hm hd.1.1
    rw [← Finset.sum_subset h_sub]
    · rw [← sum_moebius_dvd_eq hl0 hlm hm_sq]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [if_pos ⟨hd.2, hd.1.1⟩]
    · intro d hd_L hd_not_mem
      have : ¬(l ∣ d ∧ d ∣ m) := by
        intro ⟨hld, hdm⟩
        apply hd_not_mem
        simp only [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hdm, hm0⟩, hld⟩
      rw [if_neg this]
  · have h_eq_zero : (∑ d ∈ sieveLevelDivisors n s z, if l ∣ d ∧ d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      have : ¬(l ∣ d ∧ d ∣ m) := by
        intro ⟨hld, hdm⟩
        exact hlm (hld.trans hdm)
      rw [if_neg this]
    rw [h_eq_zero]
    have h_ne : m ≠ l := by
      rintro rfl
      exact hlm dvd_rfl
    rw [if_neg h_ne]

lemma selberg_weight_term_eq {n s z d : ℕ} (l : ℕ) :
    (if l ∣ d then (ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m
      else 0) =
      ∑ m ∈ sieveLevelDivisors n s z,
        if l ∣ d ∧ d ∣ m then
          (ArithmeticFunction.moebius d : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms m
        else 0 := by
  split_ifs with hld
  · rw [Finset.mul_sum]
    rw [← Finset.sum_filter]
    have h_filter : (sieveLevelDivisors n s z).filter (fun a => l ∣ d ∧ d ∣ a) =
        (sieveLevelDivisors n s z).filter (fun i => d ∣ i) := by
      ext a; simp [hld]
    rw [h_filter]
  · rw [Finset.sum_eq_zero]
    intro m _
    have : ¬(l ∣ d ∧ d ∣ m) := fun h => hld h.1
    rw [if_neg this]

lemma zero_not_mem_sieveLevelDivisors (n s z : ℕ) :
    0 ∉ sieveLevelDivisors n s z := by
  intro h0
  simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at h0
  exact h0.1.2 (Nat.eq_zero_of_zero_dvd h0.1.1)

lemma selberg_inner_sum_eq (n s z l : ℕ) :
    (∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors,
      if l ∣ d then (erdosBoundingSieve n s).nu d * selbergWeight n s z d else 0) =
    if l ∈ sieveLevelDivisors n s z then
      (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms l
    else 0 := by
  rw [sum_divisors_nu_mul_selbergWeight_eq]
  have h_congr : (∑ d ∈ sieveLevelDivisors n s z,
      if l ∣ d then (erdosBoundingSieve n s).nu d * selbergWeight n s z d else 0) =
    ∑ d ∈ sieveLevelDivisors n s z,
      if l ∣ d then (ArithmeticFunction.moebius d : ℝ) / sieveG n s z *
        ∑ m ∈ (sieveLevelDivisors n s z).filter (fun m => d ∣ m), (erdosBoundingSieve n s).selbergTerms m
      else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [nu_mul_selbergWeight_of_mem hd]
  rw [h_congr]
  simp_rw [selberg_weight_term_eq]
  rw [Finset.sum_comm]
  by_cases hl0 : l = 0
  · subst hl0
    have hl_not : 0 ∉ sieveLevelDivisors n s z := zero_not_mem_sieveLevelDivisors n s z
    rw [if_neg hl_not]
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact (zero_not_mem_sieveLevelDivisors n s z) hd
    have : ¬(0 ∣ d ∧ d ∣ m) := fun h => hd0 (Nat.eq_zero_of_zero_dvd h.1)
    rw [if_neg this]
  · have h_inner : ∀ m ∈ sieveLevelDivisors n s z,
        (∑ d ∈ sieveLevelDivisors n s z,
          if l ∣ d ∧ d ∣ m then
            (ArithmeticFunction.moebius d : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms m
          else 0) =
        if m = l then
          (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms l
        else 0 := by
      intro m hm
      have h_term : ∀ d ∈ sieveLevelDivisors n s z,
          (if l ∣ d ∧ d ∣ m then
            (ArithmeticFunction.moebius d : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms m
          else 0) =
          ((erdosBoundingSieve n s).selbergTerms m / sieveG n s z) *
            if l ∣ d ∧ d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0 := by
        intro d _
        split_ifs <;> ring
      rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum]
      rw [sum_moebius_sieveLevel_eq hl0 hm]
      split_ifs with hml
      · subst hml; ring
      · ring
    rw [Finset.sum_congr rfl h_inner]
    by_cases hl_mem : l ∈ sieveLevelDivisors n s z
    · rw [if_pos hl_mem]
      rw [Finset.sum_ite_eq' (sieveLevelDivisors n s z) l]
      simp only [hl_mem, ↓reduceIte]
    · rw [if_neg hl_mem]
      rw [Finset.sum_ite_eq' (sieveLevelDivisors n s z) l]
      simp only [hl_mem, ↓reduceIte]

lemma selberg_quad_term_eq (n s z : ℕ) {l : ℕ} (hl : l ∈ sieveLevelDivisors n s z) :
    ((erdosBoundingSieve n s).selbergTerms l)⁻¹ *
      ((if l ∈ sieveLevelDivisors n s z then
        (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms l
      else 0) ^ 2) =
    (1 / (sieveG n s z) ^ 2) * (erdosBoundingSieve n s).selbergTerms l := by
  rw [if_pos hl]
  have hl_div : l ∈ (erdosBoundingSieve n s).prodPrimes.divisors := by
    simp only [sieveLevelDivisors, Finset.mem_filter] at hl
    exact hl.1
  have hl_dvd : l ∣ (erdosBoundingSieve n s).prodPrimes := Nat.dvd_of_mem_divisors hl_div
  have hl_sq : Squarefree l :=
    Squarefree.squarefree_of_dvd hl_dvd (erdosBoundingSieve n s).prodPrimes_squarefree
  have h_mu_sq : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
    have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hl_sq
    exact_mod_cast this
  have h_pos := BoundingSieve.selbergTerms_pos hl_dvd
  have h_ne : (erdosBoundingSieve n s).selbergTerms l ≠ 0 := h_pos.ne'
  set T := (erdosBoundingSieve n s).selbergTerms l
  set G := sieveG n s z
  calc T⁻¹ * ((ArithmeticFunction.moebius l : ℝ) / G * T) ^ 2
    _ = T⁻¹ * ((ArithmeticFunction.moebius l : ℝ) ^ 2 / G ^ 2 * T ^ 2) := by ring
    _ = T⁻¹ * (1 / G ^ 2 * T ^ 2) := by rw [h_mu_sq]
    _ = (1 / G ^ 2) * (T⁻¹ * T ^ 2) := by ring
    _ = (1 / G ^ 2) * (T⁻¹ * (T * T)) := by ring
    _ = (1 / G ^ 2) * ((T⁻¹ * T) * T) := by ring
    _ = (1 / G ^ 2) * (1 * T) := by rw [inv_mul_cancel₀ h_ne]
    _ = (1 / G ^ 2) * T := by ring

lemma selberg_quad_term_of_not_mem (n s z : ℕ) {l : ℕ} (hl : l ∉ sieveLevelDivisors n s z) :
    ((erdosBoundingSieve n s).selbergTerms l)⁻¹ *
      ((if l ∈ sieveLevelDivisors n s z then
        (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * (erdosBoundingSieve n s).selbergTerms l
      else 0) ^ 2) = 0 := by
  rw [if_neg hl, zero_pow (by norm_num), mul_zero]

theorem mainSum_selbergWeight_eq (n s z : ℕ) (hz : 1 ≤ z) :
    @BoundingSieve.mainSum (erdosBoundingSieve n s)
      (BoundingSieve.lambdaSquared (selbergWeight n s z)) = 1 / sieveG n s z := by
  let s_bs := erdosBoundingSieve n s
  have h_diag := BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (selbergWeight n s z) (s := s_bs)
  rw [h_diag]
  have h_inner_congr : ∀ l ∈ s_bs.prodPrimes.divisors,
      (∑ d ∈ s_bs.prodPrimes.divisors, if l ∣ d then s_bs.nu d * selbergWeight n s z d else 0) =
      if l ∈ sieveLevelDivisors n s z then
        (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * s_bs.selbergTerms l
      else 0 := fun l _ => selberg_inner_sum_eq n s z l
  have h_step1 : (∑ l ∈ s_bs.prodPrimes.divisors, (s_bs.selbergTerms l)⁻¹ *
      (∑ d ∈ s_bs.prodPrimes.divisors, if l ∣ d then s_bs.nu d * selbergWeight n s z d else 0) ^ 2) =
    ∑ l ∈ s_bs.prodPrimes.divisors, (s_bs.selbergTerms l)⁻¹ *
      ((if l ∈ sieveLevelDivisors n s z then
        (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * s_bs.selbergTerms l
      else 0) ^ 2) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [h_inner_congr l hl]
  rw [h_step1]
  have h_sub : sieveLevelDivisors n s z ⊆ s_bs.prodPrimes.divisors := Finset.filter_subset _ _
  rw [← Finset.sum_subset h_sub]
  · have h_quad_congr : (∑ l ∈ sieveLevelDivisors n s z, (s_bs.selbergTerms l)⁻¹ *
        ((if l ∈ sieveLevelDivisors n s z then
          (ArithmeticFunction.moebius l : ℝ) / sieveG n s z * s_bs.selbergTerms l
        else 0) ^ 2)) =
      ∑ l ∈ sieveLevelDivisors n s z, (1 / (sieveG n s z) ^ 2) * s_bs.selbergTerms l := by
      apply Finset.sum_congr rfl
      intro l hl
      exact selberg_quad_term_eq n s z hl
    rw [h_quad_congr, ← Finset.mul_sum]
    have h_sum_G : (∑ l ∈ sieveLevelDivisors n s z, s_bs.selbergTerms l) = sieveG n s z := rfl
    rw [h_sum_G]
    have hG_ne : sieveG n s z ≠ 0 := (sieveG_pos n s z hz).ne'
    calc (1 / (sieveG n s z) ^ 2) * sieveG n s z
      _ = (1 / (sieveG n s z * sieveG n s z)) * sieveG n s z := by ring
      _ = (1 / sieveG n s z * (1 / sieveG n s z)) * sieveG n s z := by rw [one_div_mul_one_div]
      _ = (1 / sieveG n s z) * ((1 / sieveG n s z) * sieveG n s z) := by ring
      _ = (1 / sieveG n s z) * 1 := by rw [one_div_mul_cancel hG_ne]
      _ = 1 / sieveG n s z := mul_one _
  · intro l _ hl_not
    exact selberg_quad_term_of_not_mem n s z hl_not

lemma selbergTerms_nonneg_of_mem_sieveLevelDivisors (n s z l : ℕ)
    (hl : l ∈ sieveLevelDivisors n s z) :
    0 ≤ (erdosBoundingSieve n s).selbergTerms l := by
  have hl_div : l ∈ (erdosBoundingSieve n s).prodPrimes.divisors := by
    simp only [sieveLevelDivisors, Finset.mem_filter] at hl
    exact hl.1
  have hl_dvd : l ∣ (erdosBoundingSieve n s).prodPrimes := Nat.dvd_of_mem_divisors hl_div
  exact le_of_lt (BoundingSieve.selbergTerms_pos hl_dvd)

lemma sum_selbergTerms_filter_le_sieveG (n s z d : ℕ) :
    (∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l), (erdosBoundingSieve n s).selbergTerms l) ≤
      sieveG n s z := by
  dsimp [sieveG]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro l hl _
  exact selbergTerms_nonneg_of_mem_sieveLevelDivisors n s z l hl

lemma abs_selbergWeight_le (n s z d : ℕ) (hz : 1 ≤ z)
    (hd_div : d ∈ (erdosBoundingSieve n s).prodPrimes.divisors) :
    |selbergWeight n s z d| ≤ (d : ℝ) := by
  by_cases hd_level : d ∈ sieveLevelDivisors n s z
  · dsimp [selbergWeight]
    have hd_dvd : d ∣ (erdosBoundingSieve n s).prodPrimes := Nat.dvd_of_mem_divisors hd_div
    rw [if_pos hd_dvd]
    rw [abs_mul]
    have hG_pos := sieveG_pos n s z hz
    have h_sum_nonneg : 0 ≤ ∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l), (erdosBoundingSieve n s).selbergTerms l := by
      apply Finset.sum_nonneg
      intro l hl
      simp only [Finset.mem_filter] at hl
      exact selbergTerms_nonneg_of_mem_sieveLevelDivisors n s z l hl.1
    have h_sum_le := sum_selbergTerms_filter_le_sieveG n s z d
    have h_abs_sum : |∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l), (erdosBoundingSieve n s).selbergTerms l| =
        ∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l), (erdosBoundingSieve n s).selbergTerms l :=
      abs_of_nonneg h_sum_nonneg
    rw [h_abs_sum]
    have hd_sq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd_dvd (erdosBoundingSieve n s).prodPrimes_squarefree
    have h_abs_mu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      have := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd_sq
      exact_mod_cast this
    have h_abs_frac : |(ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / sieveG n s z| =
        (d : ℝ) / sieveG n s z := by
      rw [abs_div, abs_mul, h_abs_mu, one_mul, abs_of_pos hG_pos, abs_of_nonneg (Nat.cast_nonneg d)]
    rw [h_abs_frac]
    calc (d : ℝ) / sieveG n s z * (∑ l ∈ (sieveLevelDivisors n s z).filter (fun l => d ∣ l), (erdosBoundingSieve n s).selbergTerms l)
      _ ≤ (d : ℝ) / sieveG n s z * sieveG n s z := by
        apply mul_le_mul_of_nonneg_left h_sum_le
        exact div_nonneg (Nat.cast_nonneg d) (le_of_lt hG_pos)
      _ = (d : ℝ) * ((sieveG n s z)⁻¹ * sieveG n s z) := by ring
      _ = (d : ℝ) * 1 := by rw [inv_mul_cancel₀ hG_pos.ne']
      _ = (d : ℝ) := mul_one _
  · have hz_lt : z < d := by
      simp only [sieveLevelDivisors, Finset.mem_filter, not_and] at hd_level
      have := hd_level hd_div
      omega
    rw [selbergWeight_eq_zero_of_gt n s z d hz_lt, abs_zero]
    exact Nat.cast_nonneg d

lemma sieveLevelDivisors_subset_Icc (n s z : ℕ) :
    sieveLevelDivisors n s z ⊆ Finset.Icc 1 z := by
  intro d hd
  simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc] at hd ⊢
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  exact ⟨Nat.pos_of_ne_zero hd0, hd.2⟩

lemma sieveLevelDivisors_card_le (n s z : ℕ) :
    (sieveLevelDivisors n s z).card ≤ z := by
  have h_sub := sieveLevelDivisors_subset_Icc n s z
  have h_card := Finset.card_le_card h_sub
  rw [Nat.card_Icc] at h_card
  omega

lemma sum_sieveLevelDivisors_le (n s z : ℕ) :
    (∑ d ∈ sieveLevelDivisors n s z, (d : ℝ)) ≤ (z : ℝ) ^ 2 := by
  calc (∑ d ∈ sieveLevelDivisors n s z, (d : ℝ))
    _ ≤ ∑ d ∈ sieveLevelDivisors n s z, (z : ℝ) := by
      gcongr with d hd
      simp only [sieveLevelDivisors, Finset.mem_filter] at hd
      exact Nat.cast_le.mpr hd.2
    _ = (sieveLevelDivisors n s z).card * (z : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (z : ℝ) * (z : ℝ) := by
      gcongr
      exact Nat.cast_le.mpr (sieveLevelDivisors_card_le n s z)
    _ = (z : ℝ) ^ 2 := by ring

lemma sum_divisors_abs_selbergWeight_le (n s z : ℕ) (hz : 1 ≤ z) :
    (∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors, |selbergWeight n s z d|) ≤ (z : ℝ) ^ 2 := by
  let D := (erdosBoundingSieve n s).prodPrimes
  have h_sub : sieveLevelDivisors n s z ⊆ D.divisors := Finset.filter_subset _ _
  rw [← Finset.sum_subset h_sub]
  · calc (∑ d ∈ sieveLevelDivisors n s z, |selbergWeight n s z d|)
      _ ≤ ∑ d ∈ sieveLevelDivisors n s z, (d : ℝ) := by
        gcongr with d hd
        have hd_div : d ∈ D.divisors := h_sub hd
        exact abs_selbergWeight_le n s z d hz hd_div
      _ ≤ (z : ℝ) ^ 2 := sum_sieveLevelDivisors_le n s z
  · intro d hd_div hd_not_mem
    have hz_lt : z < d := by
      simp only [sieveLevelDivisors, Finset.mem_filter, not_and] at hd_not_mem
      have := hd_not_mem hd_div
      omega
    rw [selbergWeight_eq_zero_of_gt n s z d hz_lt, abs_zero]

lemma errSum_selbergWeight_le (n s z : ℕ) (hz : 1 ≤ z) :
    @BoundingSieve.errSum (erdosBoundingSieve n s)
      (BoundingSieve.lambdaSquared (selbergWeight n s z)) ≤ (z : ℝ) ^ 4 := by
  have h1 := errSum_lambdaSquared_le n s (selbergWeight n s z)
  have h2 := sum_divisors_abs_selbergWeight_le n s z hz
  have h_sum_nonneg : 0 ≤ ∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors, |selbergWeight n s z d| := by
    apply Finset.sum_nonneg
    intro d _
    exact abs_nonneg _
  calc @BoundingSieve.errSum (erdosBoundingSieve n s) (BoundingSieve.lambdaSquared (selbergWeight n s z))
    _ ≤ (∑ d ∈ (erdosBoundingSieve n s).prodPrimes.divisors, |selbergWeight n s z d|) ^ 2 := h1
    _ ≤ ((z : ℝ) ^ 2) ^ 2 := by
      gcongr
    _ = (z : ℝ) ^ 4 := by ring

/-- Finite Selberg Sieve Remainder Bound:
    For any n ≥ 2, s ≥ 1, and level parameter z ≥ 1, the sifted remainder set R
    satisfies:
      |R| ≤ ⌊(n - 1) / (s + 1)⌋ / G + z^4,
    where G = ∑_{d ∈ D.divisors, d ≤ z} selbergTerms(d) ≥ 1. -/
theorem selberg_remainder_bound (n s z : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hz : 1 ≤ z) :
    ((sieveRemainder n s (sievePrimes n s)).card : ℝ) ≤
      ((((n - 1) / (s + 1) : ℕ) : ℝ)) / sieveG n s z + (z : ℝ) ^ 4 := by
  let muPlus := BoundingSieve.lambdaSquared (selbergWeight n s z)
  have h_w1 : selbergWeight n s z 1 = 1 := selbergWeight_one n s z hz
  have h_upper : BoundingSieve.IsUpperMoebius muPlus :=
    BoundingSieve.upperMoebius_lambdaSquared (selbergWeight n s z) h_w1
  have h_card_le := card_remainder_le_mainSum_errSum n s hn hs muPlus h_upper
  have h_main := mainSum_selbergWeight_eq n s z hz
  have h_err := errSum_selbergWeight_le n s z hz
  dsimp [erdosBoundingSieve] at h_card_le
  calc ((sieveRemainder n s (sievePrimes n s)).card : ℝ)
    _ ≤ ((((n - 1) / (s + 1) : ℕ) : ℝ)) *
          @BoundingSieve.mainSum (erdosBoundingSieve n s) muPlus +
        @BoundingSieve.errSum (erdosBoundingSieve n s) muPlus := h_card_le
    _ = ((((n - 1) / (s + 1) : ℕ) : ℝ)) * (1 / sieveG n s z) +
        @BoundingSieve.errSum (erdosBoundingSieve n s) muPlus := by rw [h_main]
    _ ≤ ((((n - 1) / (s + 1) : ℕ) : ℝ)) * (1 / sieveG n s z) + (z : ℝ) ^ 4 := by
      gcongr
    _ = ((((n - 1) / (s + 1) : ℕ) : ℝ)) / sieveG n s z + (z : ℝ) ^ 4 := by ring

lemma selbergTerms_prime (n s p : ℕ) (hp : Nat.Prime p) :
    (erdosBoundingSieve n s).selbergTerms p = 1 / ((p : ℝ) - 1) := by
  have hp_factors : p.primeFactors = {p} := hp.primeFactors
  rw [BoundingSieve.selbergTerms_apply]
  dsimp [erdosBoundingSieve]
  rw [hp_factors, Finset.prod_singleton]
  dsimp [unitDensity]
  rw [if_neg hp.ne_zero]
  have hp_gt1 : 1 < (p : ℝ) := by
    have : 2 ≤ p := hp.two_le
    norm_cast
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  have hp_sub_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

lemma prime_mem_sieveLevelDivisors (n s z p : ℕ)
    (hp : p ∈ (sievePrimes n s).filter (fun p => p ≤ z)) :
    p ∈ sieveLevelDivisors n s z := by
  simp only [sievePrimes, sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hp ⊢
  refine ⟨⟨?_, ?_⟩, hp.2⟩
  · apply Finset.dvd_prod_of_mem id
    simp only [Finset.mem_filter]
    exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2⟩
  · have h_sq := (erdosBoundingSieve n s).prodPrimes_squarefree
    exact Squarefree.ne_zero h_sq

lemma one_not_mem_filter_sievePrimes (n s z : ℕ) :
    1 ∉ (sievePrimes n s).filter (fun p => p ≤ z) := by
  intro h
  simp only [sievePrimes, Finset.mem_filter] at h
  have hp : Nat.Prime 1 := h.1.2.1
  exact Nat.not_prime_one hp

lemma sieveG_ge_one_add_sum_primes (n s z : ℕ) (hz : 1 ≤ z) :
    1 + ∑ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), (1 / ((p : ℝ) - 1)) ≤ sieveG n s z := by
  let Pz := (sievePrimes n s).filter (fun p => p ≤ z)
  have h_sub : insert 1 Pz ⊆ sieveLevelDivisors n s z := by
    rw [Finset.insert_subset_iff]
    refine ⟨one_mem_sieveLevelDivisors n s z hz, fun p hp => prime_mem_sieveLevelDivisors n s z p hp⟩
  have h_nonneg : ∀ d ∈ sieveLevelDivisors n s z, d ∉ insert 1 Pz → 0 ≤ (erdosBoundingSieve n s).selbergTerms d := by
    intro d hd _
    simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
    exact le_of_lt (BoundingSieve.selbergTerms_pos hd.1.1)
  have h_sum_le := Finset.sum_le_sum_of_subset_of_nonneg h_sub h_nonneg
  have h_not_mem : 1 ∉ Pz := one_not_mem_filter_sievePrimes n s z
  have h_insert : (∑ d ∈ insert 1 Pz, (erdosBoundingSieve n s).selbergTerms d) =
      (erdosBoundingSieve n s).selbergTerms 1 + ∑ p ∈ Pz, (erdosBoundingSieve n s).selbergTerms p :=
    Finset.sum_insert h_not_mem
  have h_one : (erdosBoundingSieve n s).selbergTerms 1 = 1 :=
    BoundingSieve.selbergTerms_isMultiplicative.map_one
  have h_term_prime : ∀ p ∈ Pz, (erdosBoundingSieve n s).selbergTerms p = 1 / ((p : ℝ) - 1) := by
    intro p hp
    simp only [Pz, sievePrimes, Finset.mem_filter] at hp
    exact selbergTerms_prime n s p hp.1.2.1
  rw [Finset.sum_congr rfl h_term_prime] at h_insert
  rw [h_one] at h_insert
  dsimp [sieveG]
  linarith

lemma selbergTerms_of_squarefree (n s c : ℕ) (hc_sq : Squarefree c) (hc_pos : 0 < c) :
    (erdosBoundingSieve n s).selbergTerms c = (1 : ℝ) / ((Nat.totient c : ℝ)) := by
  have hc0 : c ≠ 0 := hc_pos.ne'
  rw [BoundingSieve.selbergTerms_apply]
  dsimp [erdosBoundingSieve, unitDensity]
  rw [if_neg hc0]
  have h_prod : (∏ p ∈ c.primeFactors, (1 - (if p = 0 then (0 : ℝ) else 1 / (p : ℝ)))⁻¹) =
      ∏ p ∈ c.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    rw [if_neg hp_prime.ne_zero]
    have hp_lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hp_sub : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1 : 1 - (1 : ℝ) / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
      field_simp
    rw [h1, inv_div]
  rw [h_prod]
  have h_div : (∏ p ∈ c.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) =
      (∏ p ∈ c.primeFactors, (p : ℝ)) / ∏ p ∈ c.primeFactors, ((p : ℝ) - 1) := by
    rw [Finset.prod_div_distrib]
  rw [h_div]
  have h_num : (∏ p ∈ c.primeFactors, (p : ℝ)) = (c : ℝ) := by
    have h_c : ((∏ p ∈ c.primeFactors, p : ℕ) : ℝ) = (c : ℝ) := by
      exact_mod_cast Nat.prod_primeFactors_of_squarefree hc_sq
    push_cast at h_c
    exact h_c
  have h_den : (∏ p ∈ c.primeFactors, ((p : ℝ) - 1)) = ((Nat.totient c : ℝ)) := by
    exact (cast_totient_of_squarefree hc_sq).symm
  rw [h_num, h_den]
  have hc_cast_pos : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr hc_pos
  have htot_pos : (0 : ℝ) < ((Nat.totient c : ℝ)) := by
    have : 0 < Nat.totient c := Nat.totient_pos.mpr hc_pos
    exact Nat.cast_pos.mpr this
  field_simp

lemma sieveG_ge_half_totient_ratio_mul_log (n s z : ℕ)
    (hn : 2 ≤ n) (_hs : 1 ≤ s) (hz : 2 ≤ z) (hzs : z ≤ s) :
    (1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ) ≤ sieveG n s z := by
  let C := (Finset.Icc 1 z).filter (fun c => Squarefree c ∧ c.Coprime n)
  have hn_pos : 0 < n := by omega
  have hz1 : 1 ≤ z := by omega
  have h_coprime_sum := sum_coprime_squarefree_inv_totient_ge_half n z hn_pos hz1
  have h_terms : (∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ))) =
      ∑ c ∈ C, (erdosBoundingSieve n s).selbergTerms c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc, C] at hc
    have hc_sq : Squarefree c := hc.2.1
    have hc_pos : 0 < c := hc.1.1
    rw [selbergTerms_of_squarefree n s c hc_sq hc_pos]
  have h_sub : C ⊆ sieveLevelDivisors n s z := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc, C] at hc
    obtain ⟨⟨hc1, hcz⟩, hc_sq, hc_cop⟩ := hc
    simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ?_⟩, hcz⟩
    · have hc_prod : c = ∏ p ∈ c.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hc_sq).symm
      rw [hc_prod]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hp_dvd_c : p ∣ c := Nat.dvd_of_mem_primeFactors hp
      have hp_le_c : p ≤ c := Nat.le_of_dvd hc1 hp_dvd_c
      have hp_le_s : p ≤ s := hp_le_c.trans (hcz.trans hzs)
      have hp_ge_2 : 2 ≤ p := hp_prime.two_le
      have hp_not_dvd_n : ¬ p ∣ n := by
        intro hpn
        have hp_dvd_gcd : p ∣ c.gcd n := Nat.dvd_gcd hp_dvd_c hpn
        rw [Nat.Coprime.gcd_eq_one hc_cop] at hp_dvd_gcd
        have : p ≤ 1 := Nat.le_of_dvd (by omega) hp_dvd_gcd
        omega
      simp only [sievePrimes, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp_ge_2, hp_le_s⟩, hp_prime, hp_not_dvd_n⟩
    · have h_sq := (erdosBoundingSieve n s).prodPrimes_squarefree
      exact Squarefree.ne_zero h_sq
  have h_nonneg : ∀ d ∈ sieveLevelDivisors n s z, 0 ≤ (erdosBoundingSieve n s).selbergTerms d := by
    intro d hd
    simp only [sieveLevelDivisors, Finset.mem_filter, Nat.mem_divisors] at hd
    exact le_of_lt (BoundingSieve.selbergTerms_pos hd.1.1)
  have h_sum_le : (∑ c ∈ C, (erdosBoundingSieve n s).selbergTerms c) ≤
      ∑ d ∈ sieveLevelDivisors n s z, (erdosBoundingSieve n s).selbergTerms d :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun d hd _ => h_nonneg d hd)
  dsimp [sieveG]
  calc (1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ)
    _ ≤ ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := h_coprime_sum
    _ = ∑ c ∈ C, (erdosBoundingSieve n s).selbergTerms c := h_terms
    _ ≤ ∑ d ∈ sieveLevelDivisors n s z, (erdosBoundingSieve n s).selbergTerms d := h_sum_le

lemma nat_div_le_div (m d : ℕ) (hd : 0 < d) : (((m / d : ℕ) : ℝ)) ≤ (m : ℝ) / (d : ℝ) := by
  have : (m / d) * d ≤ m := Nat.div_mul_le_self m d
  have h_cast : (((m / d) * d : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
  push_cast at h_cast
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  exact (le_div_iff₀ hd_pos).mpr (by linarith)

lemma le_ceil_of_lt_add_one {k : ℕ} {y : ℝ} (h : (k : ℝ) < y + 1) : k ≤ Nat.ceil y := by
  by_contra! h_lt
  have : (Nat.ceil y + 1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h_lt
  have h_ceil : y ≤ (Nat.ceil y : ℝ) := Nat.le_ceil y
  linarith

lemma nat_div_add_pred_le_ceil (c s : ℕ) (hs : 1 ≤ s) :
    (c + s - 1) / s ≤ Nat.ceil ((c : ℝ) / (s : ℝ)) := by
  apply le_ceil_of_lt_add_one
  have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
  have h_div : (((c + s - 1) / s : ℕ) : ℝ) ≤ ((c + s - 1 : ℕ) : ℝ) / (s : ℝ) :=
    nat_div_le_div (c + s - 1) s hs
  refine h_div.trans_lt ?_
  have h_cast_sub : ((c + s - 1 : ℕ) : ℝ) = (c : ℝ) + (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [h_cast_sub]
  have h_sub_lt : (s : ℝ) - 1 < (s : ℝ) := by linarith
  calc ((c : ℝ) + (s : ℝ) - 1) / (s : ℝ)
    _ = (c : ℝ) / (s : ℝ) + ((s : ℝ) - 1) / (s : ℝ) := by ring
    _ < (c : ℝ) / (s : ℝ) + 1 := by
      gcongr
      exact (div_lt_one hs_pos).mpr h_sub_lt

/-- Chromatic number bound for any explicit lower bound g₀ ≤ G:
    f(n) ≤ 2s + ⌈(n - 1) / (s(s + 1) g₀) + z⁴ / s⌉. -/
theorem minColors_le_of_sieveG_lower_bound (n s z : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hz : 1 ≤ z)
    (g0 : ℝ) (hg0 : 0 < g0) (hg : g0 ≤ sieveG n s z) :
    minColors n hn ≤ 2 * s + Nat.ceil (((n - 1 : ℝ) / ((s : ℝ) * (s + 1 : ℝ) * g0)) + (z : ℝ) ^ 4 / (s : ℝ)) := by
  have h_bound := minColors_le_two_s_add_remainder n s hn hs
  have h_ceil := nat_div_add_pred_le_ceil (sieveRemainder n s (sievePrimes n s)).card s hs
  have h_rem := selberg_remainder_bound n s z hn hs hz
  have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
  have hs1_pos : (0 : ℝ) < (s + 1 : ℝ) := by positivity
  have h_nat_div : ((((n - 1) / (s + 1) : ℕ) : ℝ)) ≤ ((n : ℝ) - 1) / ((s : ℝ) + 1) := by
    have h1 := nat_div_le_div (n - 1) (s + 1) (by omega)
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h3 : ((s + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by push_cast; rfl
    rwa [h2, h3] at h1
  have h_div_g : ((((n - 1) / (s + 1) : ℕ) : ℝ)) / sieveG n s z ≤
      ((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) := by
    have hG_pos := sieveG_pos n s z hz
    have h1 : ((((n - 1) / (s + 1) : ℕ) : ℝ)) / sieveG n s z ≤
        ((((n - 1) / (s + 1) : ℕ) : ℝ)) / g0 := by
      gcongr
    have h2 : ((((n - 1) / (s + 1) : ℕ) : ℝ)) / g0 ≤ ((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) := by
      calc ((((n - 1) / (s + 1) : ℕ) : ℝ)) / g0
        _ ≤ (((n : ℝ) - 1) / ((s : ℝ) + 1)) / g0 := by gcongr
        _ = ((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) := div_div ((n : ℝ) - 1) ((s : ℝ) + 1) g0
    exact h1.trans h2
  have h_R_le : ((sieveRemainder n s (sievePrimes n s)).card : ℝ) ≤
      ((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) + (z : ℝ) ^ 4 := by
    calc ((sieveRemainder n s (sievePrimes n s)).card : ℝ)
      _ ≤ ((((n - 1) / (s + 1) : ℕ) : ℝ)) / sieveG n s z + (z : ℝ) ^ 4 := h_rem
      _ ≤ ((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) + (z : ℝ) ^ 4 := by gcongr
  have h_div_s : ((sieveRemainder n s (sievePrimes n s)).card : ℝ) / (s : ℝ) ≤
      (((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) + 1) * g0)) + (z : ℝ) ^ 4 / (s : ℝ) := by
    calc ((sieveRemainder n s (sievePrimes n s)).card : ℝ) / (s : ℝ)
      _ ≤ (((n : ℝ) - 1) / (((s : ℝ) + 1) * g0) + (z : ℝ) ^ 4) / (s : ℝ) := by
        gcongr
      _ = (((n : ℝ) - 1) / (((s : ℝ) + 1) * g0)) / (s : ℝ) + (z : ℝ) ^ 4 / (s : ℝ) := by
        rw [add_div]
      _ = (((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) + 1) * g0)) + (z : ℝ) ^ 4 / (s : ℝ) := by
        rw [div_div]
        congr 2
        ring
  have h_ceil_le : Nat.ceil (((sieveRemainder n s (sievePrimes n s)).card : ℝ) / (s : ℝ)) ≤
      Nat.ceil ((((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) + 1) * g0)) + (z : ℝ) ^ 4 / (s : ℝ)) :=
    Nat.ceil_mono h_div_s
  have h_trans : ((sieveRemainder n s (sievePrimes n s)).card + s - 1) / s ≤
      Nat.ceil ((((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) + 1) * g0)) + (z : ℝ) ^ 4 / (s : ℝ)) :=
    h_ceil.trans h_ceil_le
  omega

/-- Sieve chromatic bound with prime reciprocal sum:
    f(n) ≤ 2s + ⌈(n - 1) / (s(s + 1) (1 + ∑_{p ≤ z, p ∤ n} 1/(p - 1))) + z⁴ / s⌉. -/
theorem minColors_le_of_sum_primes (n s z : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hz : 1 ≤ z) :
    minColors n hn ≤ 2 * s +
      Nat.ceil (((n - 1 : ℝ) / ((s : ℝ) * (s + 1 : ℝ) *
        (1 + ∑ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), (1 / ((p : ℝ) - 1))))) +
        (z : ℝ) ^ 4 / (s : ℝ)) := by
  let g0 := 1 + ∑ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), (1 / ((p : ℝ) - 1))
  have h_term_nonneg : ∀ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), 0 ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    simp only [sievePrimes, Finset.mem_filter] at hp
    have : 2 ≤ p := hp.1.2.1.two_le
    have : (1 : ℝ) < (p : ℝ) := by norm_cast
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  have h_sum_nonneg : 0 ≤ ∑ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), (1 / ((p : ℝ) - 1)) :=
    Finset.sum_nonneg h_term_nonneg
  have hg0_pos : 0 < g0 := by
    dsimp [g0]
    linarith
  have hg0_le : g0 ≤ sieveG n s z := sieveG_ge_one_add_sum_primes n s z hz
  exact minColors_le_of_sieveG_lower_bound n s z hn hs hz g0 hg0_pos hg0_le

/-- Sieve chromatic bound for any prime subset Q ⊆ sievePrimes n s with elements ≤ z:
    f(n) ≤ 2s + ⌈(n - 1) / (s(s + 1) (1 + ∑_{p ∈ Q} 1/(p - 1))) + z⁴ / s⌉. -/
theorem minColors_le_of_prime_subset (n s z : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hz : 1 ≤ z)
    (Q : Finset ℕ) (hQ_sub : Q ⊆ sievePrimes n s) (hQ_le : ∀ p ∈ Q, p ≤ z) :
    minColors n hn ≤ 2 * s +
      Nat.ceil (((n - 1 : ℝ) / ((s : ℝ) * (s + 1 : ℝ) *
        (1 + ∑ p ∈ Q, (1 / ((p : ℝ) - 1))))) +
        (z : ℝ) ^ 4 / (s : ℝ)) := by
  let Pz := (sievePrimes n s).filter (fun p => p ≤ z)
  have hQ_in_Pz : Q ⊆ Pz := by
    intro p hp
    simp only [Pz, Finset.mem_filter]
    exact ⟨hQ_sub hp, hQ_le p hp⟩
  have h_term_nonneg : ∀ p ∈ Pz, 0 ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    simp only [Pz, sievePrimes, Finset.mem_filter] at hp
    have : 2 ≤ p := hp.1.2.1.two_le
    have : (1 : ℝ) < (p : ℝ) := by norm_cast
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  have h_sum_le : (∑ p ∈ Q, (1 / ((p : ℝ) - 1))) ≤ ∑ p ∈ Pz, (1 / ((p : ℝ) - 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hQ_in_Pz (fun p hp _ => h_term_nonneg p hp)
  let gQ := 1 + ∑ p ∈ Q, (1 / ((p : ℝ) - 1))
  have hgQ_pos : 0 < gQ := by
    dsimp [gQ]
    have : 0 ≤ ∑ p ∈ Q, (1 / ((p : ℝ) - 1)) :=
      Finset.sum_nonneg (fun p hp => h_term_nonneg p (hQ_in_Pz hp))
    linarith
  have hgQ_le : gQ ≤ sieveG n s z := by
    have h1 : gQ ≤ 1 + ∑ p ∈ Pz, (1 / ((p : ℝ) - 1)) := by
      dsimp [gQ]; linarith
    exact h1.trans (sieveG_ge_one_add_sum_primes n s z hz)
  exact minColors_le_of_sieveG_lower_bound n s z hn hs hz gQ hgQ_pos hgQ_le

/-- Sieve chromatic bound with the sharp totient-logarithm sieve G lower bound:
    f(n) ≤ 2s + ⌈(n - 1) / (s(s + 1) ((1/2) (φ(n)/n) log z)) + z⁴ / s⌉. -/
theorem minColors_le_of_totient_log (n s z : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hz : 2 ≤ z) (hzs : z ≤ s) :
    minColors n hn ≤ 2 * s +
      Nat.ceil (((n - 1 : ℝ) / ((s : ℝ) * (s + 1 : ℝ) *
        ((1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ)))) +
        (z : ℝ) ^ 4 / (s : ℝ)) := by
  let g0 := (1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have htot_pos : (0 : ℝ) < ((Nat.totient n : ℝ)) := by
    have : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
    exact Nat.cast_pos.mpr this
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by
    have : 1 < z := by omega
    exact_mod_cast this
  have h_log_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt1
  have hg0_pos : 0 < g0 := by
    dsimp [g0]
    positivity
  have hg0_le : g0 ≤ sieveG n s z := sieveG_ge_half_totient_ratio_mul_log n s z hn hs hz hzs
  exact minColors_le_of_sieveG_lower_bound n s z hn hs (by omega) g0 hg0_pos hg0_le


/-!
### Section 5: Non-Trivial Lower Bound
-/

/-- Non-trivial lower bound: for all n ≥ 3, f(n) ≥ 2. -/
theorem minColors_ge_two (n : ℕ) (hn : 3 ≤ n) :
    2 ≤ minColors n (by omega) := by
  by_contra h
  push Not at h
  have h_cases : minColors n (by omega) = 0 ∨ minColors n (by omega) = 1 := by omega
  have ⟨c, hc⟩ := minColors_has_coloring n (by omega)
  rcases h_cases with h0 | h1
  · have h_k : minColors n (by omega) = 0 := h0
    generalize h_min : minColors n (by omega) = k at c hc h_k
    subst h_k
    have : 1 ∈ Finset.Ico 1 n := by simp; omega
    have h_fin0 := c 1
    exact Fin.elim0 h_fin0
  · have h_k : minColors n (by omega) = 1 := h1
    generalize h_min : minColors n (by omega) = k at c hc h_k
    subst h_k
    exact no_one_coloring_of_ge_three n hn c hc

/-!
### Section 6: Asymptotic Reductions and Conlon–Fox–Pham Formulation

We formalize the asymptotic context of Erdős Problem 360 / JSP-000298:
1. Alon and Erdős (1996) logarithmic improvement:
   Given any explicit lower bound on the prime reciprocal sum
   ∑_{p ≤ s, p ∤ n} 1/(p - 1) (as provided by Mertens' theorem),
   the finite sieve reduction specializes to the corresponding chromatic bound.
2. Conlon, Fox, and Pham (2021, Theorem 1.5):
   Isolates the two-sided asymptotic growth reduction f(n) ≍ F(n)
   for any prescribed growth scale F : ℕ → ℝ.
-/

/-- Abstract growth scale comparison: an upper bound witness on f(n) with respect to F(n). -/
def HasChromaticUpperBound (F : ℕ → ℝ) (C : ℝ) : Prop :=
  0 < C ∧ ∃ N0 : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N0 ≤ n →
    (minColors n hn : ℝ) ≤ C * F n

/-- Abstract growth scale comparison: a lower bound witness on f(n) with respect to F(n). -/
def HasChromaticLowerBound (F : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∃ N0 : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N0 ≤ n →
    c * F n ≤ (minColors n hn : ℝ)

/-- Conlon–Fox–Pham (2021) Asymptotic Equivalence Reduction:
    Given matching lower and upper bound witnesses with respect to a growth scale F,
    the chromatic number f(n) is asymptotically bounded between c * F(n) and C * F(n). -/
theorem conlon_fox_pham_bounds (F : ℕ → ℝ) {c C : ℝ}
    (h_lower : HasChromaticLowerBound F c)
    (h_upper : HasChromaticUpperBound F C) :
    ∃ N0 : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N0 ≤ n →
      c * F n ≤ (minColors n hn : ℝ) ∧
      (minColors n hn : ℝ) ≤ C * F n := by
  rcases h_lower.2 with ⟨N1, hN1⟩
  rcases h_upper.2 with ⟨N2, hN2⟩
  refine ⟨max N1 N2, fun n hn hmax => ?_⟩
  have h1 : N1 ≤ n := le_of_max_le_left hmax
  have h2 : N2 ≤ n := le_of_max_le_right hmax
  exact ⟨hN1 n hn h1, hN2 n hn h2⟩






/-!
### Section 7: Conlon–Fox–Pham (2021) 4-Layer Upper Bound Construction

In arXiv:2104.14766 (Theorem 1.5, Theorem 1.6, and Section 1.2.1), Conlon, Fox, and Pham
introduce a 4-layer coloring construction that achieves the optimal growth order:
  f(n) ≍ n^(1/3) (n / φ(n)) / ((log n)^(1/3) (log log n)^(2/3)).

The 4 layers consist of:
1. Interval blocks: s1 blocks covering elements x with (s1 + 1) * x ≥ n.
2. Prime multiples: |P| blocks for primes p ∤ n.
3. Reduced congruence classes modulo d (for gcd(d, n) = 1):
   For each reduced residue t mod d with gcd(t, d) = 1, there exists xt ∈ [1, d]
   satisfying xt * t ≡ n [MOD d]. Two avoiding classes are formed:
   - High congruence block: {a | a ≡ t [MOD d] ∧ xt * a > n}
   - Mid congruence block:  {a | a ≡ t [MOD d] ∧ (d + xt) * a > n ∧ xt * a < n}
   Total classes in Layer 3: 2 * |reducedResidues d| ≤ 2 * d.
4. Remainder blocks: elements x in R_cfp satisfy (s1 + 1) * x < n.
   Partitioned into blocks of size ≤ s_rem (for any s_rem ≤ s1),
   using ⌈|R_cfp| / s_rem⌉ colors.
-/

/-- The reduced residues modulo d in {1, ..., d}. -/
def reducedResidues (d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 d).filter (·.Coprime d)

lemma reducedResidues_card_le (d : ℕ) : (reducedResidues d).card ≤ d := by
  have : reducedResidues d ⊆ Finset.Icc 1 d := Finset.filter_subset _ _
  have h := Finset.card_le_card this
  rw [Nat.card_Icc] at h
  omega

/-- Congruence sum lemma: if every element of A is congruent to t mod d,
    then ∑ a ∈ A, a ≡ |A| * t [MOD d]. -/
lemma congruence_sum_modeq {d t : ℕ} (A : Finset ℕ) (hA : ∀ a ∈ A, a ≡ t [MOD d]) :
    (∑ a ∈ A, a) ≡ A.card * t [MOD d] := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [sum_empty, card_empty, Nat.zero_mul]
    exact Nat.ModEq.refl 0
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx]
    have hx_mod : x ≡ t [MOD d] := hA x (Finset.mem_insert_self x s)
    have hs_mod : (∑ a ∈ s, a) ≡ s.card * t [MOD d] :=
      ih (fun a ha => hA a (Finset.mem_insert_of_mem ha))
    have h_add := Nat.ModEq.add hx_mod hs_mod
    have h_rw : (s.card + 1) * t = t + s.card * t := by ring
    rw [h_rw]
    exact h_add

/-- Cardinality lower bound: if 1 ≤ c and c ≡ x [MOD d] with x ≤ d, then x ≤ c. -/
lemma card_ge_of_modeq (c x d : ℕ) (hc_pos : 1 ≤ c) (hx_le : x ≤ d)
    (h : c ≡ x [MOD d]) : x ≤ c := by
  have hmod : c % d = x % d := h
  by_cases hxd : x = d
  · rw [hxd, Nat.mod_self d] at hmod
    have hd_dvd : d ∣ c := Nat.dvd_of_mod_eq_zero hmod
    have hd_le : d ≤ c := Nat.le_of_dvd hc_pos hd_dvd
    omega
  · have hx_lt : x < d := by omega
    rw [Nat.mod_eq_of_lt hx_lt] at hmod
    have hc_div := (Nat.div_add_mod c d).symm
    omega

/-- Cardinality dichotomy: if 1 ≤ c and c ≡ x [MOD d] with x ≤ d,
    then either c = x or d + x ≤ c. -/
lemma card_cases_of_modeq (c x d : ℕ) (hc_pos : 1 ≤ c) (hx_le : x ≤ d)
    (_hd : 1 ≤ d) (h : c ≡ x [MOD d]) : c = x ∨ d + x ≤ c := by
  have hmod : c % d = x % d := h
  by_cases hxd : x = d
  · rw [hxd, Nat.mod_self d] at hmod
    have hd_dvd : d ∣ c := Nat.dvd_of_mod_eq_zero hmod
    rcases hd_dvd with ⟨k, rfl⟩
    have hk_pos : 1 ≤ k := by
      by_cases hk : k = 0
      · subst hk; omega
      · omega
    by_cases hk1 : k = 1
    · left; subst hk1; omega
    · right
      have hk2 : 2 ≤ k := by omega
      have : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk2
      omega
  · have hx_lt : x < d := by omega
    rw [Nat.mod_eq_of_lt hx_lt] at hmod
    have hc_div := (Nat.div_add_mod c d).symm
    by_cases hk0 : c / d = 0
    · left
      rw [hk0, Nat.mul_zero, Nat.zero_add] at hc_div
      omega
    · right
      have hk1 : 1 ≤ c / d := Nat.pos_of_ne_zero hk0
      have : d ≤ d * (c / d) := Nat.le_mul_of_pos_right d hk1
      omega

/-- Existence of modular multiplier: for d ≥ 1 and t coprime to d,
    there exists xt ∈ {1, ..., d} such that xt * t ≡ n [MOD d]. -/
lemma exists_xt_modeq (n d t : ℕ) (hd : 1 ≤ d) (ht : t.Coprime d) :
    ∃ xt ∈ Finset.Icc 1 d, xt * t ≡ n [MOD d] := by
  have hd_pos : 0 < d := by omega
  let f : Fin d → Fin d := fun x => ⟨(x.val * t) % d, Nat.mod_lt _ hd_pos⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f, Fin.mk.injEq] at hab
    have h_modeq : a.val * t ≡ b.val * t [MOD d] := hab
    have h_cancel : a.val ≡ b.val [MOD d] :=
      Nat.ModEq.cancel_right_of_coprime ht.symm.gcd_eq_one h_modeq
    ext
    have ha_lt := a.isLt
    have hb_lt := b.isLt
    have ha_mod : a.val % d = a.val := Nat.mod_eq_of_lt ha_lt
    have hb_mod : b.val % d = b.val := Nat.mod_eq_of_lt hb_lt
    change a.val % d = b.val % d at h_cancel
    rwa [ha_mod, hb_mod] at h_cancel
  have hf_surj : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf_inj
  have ⟨y, hy⟩ := hf_surj ⟨n % d, Nat.mod_lt _ hd_pos⟩
  simp only [f, Fin.mk.injEq] at hy
  have hy_modeq : y.val * t ≡ n [MOD d] := hy
  by_cases hy0 : y.val = 0
  · use d
    refine ⟨by simp [hd], ?_⟩
    have h_dt : d * t ≡ 0 [MOD d] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d t)
    have h_0_yt : (0 : ℕ) ≡ y.val * t [MOD d] := by
      rw [hy0, Nat.zero_mul]
    exact h_dt.trans (h_0_yt.trans hy_modeq)
  · use y.val
    refine ⟨by simp only [mem_Icc]; omega, hy_modeq⟩

/-- Canonical modular multiplier in {1, ..., d}. -/
noncomputable def invXt (n d t : ℕ) : ℕ :=
  if hd : 1 ≤ d then
    if ht : t.Coprime d then
      (exists_xt_modeq n d t hd ht).choose
    else 1
  else 1

lemma invXt_mem (n d t : ℕ) (hd : 1 ≤ d) (ht : t.Coprime d) :
    invXt n d t ∈ Finset.Icc 1 d := by
  dsimp [invXt]
  rw [dif_pos hd, dif_pos ht]
  exact (exists_xt_modeq n d t hd ht).choose_spec.1

lemma invXt_pos (n d t : ℕ) (hd : 1 ≤ d) (ht : t.Coprime d) : 1 ≤ invXt n d t :=
  (Finset.mem_Icc.mp (invXt_mem n d t hd ht)).1

lemma invXt_le (n d t : ℕ) (hd : 1 ≤ d) (ht : t.Coprime d) : invXt n d t ≤ d :=
  (Finset.mem_Icc.mp (invXt_mem n d t hd ht)).2

lemma invXt_modeq (n d t : ℕ) (hd : 1 ≤ d) (ht : t.Coprime d) :
    invXt n d t * t ≡ n [MOD d] := by
  dsimp [invXt]
  rw [dif_pos hd, dif_pos ht]
  exact (exists_xt_modeq n d t hd ht).choose_spec.2

/-- High congruence block: {a ∈ {1, ..., n-1} | a ≡ t [MOD d] ∧ xt * a > n}. -/
def congruenceBlockHigh (n d t xt : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun a => a ≡ t [MOD d] ∧ n < xt * a)

/-- Mid congruence block: {a ∈ {1, ..., n-1} | a ≡ t [MOD d] ∧ (d + xt) * a > n ∧ xt * a < n}. -/
def congruenceBlockMid (n d t xt : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun a => a ≡ t [MOD d] ∧ n < (d + xt) * a ∧ xt * a < n)

/-- Conlon–Fox–Pham High Block Avoidance:
    The high congruence block avoids subset sums equal to n. -/
lemma congruence_block_high_avoids (n d t xt : ℕ) (hn : 2 ≤ n) (_hd : 1 ≤ d)
    (hxt_pos : 1 ≤ xt) (hxt_le : xt ≤ d) (ht_coprime : t.Coprime d)
    (hxt_eq : xt * t ≡ n [MOD d]) :
    AvoidsSubsetSum (congruenceBlockHigh n d t xt) n := by
  rintro ⟨A, hA, h_sum⟩
  have hA_ne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.sum_empty, id_eq] at h_sum
    omega
  have hA_card_pos : 1 ≤ A.card := Finset.Nonempty.card_pos hA_ne
  have hA_mod : ∀ a ∈ A, a ≡ t [MOD d] := by
    intro a ha
    have ha_mem := hA ha
    simp only [congruenceBlockHigh, Finset.mem_filter] at ha_mem
    exact ha_mem.2.1
  have h_sum_mod := congruence_sum_modeq A hA_mod
  have h_sum_val : (∑ a ∈ A, a) = n := h_sum
  rw [h_sum_val] at h_sum_mod
  have h_equiv : A.card * t ≡ xt * t [MOD d] := h_sum_mod.symm.trans hxt_eq.symm
  have hd_gcd : d.gcd t = 1 := ht_coprime.symm.gcd_eq_one
  have h_card_mod : A.card ≡ xt [MOD d] :=
    Nat.ModEq.cancel_right_of_coprime hd_gcd h_equiv
  have h_xt_le_card : xt ≤ A.card :=
    card_ge_of_modeq A.card xt d hA_card_pos hxt_le h_card_mod
  have h_each_gt : ∀ a ∈ A, n + 1 ≤ xt * a := by
    intro a ha
    have ha_mem := hA ha
    simp only [congruenceBlockHigh, Finset.mem_filter] at ha_mem
    omega
  have h_sum_mul : xt * n = ∑ a ∈ A, (xt * a) := by
    rw [← Finset.mul_sum, h_sum_val]
  have h_sum_ge : ∑ a ∈ A, (n + 1) ≤ ∑ a ∈ A, (xt * a) :=
    Finset.sum_le_sum (fun a ha => h_each_gt a ha)
  have h_const : (∑ a ∈ A, (n + 1)) = A.card * (n + 1) := by simp
  rw [h_const, ← h_sum_mul] at h_sum_ge
  have h_bound : xt * (n + 1) ≤ xt * n := by
    calc xt * (n + 1) ≤ A.card * (n + 1) := Nat.mul_le_mul_right (n + 1) h_xt_le_card
    _ ≤ xt * n := h_sum_ge
  have : xt * (n + 1) = xt * n + xt := by ring
  omega

/-- Conlon–Fox–Pham Mid Block Avoidance:
    The mid congruence block avoids subset sums equal to n. -/
lemma congruence_block_mid_avoids (n d t xt : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hxt_pos : 1 ≤ xt) (hxt_le : xt ≤ d) (ht_coprime : t.Coprime d)
    (hxt_eq : xt * t ≡ n [MOD d]) :
    AvoidsSubsetSum (congruenceBlockMid n d t xt) n := by
  rintro ⟨A, hA, h_sum⟩
  have hA_ne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.sum_empty, id_eq] at h_sum
    omega
  have hA_card_pos : 1 ≤ A.card := Finset.Nonempty.card_pos hA_ne
  have hA_mod : ∀ a ∈ A, a ≡ t [MOD d] := by
    intro a ha
    have ha_mem := hA ha
    simp only [congruenceBlockMid, Finset.mem_filter] at ha_mem
    exact ha_mem.2.1
  have h_sum_mod := congruence_sum_modeq A hA_mod
  have h_sum_val : (∑ a ∈ A, a) = n := h_sum
  rw [h_sum_val] at h_sum_mod
  have h_equiv : A.card * t ≡ xt * t [MOD d] := h_sum_mod.symm.trans hxt_eq.symm
  have hd_gcd : d.gcd t = 1 := ht_coprime.symm.gcd_eq_one
  have h_card_mod : A.card ≡ xt [MOD d] :=
    Nat.ModEq.cancel_right_of_coprime hd_gcd h_equiv
  have h_cases := card_cases_of_modeq A.card xt d hA_card_pos hxt_le hd h_card_mod
  rcases h_cases with h_card_eq | h_card_ge
  · have h_each_lt : ∀ a ∈ A, xt * a ≤ n - 1 := by
      intro a ha
      have ha_mem := hA ha
      simp only [congruenceBlockMid, Finset.mem_filter] at ha_mem
      omega
    have h_sum_mul : xt * n = ∑ a ∈ A, (xt * a) := by
      rw [← Finset.mul_sum, h_sum_val]
    have h_sum_le : ∑ a ∈ A, (xt * a) ≤ ∑ a ∈ A, (n - 1) :=
      Finset.sum_le_sum (fun a ha => h_each_lt a ha)
    have h_const : (∑ a ∈ A, (n - 1)) = A.card * (n - 1) := by simp
    rw [h_const, ← h_sum_mul, h_card_eq] at h_sum_le
    have h_bound : xt * n ≤ xt * (n - 1) := h_sum_le
    have : xt * n = xt * (n - 1) + xt := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
    omega
  · have h_each_gt : ∀ a ∈ A, n + 1 ≤ (d + xt) * a := by
      intro a ha
      have ha_mem := hA ha
      simp only [congruenceBlockMid, Finset.mem_filter] at ha_mem
      omega
    have h_sum_mul : (d + xt) * n = ∑ a ∈ A, ((d + xt) * a) := by
      rw [← Finset.mul_sum, h_sum_val]
    have h_sum_ge : ∑ a ∈ A, (n + 1) ≤ ∑ a ∈ A, ((d + xt) * a) :=
      Finset.sum_le_sum (fun a ha => h_each_gt a ha)
    have h_const : (∑ a ∈ A, (n + 1)) = A.card * (n + 1) := by simp
    rw [h_const, ← h_sum_mul] at h_sum_ge
    have h_bound : (d + xt) * (n + 1) ≤ (d + xt) * n := by
      calc (d + xt) * (n + 1) ≤ A.card * (n + 1) := Nat.mul_le_mul_right (n + 1) h_card_ge
      _ ≤ (d + xt) * n := h_sum_ge
    have : (d + xt) * (n + 1) = (d + xt) * n + (d + xt) := by ring
    omega

/-- Conlon-Fox-Pham remainder set: elements x in {1, ..., n-1} not covered by:
    1. Interval blocks: (s1 + 1) * x < n
    2. Prime multiples: ∀ p ∈ P, ¬ p ∣ x
    3. High congruence blocks: ¬ ∃ t ∈ reducedResidues d, x ≡ t [MOD d] ∧ n < invXt n d t * x
    4. Mid congruence blocks: ¬ ∃ t ∈ reducedResidues d, x ≡ t [MOD d] ∧
       n < (d + invXt n d t) * x ∧ invXt n d t * x < n -/
noncomputable def cfpRemainder (n s1 d : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun x =>
    (s1 + 1) * x < n ∧
    (∀ p ∈ P, ¬ p ∣ x) ∧
    (∀ t ∈ reducedResidues d,
      x ≡ t [MOD d] →
      let xt := invXt n d t
      ¬ (n < xt * x) ∧ ¬ (n < (d + xt) * x ∧ xt * x < n)))

lemma cfp_remainder_subset_sieve_remainder (n s1 d : ℕ) (P : Finset ℕ) :
    cfpRemainder n s1 d P ⊆ sieveRemainder n s1 P := by
  intro x hx
  simp only [cfpRemainder, sieveRemainder, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

/-- The 4-layer family of sets in the Conlon-Fox-Pham (2021) construction. -/
noncomputable def conlonFoxPhamFamily (n s1 : ℕ) (P : Finset ℕ) (d s_rem : ℕ) (i : ℕ) : Finset ℕ :=
  if i < s1 then
    intervalBlock n (i + 1)
  else if i < s1 + P.card then
    (Finset.Ico 1 n).filter (fun x => P.toList[i - s1]! ∣ x)
  else if i < s1 + P.card + (reducedResidues d).card then
    congruenceBlockHigh n d ((reducedResidues d).toList[i - (s1 + P.card)]!) (invXt n d ((reducedResidues d).toList[i - (s1 + P.card)]!))
  else if i < s1 + P.card + 2 * (reducedResidues d).card then
    congruenceBlockMid n d ((reducedResidues d).toList[i - (s1 + P.card + (reducedResidues d).card)]!) (invXt n d ((reducedResidues d).toList[i - (s1 + P.card + (reducedResidues d).card)]!))
  else
    sieveBlock (cfpRemainder n s1 d P) s_rem (i - (s1 + P.card + 2 * (reducedResidues d).card))

/-- Conlon–Fox–Pham (2021) Upper Bound Theorem:
    Given n ≥ 2, interval block count s1 ≥ 1, modulus d ≥ 1 coprime to n,
    primes P not dividing n, and remainder partition parameter 1 ≤ s_rem ≤ s1,
    there exists a coloring of {1, ..., n-1} with
      s1 + |P| + 2 * |reducedResidues d| + ⌈|R_cfp| / s_rem⌉
    colors avoiding monochromatic subset sums to n. -/
theorem exists_coloring_conlon_fox_pham (n s1 : ℕ) (P : Finset ℕ) (d s_rem : ℕ)
    (hn : 2 ≤ n) (hs1 : 1 ≤ s1) (hd : 1 ≤ d) (hs_rem : 1 ≤ s_rem) (h_srem_le : s_rem ≤ s1)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    let T := reducedResidues d
    let R := cfpRemainder n s1 d P
    ∃ c : ℕ → Fin (s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem),
      AvoidsMonoSubsetSum n (s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem) c := by
  let T := reducedResidues d
  let R := cfpRemainder n s1 d P
  let m := s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem
  have hs1_m : s1 ≤ m :=
    (Nat.le_add_right s1 P.card).trans
      ((Nat.le_add_right (s1 + P.card) (2 * T.card)).trans
        (Nat.le_add_right (s1 + P.card + 2 * T.card) ((R.card + s_rem - 1) / s_rem)))
  have hm : 1 ≤ m := hs1.trans hs1_m
  have h_sp_m : s1 + P.card ≤ m :=
    (Nat.le_add_right (s1 + P.card) (2 * T.card)).trans
      (Nat.le_add_right (s1 + P.card + 2 * T.card) ((R.card + s_rem - 1) / s_rem))
  have h_mid_m : s1 + P.card + 2 * T.card ≤ m :=
    Nat.le_add_right (s1 + P.card + 2 * T.card) ((R.card + s_rem - 1) / s_rem)
  let S : Fin m → Finset ℕ := fun i => conlonFoxPhamFamily n s1 P d s_rem i.val
  apply exists_coloring_of_avoiding_family hm S
  · intro i
    dsimp [S, conlonFoxPhamFamily]
    split_ifs with h1 h2 h3 h4
    · exact interval_block_avoids_subset_sum n (i.val + 1) hn (by omega)
    · have h_len : i.val - s1 < P.toList.length := by
        rw [Finset.length_toList]
        omega
      rw [getElem!_pos P.toList (i.val - s1) h_len]
      apply dvd_subset_sum_free _ (P.toList[i.val - s1]) n
      · have hp_mem : P.toList[i.val - s1] ∈ P := by
          rw [← Finset.mem_toList]
          apply List.mem_iff_getElem.mpr
          exact ⟨i.val - s1, h_len, rfl⟩
        exact hP _ hp_mem
      · intro x hx
        simp only [Finset.mem_filter] at hx
        exact hx.2
    · have h_len : i.val - (s1 + P.card) < (reducedResidues d).toList.length := by
        rw [Finset.length_toList]
        omega
      rw [getElem!_pos (reducedResidues d).toList (i.val - (s1 + P.card)) h_len]
      have ht_mem : (reducedResidues d).toList[i.val - (s1 + P.card)] ∈ reducedResidues d := by
        rw [← Finset.mem_toList]
        apply List.mem_iff_getElem.mpr
        exact ⟨i.val - (s1 + P.card), h_len, rfl⟩
      have ht_mem' := ht_mem
      simp only [reducedResidues, Finset.mem_filter] at ht_mem'
      have ht_cop : ((reducedResidues d).toList[i.val - (s1 + P.card)]).Coprime d := ht_mem'.2
      exact congruence_block_high_avoids n d _ _ hn hd
        (invXt_pos n d _ hd ht_cop) (invXt_le n d _ hd ht_cop) ht_cop
        (invXt_modeq n d _ hd ht_cop)
    · have h_len : i.val - (s1 + P.card + (reducedResidues d).card) < (reducedResidues d).toList.length := by
        rw [Finset.length_toList]
        omega
      rw [getElem!_pos (reducedResidues d).toList (i.val - (s1 + P.card + (reducedResidues d).card)) h_len]
      have ht_mem : (reducedResidues d).toList[i.val - (s1 + P.card + (reducedResidues d).card)] ∈ reducedResidues d := by
        rw [← Finset.mem_toList]
        apply List.mem_iff_getElem.mpr
        exact ⟨i.val - (s1 + P.card + (reducedResidues d).card), h_len, rfl⟩
      have ht_mem' := ht_mem
      simp only [reducedResidues, Finset.mem_filter] at ht_mem'
      have ht_cop : ((reducedResidues d).toList[i.val - (s1 + P.card + (reducedResidues d).card)]).Coprime d := ht_mem'.2
      exact congruence_block_mid_avoids n d _ _ hn hd
        (invXt_pos n d _ hd ht_cop) (invXt_le n d _ hd ht_cop) ht_cop
        (invXt_modeq n d _ hd ht_cop)
    · apply small_card_block_avoids_subset_sum (sieveBlock R s_rem (i.val - (s1 + P.card + 2 * (reducedResidues d).card))) n s_rem hn
      · exact sieve_block_card_le R s_rem _
      · intro x hx
        have h_sub := sieve_block_subset R s_rem _ hx
        simp only [R, cfpRemainder, Finset.mem_filter] at h_sub
        have h_s1_x := h_sub.2.1
        have : (s_rem + 1) * x ≤ (s1 + 1) * x := Nat.mul_le_mul_right x (by omega)
        omega
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    by_cases h_large : n ≤ (s1 + 1) * x
    · have hx_pos : 0 < x := by omega
      let k := (n - 1) / x
      have hk_ge : 1 ≤ k := by
        apply Nat.div_pos
        · omega
        · exact hx_pos
      have hk_le : k ≤ s1 := by
        have : n - 1 < (s1 + 1) * x := by omega
        rw [Nat.mul_comm (s1 + 1) x] at this
        have := Nat.div_lt_of_lt_mul this
        omega
      let i_val := k - 1
      have hi_s1 : i_val < s1 := by omega
      have hi_lt : i_val < m := hi_s1.trans_le hs1_m
      use ⟨i_val, hi_lt⟩
      dsimp [S, conlonFoxPhamFamily]
      rw [if_pos hi_s1]
      have hk_eq : i_val + 1 = k := by omega
      rw [hk_eq]
      simp only [intervalBlock, Finset.mem_filter, Finset.mem_Ico, hx, true_and]
      refine ⟨?_, ?_⟩
      · have h_div_mod := Nat.div_add_mod (n - 1) x
        have h_mod := Nat.mod_lt (n - 1) hx_pos
        rw [Nat.mul_comm x k] at h_div_mod
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have : (n - 1) / x * x ≤ n - 1 := Nat.div_mul_le_self (n - 1) x
        have : k * x ≤ n - 1 := this
        omega
    · have h_small : (s1 + 1) * x < n := by omega
      by_cases h_div : ∃ p ∈ P, p ∣ x
      · obtain ⟨p, hpP, hpx⟩ := h_div
        rw [← Finset.mem_toList] at hpP
        obtain ⟨idx, h_idx, rfl⟩ := List.mem_iff_getElem.mp hpP
        have h_idx_card : idx < P.card := by
          have := h_idx
          rw [Finset.length_toList] at this
          exact this
        let i_val := s1 + idx
        have hi_lt_sp : i_val < s1 + P.card := by omega
        have hi_lt : i_val < m := hi_lt_sp.trans_le h_sp_m
        use ⟨i_val, hi_lt⟩
        dsimp [S, conlonFoxPhamFamily]
        have h1_not : ¬ i_val < s1 := by omega
        rw [if_neg h1_not, if_pos hi_lt_sp]
        have h_idx_eq : i_val - s1 = idx := by omega
        rw [h_idx_eq]
        rw [getElem!_pos P.toList idx h_idx]
        simp only [Finset.mem_filter, Finset.mem_Ico, hx, hpx, and_self]
      · push Not at h_div
        by_cases h_high : ∃ t ∈ reducedResidues d, x ≡ t [MOD d] ∧ n < invXt n d t * x
        · obtain ⟨t, ht_mem, hxt_mod, hxt_high⟩ := h_high
          have ht_in_list := ht_mem
          rw [← Finset.mem_toList] at ht_in_list
          obtain ⟨idx, h_idx, rfl⟩ := List.mem_iff_getElem.mp ht_in_list
          have h_idx_card : idx < (reducedResidues d).card := by
            have := h_idx
            rw [Finset.length_toList] at this
            exact this
          let i_val := s1 + P.card + idx
          have hi_lt_high : i_val < s1 + P.card + (reducedResidues d).card := by omega
          have hi_mid_le : s1 + P.card + (reducedResidues d).card ≤ s1 + P.card + 2 * (reducedResidues d).card := by omega
          have hi_lt : i_val < m := (hi_lt_high.trans_le hi_mid_le).trans_le h_mid_m
          use ⟨i_val, hi_lt⟩
          dsimp [S, conlonFoxPhamFamily]
          have h1_not : ¬ i_val < s1 := by omega
          have h2_not : ¬ i_val < s1 + P.card := by omega
          rw [if_neg h1_not, if_neg h2_not, if_pos hi_lt_high]
          have h_idx_eq : i_val - (s1 + P.card) = idx := by omega
          rw [h_idx_eq]
          rw [getElem!_pos (reducedResidues d).toList idx h_idx]
          simp only [congruenceBlockHigh, Finset.mem_filter, Finset.mem_Ico, hx, hxt_mod, hxt_high, and_self]
        · push Not at h_high
          by_cases h_mid : ∃ t ∈ reducedResidues d, x ≡ t [MOD d] ∧ n < (d + invXt n d t) * x ∧ invXt n d t * x < n
          · obtain ⟨t, ht_mem, hxt_mod, hxt_mid1, hxt_mid2⟩ := h_mid
            have ht_in_list := ht_mem
            rw [← Finset.mem_toList] at ht_in_list
            obtain ⟨idx, h_idx, rfl⟩ := List.mem_iff_getElem.mp ht_in_list
            have h_idx_card : idx < (reducedResidues d).card := by
              have := h_idx
              rw [Finset.length_toList] at this
              exact this
            let i_val := s1 + P.card + (reducedResidues d).card + idx
            have hi_lt_mid : i_val < s1 + P.card + 2 * (reducedResidues d).card := by omega
            have hi_lt : i_val < m := hi_lt_mid.trans_le h_mid_m
            use ⟨i_val, hi_lt⟩
            dsimp [S, conlonFoxPhamFamily]
            have h1_not : ¬ i_val < s1 := by omega
            have h2_not : ¬ i_val < s1 + P.card := by omega
            have h3_not : ¬ i_val < s1 + P.card + (reducedResidues d).card := by omega
            rw [if_neg h1_not, if_neg h2_not, if_neg h3_not, if_pos hi_lt_mid]
            have h_idx_eq : i_val - (s1 + P.card + (reducedResidues d).card) = idx := by omega
            rw [h_idx_eq]
            rw [getElem!_pos (reducedResidues d).toList idx h_idx]
            simp only [congruenceBlockMid, Finset.mem_filter, Finset.mem_Ico, hx, hxt_mod, hxt_mid1, hxt_mid2, and_self]
          · push Not at h_mid
            have hx_R : x ∈ R := by
              simp only [R, cfpRemainder, Finset.mem_filter, Finset.mem_Ico, hx, h_small, true_and]
              refine ⟨h_div, fun t ht hmod => ?_⟩
              have h1 : ¬ (n < invXt n d t * x) := by
                have := h_high t ht hmod
                omega
              have h2 : ¬ (n < (d + invXt n d t) * x ∧ invXt n d t * x < n) := by
                intro ⟨h_mid1, h_mid2⟩
                have := h_mid t ht hmod h_mid1
                omega
              exact ⟨h1, h2⟩
            obtain ⟨j, hj_lt, hj_mem⟩ := mem_sieve_block_of_mem hs_rem hx_R
            let i_val := s1 + P.card + 2 * (reducedResidues d).card + j
            have hi_lt : i_val < m :=
              Nat.add_lt_add_left hj_lt (s1 + P.card + 2 * (reducedResidues d).card)
            use ⟨i_val, hi_lt⟩
            dsimp [S, conlonFoxPhamFamily]
            have h1_not : ¬ i_val < s1 := by omega
            have h2_not : ¬ i_val < s1 + P.card := by omega
            have h3_not : ¬ i_val < s1 + P.card + (reducedResidues d).card := by omega
            have h4_not : ¬ i_val < s1 + P.card + 2 * (reducedResidues d).card := by omega
            rw [if_neg h1_not, if_neg h2_not, if_neg h3_not, if_neg h4_not]
            have : i_val - (s1 + P.card + 2 * (reducedResidues d).card) = j := by omega
            rw [this]
            exact hj_mem

/-- Conlon–Fox–Pham (2021) Chromatic Bound:
    f(n) ≤ s1 + |P| + 2 * |reducedResidues d| + ⌈|R_cfp| / s_rem⌉. -/
theorem minColors_le_conlon_fox_pham (n s1 : ℕ) (P : Finset ℕ) (d s_rem : ℕ)
    (hn : 2 ≤ n) (hs1 : 1 ≤ s1) (hd : 1 ≤ d) (hs_rem : 1 ≤ s_rem) (h_srem_le : s_rem ≤ s1)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    let T := reducedResidues d
    let R := cfpRemainder n s1 d P
    minColors n hn ≤ s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem := by
  let T := reducedResidues d
  let R := cfpRemainder n s1 d P
  obtain ⟨c, hc⟩ := exists_coloring_conlon_fox_pham n s1 P d s_rem hn hs1 hd hs_rem h_srem_le hP
  exact minColors_le n hn ⟨c, hc⟩

/-- Coarser bound with 2*d:
    f(n) ≤ s1 + |P| + 2 * d + ⌈|R_cfp| / s_rem⌉. -/
theorem minColors_le_conlon_fox_pham_coarse (n s1 : ℕ) (P : Finset ℕ) (d s_rem : ℕ)
    (hn : 2 ≤ n) (hs1 : 1 ≤ s1) (hd : 1 ≤ d) (hs_rem : 1 ≤ s_rem) (h_srem_le : s_rem ≤ s1)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    let R := cfpRemainder n s1 d P
    minColors n hn ≤ s1 + P.card + 2 * d + (R.card + s_rem - 1) / s_rem := by
  have h_main := minColors_le_conlon_fox_pham n s1 P d s_rem hn hs1 hd hs_rem h_srem_le hP
  have h_T := reducedResidues_card_le d
  omega

/-!
### Section 8: Conlon–Fox–Pham Lower Bound Formulation & Combinatorial Reductions

In arXiv:2104.14766 (Theorem 1.5/1.6 and Section 5.1), Conlon, Fox, and Pham establish the matching
lower bound f(n) ≥ c * F(n) by analyzing monochromatic subset sums via inverse additive combinatorics.

The mathematical structure of the lower bound consists of:
1. Monotonicity of Valid Colorings:
   If {1, ..., n-1} cannot be colored by k colors avoiding monochromatic subset sum n,
   then f(n) ≥ k + 1.
2. Combinatorial Pigeonhole Principle for Fibers:
   Any k-coloring of a base set S partitions S into k monochromatic classes.
   If |S| > k * M, there exists at least one monochromatic class of size ≥ M + 1.
3. Additive Progression / Dense Subset Sum Hitting:
   If every subset A ⊆ S of size ≥ M + 1 contains an arithmetic progression covering n
   (or has n ∈ subsetSums A), then this dense monochromatic class hits n.
4. Conlon–Fox–Pham Lower Bound Witness:
   Encapsulates this density-progression data into a structure `CFPLowerBoundWitness n k`,
   yielding f(n) ≥ k + 1.
5. Specialization:
   Instantiates the witness concretely for k = 1 to recover f(n) ≥ 2 for all n ≥ 3.
-/

/-- Monotone lifting of valid colorings: if a valid m-coloring exists and m ≤ k,
    then a valid k-coloring exists. -/
lemma hasValidColoring_of_le (n : ℕ) (hn : 2 ≤ n) {m k : ℕ}
    (hm : HasValidColoring n m) (hmk : m ≤ k) :
    HasValidColoring n k := by
  obtain ⟨c, hc⟩ := hm
  by_cases hm0 : m = 0
  · subst hm0
    have h1 : 1 ∈ Finset.Ico 1 n := by
      simp only [Finset.mem_Ico]
      omega
    exact Fin.elim0 (c 1)
  · have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
    have hk_pos : 1 ≤ k := hm_pos.trans hmk
    let c' : ℕ → Fin k := fun x => Fin.castLE hmk (c x)
    refine ⟨c', fun j => ?_⟩
    intro ⟨A, hA_sub, hA_sum⟩
    have hA_ne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp only [Finset.sum_empty] at hA_sum
      omega
    obtain ⟨a, ha⟩ := hA_ne
    have ha_mem := hA_sub ha
    simp only [Finset.mem_filter] at ha_mem
    have ha_val : (c' a).val = j.val := by
      rw [ha_mem.2]
    have hj_lt : j.val < m := by
      have : (c' a).val = (c a).val := rfl
      rw [this] at ha_val
      rw [← ha_val]
      exact (c a).isLt
    let j0 : Fin m := ⟨j.val, hj_lt⟩
    have hA_sub_j0 : A ⊆ (Finset.Ico 1 n).filter (fun x => c x = j0) := by
      intro x hx
      have hx_mem := hA_sub hx
      simp only [Finset.mem_filter] at hx_mem ⊢
      refine ⟨hx_mem.1, ?_⟩
      have : (c' x).val = (c x).val := rfl
      have hx_val : (c' x).val = j.val := by rw [hx_mem.2]
      rw [this] at hx_val
      ext
      exact hx_val
    have hc_j0 := hc j0
    exact hc_j0 ⟨A, hA_sub_j0, hA_sum⟩

/-- Chromatic lower bound from non-existence of valid k-coloring:
    if no k-coloring avoids monochromatic subset sums to n, then f(n) > k. -/
theorem minColors_gt_of_not_hasValidColoring (n k : ℕ) (hn : 2 ≤ n)
    (h_not : ¬ HasValidColoring n k) :
    k < minColors n hn := by
  by_contra h_le
  push Not at h_le
  have h_col := minColors_has_coloring n hn
  have h_val := hasValidColoring_of_le n hn h_col h_le
  exact h_not h_val

/-- Chromatic lower bound: f(n) ≥ k + 1 when k colors are insufficient. -/
theorem minColors_ge_of_not_hasValidColoring (n k : ℕ) (hn : 2 ≤ n)
    (h_not : ¬ HasValidColoring n k) :
    k + 1 ≤ minColors n hn :=
  minColors_gt_of_not_hasValidColoring n k hn h_not

/-- Fiber sum partition: the sum of cardinalities of color fibers equals the total cardinality. -/
lemma monochromatic_fiber_sum_eq (S : Finset ℕ) (k : ℕ) (c : ℕ → Fin k) :
    ∑ i : Fin k, (S.filter (fun x => c x = i)).card = S.card := by
  have : ∑ i : Fin k, (S.filter (fun x => c x = i)).card =
      ∑ i : Fin k, ∑ x ∈ S, if c x = i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_filter]
  rw [this, Finset.sum_comm]
  have h_inner : ∀ x ∈ S, (∑ i : Fin k, if c x = i then 1 else 0) = 1 := by
    intro x _
    have h_eq : (Finset.univ.filter (fun i : Fin k => c x = i)) = {c x} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm
    have h_sum : (∑ i : Fin k, if c x = i then 1 else 0) =
        (Finset.univ.filter (fun i : Fin k => c x = i)).card := by
      rw [Finset.card_filter]
    rw [h_sum, h_eq, Finset.card_singleton]
  have : (∑ x ∈ S, ∑ i : Fin k, if c x = i then 1 else 0) = ∑ x ∈ S, 1 :=
    Finset.sum_congr rfl h_inner
  rw [this]
  exact (Finset.card_eq_sum_ones S).symm

/-- Combinatorial Pigeonhole Principle for Colorings (strict form):
    If |S| > k * M, there exists at least one color i whose fiber has size > M. -/
lemma exists_monochromatic_fiber_strict (S : Finset ℕ) (k M : ℕ) (c : ℕ → Fin k)
    (h_card : k * M < S.card) :
    ∃ i : Fin k, M < (S.filter (fun x => c x = i)).card := by
  by_contra h_not
  push Not at h_not
  have h_sum_le : (∑ i : Fin k, (S.filter (fun x => c x = i)).card) ≤ ∑ i : Fin k, M :=
    Finset.sum_le_sum (fun i _ => h_not i)
  rw [monochromatic_fiber_sum_eq] at h_sum_le
  have h_const : (∑ i : Fin k, M) = k * M := by
    simp
  rw [h_const] at h_sum_le
  omega

/-- Subset sums: the set of all integers expressible as a sum of a subset of A. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset).image (fun B => B.sum id)

lemma mem_subsetSums_iff (A : Finset ℕ) (s : ℕ) :
    s ∈ subsetSums A ↔ ∃ B : Finset ℕ, B ⊆ A ∧ B.sum id = s := by
  simp only [subsetSums, Finset.mem_image, Finset.mem_powerset]

/-- Lemma A: Addition of subset sums of disjoint sets. -/
lemma subsetSums_add_of_disjoint {A B : Finset ℕ} (h_disj : Disjoint A B)
    {x y : ℕ} (hx : x ∈ subsetSums A) (hy : y ∈ subsetSums B) :
    x + y ∈ subsetSums (A ∪ B) := by
  rw [mem_subsetSums_iff] at hx hy ⊢
  obtain ⟨SA, hSA, rfl⟩ := hx
  obtain ⟨SB, hSB, rfl⟩ := hy
  have h_disj_S : Disjoint SA SB := by
    rw [Finset.disjoint_left] at h_disj ⊢
    intro z hzA hzB
    exact h_disj (hSA hzA) (hSB hzB)
  use SA ∪ SB
  refine ⟨Finset.union_subset_union hSA hSB, ?_⟩
  exact Finset.sum_union h_disj_S

/-- Lemma B (Single Element): Single element interval extension for subset sums. -/
lemma subsetSums_interval_extend_single {A : Finset ℕ} {t a b : ℕ}
    (ht_not : t ∉ A)
    (h_sub : Finset.Icc a b ⊆ subsetSums A)
    (ht_le : t ≤ b - a + 1)
    (hab : a ≤ b) :
    Finset.Icc a (b + t) ⊆ subsetSums (insert t A) := by
  intro x hx
  simp only [Finset.mem_Icc] at hx
  by_cases hxb : x ≤ b
  · have hx_in : x ∈ Finset.Icc a b := by simp only [Finset.mem_Icc, hx.1, hxb, and_self]
    have hx_sub := h_sub hx_in
    rw [mem_subsetSums_iff] at hx_sub ⊢
    obtain ⟨S, hS, hS_sum⟩ := hx_sub
    exact ⟨S, hS.trans (Finset.subset_insert t A), hS_sum⟩
  · push Not at hxb
    have hx_ge_at : a + t ≤ x := by omega
    let y := x - t
    have hy_in : y ∈ Finset.Icc a b := by simp only [Finset.mem_Icc]; omega
    have hy_sub := h_sub hy_in
    rw [mem_subsetSums_iff] at hy_sub ⊢
    obtain ⟨S, hS, hS_sum⟩ := hy_sub
    use insert t S
    have h_sub_ins : insert t S ⊆ insert t A := Finset.insert_subset_insert t hS
    refine ⟨h_sub_ins, ?_⟩
    have ht_not_S : t ∉ S := fun h => ht_not (hS h)
    rw [Finset.sum_insert ht_not_S, hS_sum]
    dsimp; omega

/-- Lemma B (Inductive): Interval extension for subset sums over an auxiliary disjoint set B. -/
lemma subsetSums_interval_extend {A B : Finset ℕ} {a b : ℕ}
    (h_disj : Disjoint A B)
    (h_sub : Finset.Icc a b ⊆ subsetSums A)
    (hB_le : ∀ t ∈ B, t ≤ b - a + 1)
    (hab : a ≤ b) :
    Finset.Icc a (b + B.sum id) ⊆ subsetSums (A ∪ B) := by
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, add_zero, Finset.union_empty]
    exact h_sub
  | @insert t B0 ht_not_B0 ih =>
    rw [Finset.sum_insert ht_not_B0]
    have ht_in : t ∈ insert t B0 := Finset.mem_insert_self t B0
    have ht_le : t ≤ b - a + 1 := hB_le t ht_in
    have h_disj_B0 : Disjoint A B0 := by
      rw [Finset.disjoint_left] at h_disj ⊢
      intro z hzA hzB0
      exact h_disj hzA (Finset.mem_insert_of_mem hzB0)
    have hB0_le : ∀ s ∈ B0, s ≤ b - a + 1 := fun s hs => hB_le s (Finset.mem_insert_of_mem hs)
    have ih_res := ih h_disj_B0 hB0_le
    have ht_not_A : t ∉ A := by
      rw [Finset.disjoint_right] at h_disj
      exact h_disj ht_in
    have ht_not_AB0 : t ∉ A ∪ B0 := by
      simp only [Finset.mem_union, not_or]
      exact ⟨ht_not_A, ht_not_B0⟩
    have hab' : a ≤ b + B0.sum id := hab.trans (Nat.le_add_right b (B0.sum id))
    have ht_le' : t ≤ (b + B0.sum id) - a + 1 := by omega
    have h_step := subsetSums_interval_extend_single ht_not_AB0 ih_res ht_le' hab'
    have h_union_eq : insert t (A ∪ B0) = A ∪ insert t B0 := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    rw [h_union_eq] at h_step
    have h_add_comm : b + (id t + B0.sum id) = b + B0.sum id + t := by
      dsimp [id]; omega
    rw [h_add_comm]
    exact h_step

/-- Lemma C: Scaling of subset sums: if Q scaled by v is in A, then v * m ∈ subsetSums A for m ∈ subsetSums Q. -/
lemma subsetSums_scale {Q A : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (h_sub : Q.image (fun x => v * x) ⊆ A)
    {m : ℕ} (hm : m ∈ subsetSums Q) :
    v * m ∈ subsetSums A := by
  rw [mem_subsetSums_iff] at hm ⊢
  obtain ⟨B, hB_sub, hB_sum⟩ := hm
  use B.image (fun x => v * x)
  have hB'_sub : B.image (fun x => v * x) ⊆ A :=
    (Finset.image_subset_image hB_sub).trans h_sub
  refine ⟨hB'_sub, ?_⟩
  have h_inj : Set.InjOn (fun x => v * x) B := by
    intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left hv hxy
  rw [Finset.sum_image h_inj]
  have : (∑ x ∈ B, id (v * x)) = v * B.sum id := by
    dsimp [id]
    rw [← Finset.mul_sum]
    rfl
  rw [this, hB_sum]

/-- Lemma C (Corollary): Multiple scaling hitting lemma: if v ∣ n and (n / v) ∈ subsetSums Q, then n ∈ subsetSums A. -/
lemma mem_subsetSums_of_scaled {Q A : Finset ℕ} {v n : ℕ} (hv : 0 < v) (hvn : v ∣ n)
    (h_sub : Q.image (fun x => v * x) ⊆ A)
    (hm : n / v ∈ subsetSums Q) :
    n ∈ subsetSums A := by
  have h_scale := subsetSums_scale hv h_sub hm
  rw [Nat.mul_div_cancel' hvn] at h_scale
  exact h_scale

lemma nat_le_mul_succ_div_two (m : ℕ) : m ≤ m * (m + 1) / 2 := by
  rcases m with _ | m
  · rfl
  · rw [Nat.le_div_iff_mul_le (by omega)]
    exact Nat.mul_le_mul_left (m + 1) (by omega)

lemma nat_mul_succ_div_two_add (m : ℕ) :
    m * (m + 1) / 2 + (m + 1) = (m + 1) * (m + 2) / 2 := by
  have h := (Nat.add_mul_div_right (m * (m + 1)) (m + 1) (by decide : 0 < 2)).symm
  have h_ring : m * (m + 1) + (m + 1) * 2 = (m + 1) * (m + 2) := by ring
  rw [h_ring] at h
  exact h

/-- Continuous subset sum coverage: the subset sums of {1, ..., m} contain [0, m(m+1)/2]. -/
lemma subsetSums_Icc_zero (m : ℕ) :
    Finset.Icc 0 (m * (m + 1) / 2) ⊆ subsetSums (Finset.Icc 1 m) := by
  induction m with
  | zero =>
    intro x hx
    simp only [Finset.Icc_self, Finset.mem_singleton] at hx
    subst hx
    rw [mem_subsetSums_iff]
    use ∅
    simp
  | succ m ih =>
    have h_insert : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext z; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have ht_not : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc, not_and]; intro _; omega
    have hab : 0 ≤ m * (m + 1) / 2 := by omega
    have ht_le : m + 1 ≤ m * (m + 1) / 2 - 0 + 1 := by
      have := nat_le_mul_succ_div_two m; omega
    have h_step := subsetSums_interval_extend_single ht_not ih ht_le hab
    have h_arith := nat_mul_succ_div_two_add m
    have h_rw : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := h_arith.symm
    rw [h_insert, h_rw]
    exact h_step

/-- Every integer up to m(m+1)/2 is a subset sum of {1, ..., m}. -/
lemma mem_subsetSums_Icc_of_le {m n : ℕ} (hn : n ≤ m * (m + 1) / 2) :
    n ∈ subsetSums (Finset.Icc 1 m) := by
  have h := subsetSums_Icc_zero m
  apply h
  simp only [Finset.mem_Icc]
  exact ⟨Nat.zero_le n, hn⟩

/-- Scaled consecutive interval subset sum hitting:
    if v ∣ n and (n / v) ≤ m(m+1)/2, then n is a subset sum of v * {1, ..., m}. -/
lemma mem_subsetSums_scaled_Icc_of_le {m v n : ℕ} (hv : 0 < v) (hvn : v ∣ n)
    (hn : n / v ≤ m * (m + 1) / 2) :
    n ∈ subsetSums ((Finset.Icc 1 m).image (fun x => v * x)) := by
  have h_in := mem_subsetSums_Icc_of_le hn
  rw [mem_subsetSums_iff] at h_in ⊢
  obtain ⟨B, hB_sub, hB_sum⟩ := h_in
  use B.image (fun x => v * x)
  refine ⟨Finset.image_subset_image hB_sub, ?_⟩
  have h_inj : Set.InjOn (fun x => v * x) B := by
    intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left hv hxy
  rw [Finset.sum_image h_inj]
  have : (∑ x ∈ B, id (v * x)) = v * B.sum id := by
    dsimp [id]
    rw [← Finset.mul_sum]
    rfl
  rw [this, hB_sum, Nat.mul_div_cancel' hvn]

/-- Conlon–Fox–Pham key scaled subset for lower bound analysis:
    the scaled arithmetic progression v * {1, ..., m}. -/
def cfpLowerBoundSet (v m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).image (fun x => v * x)

/-- The CFP key subset is contained in {1, ..., n-1} whenever v * m < n and 0 < v. -/
lemma cfpLowerBoundSet_subset (n v m : ℕ) (hv : 0 < v) (hvm : v * m < n) :
    cfpLowerBoundSet v m ⊆ Finset.Ico 1 n := by
  intro x hx
  simp only [cfpLowerBoundSet, Finset.mem_image, Finset.mem_Icc] at hx
  obtain ⟨y, ⟨hy1, hym⟩, rfl⟩ := hx
  simp only [Finset.mem_Ico]
  refine ⟨Nat.mul_pos hv (by omega), ?_⟩
  have : v * y ≤ v * m := Nat.mul_le_mul_left v hym
  omega

/-- Cardinality of the CFP key scaled subset equals m. -/
lemma cfpLowerBoundSet_card (v m : ℕ) (hv : 0 < v) :
    (cfpLowerBoundSet v m).card = m := by
  rw [cfpLowerBoundSet]
  have h_inj : Set.InjOn (fun x => v * x) (Finset.Icc 1 m) := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hv hxy
  rw [Finset.card_image_of_injOn h_inj, Nat.card_Icc]
  omega

/-- The subset sums of the CFP key scaled subset contain n whenever v ∣ n and n/v ≤ m(m+1)/2. -/
lemma mem_subsetSums_cfpLowerBoundSet (n v m : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (hn : n / v ≤ m * (m + 1) / 2) :
    n ∈ subsetSums (cfpLowerBoundSet v m) :=
  mem_subsetSums_scaled_Icc_of_le hv hvn hn

/-- Arithmetic progression: {a + l * d | 0 ≤ l ≤ L}. -/
def arithProg (a d L : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).image (fun l => a + l * d)

lemma mem_arithProg_iff (a d L x : ℕ) :
    x ∈ arithProg a d L ↔ ∃ l ≤ L, x = a + l * d := by
  simp only [arithProg, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Nat.lt_succ_iff.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Nat.lt_succ_iff.mpr hl, rfl⟩

lemma not_avoids_of_subsetSums {A : Finset ℕ} {n : ℕ} (hn : n ∈ subsetSums A) :
    ¬ AvoidsSubsetSum A n := by
  rw [mem_subsetSums_iff] at hn
  obtain ⟨B, hB_sub, hB_sum⟩ := hn
  intro h_avoid
  exact h_avoid ⟨B, hB_sub, hB_sum⟩

lemma not_avoids_of_arithProg_subset {A : Finset ℕ} {a d L n : ℕ}
    (h_sub : arithProg a d L ⊆ subsetSums A) (hn : n ∈ arithProg a d L) :
    ¬ AvoidsSubsetSum A n :=
  not_avoids_of_subsetSums (h_sub hn)

lemma not_avoids_of_subset {A B : Finset ℕ} {n : ℕ} (hAB : A ⊆ B)
    (hA : ¬ AvoidsSubsetSum A n) : ¬ AvoidsSubsetSum B n := by
  intro hB
  apply hA
  intro ⟨T, hT_sub, hT_sum⟩
  exact hB ⟨T, hT_sub.trans hAB, hT_sum⟩

/-- Dense subset sum hitting: every subset of S of size at least M has subset sum equal to n. -/
def DenseSubsetSumHitting (S : Finset ℕ) (M n : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ S → M ≤ A.card → ¬ AvoidsSubsetSum A n

/-- Arithmetic progression density witness: every subset of S of size at least M
    contains an arithmetic progression covering n. -/
def APDenseSubsetSumWitness (S : Finset ℕ) (M n : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ S → M ≤ A.card →
    ∃ a d L : ℕ, arithProg a d L ⊆ subsetSums A ∧ n ∈ arithProg a d L

theorem denseSubsetSumHitting_of_ap (S : Finset ℕ) (M n : ℕ)
    (hap : APDenseSubsetSumWitness S M n) :
    DenseSubsetSumHitting S M n := by
  intro A hA hM
  obtain ⟨a, d, L, h_sub, hn⟩ := hap A hA hM
  exact not_avoids_of_arithProg_subset h_sub hn

/-- Dense subset sum theorem: if |S| > k * M and every subset of size M + 1 hits n,
    then any k-coloring fails to avoid monochromatic subset sums to n. -/
theorem not_avoidsMonoSubsetSum_of_dense (n k : ℕ) (c : ℕ → Fin k)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n) (M : ℕ) (hM : k * M < S.card)
    (h_hit : DenseSubsetSumHitting S (M + 1) n) :
    ¬ AvoidsMonoSubsetSum n k c := by
  obtain ⟨i, hi⟩ := exists_monochromatic_fiber_strict S k M c hM
  let A := S.filter (fun x => c x = i)
  have hA_sub : A ⊆ S := Finset.filter_subset _ _
  have hA_card : M + 1 ≤ A.card := hi
  have hA_not : ¬ AvoidsSubsetSum A n := h_hit A hA_sub hA_card
  have hA_fiber : A ⊆ (Finset.Ico 1 n).filter (fun x => c x = i) := by
    intro x hx
    have hx_mem := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hS hx_mem.1, hx_mem.2⟩
  have h_fiber_not := not_avoids_of_subset hA_fiber hA_not
  intro h_mono
  exact h_fiber_not (h_mono i)

/-- Non-existence of valid k-coloring under dense hitting witness. -/
theorem not_hasValidColoring_of_dense (n k : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n) (M : ℕ) (hM : k * M < S.card)
    (h_hit : DenseSubsetSumHitting S (M + 1) n) :
    ¬ HasValidColoring n k := by
  rintro ⟨c, hc⟩
  exact not_avoidsMonoSubsetSum_of_dense n k c S hS M hM h_hit hc

/-- Strict lower bound from dense hitting witness: k < f(n). -/
theorem minColors_gt_of_dense (n k : ℕ) (hn : 2 ≤ n)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n) (M : ℕ) (hM : k * M < S.card)
    (h_hit : DenseSubsetSumHitting S (M + 1) n) :
    k < minColors n hn :=
  minColors_gt_of_not_hasValidColoring n k hn
    (not_hasValidColoring_of_dense n k S hS M hM h_hit)

/-- Lower bound from dense hitting witness: k + 1 ≤ f(n). -/
theorem minColors_ge_of_dense (n k : ℕ) (hn : 2 ≤ n)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n) (M : ℕ) (hM : k * M < S.card)
    (h_hit : DenseSubsetSumHitting S (M + 1) n) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_not_hasValidColoring n k hn
    (not_hasValidColoring_of_dense n k S hS M hM h_hit)

/-- Conlon–Fox–Pham Lower Bound Witness:
    Encapsulates the mathematical data that guarantees no k-coloring
    can avoid monochromatic subset sum to n.
    - S is a chosen subset of {1, ..., n-1}
    - M is the density threshold such that k * M < |S|
    - Any subset of S of size > M hits n in its subset sums. -/
structure CFPLowerBoundWitness (n k : ℕ) : Type where
  S : Finset ℕ
  hS : S ⊆ Finset.Ico 1 n
  M : ℕ
  h_card : k * M < S.card
  h_hit : DenseSubsetSumHitting S (M + 1) n

theorem minColors_ge_of_cfp_witness (n k : ℕ) (hn : 2 ≤ n)
    (w : CFPLowerBoundWitness n k) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_dense n k hn w.S w.hS w.M w.h_card w.h_hit

/-- Conlon–Fox–Pham Additive Progression Witness:
    Encapsulates the Szemerédi–Vu arithmetic progression formulation:
    every subset of size > M produces an AP covering n. -/
structure CFPAPWitness (n k : ℕ) : Type where
  S : Finset ℕ
  hS : S ⊆ Finset.Ico 1 n
  M : ℕ
  h_card : k * M < S.card
  hap : APDenseSubsetSumWitness S (M + 1) n

def CFPLowerBoundWitness.ofAP (n k : ℕ) (w : CFPAPWitness n k) : CFPLowerBoundWitness n k where
  S := w.S
  hS := w.hS
  M := w.M
  h_card := w.h_card
  h_hit := denseSubsetSumHitting_of_ap w.S (w.M + 1) n w.hap

theorem minColors_ge_of_cfp_ap_witness (n k : ℕ) (hn : 2 ≤ n)
    (w : CFPAPWitness n k) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_cfp_witness n k hn (CFPLowerBoundWitness.ofAP n k w)

/-- Conlon–Fox–Pham Asymptotic Lower Bound Reduction:
    If for all sufficiently large n, there exists a lower bound witness
    at scale k + 1 ≥ c * F(n), then f(n) satisfies HasChromaticLowerBound F c. -/
theorem hasChromaticLowerBound_of_cfp_witnesses (F : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (N0 : ℕ)
    (h_wit : ∀ n, 2 ≤ n → N0 ≤ n → ∃ k : ℕ, c * F n ≤ (k + 1 : ℝ) ∧ Nonempty (CFPLowerBoundWitness n k)) :
    HasChromaticLowerBound F c := by
  refine ⟨hc, N0, fun n hn hN => ?_⟩
  obtain ⟨k, h_scale, ⟨w⟩⟩ := h_wit n hn hN
  have h_bound := minColors_ge_of_cfp_witness n k hn w
  have h_cast : (k + 1 : ℝ) ≤ (minColors n hn : ℝ) := by exact_mod_cast h_bound
  exact h_scale.trans h_cast

/-- Unconditional concrete witness for k = 1:
    For any n ≥ 3, the pair {1, n-1} forms a CFPLowerBoundWitness n 1. -/
def cfpWitness_two (n : ℕ) (hn : 3 ≤ n) : CFPLowerBoundWitness n 1 where
  S := {1, n - 1}
  hS := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hx ⊢
    rcases hx with rfl | rfl
    · omega
    · omega
  M := 1
  h_card := by
    have h_ne : 1 ≠ n - 1 := by omega
    have h_card : ({1, n - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [h_ne]), Finset.card_singleton]
    rw [h_card]
    omega
  h_hit := by
    intro A hA hM
    have h_ne : 1 ≠ n - 1 := by omega
    have hS_card : ({1, n - 1} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [h_ne]), Finset.card_singleton]
    have hA_card : A.card = 2 := by
      have : A.card ≤ 2 := (Finset.card_le_card hA).trans_eq hS_card
      omega
    have hA_eq : A = {1, n - 1} :=
      Finset.eq_of_subset_of_card_le hA (by rw [hS_card, hA_card])
    intro h_avoid
    apply h_avoid
    use A
    refine ⟨le_rfl, ?_⟩
    rw [hA_eq]
    have : ({1, n - 1} : Finset ℕ).sum id = 1 + (n - 1) := by
      rw [Finset.sum_insert (by simp [h_ne]), Finset.sum_singleton]
      rfl
    rw [this]
    omega

/-- Alternative derivation of the non-trivial lower bound f(n) ≥ 2 for n ≥ 3
    via the general Conlon–Fox–Pham lower bound witness framework. -/
theorem minColors_ge_two_via_cfp (n : ℕ) (hn : 3 ≤ n) :
    2 ≤ minColors n (by omega) := by
  have := minColors_ge_of_cfp_witness n 1 (by omega) (cfpWitness_two n hn)
  exact this

/-- Scaled arithmetic progression lower bound witness:
    whenever v ∣ n, v * m < n, and n/v ≤ m(m+1)/2, the scaled set
    v * {1, ..., m} forms a valid lower bound witness CFPLowerBoundWitness n 1. -/
def cfpWitness_scaled (n v m : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (hvm : v * m < n) (hn : n / v ≤ m * (m + 1) / 2) (hm : 1 ≤ m) :
    CFPLowerBoundWitness n 1 where
  S := cfpLowerBoundSet v m
  hS := cfpLowerBoundSet_subset n v m hv hvm
  M := m - 1
  h_card := by
    rw [cfpLowerBoundSet_card v m hv]
    omega
  h_hit := by
    intro A hA hM
    have hS_card := cfpLowerBoundSet_card v m hv
    have hA_card : A.card = m := by
      have : A.card ≤ m := (Finset.card_le_card hA).trans_eq hS_card
      omega
    have hA_eq : A = cfpLowerBoundSet v m :=
      Finset.eq_of_subset_of_card_le hA (by rw [hS_card, hA_card])
    have hn_in := mem_subsetSums_cfpLowerBoundSet n v m hv hvn hn
    intro h_avoid
    rw [hA_eq] at h_avoid
    rw [mem_subsetSums_iff] at hn_in
    obtain ⟨B, hB_sub, hB_sum⟩ := hn_in
    exact h_avoid ⟨B, hB_sub, hB_sum⟩

/-- Chromatic lower bound from scaled arithmetic progression witness:
    f(n) ≥ 2 whenever v ∣ n, v * m < n, and n/v ≤ m(m+1)/2. -/
theorem minColors_ge_two_via_cfp_scaled (n v m : ℕ) (hn_ge : 2 ≤ n)
    (hv : 0 < v) (hvn : v ∣ n) (hvm : v * m < n) (hn : n / v ≤ m * (m + 1) / 2) (hm : 1 ≤ m) :
    2 ≤ minColors n hn_ge :=
  minColors_ge_of_cfp_witness n 1 hn_ge (cfpWitness_scaled n v m hv hvn hvm hn hm)

/-- A set of positive integers is k-diverse if for every divisor v ≥ 2,
    at least k elements are not divisible by v (Conlon–Fox–Pham 2021, Section 5.1). -/
def IsDiverse (X : Finset ℕ) (k : ℕ) : Prop :=
  ∀ v : ℕ, 2 ≤ v → k ≤ (X.filter (fun x => ¬ v ∣ x)).card

lemma isDiverse_of_le {X : Finset ℕ} {k1 k2 : ℕ}
    (h : IsDiverse X k2) (hle : k1 ≤ k2) : IsDiverse X k1 := by
  intro v hv
  exact hle.trans (h v hv)

lemma isDiverse_of_subset {X Y : Finset ℕ} {k : ℕ}
    (h : IsDiverse X k) (hsub : X ⊆ Y) : IsDiverse Y k := by
  intro v hv
  have : (X.filter (fun x => ¬ v ∣ x)) ⊆ (Y.filter (fun x => ¬ v ∣ x)) :=
    Finset.filter_subset_filter _ hsub
  exact (h v hv).trans (Finset.card_le_card this)

/-- Scaling the quotient set back by v yields a subset of the original set A. -/
lemma quotient_scale_subset (A : Finset ℕ) (v : ℕ) :
    ((A.filter (fun x => v ∣ x)).image (fun x => x / v)).image (fun y => v * y) ⊆ A := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨y, ⟨z, ⟨hzA, hzv⟩, rfl⟩, rfl⟩ := hx
  rw [Nat.mul_div_cancel' hzv]
  exact hzA

/-- If the quotient subset sums of multiples of v hit n/v, then A hits n (CFP §5.1 reduction). -/
lemma mem_subsetSums_of_quotient_hit (A : Finset ℕ) (n v : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (h_hit : n / v ∈ subsetSums ((A.filter (fun x => v ∣ x)).image (fun x => x / v))) :
    n ∈ subsetSums A := by
  exact mem_subsetSums_of_scaled hv hvn (quotient_scale_subset A v) h_hit

/-- Quotient consecutive interval subset sum hitting:
    if the quotient contains {1, ..., m} and n/v ≤ m(m+1)/2, then n/v is in its subset sums. -/
lemma mem_subsetSums_of_quotient_Icc_subset {Q : Finset ℕ} {m n v : ℕ}
    (h_sub : Finset.Icc 1 m ⊆ Q)
    (hn : n / v ≤ m * (m + 1) / 2) :
    n / v ∈ subsetSums Q := by
  have h_in := mem_subsetSums_Icc_of_le hn
  rw [mem_subsetSums_iff] at h_in ⊢
  obtain ⟨B, hB_sub, hB_sum⟩ := h_in
  exact ⟨B, hB_sub.trans h_sub, hB_sum⟩

/-- If the quotient of multiples of v in A contains {1, ..., m} and n/v ≤ m(m+1)/2,
    then n is in the subset sums of A. -/
lemma mem_subsetSums_of_scaled_Icc_subset {A : Finset ℕ} {m n v : ℕ}
    (hv : 0 < v) (hvn : v ∣ n)
    (h_sub : Finset.Icc 1 m ⊆ (A.filter (fun x => v ∣ x)).image (fun x => x / v))
    (hn : n / v ≤ m * (m + 1) / 2) :
    n ∈ subsetSums A := by
  have h_qhit := mem_subsetSums_of_quotient_Icc_subset h_sub hn
  exact mem_subsetSums_of_quotient_hit A n v hv hvn h_qhit

/-- Conlon–Fox–Pham Diverse Lower Bound Witness:
    Encapsulates the diverse subset-sum structure in CFP §5.1:
    - Base set S ⊆ {1, ..., n-1}
    - Threshold M with k * M < |S|
    - A scaling factor v dividing n
    - For any subset A ⊆ S of size ≥ M + 1, the quotient of multiples of v has n/v in its subset sums. -/
structure CFPDiverseWitness (n k : ℕ) : Type where
  S : Finset ℕ
  hS : S ⊆ Finset.Ico 1 n
  M : ℕ
  h_card : k * M < S.card
  v : ℕ
  hv : 0 < v
  hvn : v ∣ n
  h_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
    n / v ∈ subsetSums ((A.filter (fun x => v ∣ x)).image (fun x => x / v))

/-- A diverse lower bound witness CFPDiverseWitness n k induces a CFPLowerBoundWitness n k. -/
def CFPLowerBoundWitness.ofDiverse (n k : ℕ) (w : CFPDiverseWitness n k) :
    CFPLowerBoundWitness n k where
  S := w.S
  hS := w.hS
  M := w.M
  h_card := w.h_card
  h_hit := by
    intro A hA hM
    have h_quot := w.h_hit A hA hM
    have hn_in := mem_subsetSums_of_quotient_hit A n w.v w.hv w.hvn h_quot
    exact not_avoids_of_subsetSums hn_in

/-- Chromatic lower bound from a diverse lower bound witness: k + 1 ≤ f(n). -/
theorem minColors_ge_of_cfp_diverse_witness (n k : ℕ) (hn : 2 ≤ n)
    (w : CFPDiverseWitness n k) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_cfp_witness n k hn (CFPLowerBoundWitness.ofDiverse n k w)

/-!
### Section 8.3: Divisor-Extraction Iteration for Diverse Subsets (CFP §5.1)

This section formalizes the algorithmic divisor-extraction iteration from Conlon–Fox–Pham (2021) Section 5.1:
Starting from any finite subset A ⊆ [1, B] with |A| > (t - 1) * L and B < 2^L,
if A is not t-diverse, there exists d ≥ 2 dividing all but < t elements of A.
Dividing the multiples by d yields a new set Q₁ ⊆ [1, B/d] with |A| ≤ |Q₁| + (t - 1).
Iterating this at most L times produces a non-empty scaling factor v > 0 and a t-diverse subset Q
such that v * Q ⊆ A, 1 ≤ x and v * x ≤ B for all x ∈ Q, and |A| ≤ |Q| + (t - 1) * L.
-/

/-- Characterization of non-diversity: ¬ IsDiverse A t means some d ≥ 2 has < t non-multiples in A. -/
lemma not_isDiverse_iff (A : Finset ℕ) (t : ℕ) :
    ¬ IsDiverse A t ↔ ∃ d : ℕ, 2 ≤ d ∧ (A.filter (fun x => ¬ d ∣ x)).card < t := by
  simp only [IsDiverse, not_forall, not_le]
  constructor
  · rintro ⟨d, hd, hcard⟩
    exact ⟨d, hd, hcard⟩
  · rintro ⟨d, hd, hcard⟩
    exact ⟨d, hd, hcard⟩

/-- Partition bound: if < t elements of A are not divisible by d,
    then |A| is bounded by the number of multiples plus (t - 1). -/
lemma card_le_card_filter_dvd_add (A : Finset ℕ) (d t : ℕ)
    (h_not : (A.filter (fun x => ¬ d ∣ x)).card < t) :
    A.card ≤ (A.filter (fun x => d ∣ x)).card + (t - 1) := by
  have h_disj : Disjoint (A.filter (fun x => d ∣ x)) (A.filter (fun x => ¬ d ∣ x)) := by
    rw [Finset.disjoint_filter]
    intro x _ hd1 hd2
    exact hd2 hd1
  have h_u : (A.filter (fun x => d ∣ x)) ∪ (A.filter (fun x => ¬ d ∣ x)) = A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have h_part : (A.filter (fun x => d ∣ x)).card + (A.filter (fun x => ¬ d ∣ x)).card = A.card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_u]
  omega

/-- Dividing multiples of d by d is strictly injective, preserving set cardinality. -/
lemma card_image_div_eq_card_filter_dvd (A : Finset ℕ) (d : ℕ) (_hd : 0 < d) :
    ((A.filter (fun x => d ∣ x)).image (fun x => x / d)).card = (A.filter (fun x => d ∣ x)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hx_dvd : d ∣ x := (Finset.mem_filter.mp hx).2
  have hy_dvd : d ∣ y := (Finset.mem_filter.mp hy).2
  have hx_eq : x = d * (x / d) := (Nat.mul_div_cancel' hx_dvd).symm
  have hy_eq : y = d * (y / d) := (Nat.mul_div_cancel' hy_dvd).symm
  have h_div : x / d = y / d := hxy
  rw [hx_eq, hy_eq, h_div]

/-- Bound preservation for the division step: elements of Q₁ remain in [1, B / d]. -/
lemma div_step_bounds (A : Finset ℕ) (B d : ℕ) (hd : 2 ≤ d)
    (hA_ge : ∀ x ∈ A, 1 ≤ x) (hA_le : ∀ x ∈ A, x ≤ B) :
    let Q1 := (A.filter (fun x => d ∣ x)).image (fun x => x / d)
    (∀ x ∈ Q1, 1 ≤ x) ∧ (∀ x ∈ Q1, x ≤ B / d) := by
  intro Q1
  constructor
  · intro y hy
    simp only [Q1, Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨x, ⟨hxA, hxd⟩, rfl⟩ := hy
    have hd_pos : 0 < d := by omega
    have hx_pos : 0 < x := by
      have := hA_ge x hxA
      omega
    exact Nat.div_pos (Nat.le_of_dvd hx_pos hxd) hd_pos
  · intro y hy
    simp only [Q1, Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨x, ⟨hxA, _⟩, rfl⟩ := hy
    exact Nat.div_le_div_right (hA_le x hxA)

/-- Conlon–Fox–Pham (2021, Section 5.1) Divisor-Extraction Iteration Theorem:
    For any finite subset A ⊆ [1, B] with |A| > (t - 1) * L and B < 2^L,
    there exists a scaling factor v > 0 and a non-empty t-diverse subset Q such that:
    1. Elements of Q satisfy 1 ≤ x and v * x ≤ B;
    2. The scaled set v * Q is a subset of A;
    3. Q is t-diverse (for every divisor d ≥ 2, at least t elements of Q are not divisible by d);
    4. |A| ≤ |Q| + (t - 1) * L. -/
theorem exists_diverse_scaled_subset (L : ℕ) :
    ∀ (A : Finset ℕ) (B t : ℕ),
    (∀ x ∈ A, 1 ≤ x) →
    (∀ x ∈ A, x ≤ B) →
    1 ≤ t →
    B < 2 ^ L →
    (t - 1) * L < A.card →
    ∃ (v : ℕ) (Q : Finset ℕ),
      0 < v ∧
      Q.Nonempty ∧
      (∀ x ∈ Q, 1 ≤ x ∧ v * x ≤ B) ∧
      Q.image (fun x => v * x) ⊆ A ∧
      IsDiverse Q t ∧
      A.card ≤ Q.card + (t - 1) * L := by
  induction L with
  | zero =>
    intro A B _t hA_ge hA_le _ht _hB hcard
    have : B = 0 := by omega
    have hA_pos : 0 < A.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA_pos
    have hx_ge := hA_ge x hx
    have hx_le := hA_le x hx
    omega
  | succ L ih =>
    intro A B t hA_ge hA_le ht hB hcard
    by_cases hdiv : IsDiverse A t
    · use 1, A
      refine ⟨by omega, ?_, ?_, ?_, hdiv, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp only [Finset.card_empty] at hcard
        omega
      · intro x hx
        simp only [one_mul]
        exact ⟨hA_ge x hx, hA_le x hx⟩
      · intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [one_mul]
        exact hy
      · omega
    · rw [not_isDiverse_iff] at hdiv
      obtain ⟨d, hd, h_not⟩ := hdiv
      let R := A.filter (fun x => d ∣ x)
      let Q1 := R.image (fun x => x / d)
      have hd_pos : 0 < d := by omega
      have hQ1_card : Q1.card = R.card := card_image_div_eq_card_filter_dvd A d hd_pos
      have hA_le_R : A.card ≤ R.card + (t - 1) := card_le_card_filter_dvd_add A d t h_not
      have hA_le_Q1 : A.card ≤ Q1.card + (t - 1) := by omega
      have hQ1_ge_le := div_step_bounds A B d hd hA_ge hA_le
      have hQ1_ge : ∀ x ∈ Q1, 1 ≤ x := hQ1_ge_le.1
      have hQ1_le : ∀ x ∈ Q1, x ≤ B / d := hQ1_ge_le.2
      have hB_div : B / d < 2 ^ L := by
        have hd2 : 2 ≤ d := hd
        have h1 : B < d * 2 ^ L := by
          calc B < 2 ^ (L + 1) := hB
          _ = 2 * 2 ^ L := by ring
          _ ≤ d * 2 ^ L := Nat.mul_le_mul_right (2 ^ L) hd2
        exact Nat.div_lt_of_lt_mul h1
      have hcard_Q1 : (t - 1) * L < Q1.card := by
        have : (t - 1) * (L + 1) = (t - 1) * L + (t - 1) := by ring
        omega
      obtain ⟨w, Q, hw_pos, hQ_nonempty, hQ_bounds, hQ_sub, hQ_div, hQ1_card_le⟩ :=
        ih Q1 (B / d) t hQ1_ge hQ1_le ht hB_div hcard_Q1
      use d * w, Q
      refine ⟨by positivity, hQ_nonempty, ?_, ?_, hQ_div, ?_⟩
      · intro x hx
        have hx_b := hQ_bounds x hx
        refine ⟨hx_b.1, ?_⟩
        have h_assoc : (d * w) * x = d * (w * x) := by ring
        rw [h_assoc]
        have h_mul : d * (w * x) ≤ d * (B / d) := Nat.mul_le_mul_left d hx_b.2
        have h_div_le : d * (B / d) ≤ B := Nat.mul_div_le B d
        exact h_mul.trans h_div_le
      · intro y hy
        simp only [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        have h_wx_in_Q1 : w * x ∈ Q1 := by
          have : w * x ∈ Q.image (fun z => w * z) := Finset.mem_image_of_mem (fun z => w * z) hx
          exact hQ_sub this
        have h_scale : d * (w * x) ∈ Q1.image (fun z => d * z) :=
          Finset.mem_image_of_mem (fun z => d * z) h_wx_in_Q1
        have h_sub_A : Q1.image (fun z => d * z) ⊆ A := quotient_scale_subset A d
        have : (d * w) * x = d * (w * x) := by ring
        rw [this]
        exact h_sub_A h_scale
      · have : (t - 1) * (L + 1) = (t - 1) * L + (t - 1) := by ring
        omega

/-- Upper bound on the extracted scaling factor: v ≤ B whenever Q is non-empty and v * x ≤ B for x ∈ Q. -/
lemma scale_factor_le_of_mem_bounds {Q : Finset ℕ} (hQ : Q.Nonempty) {v B : ℕ}
    (h_bounds : ∀ x ∈ Q, 1 ≤ x ∧ v * x ≤ B) :
    v ≤ B := by
  obtain ⟨x, hx⟩ := hQ
  have hxb := h_bounds x hx
  have : v * 1 ≤ v * x := Nat.mul_le_mul_left v hxb.1
  omega

/-!
### Subsection 8.4: Conlon–Fox–Pham Lemma 5.8 Modular Subset Sum Coverage and Diversity Bridge

This subsection formalizes Section 5.1, Lemma 5.8 of Conlon–Fox–Pham (2021):
Given a finite set A ⊆ ℕ and d ≥ 1 such that for every divisor e ∣ d,
the number of elements in A not divisible by e is at least e - 1,
the subset sums of A cover all residue classes modulo d:
  ∀ r : ZMod d, r ∈ subsetSumsMod d A

We then bridge this to `IsDiverse Q t` and `exists_diverse_scaled_subset`,
deducing that the diverse subset Q produced by the CFP divisor extraction iteration
achieves complete modular coverage for all moduli 1 ≤ d ≤ t + 1.
-/

lemma image_add_eq_self_of_subset {d : ℕ} (S : Finset (ZMod d)) (x : ZMod d)
    (h_sub : S.image (fun r => r + x) ⊆ S) :
    S.image (fun r => r + x) = S := by
  have h_inj : Function.Injective (fun (r : ZMod d) => r + x) := by
    intro a b hab
    exact add_right_cancel hab
  have h_card : (S.image (fun r => r + x)).card = S.card :=
    Finset.card_image_of_injective S h_inj
  exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_card])

lemma filter_not_dvd_eq_of_dvd (A : Finset ℕ) (d e : ℕ) (he : e ∣ d) :
    (A.filter (fun a => ¬ d ∣ a)).filter (fun a => ¬ e ∣ a) = A.filter (fun a => ¬ e ∣ a) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha, _⟩, he_not⟩
    exact ⟨ha, he_not⟩
  · rintro ⟨ha, he_not⟩
    refine ⟨⟨ha, ?_⟩, he_not⟩
    intro hd
    exact he_not (dvd_trans he hd)

lemma subsetSums_insert (A : Finset ℕ) (x : ℕ) (hx : x ∉ A) :
    subsetSums (insert x A) = subsetSums A ∪ (subsetSums A).image (fun s => s + x) := by
  ext s
  simp only [mem_subsetSums_iff, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases hxB : x ∈ B
    · right
      refine ⟨(B.erase x).sum id, ⟨B.erase x, ?_, rfl⟩, ?_⟩
      · intro y hy
        have := hB (Finset.mem_of_mem_erase hy)
        simp only [Finset.mem_insert] at this
        cases this with
        | inl heq => exfalso; exact (Finset.ne_of_mem_erase hy) heq
        | inr hin => exact hin
      · have h_not : x ∉ B.erase x := by simp
        have h_sum : (insert x (B.erase x)).sum id = x + (B.erase x).sum id := Finset.sum_insert h_not
        rw [Finset.insert_erase hxB] at h_sum
        rw [h_sum, add_comm]
    · left
      refine ⟨B, ?_, rfl⟩
      intro y hy
      have := hB hy
      simp only [Finset.mem_insert] at this
      cases this with
      | inl heq => exfalso; subst heq; exact hxB hy
      | inr hin => exact hin
  · rintro (⟨B, hB, rfl⟩ | ⟨s', ⟨B, hB, rfl⟩, rfl⟩)
    · refine ⟨B, hB.trans (Finset.subset_insert x A), rfl⟩
    · refine ⟨insert x B, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        refine ⟨Finset.mem_insert_self x A, hB.trans (Finset.subset_insert x A)⟩
      · have : x ∉ B := fun hxB => hx (hB hxB)
        have h_sum : (insert x B).sum id = x + B.sum id := Finset.sum_insert this
        rw [h_sum, add_comm]

/-- The set of residue classes modulo d formed by subset sums of A. -/
def subsetSumsMod (d : ℕ) (A : Finset ℕ) : Finset (ZMod d) :=
  Finset.image (fun (s : ℕ) => (s : ZMod d)) (subsetSums A)

lemma mem_subsetSumsMod_iff (d : ℕ) (A : Finset ℕ) (r : ZMod d) :
    r ∈ subsetSumsMod d A ↔ ∃ B ⊆ A, (B.sum (fun x => (x : ZMod d))) = r := by
  simp only [subsetSumsMod, Finset.mem_image, mem_subsetSums_iff]
  constructor
  · rintro ⟨s, ⟨B, hB, rfl⟩, rfl⟩
    use B, hB
    push_cast
    rfl
  · rintro ⟨B, hB, rfl⟩
    use B.sum id
    refine ⟨⟨B, hB, rfl⟩, ?_⟩
    push_cast
    rfl

lemma zero_mem_subsetSumsMod (d : ℕ) (A : Finset ℕ) : (0 : ZMod d) ∈ subsetSumsMod d A := by
  rw [mem_subsetSumsMod_iff]
  use ∅
  simp

lemma subsetSumsMod_mono {d : ℕ} {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSumsMod d A ⊆ subsetSumsMod d B := by
  intro r hr
  rw [mem_subsetSumsMod_iff] at hr ⊢
  obtain ⟨C, hC, rfl⟩ := hr
  exact ⟨C, hC.trans h, rfl⟩

lemma subsetSumsMod_insert (d : ℕ) (A : Finset ℕ) (x : ℕ) (hx : x ∉ A) :
    subsetSumsMod d (insert x A) =
      subsetSumsMod d A ∪ Finset.image (fun r => r + (x : ZMod d)) (subsetSumsMod d A) := by
  simp only [subsetSumsMod]
  rw [subsetSums_insert A x hx, Finset.image_union]
  congr 1
  ext r
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨s', hs', rfl⟩, rfl⟩
    refine ⟨(s' : ZMod d), ⟨s', hs', rfl⟩, ?_⟩
    push_cast
    rfl
  · rintro ⟨r', ⟨s', hs', rfl⟩, rfl⟩
    refine ⟨s' + x, ⟨s', hs', rfl⟩, ?_⟩
    push_cast
    rfl

lemma subsetSumsMod_filter_not_dvd (d : ℕ) (A : Finset ℕ) :
    subsetSumsMod d (A.filter (fun a => ¬ d ∣ a)) = subsetSumsMod d A := by
  apply Finset.Subset.antisymm
  · exact subsetSumsMod_mono (Finset.filter_subset _ _)
  · intro r hr
    rw [mem_subsetSumsMod_iff] at hr ⊢
    obtain ⟨B, hB, rfl⟩ := hr
    let B0 := B.filter (fun a => ¬ d ∣ a)
    let B_dvd := B.filter (fun a => d ∣ a)
    have h_disj : Disjoint B0 B_dvd := by
      rw [Finset.disjoint_filter]
      intro x _ hd1 hd2
      exact hd1 hd2
    have h_u : B0 ∪ B_dvd = B := by
      ext x
      simp only [B0, B_dvd, Finset.mem_union, Finset.mem_filter]
      tauto
    have h_sum : B.sum (fun x => (x : ZMod d)) = B0.sum (fun x => (x : ZMod d)) := by
      rw [← h_u, Finset.sum_union h_disj]
      have : B_dvd.sum (fun x => (x : ZMod d)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [B_dvd, Finset.mem_filter] at hx
        obtain ⟨q, rfl⟩ := hx.2
        push_cast
        rw [CharP.cast_eq_zero (ZMod d) d, zero_mul]
      rw [this, add_zero]
    use B0
    refine ⟨?_, h_sum.symm⟩
    intro x hx
    simp only [B0, Finset.mem_filter] at hx
    simp only [Finset.mem_filter]
    exact ⟨hB hx.1, hx.2⟩

lemma zmod_gcd_mem_zmultiples (d : ℕ) [NeZero d] (h : ZMod d) :
    (d.gcd h.val : ZMod d) ∈ AddSubgroup.zmultiples h := by
  have h_bezout := Nat.gcd_eq_gcd_ab d h.val
  have h_cast : ((d.gcd h.val : ℤ) : ZMod d) =
      (((d : ℤ) * d.gcdA h.val + (h.val : ℤ) * d.gcdB h.val : ℤ) : ZMod d) := by
    rw [← h_bezout]
  push_cast at h_cast
  rw [CharP.cast_eq_zero (ZMod d) d, zero_mul, zero_add] at h_cast
  rw [ZMod.natCast_zmod_val h] at h_cast
  rw [AddSubgroup.mem_zmultiples_iff]
  use d.gcdB h.val
  rw [h_cast, zsmul_eq_mul, mul_comm]

lemma zmod_mem_zmultiples_iff_dvd (d g : ℕ) (hg : g ∣ d) (x : ℕ) :
    (x : ZMod d) ∈ AddSubgroup.zmultiples (g : ZMod d) ↔ g ∣ x := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hk_cast : ((x : ℤ) : ZMod d) = ((k * (g : ℤ) : ℤ) : ZMod d) := by
      push_cast
      rw [zsmul_eq_mul] at hk
      exact hk.symm
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at hk_cast
    have hdvd_diff : (g : ℤ) ∣ (k * (g : ℤ) - (x : ℤ)) := by
      obtain ⟨q, hq⟩ := hg
      have hd_eq : (d : ℤ) = (g : ℤ) * (q : ℤ) := by exact_mod_cast hq
      rw [hd_eq] at hk_cast
      exact dvd_of_mul_right_dvd hk_cast
    have hdvd_kg : (g : ℤ) ∣ k * (g : ℤ) := dvd_mul_left (g : ℤ) k
    have hdvd_x : (g : ℤ) ∣ (x : ℤ) := by
      have := dvd_sub hdvd_kg hdvd_diff
      ring_nf at this
      exact this
    exact Int.natCast_dvd_natCast.mp hdvd_x
  · rintro ⟨q, rfl⟩
    use q
    rw [zsmul_eq_mul, mul_comm]
    push_cast
    rfl

lemma stabilizer_closure {d : ℕ} [NeZero d] (S : Finset (ZMod d)) (K : Set (ZMod d))
    (hK : ∀ x ∈ K, ∀ s ∈ S, s + x ∈ S) :
    ∀ h ∈ AddSubgroup.closure K, ∀ s ∈ S, s + h ∈ S := by
  intro h hh
  induction hh using AddSubgroup.closure_induction with
  | mem x hx => exact hK x hx
  | zero => intro s hs; rw [add_zero]; exact hs
  | add x y hx hy ihx ihy =>
    intro s hs
    rw [← add_assoc]
    exact ihy (s + x) (ihx s hs)
  | neg x hx ih =>
    intro s hs
    have h_nsmul : ∀ n : ℕ, s + (n • x) ∈ S := by
      intro n
      induction n with
      | zero => rw [zero_nsmul, add_zero]; exact hs
      | succ n ihn =>
        rw [succ_nsmul, ← add_assoc]
        exact ih (s + n • x) ihn
    have hd_pred : d = (d - 1) + 1 := by
      have hd_pos : 0 < d := NeZero.pos d
      omega
    have hd_zero : d • x = 0 := by
      rw [nsmul_eq_mul]
      have : (d : ZMod d) = 0 := CharP.cast_eq_zero (ZMod d) d
      rw [this, zero_mul]
    have h_add : (d - 1) • x + x = 0 := by
      calc (d - 1) • x + x = (d - 1) • x + 1 • x := by rw [one_nsmul]
      _ = ((d - 1) + 1) • x := by rw [add_nsmul]
      _ = d • x := by rw [← hd_pred]
      _ = 0 := hd_zero
    have h_add2 : x + (d - 1) • x = 0 := by rw [add_comm, h_add]
    have h_neg : -x = (d - 1) • x := by
      calc -x = -x + 0 := by rw [add_zero]
      _ = -x + (x + (d - 1) • x) := by rw [h_add2]
      _ = (-x + x) + (d - 1) • x := by rw [add_assoc]
      _ = 0 + (d - 1) • x := by rw [neg_add_cancel]
      _ = (d - 1) • x := by rw [zero_add]
    rw [h_neg]
    exact h_nsmul (d - 1)

lemma card_sdiff_eq_sub {α : Type*} [DecidableEq α] {s t : Finset α} (h : t ⊆ s) :
    (s \ t).card = s.card - t.card := by
  have : t ∩ s = t := Finset.inter_eq_left.mpr h
  rw [Finset.card_sdiff, this]

/-- Conlon–Fox–Pham (2021) Lemma 5.8:
    If for every divisor e ∣ d, the number of elements of A not divisible by e is at least e - 1,
    then the subset sums of A cover all residues modulo d. -/
theorem subsetSumsMod_eq_univ_of_divisor_counts (d : ℕ) (hd : 0 < d) (A : Finset ℕ)
    (hdiv : ∀ e, e ∣ d → e - 1 ≤ (A.filter (fun a => ¬ e ∣ a)).card) :
    ∀ r : ZMod d, r ∈ subsetSumsMod d A := by
  induction d using Nat.strong_induction_on generalizing A with
  | _ d ih =>
    by_cases hd1 : d = 1
    · subst hd1
      intro r
      have : r = 0 := Subsingleton.elim r 0
      rw [this]
      exact zero_mem_subsetSumsMod 1 A
    · have hd2 : 2 ≤ d := by omega
      have inst_ne : NeZero d := ⟨by omega⟩
      let A0 := A.filter (fun a => ¬ d ∣ a)
      have hA0_eq : subsetSumsMod d A0 = subsetSumsMod d A := subsetSumsMod_filter_not_dvd d A
      rw [← hA0_eq]
      by_contra h_contra
      have h_ex_miss : ∃ r_miss : ZMod d, r_miss ∉ subsetSumsMod d A0 := by
        by_contra hall
        apply h_contra
        intro r
        by_contra hr
        exact hall ⟨r, hr⟩
      obtain ⟨r_miss, hr_miss⟩ := h_ex_miss
      let Cand := A0.powerset.filter (fun B => B.card + 1 ≤ (subsetSumsMod d B).card)
      have hCand_empty : ∅ ∈ Cand := by
        simp only [Cand, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
          Finset.card_empty, zero_add, true_and]
        have : (0 : ZMod d) ∈ subsetSumsMod d ∅ := zero_mem_subsetSumsMod d ∅
        have h_nonempty : (subsetSumsMod d ∅).Nonempty := ⟨0, this⟩
        exact Finset.Nonempty.card_pos h_nonempty
      obtain ⟨B, hB_cand, hB_max⟩ := Cand.exists_max_image Finset.card ⟨∅, hCand_empty⟩
      simp only [Cand, Finset.mem_filter, Finset.mem_powerset] at hB_cand
      obtain ⟨hB_sub_A0, hB_le_S⟩ := hB_cand
      let S := subsetSumsMod d B
      let C := A0 \ B
      have hr_miss_S : r_miss ∉ S := by
        intro hr_in
        have : S ⊆ subsetSumsMod d A0 := subsetSumsMod_mono hB_sub_A0
        exact hr_miss (this hr_in)
      have hS_card : S.card ≤ d - 1 := by
        have h_le : S.card ≤ Fintype.card (ZMod d) := Finset.card_le_univ S
        rw [ZMod.card d] at h_le
        by_contra h_contra_card
        have h_eq_d : S.card = d := by omega
        have h_univ : (Finset.univ : Finset (ZMod d)).card = d := by rw [Finset.card_univ, ZMod.card d]
        have : S = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by rw [h_eq_d, h_univ])
        have : r_miss ∈ S := by rw [this]; exact Finset.mem_univ r_miss
        exact hr_miss_S this
      have hB_card : B.card ≤ d - 2 := by
        have : B.card + 1 ≤ S.card := hB_le_S
        omega
      have hA0_card : d - 1 ≤ A0.card := hdiv d (dvd_refl d)
      have hC_card : 1 ≤ C.card := by
        have : C.card = A0.card - B.card := card_sdiff_eq_sub hB_sub_A0
        omega
      have hC_nonempty : C.Nonempty := Finset.card_pos.mp (by omega)
      have h_trans : ∀ x ∈ C, ∀ s ∈ S, s + (x : ZMod d) ∈ S := by
        intro x hx
        simp only [C, Finset.mem_sdiff] at hx
        obtain ⟨hxA0, hxB⟩ := hx
        have h_ins_sub : insert x B ⊆ A0 := by
          rw [Finset.insert_subset_iff]
          exact ⟨hxA0, hB_sub_A0⟩
        have h_ins_card : (insert x B).card = B.card + 1 := Finset.card_insert_of_notMem hxB
        by_contra h_not_in
        have h_ex_out : ∃ s_out ∈ S, s_out + (x : ZMod d) ∉ S := by
          by_contra hall
          apply h_not_in
          intro s hs
          by_contra h_out
          exact hall ⟨s, hs, h_out⟩
        obtain ⟨s_out, hs_out, hs_out_not⟩ := h_ex_out
        have h_img_not_sub : ¬ (S.image (fun r => r + (x : ZMod d)) ⊆ S) := by
          intro h_sub
          have : s_out + (x : ZMod d) ∈ S.image (fun r => r + (x : ZMod d)) :=
            Finset.mem_image_of_mem _ hs_out
          exact hs_out_not (h_sub this)
        have h_union_card : S.card + 1 ≤ (S ∪ S.image (fun r => r + (x : ZMod d))).card := by
          obtain ⟨y, hy, hy_not⟩ := Finset.not_subset.mp h_img_not_sub
          have : S ⊂ S ∪ S.image (fun r => r + (x : ZMod d)) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.subset_union_left, ?_⟩
            intro heq
            have : y ∈ S := by
              have : y ∈ S ∪ S.image (fun r => r + (x : ZMod d)) := Finset.mem_union_right S hy
              rwa [← heq] at this
            exact hy_not this
          exact Finset.card_lt_card this
        have h_mod_ins := subsetSumsMod_insert d B x hxB
        have h_cand_ins : (insert x B).card + 1 ≤ (subsetSumsMod d (insert x B)).card := by
          rw [h_mod_ins, h_ins_card]
          change B.card + 1 + 1 ≤ (S ∪ S.image (fun r => r + (x : ZMod d))).card
          have : B.card + 1 ≤ S.card := hB_le_S
          omega
        have h_ins_mem_cand : insert x B ∈ Cand := by
          simp only [Cand, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨h_ins_sub, h_cand_ins⟩
        have h_le := hB_max (insert x B) h_ins_mem_cand
        rw [h_ins_card] at h_le
        omega
      let K : Set (ZMod d) := (fun (x : ℕ) => (x : ZMod d)) '' (C : Set ℕ)
      have hK : ∀ x ∈ K, ∀ s ∈ S, s + x ∈ S := by
        rintro _ ⟨x, hx, rfl⟩ s hs
        exact h_trans x hx s hs
      have h_stab : ∀ h ∈ AddSubgroup.closure K, ∀ s ∈ S, s + h ∈ S :=
        stabilizer_closure S K hK
      let H0 := AddSubgroup.closure K
      have _inst_cyc : IsAddCyclic H0 := inferInstance
      obtain ⟨h_gen, hh_gen⟩ := IsAddCyclic.exists_generator (α := H0)
      let h0 : ZMod d := (h_gen : ZMod d)
      have hh0_in : h0 ∈ H0 := h_gen.2
      have hH0_eq_zmult : ∀ x ∈ H0, x ∈ AddSubgroup.zmultiples h0 := by
        intro x hx
        have := hh_gen ⟨x, hx⟩
        rw [AddSubgroup.mem_zmultiples_iff] at this ⊢
        obtain ⟨k, hk⟩ := this
        use k
        exact congr_arg Subtype.val hk
      let g := d.gcd h0.val
      have hg_dvd_d : g ∣ d := Nat.gcd_dvd_left d h0.val
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left h0.val hd
      have hg_in_H0 : (g : ZMod d) ∈ H0 := by
        have h_in := zmod_gcd_mem_zmultiples d h0
        rw [AddSubgroup.mem_zmultiples_iff] at h_in
        obtain ⟨k, hk⟩ := h_in
        rw [← hk]
        exact H0.zsmul_mem hh0_in k
      have hg_stab : ∀ s ∈ S, s + (g : ZMod d) ∈ S := h_stab (g : ZMod d) hg_in_H0
      have h_dvd_C : ∀ x ∈ C, g ∣ x := by
        intro x hx
        have hx_K : (x : ZMod d) ∈ K := ⟨x, hx, rfl⟩
        have hx_H0 : (x : ZMod d) ∈ H0 := AddSubgroup.subset_closure hx_K
        have hx_mult := hH0_eq_zmult (x : ZMod d) hx_H0
        have h_mult_g : (x : ZMod d) ∈ AddSubgroup.zmultiples (g : ZMod d) := by
          rw [AddSubgroup.mem_zmultiples_iff] at hx_mult ⊢
          obtain ⟨k, hk⟩ := hx_mult
          have hg_dvd_h0 : g ∣ h0.val := Nat.gcd_dvd_right d h0.val
          have hh0_mult := (zmod_mem_zmultiples_iff_dvd d g hg_dvd_d h0.val).mpr hg_dvd_h0
          rw [ZMod.natCast_zmod_val h0] at hh0_mult
          rw [AddSubgroup.mem_zmultiples_iff] at hh0_mult
          obtain ⟨m, hm⟩ := hh0_mult
          use k * m
          rw [mul_zsmul, hm, hk]
        exact (zmod_mem_zmultiples_iff_dvd d g hg_dvd_d x).mp h_mult_g
      have hg_lt_d : g < d := by
        by_contra h_ge
        have h_eq : g = d := by
          have : g ≤ d := Nat.le_of_dvd hd hg_dvd_d
          omega
        obtain ⟨x, hx⟩ := hC_nonempty
        have hxd : d ∣ x := by rw [← h_eq]; exact h_dvd_C x hx
        simp only [C, Finset.mem_sdiff, A0, Finset.mem_filter] at hx
        exact hx.1.2 hxd
      have hB_div : ∀ e, e ∣ g → e - 1 ≤ (B.filter (fun a => ¬ e ∣ a)).card := by
        intro e he
        have he_dvd_d : e ∣ d := dvd_trans he hg_dvd_d
        have h_e_A := hdiv e he_dvd_d
        have h_e_A0 : (A0.filter (fun a => ¬ e ∣ a)).card = (A.filter (fun a => ¬ e ∣ a)).card := by
          rw [← filter_not_dvd_eq_of_dvd A d e he_dvd_d]
        rw [← h_e_A0] at h_e_A
        have h_sub_B : A0.filter (fun a => ¬ e ∣ a) ⊆ B.filter (fun a => ¬ e ∣ a) := by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          refine ⟨?_, hx.2⟩
          by_contra hxB
          have : x ∈ C := by
            simp only [C, Finset.mem_sdiff]
            exact ⟨hx.1, hxB⟩
          have hgx := h_dvd_C x this
          have hex := dvd_trans he hgx
          exact hx.2 hex
        exact h_e_A.trans (Finset.card_le_card h_sub_B)
      have h_ih := ih g hg_lt_d hg_pos B hB_div
      have h_r0 := h_ih (r_miss.val : ZMod g)
      rw [mem_subsetSumsMod_iff] at h_r0
      obtain ⟨B_sub, hB_sub_B, hB_sum⟩ := h_r0
      have h_cast_g : ((B_sub.sum id : ℕ) : ZMod g) = (r_miss.val : ZMod g) := by
        have : ((B_sub.sum id : ℕ) : ZMod g) = B_sub.sum (fun x => (x : ZMod g)) := by
          push_cast
          rfl
        rw [this, hB_sum]
      let s_val : ℕ := B_sub.sum id
      have hs_in : (s_val : ZMod d) ∈ S := by
        have : s_val ∈ subsetSums B := by
          rw [mem_subsetSums_iff]
          exact ⟨B_sub, hB_sub_B, rfl⟩
        simp only [S, subsetSumsMod, Finset.mem_image]
        exact ⟨s_val, this, rfl⟩
      have h_modeq : (s_val : ℤ) ≡ (r_miss.val : ℤ) [ZMOD (g : ℤ)] := by
        have := (ZMod.intCast_eq_intCast_iff (s_val : ℤ) (r_miss.val : ℤ) g).mp
        push_cast at this
        exact this h_cast_g
      rw [Int.modEq_iff_dvd] at h_modeq
      obtain ⟨k, hk⟩ := h_modeq
      have hr_eq : (r_miss : ZMod d) = (s_val : ZMod d) + k • (g : ZMod d) := by
        have h_int : (r_miss.val : ℤ) = (s_val : ℤ) + (g : ℤ) * k := by omega
        have h_cast_d : ((r_miss.val : ℤ) : ZMod d) = (((s_val : ℤ) + (g : ℤ) * k : ℤ) : ZMod d) :=
          congr_arg _ h_int
        push_cast at h_cast_d
        rw [ZMod.natCast_zmod_val r_miss] at h_cast_d
        rw [h_cast_d]
        rw [zsmul_eq_mul, mul_comm]
      have hk_in_H0 : k • (g : ZMod d) ∈ H0 := H0.zsmul_mem hg_in_H0 k
      have h_stab_k : (s_val : ZMod d) + k • (g : ZMod d) ∈ S :=
        h_stab (k • (g : ZMod d)) hk_in_H0 (s_val : ZMod d) hs_in
      rw [hr_eq] at hr_miss_S
      exact hr_miss_S h_stab_k

/-- Modular subset sum coverage for diverse sets:
    If A is t-diverse and d - 1 ≤ t with d > 0, then A covers all residues modulo d. -/
lemma subsetSumsMod_eq_univ_of_isDiverse (d t : ℕ) (hd : 0 < d) (hdt : d - 1 ≤ t)
    (A : Finset ℕ) (h_div : IsDiverse A t) :
    ∀ r : ZMod d, r ∈ subsetSumsMod d A := by
  apply subsetSumsMod_eq_univ_of_divisor_counts d hd A
  intro e he
  by_cases he1 : e = 1
  · subst he1
    omega
  · have he2 : 2 ≤ e := by
      have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he hd
      omega
    have h_div_e := h_div e he2
    have he_le_d : e ≤ d := Nat.le_of_dvd hd he
    omega

/-- The extracted scaled diverse subset Q from `exists_diverse_scaled_subset`
    covers all residues modulo d for every modulus 1 ≤ d ≤ t + 1. -/
lemma exists_diverse_scaled_subset_mod_coverage (L : ℕ) (A : Finset ℕ) (B t : ℕ)
    (hA_ge : ∀ x ∈ A, 1 ≤ x) (hA_le : ∀ x ∈ A, x ≤ B)
    (ht : 1 ≤ t) (hB : B < 2 ^ L) (hcard : (t - 1) * L < A.card) :
    ∃ (v : ℕ) (Q : Finset ℕ),
      0 < v ∧ Q.Nonempty ∧ (∀ x ∈ Q, 1 ≤ x ∧ v * x ≤ B) ∧
      Q.image (fun x => v * x) ⊆ A ∧ IsDiverse Q t ∧
      A.card ≤ Q.card + (t - 1) * L ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ t + 1 → ∀ r : ZMod d, r ∈ subsetSumsMod d Q) := by
  obtain ⟨v, Q, hv, hQ_ne, hQ_bnd, hQ_sub, hQ_div, hQ_card⟩ :=
    exists_diverse_scaled_subset L A B t hA_ge hA_le ht hB hcard
  refine ⟨v, Q, hv, hQ_ne, hQ_bnd, hQ_sub, hQ_div, hQ_card, ?_⟩
  intro d hd1 hdt r
  exact subsetSumsMod_eq_univ_of_isDiverse d t (by omega) (by omega) Q hQ_div r

/-- Sanity check 1: Modulo 1 coverage holds trivially for the empty set. -/
lemma sanity_mod_coverage_empty : ∀ r : ZMod 1, r ∈ subsetSumsMod 1 ∅ := by
  intro r
  have : r = 0 := Subsingleton.elim r 0
  rw [this]
  exact zero_mem_subsetSumsMod 1 ∅

/-- Sanity check 2: Modulo 4 coverage for A = {1, 5, 9}. -/
lemma sanity_mod_coverage_4 : ∀ r : ZMod 4, r ∈ subsetSumsMod 4 {1, 5, 9} := by
  apply subsetSumsMod_eq_univ_of_divisor_counts 4 (by decide) {1, 5, 9}
  intro e he
  have : e ≤ 4 := Nat.le_of_dvd (by decide) he
  interval_cases e <;> revert he <;> decide

/-- Sanity check 3: Modulo 6 coverage for A = {2, 3, 4, 8, 9}. -/
lemma sanity_mod_coverage_6 : ∀ r : ZMod 6, r ∈ subsetSumsMod 6 {2, 3, 4, 8, 9} := by
  apply subsetSumsMod_eq_univ_of_divisor_counts 6 (by decide) {2, 3, 4, 8, 9}
  intro e he
  have : e ≤ 6 := Nat.le_of_dvd (by decide) he
  interval_cases e <;> revert he <;> decide

/-!
### Subsection 8.5: Conlon–Fox–Pham Lemma 5.11 Modular Subset Sum Fibers and Multiplicative Bound

This subsection formalizes Section 5.1, Lemma 5.11 of Conlon–Fox–Pham (2021):
Given a finite set A ⊆ ℕ, moduli N, d > 0 with d ∣ N, and a residue r ∈ ZMod d:
Let D = A.filter (d ∣ ·) be the multiples of d in A, and F_r = {s ∈ Σ_N(A) | π(s) = r}
be the residue fiber in ZMod N over r.
If F_r is non-empty, then:
  |Σ_N(D)| ≤ |F_r|

Summing over all residue classes in the image π(Σ_N(A)) = Σ_d(A) yields the multiplicative bound:
  |Σ_d(A)| · |Σ_N(D)| ≤ |Σ_N(A)|

When A is t-diverse and d - 1 ≤ t, Σ_d(A) covers all of ZMod d by Lemma 5.8, yielding:
  d · |Σ_N(D)| ≤ |Σ_N(A)|
-/

/-- The natural projection homomorphism from ZMod N to ZMod d when d ∣ N. -/
def zmodProj {N d : ℕ} (h : d ∣ N) (x : ZMod N) : ZMod d :=
  ZMod.castHom h (ZMod d) x

lemma zmodProj_natCast {N d : ℕ} (h : d ∣ N) (a : ℕ) :
    zmodProj h (a : ZMod N) = (a : ZMod d) := by
  simp [zmodProj]

lemma zmodProj_zero {N d : ℕ} (h : d ∣ N) :
    zmodProj h (0 : ZMod N) = 0 := by
  simp [zmodProj]

lemma zmodProj_add {N d : ℕ} (h : d ∣ N) (x y : ZMod N) :
    zmodProj h (x + y) = zmodProj h x + zmodProj h y := by
  exact map_add (ZMod.castHom h (ZMod d)) x y
lemma zmodProj_sub {N d : ℕ} (h : d ∣ N) (x y : ZMod N) :
    zmodProj h (x - y) = zmodProj h x - zmodProj h y := by
  exact map_sub (ZMod.castHom h (ZMod d)) x y


lemma zmodProj_sum {N d : ℕ} (h : d ∣ N) {α : Type*} (s : Finset α) (f : α → ZMod N) :
    zmodProj h (s.sum f) = s.sum (fun x => zmodProj h (f x)) := by
  exact map_sum (ZMod.castHom h (ZMod d)) f s

lemma zmodProj_eq_zero_of_mem_subsetSumsMod_dvd {N d : ℕ} (h : d ∣ N) (A : Finset ℕ)
    (y : ZMod N) (hy : y ∈ subsetSumsMod N (A.filter (fun x => d ∣ x))) :
    zmodProj h y = 0 := by
  rw [mem_subsetSumsMod_iff] at hy
  obtain ⟨T, hT, rfl⟩ := hy
  rw [zmodProj_sum]
  have : ∀ x ∈ T, zmodProj h (x : ZMod N) = 0 := by
    intro x hx
    have hx_dvd : d ∣ x := (Finset.mem_filter.mp (hT hx)).2
    rw [zmodProj_natCast]
    exact CharP.cast_eq_zero_iff (ZMod d) d x |>.mpr hx_dvd
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero]

/-- The fiber of subset sums in ZMod N over a residue r in ZMod d. -/
def residueFiber (N d : ℕ) (h : d ∣ N) (A : Finset ℕ) (r : ZMod d) : Finset (ZMod N) :=
  (subsetSumsMod N A).filter (fun s => zmodProj h s = r)

/-- Conlon–Fox–Pham (2021) Lemma 5.11 (Fiber Cardinality Lower Bound):
    If the residue fiber F_r is non-empty, then |subsetSumsMod N D| ≤ |F_r|,
    where D = A.filter (d ∣ ·). -/
theorem card_subsetSumsMod_dvd_le_fiber (N d : ℕ) (_hd : 0 < d) (_hN : 0 < N) (hdN : d ∣ N)
    (A : Finset ℕ) (r : ZMod d) (h_nonempty : (residueFiber N d hdN A r).Nonempty) :
    (subsetSumsMod N (A.filter (fun x => d ∣ x))).card ≤ (residueFiber N d hdN A r).card := by
  obtain ⟨s, hs⟩ := h_nonempty
  simp only [residueFiber, Finset.mem_filter] at hs
  obtain ⟨hs_in, hs_proj⟩ := hs
  rw [mem_subsetSumsMod_iff] at hs_in
  obtain ⟨B, hB_sub, rfl⟩ := hs_in
  let U := B.filter (fun x => ¬ d ∣ x)
  let V := B.filter (fun x => d ∣ x)
  have h_disj_UV : Disjoint U V := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact h1 h2
  have h_union_UV : U ∪ V = B := by
    ext x
    simp only [U, V, Finset.mem_union, Finset.mem_filter]
    tauto
  have hB_sum : B.sum (fun x => (x : ZMod N)) =
      U.sum (fun x => (x : ZMod N)) + V.sum (fun x => (x : ZMod N)) := by
    rw [← h_union_UV, Finset.sum_union h_disj_UV]
  let x : ZMod N := U.sum (fun x => (x : ZMod N))
  let y_V : ZMod N := V.sum (fun x => (x : ZMod N))
  have hy_V_in : y_V ∈ subsetSumsMod N (A.filter (fun x => d ∣ x)) := by
    rw [mem_subsetSumsMod_iff]
    refine ⟨V, ?_, rfl⟩
    intro z hz
    simp only [V, Finset.mem_filter] at hz
    simp only [Finset.mem_filter]
    exact ⟨hB_sub hz.1, hz.2⟩
  have hy_V_proj : zmodProj hdN y_V = 0 :=
    zmodProj_eq_zero_of_mem_subsetSumsMod_dvd hdN A y_V hy_V_in
  have hx_proj : zmodProj hdN x = r := by
    rwa [hB_sum, zmodProj_add, hy_V_proj, add_zero] at hs_proj
  let D := A.filter (fun x => d ∣ x)
  have h_img_sub : (subsetSumsMod N D).image (fun y => x + y) ⊆ residueFiber N d hdN A r := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mem_subsetSumsMod_iff] at hy
    obtain ⟨T, hT, rfl⟩ := hy
    have h_disj_UT : Disjoint U T := by
      rw [Finset.disjoint_left]
      intro z hzU hzT
      simp only [U, Finset.mem_filter] at hzU
      have hT_dvd : d ∣ z := (Finset.mem_filter.mp (hT hzT)).2
      exact hzU.2 hT_dvd
    have h_UT_sub : U ∪ T ⊆ A := by
      rw [Finset.union_subset_iff]
      refine ⟨?_, ?_⟩
      · intro z hz
        exact hB_sub (Finset.mem_filter.mp hz).1
      · intro z hz
        exact (Finset.mem_filter.mp (hT hz)).1
    have h_sum_UT : (U ∪ T).sum (fun z => (z : ZMod N)) = x + T.sum (fun z => (z : ZMod N)) := by
      rw [Finset.sum_union h_disj_UT]
    have hz_in : x + T.sum (fun z => (z : ZMod N)) ∈ subsetSumsMod N A := by
      rw [mem_subsetSumsMod_iff]
      exact ⟨U ∪ T, h_UT_sub, h_sum_UT⟩
    have hy_proj : zmodProj hdN (T.sum (fun z => (z : ZMod N))) = 0 :=
      zmodProj_eq_zero_of_mem_subsetSumsMod_dvd hdN A (T.sum (fun z => (z : ZMod N))) (by
        rw [mem_subsetSumsMod_iff]
        exact ⟨T, hT, rfl⟩)
    have hz_proj : zmodProj hdN (x + T.sum (fun z => (z : ZMod N))) = r := by
      rw [zmodProj_add, hx_proj, hy_proj, add_zero]
    simp only [residueFiber, Finset.mem_filter]
    exact ⟨hz_in, hz_proj⟩
  have h_inj : Function.Injective (fun (y : ZMod N) => x + y) := by
    intro a b hab
    exact add_left_cancel hab
  have h_card_img : ((subsetSumsMod N D).image (fun y => x + y)).card = (subsetSumsMod N D).card :=
    Finset.card_image_of_injective _ h_inj
  rw [← h_card_img]
  exact Finset.card_le_card h_img_sub

/-- The image of subsetSumsMod N A under the natural projection to ZMod d
    is exactly subsetSumsMod d A. -/
lemma subsetSumsMod_image_zmodProj (N d : ℕ) (hdN : d ∣ N) (A : Finset ℕ) :
    (subsetSumsMod N A).image (zmodProj hdN) = subsetSumsMod d A := by
  ext r
  simp only [Finset.mem_image, mem_subsetSumsMod_iff]
  constructor
  · rintro ⟨s, ⟨B, hB, rfl⟩, rfl⟩
    use B, hB
    rw [zmodProj_sum]
    simp_rw [zmodProj_natCast hdN]
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.sum (fun x => (x : ZMod N)), ⟨B, hB, rfl⟩, ?_⟩
    rw [zmodProj_sum]
    simp_rw [zmodProj_natCast hdN]

/-- Product lower bound:
    |subsetSumsMod d A| * |subsetSumsMod N D| ≤ |subsetSumsMod N A|. -/
theorem card_subsetSumsMod_dvd_mul_card_le (N d : ℕ) (hd : 0 < d) (hN : 0 < N) (hdN : d ∣ N)
    (A : Finset ℕ) :
    (subsetSumsMod d A).card * (subsetSumsMod N (A.filter (fun x => d ∣ x))).card ≤
      (subsetSumsMod N A).card := by
  let f := zmodProj hdN
  have h_decomp := Finset.card_eq_sum_card_image f (subsetSumsMod N A)
  rw [subsetSumsMod_image_zmodProj N d hdN A] at h_decomp
  rw [h_decomp]
  let D := A.filter (fun x => d ∣ x)
  have h_lhs : (subsetSumsMod d A).card * (subsetSumsMod N D).card =
      ∑ _ ∈ subsetSumsMod d A, (subsetSumsMod N D).card := by simp
  rw [h_lhs]
  apply Finset.sum_le_sum
  intro r hr
  have h_fib_eq : {a ∈ subsetSumsMod N A | f a = r} = residueFiber N d hdN A r := rfl
  rw [h_fib_eq]
  have hr_in : r ∈ (subsetSumsMod N A).image f := by
    rwa [subsetSumsMod_image_zmodProj N d hdN A]
  obtain ⟨s, hs_in, hs_f⟩ := Finset.mem_image.mp hr_in
  have h_nonempty : (residueFiber N d hdN A r).Nonempty := by
    use s
    simp only [residueFiber, Finset.mem_filter]
    exact ⟨hs_in, hs_f⟩
  exact card_subsetSumsMod_dvd_le_fiber N d hd hN hdN A r h_nonempty

/-- Connection with IsDiverse:
    If A is t-diverse and d - 1 ≤ t with d ∣ N, then
    d * |subsetSumsMod N D| ≤ |subsetSumsMod N A|. -/
theorem card_mul_card_subsetSumsMod_dvd_le_of_isDiverse (N d t : ℕ)
    (hd : 0 < d) (hN : 0 < N) (hdN : d ∣ N) (hdt : d - 1 ≤ t)
    (A : Finset ℕ) (h_div : IsDiverse A t) :
    d * (subsetSumsMod N (A.filter (fun x => d ∣ x))).card ≤ (subsetSumsMod N A).card := by
  have inst_ne : NeZero d := ⟨by omega⟩
  have h_univ : subsetSumsMod d A = Finset.univ := by
    ext r
    simp only [Finset.mem_univ, iff_true]
    exact subsetSumsMod_eq_univ_of_isDiverse d t hd hdt A h_div r
  have h_card_d : (subsetSumsMod d A).card = d := by
    rw [h_univ, Finset.card_univ, ZMod.card d]
  have h_prod := card_subsetSumsMod_dvd_mul_card_le N d hd hN hdN A
  rwa [h_card_d] at h_prod

-- Sanity Check 1: N = 12, d = 3, A = {1, 3, 6}
example : (subsetSumsMod 12 (({1, 3, 6} : Finset ℕ).filter (fun x => 3 ∣ x))).card = 4 := by
  have : DecidablePred (fun x : ℕ => 3 ∣ x) := fun x => Nat.decidable_dvd 3 x
  decide

example : (residueFiber 12 3 (by decide) {1, 3, 6} (0 : ZMod 3)).card = 4 := by
  decide

example : (residueFiber 12 3 (by decide) {1, 3, 6} (1 : ZMod 3)).card = 4 := by
  decide

example : (residueFiber 12 3 (by decide) {1, 3, 6} (2 : ZMod 3)).card = 0 := by
  decide

-- Sanity Check 2: N = 6, d = 2, A = {1, 7, 2}
example : (subsetSumsMod 6 (({1, 7, 2} : Finset ℕ).filter (fun x => 2 ∣ x))).card = 2 := by
  have : DecidablePred (fun x : ℕ => 2 ∣ x) := fun x => Nat.decidable_dvd 2 x
  decide

example : (residueFiber 6 2 (by decide) {1, 7, 2} (0 : ZMod 2)).card = 3 := by
  decide

example : (residueFiber 6 2 (by decide) {1, 7, 2} (1 : ZMod 2)).card = 2 := by
  decide

example : (subsetSumsMod 2 {1, 7, 2}).card * (subsetSumsMod 6 (({1, 7, 2} : Finset ℕ).filter (fun x => 2 ∣ x))).card ≤
    (subsetSumsMod 6 {1, 7, 2}).card := by
  have : DecidablePred (fun x : ℕ => 2 ∣ x) := fun x => Nat.decidable_dvd 2 x
  decide




/-!
### Subsection 8.6: Conlon–Fox–Pham Lemma 2.6 & Lemma 2.7 Translation Growth and Double Counting

In §2.1 of Conlon–Fox–Pham (2021), the growth of sumsets under greedy element addition
is analyzed using translation increments:
- 	ranslate S x = S + x = {s + x | s ∈ S}.
- delta S x = |(S + x) \ S| is the number of new elements produced by translation by x.
- smallGrowth S D = {x | delta S x ≤ D} is the set of elements with small growth.
- interCard S x = |(S + x) ∩ S|.

Key theorems formalized here:
1. delta_add_le: Subadditivity of growth delta S (x + y) ≤ delta S x + delta S y.
2. delta_sum_le_sum_delta & delta_sum_le_mul_of_forall_le (CFP Lemma 2.7):
   The growth of a sum is bounded by the sum of individual growths.
3. sum_interCard_eq_sq: Double counting identity ∑ x ∈ G, |(S + x) ∩ S| = |S|^2.
4. card_smallGrowth_mul_le & card_smallGrowth_le_div (CFP Lemma 2.6):
   |G| * (|S| - D) ≤ |S|^2 and |G| ≤ |S|^2 / (|S| - D) for any D < |S|.
5. exists_mem_large_growth: Finding an element in a candidate set T with growth > D whenever |T| > |G|.
6. card_subsetSumsMod_insert_eq: Identification of subset-sum cardinality increment upon element addition with delta.
7. 
atCast_zmod_injOn_Ico & card_image_natCast_zmod_of_Ico: Preservation of candidate cardinality under modulo projection on intervals of length ≤ d.
-/

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The translation of a finset S by an element x. -/
def translate (S : Finset G) (x : G) : Finset G :=
  S.image (fun s => s + x)

/-- The number of new elements added to S when translated by x. -/
def delta (S : Finset G) (x : G) : ℕ :=
  (translate S x \ S).card

/-- Translation preserves cardinality. -/
@[simp]
lemma card_translate (S : Finset G) (x : G) : (translate S x).card = S.card := by
  simp only [translate]
  exact Finset.card_image_of_injective S (fun _ _ h => add_right_cancel h)

/-- Translation by zero is the identity. -/
@[simp]
lemma translate_zero (S : Finset G) : translate S 0 = S := by
  ext s
  simp only [translate, Finset.mem_image, add_zero]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hs; exact ⟨s, hs, rfl⟩

/-- Composition of translations. -/
lemma translate_add (S : Finset G) (x y : G) :
    translate (translate S x) y = translate S (x + y) := by
  ext z
  simp only [translate, Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by rw [add_assoc]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s + x, ⟨s, hs, rfl⟩, add_assoc s x y⟩

/-- delta S 0 = 0. -/
@[simp]
lemma delta_zero (S : Finset G) : delta S 0 = 0 := by
  simp [delta]

/-- card (S ∪ translate S x) = S.card + delta S x. -/
lemma card_union_translate (S : Finset G) (x : G) :
    (S ∪ translate S x).card = S.card + delta S x := by
  have h_union : S ∪ translate S x = S ∪ (translate S x \ S) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h_disj : Disjoint S (translate S x \ S) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_sdiff] at hz2
    exact hz2.2 hz1
  rw [h_union, Finset.card_union_of_disjoint h_disj]
  rfl

/-- Set inclusion underlying the subadditivity of delta. -/
lemma translate_sdiff_subset_union (S : Finset G) (x y : G) :
    translate S (x + y) \ S ⊆ translate (translate S x \ S) y ∪ (translate S y \ S) := by
  intro z hz
  simp only [Finset.mem_sdiff, translate, Finset.mem_image] at hz
  obtain ⟨⟨s, hs, rfl⟩, hz_not_in⟩ := hz
  by_cases hw : s + x ∈ S
  · apply Finset.mem_union_right
    simp only [Finset.mem_sdiff, translate, Finset.mem_image]
    refine ⟨⟨s + x, hw, by rw [add_assoc]⟩, hz_not_in⟩
  · apply Finset.mem_union_left
    simp only [Finset.mem_sdiff, translate, Finset.mem_image]
    refine ⟨s + x, ⟨⟨s, hs, rfl⟩, hw⟩, by rw [add_assoc]⟩

/-- Subadditivity of delta: delta S (x + y) ≤ delta S x + delta S y. -/
lemma delta_add_le (S : Finset G) (x y : G) :
    delta S (x + y) ≤ delta S x + delta S y := by
  simp only [delta]
  have h_sub := translate_sdiff_subset_union S x y
  have h_le := Finset.card_le_card h_sub
  have h_union := Finset.card_union_le (translate (translate S x \ S) y) (translate S y \ S)
  rw [card_translate] at h_union
  exact h_le.trans h_union

/-- Conlon–Fox–Pham (2021) Lemma 2.7 (Sumset growth bound for lists):
    The growth of a sum is bounded by the sum of individual growths. -/
lemma delta_sum_le_sum_delta (S : Finset G) (xs : List G) :
    delta S xs.sum ≤ (xs.map (delta S)).sum := by
  induction xs with
  | nil =>
    simp only [List.sum_nil, List.map_nil, delta_zero, le_refl]
  | cons a as ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (delta_add_le S a as.sum).trans (Nat.add_le_add_left ih _)

/-- Conlon–Fox–Pham (2021) Lemma 2.7 (Uniform threshold version):
    If each element has delta S x ≤ D, then delta S xs.sum ≤ xs.length * D. -/
lemma delta_sum_le_mul_of_forall_le (S : Finset G) (xs : List G) (D : ℕ)
    (h : ∀ x ∈ xs, delta S x ≤ D) :
    delta S xs.sum ≤ xs.length * D := by
  induction xs with
  | nil =>
    simp only [List.sum_nil, List.length_nil, zero_mul, delta_zero, le_refl]
  | cons a as ih =>
    simp only [List.sum_cons, List.length_cons]
    have ha : delta S a ≤ D := h a (by simp)
    have has : ∀ x ∈ as, delta S x ≤ D := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ih_app := ih has
    have h_add := delta_add_le S a as.sum
    have h_step : delta S a + delta S as.sum ≤ D + as.length * D := Nat.add_le_add ha ih_app
    have h_ring : (as.length + 1) * D = D + as.length * D := by ring
    rw [h_ring]
    exact h_add.trans h_step

/-- Real threshold version of Lemma 2.7. -/
lemma delta_sum_le_mul_of_forall_le_real (S : Finset G) (xs : List G) (D : ℝ)
    (h : ∀ x ∈ xs, (delta S x : ℝ) ≤ D) :
    (delta S xs.sum : ℝ) ≤ (xs.length : ℝ) * D := by
  induction xs with
  | nil =>
    simp only [List.sum_nil, List.length_nil, Nat.cast_zero, zero_mul, delta_zero, le_refl]
  | cons a as ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha : (delta S a : ℝ) ≤ D := h a (by simp)
    have has : ∀ x ∈ as, (delta S x : ℝ) ≤ D := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ih_app := ih has
    have h_add : (delta S (a + as.sum) : ℝ) ≤ (delta S a : ℝ) + (delta S as.sum : ℝ) := by
      exact_mod_cast delta_add_le S a as.sum
    have h_step : (delta S a : ℝ) + (delta S as.sum : ℝ) ≤ D + (as.length : ℝ) * D :=
      add_le_add ha ih_app
    have h_ring : ((as.length : ℝ) + 1) * D = D + (as.length : ℝ) * D := by ring
    rw [h_ring]
    exact h_add.trans h_step

/-- Small growth set with natural threshold. -/
def smallGrowth (S : Finset G) (D : ℕ) [Fintype G] : Finset G :=
  Finset.univ.filter (fun x => delta S x ≤ D)

/-- Small growth set with real threshold. -/
noncomputable def smallGrowthR (S : Finset G) (D : ℝ) [Fintype G] : Finset G :=
  Finset.univ.filter (fun x => (delta S x : ℝ) ≤ D)

/-- The intersection cardinality I(x) = |(S + x) ∩ S|. -/
def interCard (S : Finset G) (x : G) : ℕ :=
  (translate S x ∩ S).card

/-- I(x) + delta S x = S.card. -/
lemma interCard_add_delta (S : Finset G) (x : G) :
    interCard S x + delta S x = S.card := by
  have h_union : translate S x = (translate S x ∩ S) ∪ (translate S x \ S) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h_disj : Disjoint (translate S x ∩ S) (translate S x \ S) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hz1 hz2
    exact hz2.2 hz1.2
  have h_card : (translate S x).card = (translate S x ∩ S).card + (translate S x \ S).card := by
    conv_lhs => rw [h_union]
    exact Finset.card_union_of_disjoint h_disj
  rw [card_translate] at h_card
  exact h_card.symm

/-- Bijection between the fiber of difference and (S + x) ∩ S. -/
lemma card_fiber_sub_eq_interCard (S : Finset G) (x : G) :
    ((S ×ˢ S).filter (fun p => p.1 - p.2 = x)).card = interCard S x := by
  simp only [interCard]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [Finset.mem_inter, translate, Finset.mem_image]
    refine ⟨⟨p.2, hp.1.2, ?_⟩, hp.1.1⟩
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp hp.2).symm
  · intro p1 hp1 p2 hp2 h
    simp only [Finset.mem_filter] at hp1 hp2
    have h1 : p1.2 = p1.1 - x := by rw [← hp1.2, sub_sub_self]
    have h2 : p2.2 = p2.1 - x := by rw [← hp2.2, sub_sub_self]
    ext
    · exact h
    · rw [h1, h2, h]
  · intro s hs
    simp only [Finset.mem_inter, translate, Finset.mem_image] at hs
    obtain ⟨⟨b, hb, rfl⟩, hs_in⟩ := hs
    refine ⟨(b + x, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hs_in, hb⟩, by rw [add_sub_cancel_left]⟩

/-- Double counting sum: ∑ x : G, I(x) = S.card ^ 2. -/
lemma sum_interCard_eq_sq [Fintype G] (S : Finset G) :
    ∑ x : G, interCard S x = S.card ^ 2 := by
  have h_fiber : ∑ x : G, ((S ×ˢ S).filter (fun p => p.1 - p.2 = x)).card = (S ×ˢ S).card := by
    exact (Finset.card_eq_sum_card_fiberwise (f := fun (p : G × G) => p.1 - p.2)
      (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)).symm
  have h_step : ∑ x : G, interCard S x = ∑ x : G, ((S ×ˢ S).filter (fun p => p.1 - p.2 = x)).card := by
    apply Finset.sum_congr rfl
    intro x _
    exact (card_fiber_sub_eq_interCard S x).symm
  rw [h_step, h_fiber, Finset.card_product, sq]

/-- Conlon–Fox–Pham (2021) Lemma 2.6 (Division-free natural bound):
    |G| * (|S| - D) ≤ |S|^2. -/
theorem card_smallGrowth_mul_le [Fintype G] (S : Finset G) (D : ℕ) :
    (smallGrowth S D).card * (S.card - D) ≤ S.card ^ 2 := by
  have h_sum_le : ∑ _x ∈ smallGrowth S D, (S.card - D) ≤ ∑ x ∈ smallGrowth S D, interCard S x := by
    apply Finset.sum_le_sum
    intro x hx
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h_id := interCard_add_delta S x
    omega
  have h_sub_univ : ∑ x ∈ smallGrowth S D, interCard S x ≤ ∑ x : G, interCard S x := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro _
    exact Nat.zero_le _
  rw [sum_interCard_eq_sq S] at h_sub_univ
  have h_card_mul : (smallGrowth S D).card * (S.card - D) = ∑ _x ∈ smallGrowth S D, (S.card - D) := by
    simp
  rw [h_card_mul]
  exact h_sum_le.trans h_sub_univ

/-- Natural division version of Lemma 2.6. -/
theorem card_smallGrowth_le_div [Fintype G] (S : Finset G) (D : ℕ) (hD : D < S.card) :
    (smallGrowth S D).card ≤ S.card ^ 2 / (S.card - D) :=
  (Nat.le_div_iff_mul_le (by omega)).mpr (card_smallGrowth_mul_le S D)

/-- Real division-free version of Lemma 2.6. -/
theorem card_smallGrowthR_mul_le [Fintype G] (S : Finset G) (D : ℝ) :
    ((smallGrowthR S D).card : ℝ) * ((S.card : ℝ) - D) ≤ (S.card : ℝ) ^ 2 := by
  have h_sum_le : ∑ _x ∈ smallGrowthR S D, ((S.card : ℝ) - D) ≤ ∑ x ∈ smallGrowthR S D, (interCard S x : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    simp only [smallGrowthR, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have h_id := interCard_add_delta S x
    have h_id_r : (interCard S x : ℝ) + (delta S x : ℝ) = (S.card : ℝ) := by
      exact_mod_cast h_id
    linarith
  have h_sub_univ : ∑ x ∈ smallGrowthR S D, (interCard S x : ℝ) ≤ ∑ x : G, (interCard S x : ℝ) := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro _
    exact Nat.cast_nonneg _
  have h_univ_eq : ∑ x : G, (interCard S x : ℝ) = (S.card : ℝ) ^ 2 := by
    have := sum_interCard_eq_sq S
    exact_mod_cast this
  rw [h_univ_eq] at h_sub_univ
  have h_card_mul : ∑ _x ∈ smallGrowthR S D, ((S.card : ℝ) - D) = ((smallGrowthR S D).card : ℝ) * ((S.card : ℝ) - D) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_card_mul] at h_sum_le
  exact h_sum_le.trans h_sub_univ

/-- Real division version of Lemma 2.6. -/
theorem card_smallGrowthR_le_div [Fintype G] (S : Finset G) (D : ℝ) (hD : D < (S.card : ℝ)) :
    ((smallGrowthR S D).card : ℝ) ≤ (S.card : ℝ) ^ 2 / ((S.card : ℝ) - D) := by
  have h_pos : 0 < (S.card : ℝ) - D := by linarith
  have h_mul := card_smallGrowthR_mul_le S D
  rw [le_div_iff₀ h_pos]
  exact h_mul

/-- Selection of element with growth strictly exceeding threshold (natural version). -/
lemma exists_mem_large_growth [Fintype G] (S : Finset G) (T : Finset G) (D : ℕ)
    (h_card : (smallGrowth S D).card < T.card) :
    ∃ a ∈ T, D < delta S a := by
  by_contra! h
  have h_sub : T ⊆ smallGrowth S D := by
    intro x hx
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x hx
  have h_le := Finset.card_le_card h_sub
  omega

/-- Selection of element with growth strictly exceeding threshold (real version). -/
lemma exists_mem_large_growth_real [Fintype G] (S : Finset G) (T : Finset G) (D : ℝ)
    (h_card : ((smallGrowthR S D).card : ℝ) < (T.card : ℝ)) :
    ∃ a ∈ T, D < (delta S a : ℝ) := by
  by_contra! h
  have h_sub : T ⊆ smallGrowthR S D := by
    intro x hx
    simp only [smallGrowthR, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h x hx
  have h_le := Finset.card_le_card h_sub
  have : (T.card : ℝ) ≤ ((smallGrowthR S D).card : ℝ) := Nat.cast_le.mpr h_le
  linarith

/-- Incremental cardinality formula for subsetSumsMod upon inserting an element:
    |subsetSumsMod d (insert x A)| = |subsetSumsMod d A| + delta (subsetSumsMod d A) (x : ZMod d). -/
lemma card_subsetSumsMod_insert_eq (d : ℕ) (A : Finset ℕ) (x : ℕ) (hx : x ∉ A) :
    (subsetSumsMod d (insert x A)).card =
      (subsetSumsMod d A).card + delta (subsetSumsMod d A) (x : ZMod d) := by
  have h_ins := subsetSumsMod_insert d A x hx
  have h_trans : Finset.image (fun r => r + (x : ZMod d)) (subsetSumsMod d A) =
      translate (subsetSumsMod d A) (x : ZMod d) := rfl
  rw [h_trans] at h_ins
  rw [h_ins]
  exact card_union_translate (subsetSumsMod d A) (x : ZMod d)

/-- Modulo injectivity on an interval of length ≤ d. -/
lemma natCast_zmod_injOn_Ico (d y : ℕ) (A : Finset ℕ)
    (hA : ∀ x ∈ A, y ≤ x ∧ x < y + d) :
    Set.InjOn (fun (x : ℕ) => (x : ZMod d)) (A : Set ℕ) := by
  intro a ha b hb hab
  have ha_bounds := hA a ha
  have hb_bounds := hA b hb
  by_cases hd : d = 0
  · subst hd; omega
  have inst_ne : NeZero d := ⟨hd⟩
  rw [ZMod.natCast_eq_natCast_iff] at hab
  have h_diff_a : a - y < d := by omega
  have h_diff_b : b - y < d := by omega
  have h_sub_a : a - y + y = a := Nat.sub_add_cancel ha_bounds.1
  have h_sub_b : b - y + y = b := Nat.sub_add_cancel hb_bounds.1
  have h_modeq : (a - y) % d = (b - y) % d := by
    have h1 : (a - y + y) ≡ (b - y + y) [MOD d] := by
      rw [h_sub_a, h_sub_b]
      exact hab
    exact Nat.ModEq.add_right_cancel' y h1
  rw [Nat.mod_eq_of_lt h_diff_a, Nat.mod_eq_of_lt h_diff_b] at h_modeq
  omega

/-- Cardinality preservation under modulo projection on an interval of length ≤ d. -/
lemma card_image_natCast_zmod_of_Ico (d y : ℕ) (A : Finset ℕ)
    (hA : ∀ x ∈ A, y ≤ x ∧ x < y + d) :
    (A.image (fun (x : ℕ) => (x : ZMod d))).card = A.card := by
  exact Finset.card_image_of_injOn (natCast_zmod_injOn_Ico d y A hA)

-- Sanity Check 1: N = 7, S = {0, 1, 2}, D = 1
example : (smallGrowth ({0, 1, 2} : Finset (ZMod 7)) 1) = {0, 1, 6} := by
  decide

example : (smallGrowth ({0, 1, 2} : Finset (ZMod 7)) 1).card * (3 - 1) ≤ 3 ^ 2 := by
  decide

-- Sanity Check 2: N = 6, S = {0, 2, 4}, D = 0
example : (smallGrowth ({0, 2, 4} : Finset (ZMod 6)) 0) = {0, 2, 4} := by
  decide

example : (smallGrowth ({0, 2, 4} : Finset (ZMod 6)) 0).card * (3 - 0) ≤ 3 ^ 2 := by
  decide


/-!
### Section 9: The Master Theorems for Erdős Problem JSP-000298 (Erdős #360)

This section synthesizes the three historical milestones of Erdős Problem 360 into unified master theorems:
1. `erdos_problem_360_finite_master`:
   Exact two-sided bounds for any specific integer n ≥ 3 given a lower bound witness and CFP configuration.
2. `erdos_problem_360_unconditional_master`:
   Unconditional non-trivial lower bound f(n) ≥ 2 and CFP 4-layer upper bound for all n ≥ 3.
3. `erdos_problem_360_asymptotic_master`:
   Conlon–Fox–Pham (2021) two-sided asymptotic growth equivalence f(n) ≍ F(n).
4. `erdos_problem_360_unified_solution`:
   Grand synthesis unifying the cubic root baseline, Selberg prime sieve improvement,
   CFP 4-layer upper bound, CFP inverse additive lower bound, and asymptotic growth equivalence.
-/

/-- Finite Master Theorem for Erdős Problem JSP-000298 (Erdős #360):
    For any integer n ≥ 3, any lower bound witness w : CFPLowerBoundWitness n k,
    and any valid Conlon–Fox–Pham 4-layer configuration
    (s1 interval blocks, prime set P not dividing n, modulus d, and remainder step s_rem ≤ s1),
    the chromatic number f(n) is rigorously sandwiched between k + 1 and the 4-layer upper bound:
      k + 1 ≤ f(n) ≤ s1 + |P| + 2 * |reducedResidues d| + ⌈|R_cfp| / s_rem⌉. -/
theorem erdos_problem_360_finite_master (n : ℕ) (hn : 3 ≤ n)
    (s1 : ℕ) (hs1 : 1 ≤ s1) (P : Finset ℕ) (d s_rem : ℕ)
    (hd : 1 ≤ d) (hs_rem : 1 ≤ s_rem) (h_srem_le : s_rem ≤ s1)
    (hP : ∀ p ∈ P, ¬ p ∣ n)
    (k : ℕ) (w : CFPLowerBoundWitness n k) :
    let T := reducedResidues d
    let R := cfpRemainder n s1 d P
    k + 1 ≤ minColors n (by omega) ∧
    minColors n (by omega) ≤ s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem := by
  refine ⟨minColors_ge_of_cfp_witness n k (by omega) w,
          minColors_le_conlon_fox_pham n s1 P d s_rem (by omega) hs1 hd hs_rem h_srem_le hP⟩

/-!
### Subsection 8.7: Iterated Sumsets and Kneser–Lemma 2.3 Algebraic Bridge (CFP Lemma 2.3)

In §2.1 of Conlon–Fox–Pham (2021), Lemma 2.3 provides the growth of iterated sumsets:
for a subset T of a finite abelian group G containing 0 and generating G,
  min (|G|) ((k + 1) * |T| / 2) ≤ |k T|.

Here we formalize:
1. sumset A B: standard sumset in an additive abelian group.
2. iterSum k T: k-fold iterated sumset, with decomposition iterSum (a + b) T = sumset (iterSum a T) (iterSum b T).
3. iterSum_mono_of_zero_mem: monotonicity under 0 ∈ T.
4. iterSum_smallGrowth_subset: containment of iterated small growth sumsets in small growth of scaled threshold.
5. cochrane_ostergaard_spencer_arith_le: Cochrane–Ostergaard–Spencer algebraic inequality:
   for k ≥ 1 and q ≥ 2, (k + 1) * q ≤ 2 * (k * (q - 1) + 1).
6. iterSum_growth_bound_of_kneser_data: deduced bound (k + 1) * |T| ≤ 2 * |kT| from Kneser bounds.
7. iterSum_card_ge_of_kneser_hyp and iterSum_card_ge_of_kneser_hyp_real:
   natural and real-valued conditional growth interfaces for Lemma 2.3.
-/

/-- Single-step expansion when 0 ∈ T: kT ⊆ (k + 1)T. -/
lemma iterSum_subset_succ (T : Finset G) (h0 : 0 ∈ T) (k : ℕ) :
    iterSum k T ⊆ iterSum (k + 1) T := by
  intro x hx
  simp only [iterSum_succ, mem_sumset_iff]
  exact ⟨x, hx, 0, h0, add_zero x⟩

/-- Monotonicity of iterated sumsets when 0 ∈ T. -/
lemma iterSum_mono_of_zero_mem (T : Finset G) (h0 : 0 ∈ T) {k1 k2 : ℕ} (h : k1 ≤ k2) :
    iterSum k1 T ⊆ iterSum k2 T := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  clear h
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    exact Finset.Subset.trans ih (iterSum_subset_succ T h0 (k1 + d))

/-- Small growth is preserved under iterated sumsets:
    kT ⊆ smallGrowth S (k * D) when T ⊆ smallGrowth S D. -/
lemma iterSum_smallGrowth_subset [Fintype G] (S : Finset G) (D : ℕ) (k : ℕ) :
    iterSum k (smallGrowth S D) ⊆ smallGrowth S (k * D) := by
  induction k with
  | zero =>
    intro x hx
    simp only [iterSum_zero, Finset.mem_singleton] at hx
    subst hx
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [delta_zero, Nat.zero_mul]
  | succ k ih =>
    intro z hz
    simp only [iterSum_succ, mem_sumset_iff] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hx_growth : delta S x ≤ k * D := by
      have := ih hx
      simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hy_growth : delta S y ≤ D := by
      have := hy
      simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and]
    have h_add := delta_add_le S x y
    have : delta S x + delta S y ≤ k * D + D := Nat.add_le_add hx_growth hy_growth
    have h_ring : (k + 1) * D = k * D + D := by ring
    rw [h_ring]
    exact h_add.trans this

/-- Cochrane–Ostergaard–Spencer algebraic bridge from Kneser to Lemma 2.3:
    If 2 ≤ q and 1 ≤ k, then (k + 1) * q ≤ 2 * (k * (q - 1) + 1). -/
lemma cochrane_ostergaard_spencer_arith_le (k q : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) :
    (k + 1) * q ≤ 2 * (k * (q - 1) + 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = 1 + k' := ⟨k - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = 2 + q' := ⟨q - 2, by omega⟩
  have hq1 : 2 + q' - 1 = q' + 1 := by omega
  rw [hq1]
  have h_lhs : (1 + k' + 1) * (2 + q') = k' * q' + 2 * k' + 2 * q' + 4 := by ring
  have h_rhs : 2 * ((1 + k') * (q' + 1) + 1) = 2 * (k' * q') + 2 * k' + 2 * q' + 4 := by ring
  rw [h_lhs, h_rhs]
  omega

/-- The Kneser bridge theorem:
    Under Kneser bounds |kT| ≥ (k * (q - 1) + 1) * |H| and |T| ≤ q * |H|
    with q ≥ 2, we deduce (k + 1) * |T| ≤ 2 * |kT|. -/
theorem iterSum_growth_bound_of_kneser_data (card_kT card_T card_H k q : ℕ)
    (hk : 1 ≤ k) (hq : 2 ≤ q)
    (h_T_le : card_T ≤ q * card_H)
    (h_kT_ge : (k * (q - 1) + 1) * card_H ≤ card_kT) :
    (k + 1) * card_T ≤ 2 * card_kT := by
  have h_arith := cochrane_ostergaard_spencer_arith_le k q hk hq
  have h1 : (k + 1) * card_T ≤ (k + 1) * (q * card_H) :=
    Nat.mul_le_mul_left (k + 1) h_T_le
  have h_assoc : (k + 1) * (q * card_H) = ((k + 1) * q) * card_H := by ring
  rw [h_assoc] at h1
  have h2 : ((k + 1) * q) * card_H ≤ (2 * (k * (q - 1) + 1)) * card_H :=
    Nat.mul_le_mul_right card_H h_arith
  have h3 : (2 * (k * (q - 1) + 1)) * card_H = 2 * ((k * (q - 1) + 1) * card_H) := by ring
  rw [h3] at h2
  have h4 : 2 * ((k * (q - 1) + 1) * card_H) ≤ 2 * card_kT :=
    Nat.mul_le_mul_left 2 h_kT_ge
  exact h1.trans (h2.trans h4)

/-- Stabilizer of a finset S in G: elements x such that delta S x = 0. -/
def stab (S : Finset G) [Fintype G] : Finset G :=
  Finset.univ.filter (fun x => delta S x = 0)

/-- Conditional interface for Conlon–Fox–Pham (2021) Lemma 2.3:
    For a set T in a finite abelian group G containing 0 and generating G,
    either |kT| = |G| or 2 * |kT| ≥ (k + 1) * |T|. -/
theorem iterSum_card_ge_of_kneser_hyp [Fintype G] (T : Finset G) (k : ℕ)
    (hk : 1 ≤ k)
    (h_kneser : (iterSum k T).card = Fintype.card G ∨
      ∃ card_H q : ℕ, 2 ≤ q ∧ T.card ≤ q * card_H ∧
        (k * (q - 1) + 1) * card_H ≤ (iterSum k T).card) :
    min (2 * Fintype.card G) ((k + 1) * T.card) ≤ 2 * (iterSum k T).card := by
  cases h_kneser with
  | inl h_full =>
    rw [h_full]
    exact min_le_left _ _
  | inr h_sub =>
    obtain ⟨card_H, q, hq, hT, hkT⟩ := h_sub
    have h_bound := iterSum_growth_bound_of_kneser_data (iterSum k T).card T.card card_H k q hk hq hT hkT
    exact (min_le_right _ _).trans h_bound

/-- Real version of the conditional Lemma 2.3 interface. -/
theorem iterSum_card_ge_of_kneser_hyp_real [Fintype G] (T : Finset G) (k : ℕ)
    (hk : 1 ≤ k)
    (h_kneser : (iterSum k T).card = Fintype.card G ∨
      ∃ card_H q : ℕ, 2 ≤ q ∧ T.card ≤ q * card_H ∧
        (k * (q - 1) + 1) * card_H ≤ (iterSum k T).card) :
    min (Fintype.card G : ℝ) (((k + 1 : ℝ) * (T.card : ℝ)) / 2) ≤ ((iterSum k T).card : ℝ) := by
  have h_int := iterSum_card_ge_of_kneser_hyp T k hk h_kneser
  have h_min := min_le_iff.mp h_int
  rcases h_min with h | h
  · have : Fintype.card G ≤ (iterSum k T).card := by omega
    have : (Fintype.card G : ℝ) ≤ ((iterSum k T).card : ℝ) := Nat.cast_le.mpr this
    exact (min_le_left _ _).trans this
  · have : ((k + 1 : ℝ) * (T.card : ℝ)) / 2 ≤ ((iterSum k T).card : ℝ) := by
      have h_real : ((k + 1) * T.card : ℝ) ≤ ((2 * (iterSum k T).card : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h_real
      linarith
    exact (min_le_right _ _).trans this

/-!
### Subsection 8.8: Subgroup Index, Scaled Coprimality and Fiber Coordinates (P04)

In §5.1 of Conlon–Fox–Pham (2021), when analyzing residue classes modulo t,
the remaining candidate set B may have integer gcd not dividing t.
The true subgroup index is:
  g = gcd(t, gcd of all elements of B).

Here we formalize:
1. subgroupIndex t B = Nat.gcd t (B.gcd id): the exact subgroup index dividing t.
2. Positivity, divisibility, and monotonicity: B' ⊆ B → g(B) ∣ g(B').
3. Strict increase doubles the index: g(B) < g(B') → 2 * g(B) ≤ g(B').
4. subgroupIndex_scaled_coprime: the scaled set {a / g | a ∈ B} generates ZMod (t / g).
5. 
atCast_zmod_div_injOn_Ico & card_image_natCast_zmod_div_of_Ico:
   injectivity and cardinality preservation under scaled projection on intervals of length ≤ t / g.
6. Fiber coordinates:
   
iber h S r (connecting to existing 
esidueFiber),
   card_eq_sum_image_fibers,
   delta_fiber_le_delta,
   centerFiber: centering fibers to the kernel subgroup,
   card_centerFiber, centerFiber_subset_kernel, and delta_centerFiber_eq.
-/

/-- The subgroup index g = gcd(t, gcd of all elements of B). -/
def subgroupIndex (t : ℕ) (B : Finset ℕ) : ℕ :=
  Nat.gcd t (B.gcd id)

lemma subgroupIndex_pos (t : ℕ) (B : Finset ℕ) (ht : 0 < t) :
    0 < subgroupIndex t B :=
  Nat.gcd_pos_of_pos_left (B.gcd id) ht

lemma subgroupIndex_dvd_modulus (t : ℕ) (B : Finset ℕ) :
    subgroupIndex t B ∣ t :=
  Nat.gcd_dvd_left t (B.gcd id)

lemma subgroupIndex_dvd_mem (t : ℕ) (B : Finset ℕ) {a : ℕ} (ha : a ∈ B) :
    subgroupIndex t B ∣ a := by
  have h1 : subgroupIndex t B ∣ B.gcd id := Nat.gcd_dvd_right t (B.gcd id)
  have h2 : B.gcd id ∣ a := Finset.gcd_dvd ha
  exact h1.trans h2

lemma subgroupIndex_mono (t : ℕ) {B B' : Finset ℕ} (hsub : B' ⊆ B) :
    subgroupIndex t B ∣ subgroupIndex t B' := by
  apply Nat.dvd_gcd (subgroupIndex_dvd_modulus t B)
  have h1 : subgroupIndex t B ∣ B.gcd id := Nat.gcd_dvd_right t (B.gcd id)
  have h2 : B.gcd id ∣ B'.gcd id := Finset.gcd_mono hsub
  exact h1.trans h2

lemma subgroupIndex_doubles_of_lt (t : ℕ) {B B' : Finset ℕ} (ht : 0 < t) (hsub : B' ⊆ B)
    (hlt : subgroupIndex t B < subgroupIndex t B') :
    2 * subgroupIndex t B ≤ subgroupIndex t B' := by
  have hdvd := subgroupIndex_mono t hsub
  have hpos := subgroupIndex_pos t B ht
  obtain ⟨c, hc⟩ := hdvd
  have hc_gt_one : 1 < c := by
    by_contra! hc_le
    interval_cases c
    · rw [hc, mul_zero] at hlt
      omega
    · rw [hc, mul_one] at hlt
      omega
  have : 2 ≤ c := hc_gt_one
  calc 2 * subgroupIndex t B ≤ c * subgroupIndex t B := Nat.mul_le_mul_right (subgroupIndex t B) this
  _ = subgroupIndex t B' := by rw [mul_comm, hc]

lemma subgroupIndex_le_of_mem (t : ℕ) {B : Finset ℕ} {a : ℕ} (ha : a ∈ B) (ha_pos : 0 < a) :
    subgroupIndex t B ≤ a :=
  Nat.le_of_dvd ha_pos (subgroupIndex_dvd_mem t B ha)

lemma subgroupIndex_le_modulus (t : ℕ) (B : Finset ℕ) (ht : 0 < t) :
    subgroupIndex t B ≤ t :=
  Nat.le_of_dvd ht (subgroupIndex_dvd_modulus t B)

/-- Coprimality of the scaled set with (t / g):
    the elements {a / g | a ∈ B} generate ZMod (t / g). -/
theorem subgroupIndex_scaled_coprime (t : ℕ) (B : Finset ℕ) (ht : 0 < t) :
    let g := subgroupIndex t B
    Nat.gcd (t / g) ((B.image (fun x => x / g)).gcd id) = 1 := by
  intro g
  let d := Nat.gcd (t / g) ((B.image (fun x => x / g)).gcd id)
  have hd_t : d ∣ t / g := Nat.gcd_dvd_left _ _
  have hd_B : d ∣ (B.image (fun x => x / g)).gcd id := Nat.gcd_dvd_right _ _
  have hg_dvd_t : g ∣ t := subgroupIndex_dvd_modulus t B
  have hg_pos : 0 < g := subgroupIndex_pos t B ht
  have hdg_dvd_t : d * g ∣ t := by
    have : d * g ∣ (t / g) * g := Nat.mul_dvd_mul_right hd_t g
    rwa [Nat.div_mul_cancel hg_dvd_t] at this
  have hdg_dvd_mem : ∀ a ∈ B, d * g ∣ a := by
    intro a ha
    have ha_img : a / g ∈ B.image (fun x => x / g) := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hd_ag : d ∣ a / g := hd_B.trans (Finset.gcd_dvd ha_img)
    have hg_dvd_a : g ∣ a := subgroupIndex_dvd_mem t B ha
    have : d * g ∣ (a / g) * g := Nat.mul_dvd_mul_right hd_ag g
    rwa [Nat.div_mul_cancel hg_dvd_a] at this
  have hdg_dvd_Bgcd : d * g ∣ B.gcd id := Finset.dvd_gcd hdg_dvd_mem
  have hdg_dvd_g : d * g ∣ g := by
    have : d * g ∣ Nat.gcd t (B.gcd id) := Nat.dvd_gcd hdg_dvd_t hdg_dvd_Bgcd
    exact this
  have : d * g ≤ 1 * g := by
    have h_le := Nat.le_of_dvd hg_pos hdg_dvd_g
    rwa [one_mul]
  have hd_le_one : d ≤ 1 := Nat.le_of_mul_le_mul_right this hg_pos
  have hd_pos : 0 < d := by
    apply Nat.gcd_pos_of_pos_left
    have h_div_pos : 0 < t / g := Nat.div_pos (subgroupIndex_le_modulus t B ht) hg_pos
    exact h_div_pos
  omega

-- Sanity checks from P04:
-- 1. B = {6, 10}, t = 15: integer gcd is 2, but does not divide 15; subgroupIndex is 1.
example : subgroupIndex 15 {6, 10} = 1 := by
  decide

-- 2. B = {6, 10}, t = 12: subgroupIndex is 2.
example : subgroupIndex 12 {6, 10} = 2 := by
  decide

-- 3. t = 1: subgroupIndex is 1.
example : subgroupIndex 1 {6, 10} = 1 := by
  decide

/-- Scaled injectivity on an interval of length ≤ t / g. -/
lemma natCast_zmod_div_injOn_Ico (t g L : ℕ) (B : Finset ℕ)
    (_hg : 0 < g) (h_dvd : ∀ x ∈ B, g ∣ x)
    (hB : ∀ x ∈ B, L ≤ x / g ∧ x / g < L + t / g) :
    Set.InjOn (fun (x : ℕ) => ((x / g : ℕ) : ZMod (t / g))) (B : Set ℕ) := by
  intro a ha b hb hab
  have ha_dvd := h_dvd a ha
  have hb_dvd := h_dvd b hb
  have h_inj := natCast_zmod_injOn_Ico (t / g) L (B.image (fun x => x / g)) (by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hB x hx)
  have ha_in : a / g ∈ (B.image (fun x => x / g) : Set ℕ) := Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hb_in : b / g ∈ (B.image (fun x => x / g) : Set ℕ) := Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  have h_div_eq : a / g = b / g := h_inj ha_in hb_in hab
  have ha_eq : a = (a / g) * g := (Nat.div_mul_cancel ha_dvd).symm
  have hb_eq : b = (b / g) * g := (Nat.div_mul_cancel hb_dvd).symm
  rw [ha_eq, hb_eq, h_div_eq]

/-- Cardinality preservation under scaled modulo projection. -/
lemma card_image_natCast_zmod_div_of_Ico (t g L : ℕ) (B : Finset ℕ)
    (hg : 0 < g) (h_dvd : ∀ x ∈ B, g ∣ x)
    (hB : ∀ x ∈ B, L ≤ x / g ∧ x / g < L + t / g) :
    (B.image (fun (x : ℕ) => ((x / g : ℕ) : ZMod (t / g)))).card = B.card := by
  exact Finset.card_image_of_injOn (natCast_zmod_div_injOn_Ico t g L B hg h_dvd hB)

/-- A fiber of a subset S ⊆ ZMod N over residue r ∈ ZMod d. -/
def fiber {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d) : Finset (ZMod N) :=
  S.filter (fun s => zmodProj h s = r)

lemma fiber_subset {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d) :
    fiber h S r ⊆ S :=
  Finset.filter_subset _ _

lemma disjoint_fibers {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) {r1 r2 : ZMod d} (hne : r1 ≠ r2) :
    Disjoint (fiber h S r1) (fiber h S r2) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [fiber, Finset.mem_filter] at hx1 hx2
  exact hne (hx1.2.symm.trans hx2.2)

lemma card_eq_sum_image_fibers {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) :
    S.card = ∑ r ∈ S.image (zmodProj h), (fiber h S r).card := by
  have h_decomp := Finset.card_eq_sum_card_image (zmodProj h) S
  exact h_decomp

/-- When translation x has zmodProj h x = 0 (i.e. x is in the kernel),
    translation by x preserves fibers. -/
lemma translate_fiber_subset {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (x : ZMod N)
    (hx : zmodProj h x = 0) (r : ZMod d) :
    translate (fiber h S r) x ⊆ fiber h (translate S x) r := by
  intro z hz
  simp only [translate, Finset.mem_image, fiber, Finset.mem_filter] at hz ⊢
  obtain ⟨s, ⟨hs_in, hs_proj⟩, rfl⟩ := hz
  refine ⟨⟨s, hs_in, rfl⟩, ?_⟩
  rw [zmodProj_add, hs_proj, hx, add_zero]

/-- Single fiber growth is bounded by total growth when zmodProj h x = 0. -/
lemma delta_fiber_le_delta {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (x : ZMod N)
    (hx : zmodProj h x = 0) (r : ZMod d) :
    delta (fiber h S r) x ≤ delta S x := by
  simp only [delta]
  have h_sub : translate (fiber h S r) x \ fiber h S r ⊆ translate S x \ S := by
    intro z hz
    simp only [Finset.mem_sdiff, translate, Finset.mem_image, fiber, Finset.mem_filter] at hz ⊢
    obtain ⟨⟨s, ⟨hs_in, hs_proj⟩, rfl⟩, hz_not_fib⟩ := hz
    refine ⟨⟨s, hs_in, rfl⟩, ?_⟩
    intro hz_in
    apply hz_not_fib
    refine ⟨hz_in, ?_⟩
    rw [zmodProj_add, hs_proj, hx, add_zero]
  exact Finset.card_le_card h_sub

/-- Coordinate centering of a fiber around a basepoint x0:
    shifts fiber elements to the kernel (multiples of d). -/
def centerFiber {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d) (x0 : ZMod N) : Finset (ZMod N) :=
  (fiber h S r).image (fun s => s - x0)

/-- Center fiber preserves cardinality. -/
lemma card_centerFiber {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d) (x0 : ZMod N) :
    (centerFiber h S r x0).card = (fiber h S r).card := by
  simp only [centerFiber]
  exact Finset.card_image_of_injective _ (fun a b hab => by
    rw [← sub_add_cancel a x0, hab, sub_add_cancel])

/-- Center fiber elements lie in the kernel of zmodProj when x0 is in the fiber. -/
lemma centerFiber_subset_kernel {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d)
    (x0 : ZMod N) (hx0 : zmodProj h x0 = r) :
    ∀ y ∈ centerFiber h S r x0, zmodProj h y = 0 := by
  intro y hy
  simp only [centerFiber, Finset.mem_image, fiber, Finset.mem_filter] at hy
  obtain ⟨s, ⟨_, hs_proj⟩, rfl⟩ := hy
  rw [zmodProj_sub, hs_proj, hx0, sub_self]

/-- Translation of centered fiber by an element in the kernel matches translation of the original fiber. -/
lemma delta_centerFiber_eq {N d : ℕ} (h : d ∣ N) (S : Finset (ZMod N)) (r : ZMod d)
    (x0 : ZMod N) (x : ZMod N) :
    delta (centerFiber h S r x0) x = delta (fiber h S r) x := by
  simp only [delta, centerFiber, translate]
  have h_img1 : ((fiber h S r).image (fun s => s - x0)).image (fun s => s + x) =
      ((fiber h S r).image (fun s => s + x)).image (fun s => s - x0) := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s + x, ⟨s, hs, rfl⟩, by ring⟩
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s - x0, ⟨s, hs, rfl⟩, by ring⟩
  rw [h_img1]
  have h_sdiff : ((fiber h S r).image (fun s => s + x)).image (fun s => s - x0) \
                 (fiber h S r).image (fun s => s - x0) =
                 (((fiber h S r).image (fun s => s + x)) \ (fiber h S r)).image (fun s => s - x0) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨⟨s1, hs1, rfl⟩, hz_not⟩
      refine ⟨s1, ⟨hs1, ?_⟩, rfl⟩
      intro hs1_in
      exact hz_not ⟨s1, hs1_in, rfl⟩
    · rintro ⟨s1, ⟨hs1_trans, hs1_not⟩, rfl⟩
      refine ⟨⟨s1, hs1_trans, rfl⟩, ?_⟩
      rintro ⟨s2, hs2, heq⟩
      have : s1 = s2 := by rw [← sub_add_cancel s1 x0, ← heq, sub_add_cancel]
      subst this
      exact hs1_not hs2
  rw [h_sdiff]
  exact Finset.card_image_of_injective _ (fun a b hab => by
    rw [← sub_add_cancel a x0, hab, sub_add_cancel])

/-!
### 15. Integer Arithmetic Progressions and Coset AP Lifting (Conlon–Fox–Pham 2021, Lemma 5.10 / Phase P08)

Integer AP representations, cardinality preservation, coset AP lifting, and length sum bounds.
-/

/-- A coset arithmetic progression in ZMod N with subgroup H, start c, step v, and length ell. -/
structure CosetAP (N : ℕ) where
  H : AddSubgroup (ZMod N)
  c : ZMod N
  v : ZMod N
  ell : ℕ

/-- The elements of a coset arithmetic progression as a finite set in ZMod N. -/
noncomputable def CosetAP.toFinset {N : ℕ} [NeZero N] (R : CosetAP N) : Finset (ZMod N) :=
  (Finset.range R.ell).biUnion (fun j =>
    ((R.H : Set (ZMod N)).toFinset).image (fun h => R.c + (j : ZMod N) * R.v + h))

/-- Cardinality of a CosetAP is bounded by ell * |H|. -/
lemma CosetAP.card_toFinset_le {N : ℕ} [NeZero N] (R : CosetAP N) :
    R.toFinset.card ≤ R.ell * (R.H : Set (ZMod N)).toFinset.card := by
  dsimp [CosetAP.toFinset]
  have h := Finset.card_biUnion_le (s := Finset.range R.ell)
    (t := fun j => ((R.H : Set (ZMod N)).toFinset).image (fun h => R.c + (j : ZMod N) * R.v + h))
  have h_img : ∀ j ∈ Finset.range R.ell,
      (((R.H : Set (ZMod N)).toFinset).image (fun h => R.c + (j : ZMod N) * R.v + h)).card ≤
      (R.H : Set (ZMod N)).toFinset.card := by
    intro j _hj
    exact Finset.card_image_le
  have h_sum : ∑ j ∈ Finset.range R.ell,
      (((R.H : Set (ZMod N)).toFinset).image (fun h => R.c + (j : ZMod N) * R.v + h)).card ≤
      ∑ _j ∈ Finset.range R.ell, (R.H : Set (ZMod N)).toFinset.card :=
    Finset.sum_le_sum h_img
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h_sum
  exact h.trans h_sum

/-- An integer arithmetic progression with start a, common difference b > 0, and length k. -/
structure IntAP where
  a : ℤ
  b : ℕ
  hb : 0 < b
  k : ℕ

/-- The elements of an integer arithmetic progression as a finite set. -/
def IntAP.toFinset (P : IntAP) : Finset ℤ :=
  (Finset.range P.k).image (fun (j : ℕ) => P.a + (j : ℤ) * (P.b : ℤ))

/-- The cardinality of an IntAP with positive step is exactly its length k. -/
lemma IntAP.card_toFinset (P : IntAP) : P.toFinset.card = P.k := by
  dsimp [IntAP.toFinset]
  rw [Finset.card_image_of_injective (Finset.range P.k)]
  · exact Finset.card_range P.k
  · intro x y hxy
    have hb_pos := P.hb
    have hb_ne : (P.b : ℤ) ≠ 0 := by omega
    have : (x : ℤ) * (P.b : ℤ) = (y : ℤ) * (P.b : ℤ) := by linarith
    have : (x : ℤ) = (y : ℤ) := mul_right_cancel₀ hb_ne this
    exact_mod_cast this

/-- Injectivity of the integer arithmetic progression mapping when common difference b > 0. -/
lemma IntAP.inj_of_hb (P : IntAP) :
    ∀ x y : ℕ, P.a + (x : ℤ) * (P.b : ℤ) = P.a + (y : ℤ) * (P.b : ℤ) → x = y := by
  intro x y hxy
  have hb_pos := P.hb
  have hb_ne : (P.b : ℤ) ≠ 0 := by omega
  have : (x : ℤ) * (P.b : ℤ) = (y : ℤ) * (P.b : ℤ) := by linarith
  have : (x : ℤ) = (y : ℤ) := mul_right_cancel₀ hb_ne this
  exact_mod_cast this

/-- Fundamental separation principle for linear congruences:
    For any common difference b coprime to modulus d > 0, any two distinct solutions
    j1 < j2 to d ∣ a + j * b have gap at least d. -/
lemma linear_dvd_sub_ge_d (a : ℤ) (b : ℕ) (d : ℕ) (_hd : 0 < d) (hbd : Nat.Coprime b d)
    (j1 j2 : ℕ) (h_lt : j1 < j2)
    (h1 : (d : ℤ) ∣ (a + (j1 : ℤ) * (b : ℤ)))
    (h2 : (d : ℤ) ∣ (a + (j2 : ℤ) * (b : ℤ))) :
    d ≤ j2 - j1 := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  have h_diff : (a + (j2 : ℤ) * (b : ℤ)) - (a + (j1 : ℤ) * (b : ℤ)) = (k2 - k1) * (d : ℤ) := by
    rw [hk2, hk1]
    ring
  have h_eq : (a + (j2 : ℤ) * (b : ℤ)) - (a + (j1 : ℤ) * (b : ℤ)) = ((j2 : ℤ) - (j1 : ℤ)) * (b : ℤ) := by ring
  rw [h_eq] at h_diff
  have hj_cast : (j2 : ℤ) - (j1 : ℤ) = ((j2 - j1 : ℕ) : ℤ) := (Int.ofNat_sub (by omega)).symm
  rw [hj_cast] at h_diff
  have hdvd_int : (d : ℤ) ∣ ((j2 - j1 : ℕ) : ℤ) * (b : ℤ) := by
    use (k2 - k1)
    rw [h_diff, mul_comm]
  have hdvd_nat : d ∣ (j2 - j1) * b := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_mul]
    exact hdvd_int
  have h_dvd : d ∣ (j2 - j1) := (Nat.Coprime.symm hbd).dvd_of_dvd_mul_right hdvd_nat
  have h_pos : 0 < j2 - j1 := by omega
  exact Nat.le_of_dvd h_pos h_dvd

/-- Any d-separated subset of Finset.range k has cardinality at most k / d + 1. -/
lemma card_le_div_add_one_of_separated {k d : ℕ} (hd : 0 < d)
    (S : Finset ℕ) (hS : S ⊆ Finset.range k)
    (h_sep : ∀ j1 ∈ S, ∀ j2 ∈ S, j1 < j2 → d ≤ j2 - j1) :
    S.card ≤ k / d + 1 := by
  have h_inj : ∀ j1 ∈ S, ∀ j2 ∈ S, j1 / d = j2 / d → j1 = j2 := by
    intro j1 hj1 j2 hj2 heq
    rcases lt_trichotomy j1 j2 with hlt | heq' | hgt
    · have hle := h_sep j1 hj1 j2 hj2 hlt
      have : j1 / d + 1 = (j1 + d) / d := by rw [Nat.add_div_right _ hd]
      have : (j1 + d) / d ≤ j2 / d := Nat.div_le_div_right (by omega)
      omega
    · exact heq'
    · have hle := h_sep j2 hj2 j1 hj1 hgt
      have : j2 / d + 1 = (j2 + d) / d := by rw [Nat.add_div_right _ hd]
      have : (j2 + d) / d ≤ j1 / d := Nat.div_le_div_right (by omega)
      omega
  have h_sub : S.image (fun j => j / d) ⊆ Finset.range (k / d + 1) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    rcases hx with ⟨j, hj, rfl⟩
    have hj_lt : j < k := Finset.mem_range.mp (hS hj)
    have : j / d ≤ k / d := Nat.div_le_div_right (by omega)
    omega
  have h_card_eq : (S.image (fun j => j / d)).card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    exact h_inj x hx y hy hxy
  rw [← h_card_eq]
  have := Finset.card_le_card h_sub
  rw [Finset.card_range] at this
  exact this

/-- Number of index solutions j < P.k to d ∣ a + j * b is bounded by P.k / d + 1. -/
lemma card_filter_range_dvd_le (P : IntAP) (d : ℕ) (hd : 0 < d) (hbd : Nat.Coprime P.b d) :
    ((Finset.range P.k).filter (fun (j : ℕ) => (d : ℤ) ∣ (P.a + (j : ℤ) * (P.b : ℤ)))).card ≤ P.k / d + 1 := by
  let S := (Finset.range P.k).filter (fun (j : ℕ) => (d : ℤ) ∣ (P.a + (j : ℤ) * (P.b : ℤ)))
  have hS_sub : S ⊆ Finset.range P.k := Finset.filter_subset _ _
  have h_sep : ∀ j1 ∈ S, ∀ j2 ∈ S, j1 < j2 → d ≤ j2 - j1 := by
    intro j1 hj1 j2 hj2 hlt
    simp only [Finset.mem_filter, S] at hj1 hj2
    exact linear_dvd_sub_ge_d P.a P.b d hd hbd j1 j2 hlt hj1.2 hj2.2
  exact card_le_div_add_one_of_separated hd S hS_sub h_sep

/-- Number of elements of an integer AP divisible by d (coprime to b) is at most P.k / d + 1. -/
lemma card_filter_dvd_toFinset_le (P : IntAP) (d : ℕ) (hd : 0 < d) (hbd : Nat.Coprime P.b d) :
    (P.toFinset.filter (fun z => (d : ℤ) ∣ z)).card ≤ P.k / d + 1 := by
  dsimp [IntAP.toFinset]
  rw [Finset.filter_image]
  exact (Finset.card_image_le (f := fun (j : ℕ) => P.a + (j : ℤ) * (P.b : ℤ))).trans (card_filter_range_dvd_le P d hd hbd)

/-- Equivalence between natural divisibility of natAbs and integer divisibility. -/
lemma dvd_natAbs_iff (d : ℕ) (z : ℤ) : d ∣ z.natAbs ↔ (d : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]

/-- Natural divisibility bound on integer AP elements. -/
lemma card_filter_natAbs_dvd_toFinset_le (P : IntAP) (d : ℕ) (hd : 0 < d) (hbd : Nat.Coprime P.b d) :
    (P.toFinset.filter (fun z => d ∣ z.natAbs)).card ≤ P.k / d + 1 := by
  have h_eq : (P.toFinset.filter (fun z => d ∣ z.natAbs)) =
      (P.toFinset.filter (fun z => (d : ℤ) ∣ z)) := by
    ext z
    simp only [Finset.mem_filter, dvd_natAbs_iff]
  rw [h_eq]
  exact card_filter_dvd_toFinset_le P d hd hbd

/-- Real-valued upper bound on the number of elements in an integer AP divisible by d:
    #\{z \in P.toFinset | d ∣ |z|\} ≤ P.k / d + 1. -/
lemma card_filter_natAbs_dvd_toFinset_real_le (P : IntAP) (d : ℕ)
    (hd : 0 < d) (h_coprime : Nat.Coprime P.b d) :
    ((P.toFinset.filter (fun z => d ∣ z.natAbs)).card : ℝ) ≤ (P.k : ℝ) / (d : ℝ) + 1 := by
  have h_nat := card_filter_natAbs_dvd_toFinset_le P d hd h_coprime
  have h_cast : ((P.toFinset.filter (fun z => d ∣ z.natAbs)).card : ℝ) ≤ ((P.k / d + 1 : ℕ) : ℝ) := by
    exact_mod_cast h_nat
  have h_div_le : ((P.k / d : ℕ) : ℝ) ≤ (P.k : ℝ) / (d : ℝ) := Nat.cast_div_le
  have h_add : ((P.k / d + 1 : ℕ) : ℝ) = ((P.k / d : ℕ) : ℝ) + 1 := by push_cast; rfl
  rw [h_add] at h_cast
  linarith

/-- Lifting a coset of a cyclic subgroup H ≤ ZMod N of order h (with h ∣ N)
    to an integer arithmetic progression of length h with common difference N / h. -/
def cosetAPLift (N h : ℕ) (hN_pos : 0 < N) (hh_pos : 0 < h) (hhN : h ∣ N) (c : ℤ) : IntAP where
  a := c
  b := N / h
  hb := Nat.div_pos (Nat.le_of_dvd hN_pos hhN) hh_pos
  k := h

/-- Cardinality of the lifted coset arithmetic progression equals the subgroup order h. -/
lemma cosetAPLift_card (N h : ℕ) (hN_pos : 0 < N) (hh_pos : 0 < h) (hhN : h ∣ N) (c : ℤ) :
    (cosetAPLift N h hN_pos hh_pos hhN c).toFinset.card = h := by
  rw [IntAP.card_toFinset]
  rfl

/-- Exact length sum identity for a family of q lifted coset APs each of length h:
    sum of lengths = q * h. -/
lemma coset_family_length_sum_eq (q h : ℕ) (APs : Fin q → IntAP)
    (h_len : ∀ i, (APs i).k = h) :
    ∑ i, (APs i).k = q * h := by
  simp [h_len]

/-- CFP Lemma 5.10 Branch A length sum upper bound:
    For a disjoint coset family partitioning R (so q * h = |R|),
    the total length sum is at most 3 * |R|. -/
lemma coset_family_length_sum_le_three_mul (R_card : ℕ) (q h : ℕ)
    (h_prod : q * h = R_card) :
    q * h ≤ 3 * R_card := by
  omega

/-- Definition of rough elements in an integer arithmetic progression P with respect to sieve modulus Q. -/
def roughCount (P : IntAP) (Q : ℕ) : ℕ :=
  (P.toFinset.filter (fun a => Nat.Coprime a.natAbs Q)).card

/-- Exact equality between roughCount on the AP set and filtering indices in Finset.range P.k. -/
lemma roughCount_eq_card_filter_range (P : IntAP) (Q : ℕ) :
    roughCount P Q = ((Finset.range P.k).filter (fun (j : ℕ) =>
      Nat.Coprime (P.a + (j : ℤ) * (P.b : ℤ)).natAbs Q)).card := by
  dsimp [roughCount, IntAP.toFinset]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ (fun x y hxy => P.inj_of_hb x y hxy)]

/-- For sieve modulus Q = 1, all elements are coprime, so roughCount P 1 = P.k. -/
lemma roughCount_one (P : IntAP) : roughCount P 1 = P.k := by
  dsimp [roughCount]
  have h_filt : (P.toFinset.filter (fun a => Nat.Coprime a.natAbs 1)) = P.toFinset := by
    ext a
    simp
  rw [h_filt, P.card_toFinset]

/-- Monotonicity of roughCount with respect to sieve modulus divisibility:
    if Q1 ∣ Q2, then roughCount P Q2 ≤ roughCount P Q1. -/
lemma roughCount_mono (P : IntAP) {Q1 Q2 : ℕ} (h : Q1 ∣ Q2) :
    roughCount P Q2 ≤ roughCount P Q1 := by
  dsimp [roughCount]
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  exact Nat.Coprime.coprime_dvd_right h ha.2

/-- Universal upper bound: roughCount P Q is always bounded by the length P.k. -/
lemma roughCount_le_card (P : IntAP) (Q : ℕ) : roughCount P Q ≤ P.k := by
  have h1 : 1 ∣ Q := one_dvd Q
  have h_mono := roughCount_mono P h1
  rw [roughCount_one] at h_mono
  exact h_mono

/-- If every element of B is coprime to Q, and B is covered by a union of APs,
    then |B| is bounded by the sum of rough counts of the APs. -/
lemma card_le_sum_roughCount_of_subset_bUnion {ι : Type*} [DecidableEq ι]
    (B : Finset ℤ) (Q : ℕ) (hB_rough : ∀ a ∈ B, Nat.Coprime a.natAbs Q)
    (I : Finset ι) (APs : ι → IntAP)
    (h_cov : B ⊆ I.biUnion (fun i => (APs i).toFinset)) :
    B.card ≤ ∑ i ∈ I, roughCount (APs i) Q := by
  have h_sub : B ⊆ I.biUnion (fun i => (APs i).toFinset.filter (fun a => Nat.Coprime a.natAbs Q)) := by
    intro a ha
    have ha_cov := h_cov ha
    simp only [mem_biUnion] at ha_cov ⊢
    rcases ha_cov with ⟨i, hi, ha_AP⟩
    refine ⟨i, hi, ?_⟩
    simp only [mem_filter]
    exact ⟨ha_AP, hB_rough a ha⟩
  have h_card := card_le_card h_sub
  dsimp [roughCount]
  exact h_card.trans card_biUnion_le

/-- Summing the Selberg sieve rough count bound over an AP family covering B:
    If each AP satisfies the roughCount bound and total length ≤ 3 * |R| ≤ 384 * d,
    then |B| ≤ 384 * d * C_sieve. For C_sieve = 256 * log(log n) / log r,
    this yields 384 * 256 * d * log(log n) / log r = 98304 * d * log(log n) / log r. -/
lemma card_le_sieve_bound_of_ap_family {ι : Type*} [DecidableEq ι]
    (B : Finset ℤ) (Q : ℕ) (hB_rough : ∀ a ∈ B, Nat.Coprime a.natAbs Q)
    (I : Finset ι) (APs : ι → IntAP)
    (h_cov : B ⊆ I.biUnion (fun i => (APs i).toFinset))
    (d : ℕ) (_n _r : ℕ) (C_sieve : ℝ) (hC_nonneg : 0 ≤ C_sieve)
    (h_sieve : ∀ i ∈ I, (roughCount (APs i) Q : ℝ) ≤ ((APs i).k : ℝ) * C_sieve)
    (h_sum_len : (∑ i ∈ I, (APs i).k : ℝ) ≤ 384 * (d : ℝ)) :
    (B.card : ℝ) ≤ 384 * (d : ℝ) * C_sieve := by
  have h1 : (B.card : ℝ) ≤ (∑ i ∈ I, roughCount (APs i) Q : ℝ) := by
    exact_mod_cast card_le_sum_roughCount_of_subset_bUnion B Q hB_rough I APs h_cov
  have h2 : (∑ i ∈ I, roughCount (APs i) Q : ℝ) ≤ (∑ i ∈ I, ((APs i).k : ℝ)) * C_sieve := by
    rw [sum_mul]
    apply sum_le_sum
    intro i hi
    exact h_sieve i hi
  calc (B.card : ℝ) ≤ (∑ i ∈ I, roughCount (APs i) Q : ℝ) := h1
  _ ≤ (∑ i ∈ I, ((APs i).k : ℝ)) * C_sieve := h2
  _ ≤ 384 * (d : ℝ) * C_sieve := by
    exact mul_le_mul_of_nonneg_right h_sum_len hC_nonneg

/-- A family of integer arithmetic progressions covering B with length and step bounds
    matching CFP Lemma 5.10 / P17 specification. -/
structure IntAPCover (B : Finset ℤ) (R_card : ℕ) (t n : ℕ) where
  ι : Type
  [instDecEq : DecidableEq ι]
  I : Finset ι
  APs : ι → IntAP
  h_cov : B ⊆ I.biUnion (fun i => (APs i).toFinset)
  h_sum_len : ∑ i ∈ I, (APs i).k ≤ 3 * R_card
  h_min_len : ∀ i ∈ I, R_card ≤ (APs i).k ^ 3
  h_step_pos : ∀ i ∈ I, 0 < (APs i).b
  h_step_le_t : ∀ i ∈ I, (APs i).b ≤ t
  h_t_le_n : t ≤ n

attribute [instance] IntAPCover.instDecEq

/-- Scaled coset AP lift: Lifting a coset to an integer AP with common difference t / h. -/
def scaledCosetAPLift (t h : ℕ) (ht_pos : 0 < t) (hh_pos : 0 < h)
    (h_dvd : h ∣ t) (c : ℤ) : IntAP where
  a := c
  b := t / h
  hb := Nat.div_pos (Nat.le_of_dvd ht_pos h_dvd) hh_pos
  k := h

/-- Length of a scaled coset AP lift is h. -/
lemma scaledCosetAPLift_k (t h : ℕ) (ht_pos : 0 < t) (hh_pos : 0 < h)
    (h_dvd : h ∣ t) (c : ℤ) :
    (scaledCosetAPLift t h ht_pos hh_pos h_dvd c).k = h := rfl

/-- Common difference of a scaled coset AP lift is bounded by t. -/
lemma scaledCosetAPLift_b_le (t h : ℕ) (ht_pos : 0 < t) (hh_pos : 0 < h)
    (h_dvd : h ∣ t) (c : ℤ) :
    (scaledCosetAPLift t h ht_pos hh_pos h_dvd c).b ≤ t := by
  dsimp [scaledCosetAPLift]
  exact Nat.div_le_self t h

/-- Every element x in an additive subgroup H ≤ ZMod N has x.val divisible by N / |H|. -/
lemma zmod_subgroup_val_dvd (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N))
    (x : ZMod N) (hx : x ∈ H) :
    let h := (H : Set (ZMod N)).toFinset.card
    (N / h) ∣ x.val := by
  intro h
  have h_card : (H : Set (ZMod N)).toFinset.card = Fintype.card H := Set.toFinset_card (H : Set (ZMod N))
  have h_nsmul : Fintype.card H • (⟨x, hx⟩ : H) = 0 := @card_nsmul_eq_zero H _ _ ⟨x, hx⟩
  have h_zero : h • x = 0 := by
    have h_val := congr_arg (fun (y : H) => (y : ZMod N)) h_nsmul
    change Fintype.card H • x = 0 at h_val
    dsimp [h]
    rw [h_card]
    exact h_val
  have h_cast : ((h * x.val : ℕ) : ZMod N) = 0 := by
    calc ((h * x.val : ℕ) : ZMod N) = (h : ZMod N) * (x.val : ZMod N) := by push_cast; rfl
    _ = (h : ZMod N) * x := by rw [ZMod.natCast_zmod_val]
    _ = h • x := by rw [nsmul_eq_mul]
    _ = 0 := h_zero
  have hdvd : N ∣ h * x.val := (CharP.cast_eq_zero_iff (ZMod N) N (h * x.val)).mp h_cast
  have hh_dvd : h ∣ N := by
    have h_lag := AddSubgroup.card_addSubgroup_dvd_card H
    rw [Nat.card_zmod N, Nat.card_eq_fintype_card, ← h_card] at h_lag
    exact h_lag
  have h0 : (0 : ZMod N) ∈ (H : Set (ZMod N)).toFinset := by
    rw [Set.mem_toFinset]
    exact H.zero_mem
  have hh_pos : 0 < h := Finset.card_pos.mpr ⟨0, h0⟩
  have h_dvd_mul : h * (N / h) ∣ h * x.val := by
    have h_eq : h * (N / h) = N := Nat.mul_div_cancel' hh_dvd
    rwa [h_eq]
  exact (Nat.mul_dvd_mul_iff_left hh_pos).mp h_dvd_mul

/-- Scaled subgroup elements have coordinates divisible by t / |H|. -/
lemma zmod_subgroup_scaled_val_dvd (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N))
    (t g : ℕ) (h_gN : g * N = t)
    (x : ZMod N) (hx : x ∈ H) :
    let h := (H : Set (ZMod N)).toFinset.card
    (t / h) ∣ g * x.val := by
  intro h
  have hdvd := zmod_subgroup_val_dvd N H x hx
  rcases hdvd with ⟨k, hk⟩
  have hh_dvd : h ∣ N := by
    have h_card : (H : Set (ZMod N)).toFinset.card = Fintype.card H := Set.toFinset_card (H : Set (ZMod N))
    have h_lag := AddSubgroup.card_addSubgroup_dvd_card H
    rw [Nat.card_zmod N, Nat.card_eq_fintype_card, ← h_card] at h_lag
    exact h_lag
  use k
  rw [hk]
  have h_mul : g * (N / h * k) = (g * (N / h)) * k := by ring
  rw [h_mul]
  have h_assoc : g * (N / h) = (g * N) / h := (Nat.mul_div_assoc g hh_dvd).symm
  rw [h_assoc, h_gN]

/-- Constructing an IntAPCover from a general finite indexed family of integer APs
    covering B with length sum ≤ 3 * R_card and minimum length R_card ≤ k^3. -/
def intAPCover_of_family
    (B : Finset ℤ) (R_card t n : ℕ) (htn : t ≤ n)
    {ι : Type} [DecidableEq ι] (I : Finset ι) (APs : ι → IntAP)
    (h_cov : B ⊆ I.biUnion (fun i => (APs i).toFinset))
    (h_sum_len : ∑ i ∈ I, (APs i).k ≤ 3 * R_card)
    (h_min_len : ∀ i ∈ I, R_card ≤ (APs i).k ^ 3)
    (h_step_pos : ∀ i ∈ I, 0 < (APs i).b)
    (h_step_le_t : ∀ i ∈ I, (APs i).b ≤ t) :
    IntAPCover B R_card t n where
  ι := ι
  I := I
  APs := APs
  h_cov := h_cov
  h_sum_len := h_sum_len
  h_min_len := h_min_len
  h_step_pos := h_step_pos
  h_step_le_t := h_step_le_t
  h_t_le_n := htn

/-- An IntAPCover consisting of a single arithmetic progression covering B. -/
def intAPCover_of_single
    (B : Finset ℤ) (R_card t n : ℕ) (htn : t ≤ n)
    (P : IntAP)
    (h_cov : B ⊆ P.toFinset)
    (h_k_le : P.k ≤ 3 * R_card)
    (h_k_ge : R_card ≤ P.k ^ 3)
    (h_step_le : P.b ≤ t) :
    IntAPCover B R_card t n where
  ι := Unit
  I := {()}
  APs := fun _ => P
  h_cov := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨(), by simp, h_cov hx⟩
  h_sum_len := by
    simp only [Finset.sum_singleton]
    exact h_k_le
  h_min_len := by
    intro i _hi
    exact h_k_ge
  h_step_pos := by
    intro i _hi
    exact P.hb
  h_step_le_t := by
    intro i _hi
    exact h_step_le
  h_t_le_n := htn

/-- An IntAPCover consisting of a family of q arithmetic progressions each of length h. -/
def intAPCover_of_coset_family
    (B : Finset ℤ) (R_card t n : ℕ) (htn : t ≤ n)
    (q h : ℕ) (APs : Fin q → IntAP)
    (h_cov : B ⊆ (Finset.univ : Finset (Fin q)).biUnion (fun i => (APs i).toFinset))
    (h_len : ∀ i, (APs i).k = h)
    (h_sum_le : q * h ≤ 3 * R_card)
    (h_min_len : R_card ≤ h ^ 3)
    (h_step_le : ∀ i, (APs i).b ≤ t) :
    IntAPCover B R_card t n where
  ι := Fin q
  I := Finset.univ
  APs := APs
  h_cov := h_cov
  h_sum_len := by
    have h_sum := coset_family_length_sum_eq q h APs h_len
    rw [h_sum]
    exact h_sum_le
  h_min_len := by
    intro i _hi
    rw [h_len i]
    exact h_min_len
  h_step_pos := by
    intro i _hi
    exact (APs i).hb
  h_step_le_t := by
    intro i _hi
    exact h_step_le i
  h_t_le_n := htn

/-!
### 16. Finite Numerical Parameter Package (Conlon–Fox–Pham 2021, Lemma 5.6 Finite Conditions / Phase P12)

Explicit parameter interface separating finite combinatorial conditions from real analytic asymptotic bounds.
-/

/-- Finite combinatorial parameter package for Conlon–Fox–Pham Lemma 5.6.
    Explicitly separates discrete combinatorial hypotheses and bounds from
    the real-analytic parameter instantiation (completed in Phase P19). -/
structure FiniteConditions where
  -- Core discrete parameters
  t : ℕ                  -- Modulus of subset sums
  ht_pos : 0 < t
  A : Finset ℕ           -- Candidate set of positive integers
  hA_pos : ∀ a ∈ A, 0 < a
  v : ℕ                  -- Common divisor scaling factor
  hv_pos : 0 < v
  K : ℕ                  -- Greedy iteration step count
  M : ℕ                  -- Minimum remaining candidates threshold
  hM_pos : 0 < M
  k_div : ℕ              -- Diversity parameter of A
  U : ℕ                  -- Small-fiber growth threshold
  hU_pos : 0 < U
  D : ℕ                  -- Single-step translation growth increment threshold
  hD_pos : 0 < D
  gMax : ℕ               -- Uniform upper bound on subgroup indices during iteration
  hgMax_pos : 0 < gMax

  -- Paper layer parameters
  xi : ℝ                 -- Linear density lower bound constant (e.g. 1/128 or ξ_DF)
  hxi_pos : 0 < xi
  ell : ℕ                -- Chromatic reduction parameter
  hell_pos : 0 < ell

  -- Growth step budget for Claim 1
  B_growth : ℕ           -- Maximum number of growth steps
  hB_le_K : B_growth ≤ K

  -- Explicit Numerical and Combinatorial Hypotheses:
  hK_add_M_le : K + M ≤ A.card
  hA_diverse : IsDiverse A k_div
  h_subgroup_le : ∀ B ⊆ A, M ≤ B.card → subgroupIndex t B ≤ gMax
  h_subgroup_diverse : ∀ B ⊆ A, M ≤ B.card → subgroupIndex t B - 1 ≤ k_div
  h_small_fiber_bound : U < t / (2 * gMax)
  h_growth_threshold : 8 * D < U
  h_growth_budget : (32 : ℝ) / (ell : ℝ) * (t : ℝ) ≤ (D * (K - B_growth) : ℝ)

/-!
### 17. Greedy Iteration State Machine & Stage Classification (Conlon–Fox–Pham 2021, Lemma 5.6 Iteration / Phase P13)

Discrete state, stage classification (growth, unsaturated, saturated), and invariant preservation.
-/

/-- A state in the greedy element selection process for CFP Lemma 5.6. -/
structure GreedyState (A : Finset ℕ) where
  E : Finset ℕ
  hE_sub : E ⊆ A

/-- Remaining unselected candidates at state st. -/
def GreedyState.B {A : Finset ℕ} (st : GreedyState A) : Finset ℕ :=
  A \ st.E

/-- Modulo t subset sums generated by the selected elements st.E. -/
def GreedyState.S {A : Finset ℕ} (t : ℕ) (st : GreedyState A) : Finset (ZMod t) :=
  subsetSumsMod t st.E

/-- Subgroup index generated by the remaining candidates st.B modulo t. -/
def GreedyState.g {A : Finset ℕ} (t : ℕ) (st : GreedyState A) : ℕ :=
  subgroupIndex t st.B

/-- Number of remaining candidates is |A| - |E|. -/
lemma GreedyState.card_B {A : Finset ℕ} (st : GreedyState A) :
    st.B.card = A.card - st.E.card :=
  card_sdiff_eq_sub st.hE_sub

/-- When |E| ≤ K, at least M candidates remain unselected. -/
lemma GreedyState.B_card_ge {fc : FiniteConditions} (st : GreedyState fc.A)
    (hj : st.E.card ≤ fc.K) : fc.M ≤ st.B.card := by
  have h_card := st.card_B
  have hKM := fc.hK_add_M_le
  omega

/-- Remaining candidate set is non-empty at any step j ≤ K. -/
lemma GreedyState.B_nonempty {fc : FiniteConditions} (st : GreedyState fc.A)
    (hj : st.E.card ≤ fc.K) : st.B.Nonempty := by
  have hM := st.B_card_ge hj
  have hM_pos := fc.hM_pos
  exact Finset.card_pos.mp (by omega)

/-- Growth stage: there exists a non-empty residue fiber with cardinality ≤ U. -/
def isGrowthStage {A : Finset ℕ} (t U : ℕ) (st : GreedyState A) : Prop :=
  let hd := subgroupIndex_dvd_modulus t st.B
  ∃ r ∈ (st.S t).image (zmodProj hd), (fiber hd (st.S t) r).card ≤ U

/-- Saturated stage: every non-empty residue fiber has
    cardinality ≥ xi * t / g. -/
def isSaturatedStage {A : Finset ℕ} (t : ℕ) (xi : ℝ) (st : GreedyState A) : Prop :=
  let hd := subgroupIndex_dvd_modulus t st.B
  let g := st.g t
  ∀ r ∈ (st.S t).image (zmodProj hd), xi * (t : ℝ) / (g : ℝ) ≤ ((fiber hd (st.S t) r).card : ℝ)

/-- Unsaturated stage: neither growth stage nor saturated stage. -/
def isUnsaturatedStage {A : Finset ℕ} (t U : ℕ) (xi : ℝ) (st : GreedyState A) : Prop :=
  ¬ isGrowthStage t U st ∧ ¬ isSaturatedStage t xi st

/-- Greedy step: existence of a candidate in B maximizing the translation growth of S. -/
lemma exists_greedy_element {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB_nonempty : st.B.Nonempty) :
    ∃ a ∈ st.B, ∀ x ∈ st.B, delta (st.S t) (x : ZMod t) ≤ delta (st.S t) (a : ZMod t) :=
  Finset.exists_max_image st.B (fun x => delta (st.S t) (x : ZMod t)) hB_nonempty

/-- Transition to next state by inserting chosen candidate  ∈ st.B. -/
def nextState {A : Finset ℕ} (st : GreedyState A) (a : ℕ) (ha : a ∈ st.B) : GreedyState A where
  E := insert a st.E
  hE_sub := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (Finset.mem_sdiff.mp ha).1
    · exact st.hE_sub hx

/-- Candidate addition strictly increments the chosen set cardinality by 1. -/
lemma nextState_card {A : Finset ℕ} (st : GreedyState A) (a : ℕ) (ha : a ∈ st.B) :
    (nextState st a ha).E.card = st.E.card + 1 := by
  dsimp [nextState]
  rw [Finset.card_insert_of_notMem]
  intro h_in
  exact (Finset.mem_sdiff.mp ha).2 h_in

/-- Subset sums are monotone under state transitions: S_j ⊆ S_{j+1}. -/
lemma nextState_S_mono {A : Finset ℕ} (t : ℕ) (st : GreedyState A) (a : ℕ) (ha : a ∈ st.B) :
    st.S t ⊆ (nextState st a ha).S t := by
  apply subsetSumsMod_mono
  intro x hx
  simp [nextState, hx]

/-- Subgroup index divisibility invariant: g(B) ∣ g(B') under candidate removal. -/
lemma nextState_g_dvd {A : Finset ℕ} (t : ℕ) (st : GreedyState A) (a : ℕ) (ha : a ∈ st.B) :
    st.g t ∣ (nextState st a ha).g t := by
  apply subgroupIndex_mono
  dsimp [nextState, GreedyState.B]
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_insert] at hx
  exact Finset.mem_sdiff.mpr ⟨hx.1, fun hxE => hx.2 (Or.inr hxE)⟩

/-!
### 18. Saturated Branch Elimination and Linear Density Lower Bound (Conlon–Fox–Pham 2021, Lemma 5.6 Saturated Branch / Phase P14)

Closed proof that if a saturated stage occurs, the final modular subset sums achieve the target linear density.
-/

/-- When remaining candidates B are all divisible by d, the subset sums modulo d
    of E equal the subset sums of E ∪ B. -/
lemma subsetSumsMod_eq_of_compl_dvd {d : ℕ} (A E B : Finset ℕ)
    (h_union : A = E ∪ B) (hB : ∀ b ∈ B, d ∣ b) :
    subsetSumsMod d E = subsetSumsMod d A := by
  have h_filter : A.filter (fun a => ¬ d ∣ a) = E.filter (fun a => ¬ d ∣ a) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hndvd⟩
      rw [h_union, Finset.mem_union] at hx
      rcases hx with hxE | hxB
      · exact ⟨hxE, hndvd⟩
      · exact (hndvd (hB x hxB)).elim
    · rintro ⟨hxE, hndvd⟩
      rw [h_union, Finset.mem_union]
      exact ⟨Or.inl hxE, hndvd⟩
  rw [← subsetSumsMod_filter_not_dvd d E, ← h_filter, subsetSumsMod_filter_not_dvd d A]

/-- Fiber sum lower bound: if π(S) = univ (all residue fibers non-empty) and every fiber
    satisfies |F_r| ≥ bound, then |S| ≥ g * bound. -/
lemma card_ge_of_fibers_ge {t g : ℕ} (h : g ∣ t) [NeZero g] (S : Finset (ZMod t)) (bound : ℝ)
    (h_univ : S.image (zmodProj h) = Finset.univ)
    (h_fiber_bound : ∀ r : ZMod g, bound ≤ ((fiber h S r).card : ℝ)) :
    (g : ℝ) * bound ≤ (S.card : ℝ) := by
  rw [card_eq_sum_image_fibers h S, h_univ]
  have h_sum_le : (Finset.univ : Finset (ZMod g)).sum (fun _ => bound) ≤
                  (Finset.univ : Finset (ZMod g)).sum (fun r => ((fiber h S r).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro r _
    exact h_fiber_bound r
  rw [Finset.sum_const, nsmul_eq_mul] at h_sum_le
  have h_card_univ : (Finset.univ : Finset (ZMod g)).card = g := ZMod.card g
  rw [h_card_univ] at h_sum_le
  have h_cast : (((Finset.univ : Finset (ZMod g)).sum (fun r => (fiber h S r).card) : ℕ) : ℝ) =
                (Finset.univ : Finset (ZMod g)).sum (fun r => ((fiber h S r).card : ℝ)) := by
    push_cast; rfl
  rw [← h_cast] at h_sum_le
  exact h_sum_le

/-- Product cancellation helper: g * (xi * t / g) = xi * t for positive g. -/
lemma mul_div_cancel_of_pos (g : ℕ) (hg : 0 < g) (xi t : ℝ) :
    (g : ℝ) * (xi * t / (g : ℝ)) = xi * t := by
  have : (g : ℝ) ≠ 0 := by norm_cast; omega
  exact mul_div_cancel₀ (xi * t) this

/-- CFP Lemma 5.6 Saturated Branch Closure (Phase P14):
    If at any step j ≤ K of the greedy iteration, the state st is saturated,
    then the final subset sums satisfy the target linear density lower bound:
      ξ * t ≤ |Σ_t(A)|. -/
theorem card_subsetSumsMod_ge_of_saturated (fc : FiniteConditions)
    (st : GreedyState fc.A) (hj : st.E.card ≤ fc.K)
    (h_sat : isSaturatedStage fc.t fc.xi st) :
    fc.xi * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  have hB_ge := st.B_card_ge hj
  have hB_sub : st.B ⊆ fc.A := Finset.sdiff_subset
  have hg_div := fc.h_subgroup_diverse st.B hB_sub hB_ge
  have hg_pos := subgroupIndex_pos fc.t st.B fc.ht_pos
  let g := st.g fc.t
  have hg_pos' : 0 < g := hg_pos
  have : NeZero g := ⟨by omega⟩
  have hd : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t st.B
  have h_union : fc.A = st.E ∪ st.B := (Finset.union_sdiff_of_subset st.hE_sub).symm
  have h_dvd : ∀ b ∈ st.B, g ∣ b := fun b hb => subgroupIndex_dvd_mem fc.t st.B hb
  have h_eq_compl : subsetSumsMod g st.E = subsetSumsMod g fc.A :=
    subsetSumsMod_eq_of_compl_dvd fc.A st.E st.B h_union h_dvd
  have h_univ_g : subsetSumsMod g st.E = Finset.univ := by
    ext r
    simp only [Finset.mem_univ, iff_true]
    by_cases hg2 : 2 ≤ g
    · rw [h_eq_compl]
      exact subsetSumsMod_eq_univ_of_isDiverse g fc.k_div (by omega) hg_div fc.A fc.hA_diverse r
    · have hg1 : g = 1 := by omega
      have : Subsingleton (ZMod g) := by rw [hg1]; infer_instance
      have hr0 : r = 0 := Subsingleton.elim r 0
      rw [hr0]
      exact zero_mem_subsetSumsMod g st.E
  have h_proj_univ : (st.S fc.t).image (zmodProj hd) = Finset.univ := by
    dsimp [GreedyState.S]
    rw [subsetSumsMod_image_zmodProj fc.t g hd st.E, h_univ_g]
  have h_fiber_all : ∀ r : ZMod g,
      fc.xi * (fc.t : ℝ) / (g : ℝ) ≤ ((fiber hd (st.S fc.t) r).card : ℝ) := by
    intro r
    have hr_in : r ∈ (st.S fc.t).image (zmodProj hd) := by
      rw [h_proj_univ]
      exact Finset.mem_univ r
    exact h_sat r hr_in
  have h_sum_bnd := card_ge_of_fibers_ge hd (st.S fc.t) (fc.xi * (fc.t : ℝ) / (g : ℝ))
                    h_proj_univ h_fiber_all
  rw [mul_div_cancel_of_pos g hg_pos'] at h_sum_bnd
  have h_sub_card : (st.S fc.t).card ≤ (subsetSumsMod fc.t fc.A).card := by
    dsimp [GreedyState.S]
    exact Finset.card_le_card (subsetSumsMod_mono st.hE_sub)
  have h_cast : ((st.S fc.t).card : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
    exact_mod_cast h_sub_card
  linarith


/-!
### 19. Single-Step Growth Bounds for Growth Stage (Conlon–Fox–Pham 2021, Lemma 5.6 Claim 1 / Phase P15)

Two range bounds for the growth stage:
- Range 1: 2 * |S| < |T| ==> exists element with growth > |S| / 2.
- Range 2: |T| / 2 <= |S| <= U ==> arithmetic contradiction on small growth.
-/

/-- Double counting bound on small growth elements with threshold D = S.card / 2:
    |G_{s/2}| <= 2s. -/
lemma card_smallGrowth_half_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (hS : 0 < S.card) :
    (smallGrowth S (S.card / 2)).card ≤ 2 * S.card := by
  have h_mul := card_smallGrowth_mul_le S (S.card / 2)
  have h_diff : 0 < S.card - S.card / 2 := by omega
  have h_bound : S.card ^ 2 ≤ 2 * S.card * (S.card - S.card / 2) := by
    generalize hq : S.card / 2 = q
    generalize hr : S.card % 2 = r
    have h_eq : S.card = 2 * q + r := by
      have := (Nat.div_add_mod S.card 2).symm
      omega
    have h_sub : 2 * q + r - q = q + r := by omega
    have h_alg : (2 * q + r) ^ 2 ≤ 2 * (2 * q + r) * (q + r) := by nlinarith
    rw [h_eq, h_sub]
    exact h_alg
  have : (smallGrowth S (S.card / 2)).card * (S.card - S.card / 2) ≤ 2 * S.card * (S.card - S.card / 2) :=
    h_mul.trans h_bound
  exact Nat.le_of_mul_le_mul_right this h_diff

/-- Range 1 of CFP Claim 1 (Phase P15):
    If 2 * |S| < |T|, then there exists an element in T with translation growth > |S| / 2. -/
lemma exists_large_growth_of_two_mul_lt {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S T : Finset G) (hS : 0 < S.card) (hT : 2 * S.card < T.card) :
    ∃ x ∈ T, S.card / 2 < delta S x := by
  have h_small := card_smallGrowth_half_le S hS
  have h_lt : (smallGrowth S (S.card / 2)).card < T.card := by omega
  exact exists_mem_large_growth S T (S.card / 2) h_lt

/-- Floor property for Range 2 contradiction: 4s < (floor(4s/b) + 1) * b. -/
lemma floor_mul_succ_gt (s b : ℕ) (hb : 0 < b) :
    4 * s < (4 * s / b + 1) * b := by
  have h_div : 4 * s = b * (4 * s / b) + (4 * s) % b := (Nat.div_add_mod (4 * s) b).symm
  have h_mod : (4 * s) % b < b := Nat.mod_lt (4 * s) hb
  rw [add_mul, one_mul, mul_comm (4 * s / b) b]
  omega

/-- Range 2 contradiction inequality:
    If (q + 1) * b ≤ 4s and 4s < (q + 1) * b, then False. -/
lemma range2_arith_contradiction (s b q : ℕ) (hb : 0 < b) (hq : q = 4 * s / b)
    (h_le : (q + 1) * b ≤ 4 * s) : False := by
  have h_gt := floor_mul_succ_gt s b hb
  rw [← hq] at h_gt
  omega

/-!
### 20. Combinatorial Core F1 of CFP Lemma 5.6 (Phases P16, P17, P18)
-/

/-- Initial empty greedy state. -/
def initialGreedyState (A : Finset ℕ) : GreedyState A where
  E := ∅
  hE_sub := Finset.empty_subset A

/-- Modulo t subset sums of elements in E divisible by g (Conlon–Fox–Pham 2021, §5.1 T_g(E)). -/
def selectedMultiplesSums (t g : ℕ) (E : Finset ℕ) : Finset (ZMod t) :=
  subsetSumsMod t (E.filter (fun a => g ∣ a))

lemma zero_mem_selectedMultiplesSums (t g : ℕ) (E : Finset ℕ) :
    (0 : ZMod t) ∈ selectedMultiplesSums t g E :=
  zero_mem_subsetSumsMod t _

lemma card_selectedMultiplesSums_pos (t g : ℕ) (E : Finset ℕ) :
    0 < (selectedMultiplesSums t g E).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_selectedMultiplesSums t g E⟩

lemma one_le_card_selectedMultiplesSums (t g : ℕ) (E : Finset ℕ) :
    1 ≤ (selectedMultiplesSums t g E).card :=
  card_selectedMultiplesSums_pos t g E

lemma selectedMultiplesSums_mono (t g : ℕ) {E E' : Finset ℕ} (hEE' : E ⊆ E') :
    selectedMultiplesSums t g E ⊆ selectedMultiplesSums t g E' :=
  subsetSumsMod_mono (Finset.filter_subset_filter _ hEE')

lemma card_selectedMultiplesSums_le_of_subset (t g : ℕ) {E E' : Finset ℕ} (hEE' : E ⊆ E') :
    (selectedMultiplesSums t g E).card ≤ (selectedMultiplesSums t g E').card :=
  Finset.card_le_card (selectedMultiplesSums_mono t g hEE')

lemma card_selectedMultiplesSums_insert_eq (t g : ℕ) (E : Finset ℕ) (a : ℕ)
    (ha_not : a ∉ E) (ha_dvd : g ∣ a) :
    (selectedMultiplesSums t g (insert a E)).card =
      (selectedMultiplesSums t g E).card + delta (selectedMultiplesSums t g E) (a : ZMod t) := by
  dsimp [selectedMultiplesSums]
  have h_filter : (insert a E).filter (fun x => g ∣ x) = insert a (E.filter (fun x => g ∣ x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hg⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, hg⟩
    · rintro (rfl | ⟨hx, hg⟩)
      · exact ⟨Or.inl rfl, ha_dvd⟩
      · exact ⟨Or.inr hx, hg⟩
  rw [h_filter]
  have ha_not_filter : a ∉ E.filter (fun x => g ∣ x) := by
    intro h
    exact ha_not (Finset.mem_filter.mp h).1
  exact card_subsetSumsMod_insert_eq t (E.filter (fun x => g ∣ x)) a ha_not_filter

lemma card_selectedMultiplesSums_le_U {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (ht_pos : 0 < t) (h_grow : isGrowthStage t U st) :
    (selectedMultiplesSums t (st.g t) st.E).card ≤ U := by
  rcases h_grow with ⟨r, hr_img, hr_card⟩
  have hd : st.g t ∣ t := subgroupIndex_dvd_modulus t st.B
  have hg_pos : 0 < st.g t := subgroupIndex_pos t st.B ht_pos
  simp only [Finset.mem_image] at hr_img
  rcases hr_img with ⟨s, hs_in, rfl⟩
  have hs_mem : s ∈ residueFiber t (st.g t) hd st.E (zmodProj hd s) :=
    Finset.mem_filter.mpr ⟨hs_in, rfl⟩
  have h_nonempty : (residueFiber t (st.g t) hd st.E (zmodProj hd s)).Nonempty := ⟨s, hs_mem⟩
  have h_le_fiber := card_subsetSumsMod_dvd_le_fiber t (st.g t) hg_pos ht_pos hd st.E (zmodProj hd s) h_nonempty
  change (residueFiber t (st.g t) hd st.E (zmodProj hd s)).card ≤ U at hr_card
  exact h_le_fiber.trans hr_card

/-- Residue of the chosen small fiber during a growth stage (auxiliary tool). -/
noncomputable def growthResidue {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (h_grow : isGrowthStage t U st) : ZMod (st.g t) :=
  h_grow.choose

/-- The chosen small fiber during a growth stage (auxiliary tool). -/
noncomputable def growthFiber {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (h_grow : isGrowthStage t U st) : Finset (ZMod t) :=
  fiber (subgroupIndex_dvd_modulus t st.B) (st.S t) (growthResidue t U st h_grow)

/-- The chosen small fiber has cardinality bounded by U. -/
lemma card_growthFiber_le {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (h_grow : isGrowthStage t U st) :
    (growthFiber t U st h_grow).card ≤ U :=
  h_grow.choose_spec.2

/-- Existence of a candidate in B maximizing the translation growth of selected multiples sums. -/
lemma exists_growth_element {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB_nonempty : st.B.Nonempty) :
    ∃ a ∈ st.B, ∀ x ∈ st.B,
      delta (selectedMultiplesSums t (st.g t) st.E) (x : ZMod t) ≤
      delta (selectedMultiplesSums t (st.g t) st.E) (a : ZMod t) :=
  Finset.exists_max_image st.B (fun x => delta (selectedMultiplesSums t (st.g t) st.E) (x : ZMod t)) hB_nonempty

/-- Deterministic candidate selection in growth stage maximizing selected multiples sums delta. -/
noncomputable def growthChoice {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) : ℕ :=
  (exists_growth_element t st hB).choose

lemma growthChoice_mem {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) :
    growthChoice t st hB ∈ st.B :=
  (exists_growth_element t st hB).choose_spec.1

lemma growthChoice_max {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) (x : ℕ) (hx : x ∈ st.B) :
    delta (selectedMultiplesSums t (st.g t) st.E) (x : ZMod t) ≤
    delta (selectedMultiplesSums t (st.g t) st.E) (growthChoice t st hB : ZMod t) :=
  (exists_growth_element t st hB).choose_spec.2 x hx

/-- Deterministic ordinary candidate selection maximizing total modular delta. -/
noncomputable def ordinaryChoice {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) : ℕ :=
  (exists_greedy_element t st hB).choose

lemma ordinaryChoice_mem {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) :
    ordinaryChoice t st hB ∈ st.B :=
  (exists_greedy_element t st hB).choose_spec.1

lemma ordinaryChoice_max {A : Finset ℕ} (t : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) (x : ℕ) (hx : x ∈ st.B) :
    delta (st.S t) (x : ZMod t) ≤ delta (st.S t) (ordinaryChoice t st hB : ZMod t) :=
  (exists_greedy_element t st hB).choose_spec.2 x hx

/-- Unified Stage-Aware Greedy Candidate Selection (Conlon–Fox–Pham 2021, §5.1):
    - Growth stage: maximize delta of selected multiples sums δ(selectedMultiplesSums, a).
    - Ordinary stage: maximize total modular delta δ(S, a) for Claim 2. -/
noncomputable def greedyChoice {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) : ℕ :=
  if isGrowthStage t U st then
    growthChoice t st hB
  else
    ordinaryChoice t st hB

lemma greedyChoice_mem {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) :
    greedyChoice t U st hB ∈ st.B := by
  dsimp [greedyChoice]
  split_ifs
  · exact growthChoice_mem t st hB
  · exact ordinaryChoice_mem t st hB

lemma greedyChoice_growth_max {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) (h_grow : isGrowthStage t U st) (x : ℕ) (hx : x ∈ st.B) :
    delta (selectedMultiplesSums t (st.g t) st.E) (x : ZMod t) ≤
    delta (selectedMultiplesSums t (st.g t) st.E) (greedyChoice t U st hB : ZMod t) := by
  dsimp [greedyChoice]
  rw [if_pos h_grow]
  exact growthChoice_max t st hB x hx

lemma greedyChoice_ordinary_max {A : Finset ℕ} (t U : ℕ) (st : GreedyState A)
    (hB : st.B.Nonempty) (h_not_grow : ¬ isGrowthStage t U st) (x : ℕ) (hx : x ∈ st.B) :
    delta (st.S t) (x : ZMod t) ≤ delta (st.S t) (greedyChoice t U st hB : ZMod t) := by
  dsimp [greedyChoice]
  rw [if_neg h_not_grow]
  exact ordinaryChoice_max t st hB x hx

/-- Recursive trajectory of greedy states with stage-aware candidate selection.
    If remaining candidates are non-empty and j < K, pick the stage-aware greedy element. -/
noncomputable def greedySeq (fc : FiniteConditions) : ℕ → GreedyState fc.A
  | 0 => initialGreedyState fc.A
  | j + 1 =>
    if j < fc.K then
      let st := greedySeq fc j
      if hB : st.B.Nonempty then
        nextState st (greedyChoice fc.t fc.U st hB) (greedyChoice_mem fc.t fc.U st hB)
      else st
    else greedySeq fc j

/-- Base case: initial chosen set is empty, card is 0. -/
@[simp]
lemma greedySeq_zero_E (fc : FiniteConditions) :
    (greedySeq fc 0).E = ∅ := rfl

@[simp]
lemma card_greedySeq_zero_E (fc : FiniteConditions) :
    (greedySeq fc 0).E.card = 0 := by simp [greedySeq_zero_E]

/-- Cardinality of chosen set E at step j <= K is exactly j. -/
lemma card_greedySeq_E (fc : FiniteConditions) (j : ℕ) (hj : j ≤ fc.K) :
    (greedySeq fc j).E.card = j := by
  induction j with
  | zero => exact card_greedySeq_zero_E fc
  | succ j ih =>
    have hj_lt : j < fc.K := by omega
    have ih_j : (greedySeq fc j).E.card = j := ih (by omega)
    have h_nonempty : (greedySeq fc j).B.Nonempty :=
      (greedySeq fc j).B_nonempty (by omega)
    dsimp [greedySeq]
    rw [if_pos hj_lt, dif_pos h_nonempty]
    rw [nextState_card]
    rw [ih_j]

/-- Subset sum inclusion: subset sums at step j are contained in total subset sums. -/
lemma greedySeq_S_subset (fc : FiniteConditions) (j : ℕ) :
    (greedySeq fc j).S fc.t ⊆ subsetSumsMod fc.t fc.A :=
  subsetSumsMod_mono (greedySeq fc j).hE_sub

/-- Helper for the delta increment at step j. -/
noncomputable def greedyDelta (fc : FiniteConditions) (j : ℕ) : ℕ :=
  if hj : j < fc.K then
    let st := greedySeq fc j
    have hB : st.B.Nonempty := st.B_nonempty (by rw [card_greedySeq_E fc j (by omega)]; omega)
    delta (st.S fc.t) (greedyChoice fc.t fc.U st hB : ZMod fc.t)
  else 0

/-- Step increment formula for subset sums cardinality. -/
lemma card_greedySeq_S_succ (fc : FiniteConditions) (j : ℕ) (hj : j < fc.K) :
    ((greedySeq fc (j + 1)).S fc.t).card =
      ((greedySeq fc j).S fc.t).card + greedyDelta fc j := by
  let st := greedySeq fc j
  have hB : st.B.Nonempty := st.B_nonempty (by rw [card_greedySeq_E fc j (by omega)]; omega)
  have hj_card : st.E.card ≤ fc.K := by rw [card_greedySeq_E fc j (by omega)]; omega
  have h_notMem : greedyChoice fc.t fc.U st hB ∉ st.E :=
    (Finset.mem_sdiff.mp (greedyChoice_mem fc.t fc.U st hB)).2
  dsimp [greedySeq]
  rw [if_pos hj, dif_pos hB]
  dsimp [GreedyState.S, nextState, greedyDelta]
  rw [dif_pos hj]
  rw [card_subsetSumsMod_insert_eq fc.t st.E (greedyChoice fc.t fc.U st hB) h_notMem]

/-- Telescoping sum lower bound: sum of delta increments is bounded by the final subset sums size. -/
lemma sum_delta_le_card_final (fc : FiniteConditions) :
    ∑ j ∈ Finset.range fc.K, greedyDelta fc j ≤ ((greedySeq fc fc.K).S fc.t).card := by
  have h_tel : ∀ k ≤ fc.K, ∑ j ∈ Finset.range k, greedyDelta fc j ≤ ((greedySeq fc k).S fc.t).card := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      have hk_lt : k < fc.K := by omega
      have ih_k := ih (by omega)
      have h_succ := card_greedySeq_S_succ fc k hk_lt
      omega
  exact h_tel fc.K (le_refl _)

/-- Master telescoping bound: sum of delta increments is bounded by the total subset sums card. -/
lemma sum_delta_le_total (fc : FiniteConditions) :
    ∑ j ∈ Finset.range fc.K, greedyDelta fc j ≤ (subsetSumsMod fc.t fc.A).card := by
  have h_final := sum_delta_le_card_final fc
  have h_sub := greedySeq_S_subset fc fc.K
  have h_card_le := Finset.card_le_card h_sub
  omega

/-- Growth steps during the greedy iteration. -/
noncomputable def growthSteps (fc : FiniteConditions) : Finset ℕ :=
  (Finset.range fc.K).filter (fun j => isGrowthStage fc.t fc.U (greedySeq fc j))

/-- Saturated steps during the greedy iteration. -/
noncomputable def saturatedSteps (fc : FiniteConditions) : Finset ℕ :=
  (Finset.range fc.K).filter (fun j => isSaturatedStage fc.t fc.xi (greedySeq fc j))

/-- Unsaturated steps during the greedy iteration. -/
noncomputable def unsaturatedSteps (fc : FiniteConditions) : Finset ℕ :=
  (Finset.range fc.K).filter (fun j => isUnsaturatedStage fc.t fc.U fc.xi (greedySeq fc j))

/-- Growth and unsaturated steps are disjoint. -/
lemma disjoint_growth_unsaturated (fc : FiniteConditions) :
    Disjoint (growthSteps fc) (unsaturatedSteps fc) := by
  rw [Finset.disjoint_left]
  intro j hj_grow hj_unsat
  simp only [growthSteps, Finset.mem_filter] at hj_grow
  simp only [unsaturatedSteps, Finset.mem_filter] at hj_unsat
  dsimp [isUnsaturatedStage] at hj_unsat
  exact hj_unsat.2.1 hj_grow.2

/-- Saturated, growth, and unsaturated steps cover all steps j < K. -/
lemma steps_partition (fc : FiniteConditions) (j : ℕ) (hj : j < fc.K) :
    j ∈ saturatedSteps fc ∨ j ∈ growthSteps fc ∨ j ∈ unsaturatedSteps fc := by
  have hj_range : j ∈ Finset.range fc.K := Finset.mem_range.mpr hj
  by_cases h_sat : isSaturatedStage fc.t fc.xi (greedySeq fc j)
  · left; simp only [saturatedSteps, Finset.mem_filter, hj_range, h_sat, and_self]
  · right
    by_cases h_grow : isGrowthStage fc.t fc.U (greedySeq fc j)
    · left; simp only [growthSteps, Finset.mem_filter, hj_range, h_grow, and_self]
    · right; simp only [unsaturatedSteps, Finset.mem_filter, hj_range, true_and]; exact ⟨h_grow, h_sat⟩

/-- When saturated steps are empty, unsaturated steps are bounded below by K - B_growth. -/
lemma card_unsaturatedSteps_ge (fc : FiniteConditions)
    (h_no_sat : saturatedSteps fc = ∅)
    (h_growth_budget : (growthSteps fc).card ≤ fc.B_growth) :
    fc.K - fc.B_growth ≤ (unsaturatedSteps fc).card := by
  have h_union : Finset.range fc.K = growthSteps fc ∪ unsaturatedSteps fc := by
    ext j
    constructor
    · intro hj
      have hj_lt : j < fc.K := Finset.mem_range.mp hj
      rcases steps_partition fc j hj_lt with h1 | h2 | h3
      · rw [h_no_sat] at h1
        simp at h1
      · exact Finset.mem_union_left _ h2
      · exact Finset.mem_union_right _ h3
    · intro hj
      simp only [Finset.mem_union, growthSteps, unsaturatedSteps, Finset.mem_filter] at hj
      rcases hj with ⟨hj, _⟩ | ⟨hj, _⟩ <;> exact hj
  have h_disj := disjoint_growth_unsaturated fc
  have h_card_union : (Finset.range fc.K).card = (growthSteps fc).card + (unsaturatedSteps fc).card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  rw [Finset.card_range] at h_card_union
  have hB := fc.hB_le_K
  omega

/-- CFP Lemma 5.6 Finite Conditions Version (Combinatorial Core F1 / Phase P18):
    Under the explicit numerical and combinatorial hypotheses of FiniteConditions,
    the modular subset sums satisfy the linear density lower bound:
      min(xi, 32 / ell) * t ≤ |Σ_t(A)|. -/
theorem cfp_lemma_5_6_finite_core (fc : FiniteConditions)
    (h_growth_budget_bound : (growthSteps fc).card ≤ fc.B_growth)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  by_cases h_sat_nonempty : (saturatedSteps fc).Nonempty
  · rcases h_sat_nonempty with ⟨j, hj⟩
    simp only [saturatedSteps, Finset.mem_filter, Finset.mem_range] at hj
    have hj_lt := hj.1
    have hj_sat := hj.2
    have hj_card : (greedySeq fc j).E.card ≤ fc.K := by
      rw [card_greedySeq_E fc j (by omega)]
      omega
    have h_sat_bound := card_subsetSumsMod_ge_of_saturated fc (greedySeq fc j) hj_card hj_sat
    have h_min_le : min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) ≤ fc.xi := min_le_left _ _
    have ht_nonneg : 0 ≤ (fc.t : ℝ) := by positivity
    have h_mul_le : min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ fc.xi * (fc.t : ℝ) :=
      mul_le_mul_of_nonneg_right h_min_le ht_nonneg
    exact h_mul_le.trans h_sat_bound
  · rw [Finset.nonempty_iff_ne_empty, not_not] at h_sat_nonempty
    have h_unsat_card := card_unsaturatedSteps_ge fc h_sat_nonempty h_growth_budget_bound
    have h_sum_ge : (unsaturatedSteps fc).card * fc.D ≤ ∑ j ∈ unsaturatedSteps fc, greedyDelta fc j := by
      have : ∑ j ∈ unsaturatedSteps fc, fc.D ≤ ∑ j ∈ unsaturatedSteps fc, greedyDelta fc j := by
        apply Finset.sum_le_sum
        intro j hj
        exact h_unsaturated_step_growth j hj
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have h_sub_sum : ∑ j ∈ unsaturatedSteps fc, greedyDelta fc j ≤ ∑ j ∈ Finset.range fc.K, greedyDelta fc j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [unsaturatedSteps, Finset.mem_filter] at hj
        exact hj.1
      · intro j _ _
        dsimp [greedyDelta]
        split_ifs <;> omega
    have h_total := sum_delta_le_total fc
    have h_unsat_le_D : (fc.K - fc.B_growth) * fc.D ≤ (unsaturatedSteps fc).card * fc.D :=
      Nat.mul_le_mul_right fc.D h_unsat_card
    have h_K_sub_le : (fc.K - fc.B_growth) * fc.D ≤ (subsetSumsMod fc.t fc.A).card := by
      omega
    have h_K_sub_real : (fc.D : ℝ) * ((fc.K : ℝ) - (fc.B_growth : ℝ)) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
      have h_cast : (fc.D : ℝ) * ((fc.K : ℝ) - (fc.B_growth : ℝ)) = ((fc.D * (fc.K - fc.B_growth) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub fc.hB_le_K]
      rw [h_cast]
      exact_mod_cast (by rw [mul_comm] at h_K_sub_le; exact h_K_sub_le)
    have h_budget := fc.h_growth_budget
    have h_density_le : (32 : ℝ) / (fc.ell : ℝ) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) :=
      h_budget.trans h_K_sub_real
    have h_min_le : min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) ≤ (32 : ℝ) / (fc.ell : ℝ) := min_le_right _ _
    have ht_nonneg : 0 ≤ (fc.t : ℝ) := by positivity
    have h_mul_le : min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ (32 : ℝ) / (fc.ell : ℝ) * (fc.t : ℝ) :=
      mul_le_mul_of_nonneg_right h_min_le ht_nonneg
    exact h_mul_le.trans h_density_le


/-!
### 21. Parameter Instantiation, Arithmetic Adapter & Non-Vacuity (Phase P19)

Number-theoretic rough candidate infrastructure (CFP §5.1, Lemma 5.3 & Phase P11),
concrete non-vacuous realizability of FiniteConditions, arithmetic parameter configuration,
and CFP Lemma 5.6 master specialization for m = n.
-/

/-- Example concrete instance of FiniteConditions proving non-vacuity and satisfiability. -/
noncomputable def concreteFiniteConditions : FiniteConditions where
  t := 20
  ht_pos := by decide
  A := {1, 3, 7}
  hA_pos := by
    intro a ha
    fin_cases ha <;> decide
  v := 1
  hv_pos := by decide
  K := 2
  M := 1
  hM_pos := by decide
  k_div := 1
  U := 9
  hU_pos := by decide
  D := 1
  hD_pos := by decide
  gMax := 1
  hgMax_pos := by decide
  xi := (1 : ℝ) / 128
  hxi_pos := by norm_num
  ell := 1024
  hell_pos := by decide
  B_growth := 0
  hB_le_K := by decide
  hK_add_M_le := by decide
  hA_diverse := by
    intro d hd
    have h_not_dvd_one : ¬ d ∣ 1 := by
      intro h_dvd
      have : d ≤ 1 := Nat.le_of_dvd (by decide) h_dvd
      omega
    have h_mem_filter : 1 ∈ ({1, 3, 7} : Finset ℕ).filter (fun x => ¬ d ∣ x) := by
      simp only [Finset.mem_filter, Finset.mem_insert, true_or, true_and]
      exact h_not_dvd_one
    have h_card_ge := Finset.card_le_card (Finset.singleton_subset_iff.mpr h_mem_filter)
    rw [Finset.card_singleton] at h_card_ge
    exact h_card_ge
  h_subgroup_le := by
    intro B hB hM
    have h_nonempty : B.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      subst h_empty
      simp only [Finset.card_empty] at hM
      omega
    rcases h_nonempty with ⟨b, hb⟩
    have hb_A := hB hb
    dsimp [subgroupIndex]
    have h_dvd_gcd : Finset.gcd B id ∣ b := Finset.gcd_dvd hb
    have h_gcd_dvd_b : Nat.gcd 20 (Finset.gcd B id) ∣ Nat.gcd 20 b :=
      Nat.dvd_gcd (Nat.gcd_dvd_left 20 _) (dvd_trans (Nat.gcd_dvd_right 20 _) h_dvd_gcd)
    have hb_cases : b = 1 ∨ b = 3 ∨ b = 7 := by
      fin_cases hb_A <;> simp
    rcases hb_cases with rfl | rfl | rfl
    · have h1 : Nat.gcd 20 1 = 1 := by decide
      rw [h1] at h_gcd_dvd_b
      exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
    · have h3 : Nat.gcd 20 3 = 1 := by decide
      rw [h3] at h_gcd_dvd_b
      exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
    · have h7 : Nat.gcd 20 7 = 1 := by decide
      rw [h7] at h_gcd_dvd_b
      exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
  h_subgroup_diverse := by
    intro B hB hM
    have h_le : subgroupIndex 20 B ≤ 1 := by
      have h_nonempty : B.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h_empty
        subst h_empty
        simp only [Finset.card_empty] at hM
        omega
      rcases h_nonempty with ⟨b, hb⟩
      have hb_A := hB hb
      dsimp [subgroupIndex]
      have h_dvd_gcd : Finset.gcd B id ∣ b := Finset.gcd_dvd hb
      have h_gcd_dvd_b : Nat.gcd 20 (Finset.gcd B id) ∣ Nat.gcd 20 b :=
        Nat.dvd_gcd (Nat.gcd_dvd_left 20 _) (dvd_trans (Nat.gcd_dvd_right 20 _) h_dvd_gcd)
      have hb_cases : b = 1 ∨ b = 3 ∨ b = 7 := by
        fin_cases hb_A <;> simp
      rcases hb_cases with rfl | rfl | rfl
      · rw [show Nat.gcd 20 1 = 1 by decide] at h_gcd_dvd_b
        exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
      · rw [show Nat.gcd 20 3 = 1 by decide] at h_gcd_dvd_b
        exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
      · rw [show Nat.gcd 20 7 = 1 by decide] at h_gcd_dvd_b
        exact Nat.le_of_dvd (by decide) h_gcd_dvd_b
    omega
  h_small_fiber_bound := by decide
  h_growth_threshold := by decide
  h_growth_budget := by norm_num

/-- Non-vacuity theorem: FiniteConditions is non-empty and realizable. -/
theorem finiteConditions_realizable : Nonempty FiniteConditions :=
  ⟨concreteFiniteConditions⟩

/-- Primorial W associated with a finite set of primes P: product of all primes in P. -/
def primorialProd (P : Finset ℕ) : ℕ :=
  ∏ p ∈ P, p

/-- The canonical Conlon–Fox–Pham ratio τ(W, m) = φ(W * m) / (W * m). -/
noncomputable def cfpTau (W m : ℕ) : ℝ :=
  (Nat.totient (W * m) : ℝ) / ((W * m : ℕ) : ℝ)

/-- Strict positivity of τ(W, m) when W and m are positive. -/
lemma cfpTau_pos (W m : ℕ) (hW : 0 < W) (hm : 0 < m) : 0 < cfpTau W m := by
  dsimp [cfpTau]
  have h_prod : 0 < W * m := Nat.mul_pos hW hm
  have h_tot : 0 < Nat.totient (W * m) := Nat.totient_pos.mpr h_prod
  positivity

/-- Number-theoretic rough candidate membership in Y(y, m, W) (CFP §5.1 / Phase P11). -/
def inY (y m W : ℕ) (a : ℕ) : Prop :=
  y ≤ a ∧ a < 2 * y ∧
  ∃ q u : ℕ, a = q * u ∧ u ∣ m ∧ u ^ 16 ≤ y ∧ q.Coprime (W * m)

/-- Scaled candidate membership in Y_v(y, m, W, v) (CFP §5.1 / Phase P11). -/
def inY_v (y m W v : ℕ) (a : ℕ) : Prop :=
  y ≤ v * a ∧ v * a < 2 * y ∧
  ∃ q u : ℕ, a = q * u ∧ (v * u) ∣ m ∧ (v * u) ^ 16 ≤ y ∧ q.Coprime (W * m)

/-- Multiplication by v maps candidates from Y_v to Y (Phase P11-A bridge). -/
lemma mem_Y_of_mem_Y_v (y m W v a : ℕ) (ha : inY_v y m W v a) : inY y m W (v * a) := by
  rcases ha with ⟨h_ge, h_lt, q, u, rfl, h_dvd, h_pow, h_coprime⟩
  refine ⟨h_ge, h_lt, q, v * u, ?_, h_dvd, h_pow, h_coprime⟩
  ring

/-- Extraction of coprime components from inY_v candidates:
    Every candidate a ∈ Y_v factors as a = q * u where q is coprime to W and m. -/
lemma coprime_q_W_of_inY_v {y m W v a : ℕ} (ha : inY_v y m W v a) :
    ∃ q u : ℕ, a = q * u ∧ Nat.Coprime q W ∧ Nat.Coprime q m := by
  rcases ha with ⟨_, _, q, u, rfl, _, _, hcop⟩
  have ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcop
  exact ⟨q, u, rfl, h1, h2⟩

/-- Arithmetic parameter configuration for Conlon–Fox–Pham Lemma 5.6.
    Explicitly bundles number-theoretic data (target n, scaling v, modulus t, set A)
    and maps them to the verified discrete interface FiniteConditions. -/
structure CFPArithParams where
  n : ℕ                  -- Target integer (m = n for Erdős Problem 360)
  hn : 2 ≤ n
  t : ℕ                  -- Modulus of subset sums
  ht_pos : 0 < t
  A : Finset ℕ           -- Candidate subset
  hA_pos : ∀ a ∈ A, 0 < a
  v : ℕ                  -- Divisor scaling factor
  hv_pos : 0 < v
  hvn : v ∣ n            -- v divides n (since m = n)
  K : ℕ                  -- Greedy iteration step count
  M : ℕ                  -- Minimum remaining candidates
  hM_pos : 0 < M
  k_div : ℕ              -- Diversity parameter
  U : ℕ                  -- Small-fiber threshold
  hU_pos : 0 < U
  D : ℕ                  -- Translation increment threshold
  hD_pos : 0 < D
  gMax : ℕ               -- Max subgroup index bound
  hgMax_pos : 0 < gMax
  xi : ℝ                 -- Linear density constant
  hxi_pos : 0 < xi
  ell : ℕ                -- Chromatic parameter
  hell_pos : 0 < ell
  B_growth : ℕ           -- Growth step budget
  hB_le_K : B_growth ≤ K

  -- Numerical and Combinatorial Conditions:
  hK_add_M_le : K + M ≤ A.card
  hA_diverse : IsDiverse A k_div
  h_subgroup_le : ∀ B ⊆ A, M ≤ B.card → subgroupIndex t B ≤ gMax
  h_subgroup_diverse : ∀ B ⊆ A, M ≤ B.card → subgroupIndex t B - 1 ≤ k_div
  h_small_fiber_bound : U < t / (2 * gMax)
  h_growth_threshold : 8 * D < U
  h_growth_budget : (32 : ℝ) / (ell : ℝ) * (t : ℝ) ≤ (D * (K - B_growth) : ℝ)

/-- Canonical mapping from CFPArithParams to the verified FiniteConditions structure. -/
def CFPArithParams.toFiniteConditions (p : CFPArithParams) : FiniteConditions where
  t := p.t
  ht_pos := p.ht_pos
  A := p.A
  hA_pos := p.hA_pos
  v := p.v
  hv_pos := p.hv_pos
  K := p.K
  M := p.M
  hM_pos := p.hM_pos
  k_div := p.k_div
  U := p.U
  hU_pos := p.hU_pos
  D := p.D
  hD_pos := p.hD_pos
  gMax := p.gMax
  hgMax_pos := p.hgMax_pos
  xi := p.xi
  hxi_pos := p.hxi_pos
  ell := p.ell
  hell_pos := p.hell_pos
  B_growth := p.B_growth
  hB_le_K := p.hB_le_K
  hK_add_M_le := p.hK_add_M_le
  hA_diverse := p.hA_diverse
  h_subgroup_le := p.h_subgroup_le
  h_subgroup_diverse := p.h_subgroup_diverse
  h_small_fiber_bound := p.h_small_fiber_bound
  h_growth_threshold := p.h_growth_threshold
  h_growth_budget := p.h_growth_budget

/-- CFP Lemma 5.6 Specialized to m = n (Phase P19 Master Theorem):
    For any valid arithmetic parameter configuration p : CFPArithParams,
    if the growth budget bound and unsaturated step growth hold,
    then the modular subset sums satisfy the linear density bound:
      min(xi, 32 / ell) * t ≤ |Σ_t(A)|. -/
theorem cfp_lemma_5_6_m_eq_n (p : CFPArithParams)
    (h_growth_budget_bound : (growthSteps p.toFiniteConditions).card ≤ p.B_growth)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps p.toFiniteConditions, p.D ≤ greedyDelta p.toFiniteConditions j) :
    min p.xi ((32 : ℝ) / (p.ell : ℝ)) * (p.t : ℝ) ≤ ((subsetSumsMod p.t p.A).card : ℝ) :=
  cfp_lemma_5_6_finite_core p.toFiniteConditions h_growth_budget_bound h_unsaturated_step_growth

/-- Connection to Diverse Lower Bound Witness:
    If subset sums achieve target hitting in the quotient under scaling factor v,
    a CFPDiverseWitness n k guarantees the chromatic lower bound k + 1 ≤ f(n). -/
theorem chromatic_lower_bound_of_diverse_density (n k : ℕ) (hn : 2 ≤ n)
    (w : CFPDiverseWitness n k) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_cfp_diverse_witness n k hn w


/-!
### 22. Diverse Subset Extraction and Subsampling (Conlon–Fox–Pham 2021, Lemma 5.4 / Phase 21)

This section establishes deterministic and interface theorems for extracting diverse subsets
from a given diverse candidate set, as required by CFP §5.1 Lemma 5.4:
1. Exact filter difference bounds and controlled diversity loss under subset extraction.
2. Diversity retention under element-wise and finset-wise removal (A \ E is (k - |E|)-diverse).
3. Application to greedy iteration state machine: remaining candidates st.B retain diversity.
4. Formal mathematical specification of CFP Lemma 5.4 subsampling interface.
5. Deterministic realization of Lemma 5.4 under controlled loss.
-/

/-- Difference of filtered non-divisible sets is contained in the difference of sets. -/
lemma filter_not_dvd_sdiff_subset (A B : Finset ℕ) (d : ℕ) :
    ((A.filter (fun x => ¬ d ∣ x)) \ (B.filter (fun x => ¬ d ∣ x))) ⊆ A \ B := by
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1.1, ?_⟩
  intro hxB
  exact hx.2 ⟨hxB, hx.1.2⟩

/-- Auxiliary: cardinality of difference for a subset. -/
lemma card_sdiff_of_subset {α : Type*} [DecidableEq α] {A B : Finset α} (hBA : B ⊆ A) :
    (A \ B).card = A.card - B.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]

/-- Upper bound on the loss of non-divisible elements when passing to a subset. -/
lemma card_filter_not_dvd_le_card_add_sdiff (A B : Finset ℕ) (d : ℕ) :
    (A.filter (fun x => ¬ d ∣ x)).card ≤
      (B.filter (fun x => ¬ d ∣ x)).card + (A \ B).card := by
  have h_sub : (A.filter (fun x => ¬ d ∣ x)) ⊆
      (B.filter (fun x => ¬ d ∣ x)) ∪ (A \ B) := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxB, hx.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx.1, hxB⟩)
  have h_card := Finset.card_le_card h_sub
  have h_union := Finset.card_union_le (B.filter (fun x => ¬ d ∣ x)) (A \ B)
  exact h_card.trans h_union

/-- Deterministic Diversity Preservation Theorem (Generalizing CFP Lemma 5.4):
    If A is k-diverse and B ⊆ A satisfies |A| - |B| ≤ k - k', then B is k'-diverse. -/
theorem isDiverse_subset_of_card_diff_le {A B : Finset ℕ} {k k' : ℕ}
    (hA : IsDiverse A k) (hBA : B ⊆ A)
    (h_loss : A.card - B.card ≤ k - k')
    (hk' : k' ≤ k) :
    IsDiverse B k' := by
  intro d hd
  have h_bound := card_filter_not_dvd_le_card_add_sdiff A B d
  rw [card_sdiff_of_subset hBA] at h_bound
  have h_div := hA d hd
  omega

/-- Removing a single element from a k-diverse set leaves a (k - 1)-diverse set. -/
lemma isDiverse_sdiff_singleton {A : Finset ℕ} {k : ℕ} (x : ℕ)
    (hA : IsDiverse A k) (hx : x ∈ A) (hk : 1 ≤ k) :
    IsDiverse (A \ {x}) (k - 1) := by
  have h_sub : {x} ⊆ A := Finset.singleton_subset_iff.mpr hx
  have h_card : (A \ {x}).card = A.card - 1 := by
    rw [card_sdiff_of_subset h_sub, Finset.card_singleton]
  apply isDiverse_subset_of_card_diff_le hA Finset.sdiff_subset _ (by omega)
  rw [h_card]
  have : 1 ≤ A.card := by
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  omega

/-- Removing any subset E ⊆ A of size r ≤ k leaves a (k - r)-diverse set. -/
theorem isDiverse_sdiff_finset {A E : Finset ℕ} {k : ℕ}
    (hA : IsDiverse A k) (hEA : E ⊆ A) (hr : E.card ≤ k) :
    IsDiverse (A \ E) (k - E.card) := by
  have h_card : (A \ E).card = A.card - E.card := card_sdiff_of_subset hEA
  apply isDiverse_subset_of_card_diff_le hA Finset.sdiff_subset _ (by omega)
  rw [h_card]
  have : E.card ≤ A.card := Finset.card_le_card hEA
  omega

/-- The remaining candidate set st.B in GreedyState retains diversity k_div - |E|. -/
lemma GreedyState.isDiverse_B {fc : FiniteConditions} (st : GreedyState fc.A)
    (h_card : st.E.card ≤ fc.k_div) :
    IsDiverse st.B (fc.k_div - st.E.card) :=
  isDiverse_sdiff_finset fc.hA_diverse st.hE_sub h_card

/-- Existence of a diverse subset of any prescribed size s with controlled loss. -/
theorem exists_diverse_subset_of_card_eq {A : Finset ℕ} {k k' s : ℕ}
    (hA : IsDiverse A k) (hs_le : s ≤ A.card)
    (h_loss : A.card - s ≤ k - k') (hk' : k' ≤ k) :
    ∃ B ⊆ A, B.card = s ∧ IsDiverse B k' := by
  obtain ⟨B, hBA, hB_card⟩ := Finset.exists_subset_card_eq hs_le
  refine ⟨B, hBA, hB_card, ?_⟩
  apply isDiverse_subset_of_card_diff_le hA hBA _ hk'
  rw [hB_card]
  exact h_loss

/-- Formal mathematical specification of Conlon–Fox–Pham Lemma 5.4 Subsampling Interface:
    For parameters k, h with h ≥ 2, a k-diverse set admits a subset B of size at least
    |A| / h that retains diversity at least k / (2 * h). -/
def CFPLemma54Statement (k h : ℕ) : Prop :=
  ∀ (A : Finset ℕ), IsDiverse A k →
    ∃ B ⊆ A, A.card / h ≤ B.card ∧ IsDiverse B (k / (2 * h))

/-- Deterministic realization of CFP Lemma 5.4:
    Whenever the cardinality loss condition holds, Lemma 5.4 is unconditionally satisfied. -/
theorem cfp_lemma_5_4_of_deterministic (k h : ℕ) (_hh : 2 ≤ h)
    (h_cond : ∀ A : Finset ℕ, IsDiverse A k → A.card - A.card / h ≤ k - k / (2 * h)) :
    CFPLemma54Statement k h := by
  intro A hA
  obtain ⟨B, hBA, hB_card, hB_div⟩ := exists_diverse_subset_of_card_eq
    hA (Nat.div_le_self A.card h) (h_cond A hA) (Nat.div_le_self k (2 * h))
  refine ⟨B, hBA, by rw [hB_card], hB_div⟩

/-- Any k-diverse set with k ≥ 1 has greatest common divisor at most 1. -/
lemma isDiverse_gcd_le_one {A : Finset ℕ} {k : ℕ} (hA : IsDiverse A k) (hk : 1 ≤ k) :
    A.gcd id ≤ 1 := by
  by_contra! h
  have hd : 2 ≤ A.gcd id := h
  have h_div := hA (A.gcd id) hd
  have h_empty : A.filter (fun x => ¬ A.gcd id ∣ x) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x hxA h_not_dvd
    exact h_not_dvd (Finset.gcd_dvd hxA)
  rw [h_empty, Finset.card_empty] at h_div
  omega

/-- Any k-diverse set with k ≥ 1 containing at least one positive element has gcd equal to 1. -/
lemma isDiverse_gcd_eq_one {A : Finset ℕ} {k : ℕ} (hA : IsDiverse A k) (hk : 1 ≤ k)
    (h_pos : ∃ x ∈ A, 0 < x) :
    A.gcd id = 1 := by
  have h_le := isDiverse_gcd_le_one hA hk
  obtain ⟨x, hx, hx_pos⟩ := h_pos
  have h_dvd : A.gcd id ∣ x := Finset.gcd_dvd hx
  have h_ne_zero : A.gcd id ≠ 0 := by
    intro h0
    rw [h0] at h_dvd
    have : x = 0 := Nat.eq_zero_of_zero_dvd h_dvd
    omega
  omega

/-- The subgroup index of a k-diverse set with k ≥ 1 containing a positive element is 1. -/
lemma subgroupIndex_eq_one_of_isDiverse (t : ℕ) {B : Finset ℕ} {k : ℕ}
    (hB : IsDiverse B k) (hk : 1 ≤ k) (h_pos : ∃ x ∈ B, 0 < x) :
    subgroupIndex t B = 1 := by
  dsimp [subgroupIndex]
  rw [isDiverse_gcd_eq_one hB hk h_pos, Nat.gcd_one_right]


/-- Two-stage disjoint diverse subset extraction:
    From a k-diverse set A, we can extract two disjoint subsets A₁ and A₂ of prescribed
    sizes s₁ and s₂ that retain k₁- and k₂-diversity respectively, provided the loss is controlled. -/
theorem exists_disjoint_diverse_subsets {A : Finset ℕ} {k k₁ k₂ s₁ s₂ : ℕ}
    (hA : IsDiverse A k)
    (hs_sum : s₁ + s₂ ≤ A.card)
    (h_loss₁ : A.card - s₁ ≤ k - k₁)
    (h_loss₂ : A.card - s₂ ≤ k - k₂)
    (hk₁ : k₁ ≤ k) (hk₂ : k₂ ≤ k) :
    ∃ A₁ A₂ : Finset ℕ,
      A₁ ⊆ A ∧ A₂ ⊆ A ∧
      Disjoint A₁ A₂ ∧
      A₁.card = s₁ ∧ A₂.card = s₂ ∧
      IsDiverse A₁ k₁ ∧ IsDiverse A₂ k₂ := by
  obtain ⟨U, hUA, hU_card⟩ := Finset.exists_subset_card_eq hs_sum
  have hs1_le_U : s₁ ≤ U.card := by omega
  obtain ⟨A₁, hA1_U, hA1_card⟩ := Finset.exists_subset_card_eq hs1_le_U
  let A₂ := U \ A₁
  have hA2_sub : A₂ ⊆ A := Finset.sdiff_subset.trans hUA
  have hA1_A : A₁ ⊆ A := hA1_U.trans hUA
  have h_disj : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [A₂, Finset.mem_sdiff] at hx2
    exact hx2.2 hx1
  have hA2_card : A₂.card = s₂ := by
    dsimp [A₂]
    rw [card_sdiff_of_subset hA1_U, hU_card, hA1_card]
    omega
  refine ⟨A₁, A₂, hA1_A, hA2_sub, h_disj, hA1_card, hA2_card, ?_, ?_⟩
  · apply isDiverse_subset_of_card_diff_le hA hA1_A _ hk₁
    rw [hA1_card]
    exact h_loss₁
  · apply isDiverse_subset_of_card_diff_le hA hA2_sub _ hk₂
    rw [hA2_card]
    exact h_loss₂

/-- End-to-end Divisor-Extraction and Diversity Preservation Pipeline:
    Given a scaling factor v > 0 and a t-diverse set Q with v * Q ⊆ A₀,
    subsampling via Lemma 5.4 extracts a diverse candidate set A ⊆ Q
    of prescribed target size s retaining k'-diversity, with v * A ⊆ A₀. -/
theorem exists_scaled_diverse_candidate (A₀ : Finset ℕ) (B t s k' : ℕ)
    (hk' : k' ≤ t)
    (v : ℕ) (Q : Finset ℕ)
    (_hv : 0 < v)
    (hQ_bnd : ∀ x ∈ Q, 1 ≤ x ∧ v * x ≤ B)
    (hQ_img : Q.image (fun x => v * x) ⊆ A₀)
    (hQ_div : IsDiverse Q t)
    (hs_le : s ≤ Q.card)
    (h_loss : Q.card - s ≤ t - k') :
    ∃ (A : Finset ℕ),
      (∀ x ∈ A, 1 ≤ x ∧ v * x ≤ B) ∧
      A.image (fun x => v * x) ⊆ A₀ ∧
      A.card = s ∧
      IsDiverse A k' := by
  obtain ⟨A, hAQ, hA_card, hA_div⟩ :=
    exists_diverse_subset_of_card_eq hQ_div hs_le h_loss hk'
  refine ⟨A, ?_, ?_, hA_card, hA_div⟩
  · intro x hx
    exact hQ_bnd x (hAQ hx)
  · have h_img_sub : A.image (fun x => v * x) ⊆ Q.image (fun x => v * x) :=
      Finset.image_subset_image hAQ
    exact h_img_sub.trans hQ_img

/-- Candidate set from diverse extraction satisfies the FiniteConditions diversity and capacity requirements:
    If Q is t-diverse and A ⊆ Q of size K + M has loss at most t - k_div,
    then A satisfies K + M ≤ |A| and IsDiverse A k_div. -/
lemma diverse_candidate_satisfies_finiteConditions {Q : Finset ℕ} {t K M k_div : ℕ}
    (hQ : IsDiverse Q t)
    (hs_le : K + M ≤ Q.card)
    (h_loss : Q.card - (K + M) ≤ t - k_div)
    (hk_div : k_div ≤ t) :
    ∃ A ⊆ Q, K + M ≤ A.card ∧ IsDiverse A k_div := by
  obtain ⟨A, hAQ, hA_card, hA_div⟩ :=
    exists_diverse_subset_of_card_eq hQ hs_le h_loss hk_div
  exact ⟨A, hAQ, by omega, hA_div⟩

/-- Full mathematical specification of Conlon–Fox–Pham Lemma 5.4 Subsampling Interface:
    For parameters k, h with h ≥ 2 and range bound N, any k-diverse subset of [1, N]
    contains a subset B of size |A| / h that retains k / (2 * h) diversity. -/
def CFPLemma54FullStatement (k h N : ℕ) : Prop :=
  ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → IsDiverse A k →
    ∃ B ⊆ A, B.card = A.card / h ∧ IsDiverse B (k / (2 * h))

/-- Realization of full CFP Lemma 5.4 under deterministic loss budget:
    Whenever the loss budget holds, every k-diverse subset admits a diverse subsample of exact size |A| / h. -/
theorem cfp_lemma_5_4_full_of_deterministic (k h N : ℕ) (_hh : 2 ≤ h)
    (h_cond : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsDiverse A k → A.card - A.card / h ≤ k - k / (2 * h)) :
    CFPLemma54FullStatement k h N := by
  intro A hAN hA
  obtain ⟨B, hBA, hB_card, hB_div⟩ := exists_diverse_subset_of_card_eq
    hA (Nat.div_le_self A.card h) (h_cond A hAN hA) (Nat.div_le_self k (2 * h))
  exact ⟨B, hBA, hB_card, hB_div⟩

/-- Subsets of size s that retain k'-diversity. -/
noncomputable def CFPLemma54Subsets (A : Finset ℕ) (s k' : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard s).filter (fun B => IsDiverse B k')

/-- When the loss condition holds, EVERY subset of size s is k'-diverse. -/
theorem cfp_lemma_5_4_all_subsets_diverse {A : Finset ℕ} {s k k' : ℕ}
    (hA : IsDiverse A k)
    (h_loss : A.card - s ≤ k - k')
    (hk' : k' ≤ k) :
    CFPLemma54Subsets A s k' = A.powersetCard s := by
  ext B
  simp only [CFPLemma54Subsets, Finset.mem_filter, Finset.mem_powersetCard, and_iff_left_iff_imp]
  rintro ⟨hBA, hB_card⟩
  apply isDiverse_subset_of_card_diff_le hA hBA _ hk'
  rw [hB_card]
  exact h_loss

/-- Exact count of diverse subsets when loss is controlled:
    all (Nat.choose |A| s) subsets are diverse. -/
theorem card_CFPLemma54Subsets_eq {A : Finset ℕ} {s k k' : ℕ}
    (hA : IsDiverse A k)
    (h_loss : A.card - s ≤ k - k')
    (hk' : k' ≤ k) :
    (CFPLemma54Subsets A s k').card = Nat.choose A.card s := by
  rw [cfp_lemma_5_4_all_subsets_diverse hA h_loss hk', Finset.card_powersetCard]

/-- Combinatorial partition of a finite set into m pairwise disjoint subsets of equal size s. -/
theorem exists_disjoint_subsets_list {α : Type*} [DecidableEq α]
    (A : Finset α) (m s : ℕ) (h_card : m * s ≤ A.card) :
    ∃ L : List (Finset α),
      L.length = m ∧
      (∀ B ∈ L, B ⊆ A) ∧
      (∀ B ∈ L, B.card = s) ∧
      L.Pairwise Disjoint := by
  induction m generalizing A with
  | zero =>
    refine ⟨[], rfl, by simp, by simp, List.Pairwise.nil⟩
  | succ m ih =>
    have h_prod : (m + 1) * s = m * s + s := Nat.succ_mul m s
    have hs_le : s ≤ A.card := by omega
    obtain ⟨B0, hB0_sub, hB0_card⟩ := Finset.exists_subset_card_eq hs_le
    let A' := A \ B0
    have hA'_card : m * s ≤ A'.card := by
      rw [Finset.card_sdiff_of_subset hB0_sub, hB0_card]
      omega
    obtain ⟨L', hlen', hsub', hcard', hdisj'⟩ := ih A' hA'_card
    refine ⟨B0 :: L', ?_, ?_, ?_, ?_⟩
    · simp [hlen']
    · intro B hB
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB_in
      · exact hB0_sub
      · have := hsub' B hB_in
        exact this.trans Finset.sdiff_subset
    · intro B hB
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB_in
      · exact hB0_card
      · exact hcard' B hB_in
    · apply List.Pairwise.cons
      · intro B hB
        have hB_sub_A' : B ⊆ A' := hsub' B hB
        rw [Finset.disjoint_left]
        intro x hx0 hxB
        have hx_A' := hB_sub_A' hxB
        simp only [A', Finset.mem_sdiff] at hx_A'
        exact hx_A'.2 hx0
      · exact hdisj'

/-- Conlon–Fox–Pham Lemma 5.4 Multi-Subset Diverse Partition (List Form):
    From a k-diverse set A, whenever m * s ≤ |A| and |A| - s ≤ k - k' with k' ≤ k,
    there exists a list of m mutually disjoint subsets of size s that all retain k'-diversity. -/
theorem exists_disjoint_diverse_list {A : Finset ℕ} {k k' m s : ℕ}
    (hA : IsDiverse A k)
    (h_card : m * s ≤ A.card)
    (h_loss : A.card - s ≤ k - k')
    (hk' : k' ≤ k) :
    ∃ L : List (Finset ℕ),
      L.length = m ∧
      (∀ B ∈ L, B ⊆ A) ∧
      (∀ B ∈ L, B.card = s) ∧
      (∀ B ∈ L, IsDiverse B k') ∧
      L.Pairwise Disjoint := by
  obtain ⟨L, hlen, hsub, hcard, hdisj⟩ := exists_disjoint_subsets_list A m s h_card
  refine ⟨L, hlen, hsub, hcard, ?_, hdisj⟩
  intro B hB
  apply isDiverse_subset_of_card_diff_le hA (hsub B hB) _ hk'
  rw [hcard B hB]
  exact h_loss

/-- Pairwise disjointness indexed by Fin for any pairwise disjoint list. -/
lemma pairwise_get_of_pairwise {α : Type*} {L : List (Finset α)} (h : L.Pairwise Disjoint)
    (i j : Fin L.length) (hij : i ≠ j) : Disjoint (L.get i) (L.get j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  dsimp at hij ⊢
  rcases lt_or_gt_of_ne (fun h_eq => hij (Fin.ext h_eq)) with hlt | hgt
  · exact List.pairwise_iff_get.mp h ⟨i, hi⟩ ⟨j, hj⟩ hlt
  · exact (List.pairwise_iff_get.mp h ⟨j, hj⟩ ⟨i, hi⟩ hgt).symm

/-- Conlon–Fox–Pham Lemma 5.4 Multi-Subset Diverse Family:
    From a k-diverse set A, whenever m * s ≤ |A| and |A| - s ≤ k - k' with k' ≤ k,
    there exists a family V : Fin m → Finset ℕ of pairwise disjoint subsets of size s
    that all retain k'-diversity. -/
theorem exists_disjoint_diverse_family {A : Finset ℕ} {k k' m s : ℕ}
    (hA : IsDiverse A k)
    (h_card : m * s ≤ A.card)
    (h_loss : A.card - s ≤ k - k')
    (hk' : k' ≤ k) :
    ∃ V : Fin m → Finset ℕ,
      (∀ i, V i ⊆ A) ∧
      (∀ i, (V i).card = s) ∧
      (∀ i, IsDiverse (V i) k') ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) := by
  obtain ⟨L, hlen, hsub, hcard, hdiv, hdisj⟩ :=
    exists_disjoint_diverse_list hA h_card h_loss hk'
  let V : Fin m → Finset ℕ := fun i => L.get ⟨i.1, by omega⟩
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro i
    have h_mem : V i ∈ L := List.get_mem L ⟨i.1, by omega⟩
    exact hsub (V i) h_mem
  · intro i
    have h_mem : V i ∈ L := List.get_mem L ⟨i.1, by omega⟩
    exact hcard (V i) h_mem
  · intro i
    have h_mem : V i ∈ L := List.get_mem L ⟨i.1, by omega⟩
    exact hdiv (V i) h_mem
  · intro i j hij
    dsimp [V]
    have hij' : (⟨i.1, by omega⟩ : Fin L.length) ≠ ⟨j.1, by omega⟩ := by
      intro h_eq
      apply hij
      ext
      exact Fin.mk.inj h_eq
    exact pairwise_get_of_pairwise hdisj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij'

/-- Extraction of a disjoint diverse pair from a diverse family of size m ≥ 2. -/
theorem exists_disjoint_diverse_pair_of_family {A : Finset ℕ} {k' m s : ℕ}
    (hm : 2 ≤ m)
    (V : Fin m → Finset ℕ)
    (h_sub : ∀ i, V i ⊆ A)
    (h_card : ∀ i, (V i).card = s)
    (h_div : ∀ i, IsDiverse (V i) k')
    (h_disj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) :
    ∃ A1 A2 : Finset ℕ,
      A1 ⊆ A ∧ A2 ⊆ A ∧
      Disjoint A1 A2 ∧
      A1.card = s ∧ A2.card = s ∧
      IsDiverse A1 k' ∧ IsDiverse A2 k' := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h_ne : i0 ≠ i1 := by
    intro h_eq
    have : (0 : ℕ) = 1 := Fin.mk.inj h_eq
    omega
  refine ⟨V i0, V i1, h_sub i0, h_sub i1, h_disj i0 i1 h_ne, h_card i0, h_card i1, h_div i0, h_div i1⟩

/-- Full Conlon–Fox–Pham Lemma 5.4 Diverse Partition Theorem:
    Partitioning A into h disjoint subsets of size |A| / h, each retaining k / (2 * h) diversity
    whenever the loss budget holds. -/
theorem exists_disjoint_diverse_partition_of_div {A : Finset ℕ} {k h : ℕ}
    (hA : IsDiverse A k) (_hh : 1 ≤ h)
    (h_loss : A.card - A.card / h ≤ k - k / (2 * h))
    (hk_div : k / (2 * h) ≤ k) :
    ∃ V : Fin h → Finset ℕ,
      (∀ i, V i ⊆ A) ∧
      (∀ i, (V i).card = A.card / h) ∧
      (∀ i, IsDiverse (V i) (k / (2 * h))) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) := by
  have h_card : h * (A.card / h) ≤ A.card := by
    rw [mul_comm]
    exact Nat.div_mul_le_self A.card h
  exact exists_disjoint_diverse_family hA h_card h_loss hk_div


/-!
### 23. Modulo Density to Integer Subset Sum Growth (Conlon–Fox–Pham 2021, Lemma 2.5 & Lemma 5.5 / Phase 22)

This section translates modular subset sum density (from Lemma 5.6) to integer subset sum growth:
1. Monotonicity of subset sums: A ⊆ B ⟹ Σ(A) ⊆ Σ(B).
2. Maximum fiber element selection in Σ(A) modulo m.
3. Conlon–Fox–Pham Lemma 2.5: |Σ(A)| + |Σ_m(A)| ≤ |Σ(A ∪ {m})| for m ∉ A, m > 0.
4. Iterated disjoint sumset growth: |Σ(S)| + ∑_{b ∈ B} |Σ_b(S)| ≤ |Σ(S ∪ B)|.
5. Uniform modular bound on disjoint union: |B| * L ≤ |Σ(S ∪ B)| when ∀ b ∈ B, L ≤ |Σ_b(S)|.
6. CFP Lemma 5.5 Master Theorem: |Σ(A)| ≥ |A_2| * c * (y / v) for diverse A_1, A_2 ⊆ A.
7. Lemma 5.5 scale specialization: |Σ(A)| ≥ s * min(xi, 32/ell) * (y / v).
-/

/-- Monotonicity of integer subset sums under subset inclusion. -/
lemma subsetSums_mono {A B : Finset ℕ} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B := by
  intro x hx
  simp only [mem_subsetSums_iff] at hx ⊢
  rcases hx with ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

/-- Maximum fiber element in subsetSums A for residue class r modulo m. -/
noncomputable def maxFiberElem (A : Finset ℕ) (m : ℕ) (r : ZMod m) : ℕ :=
  if h : ((subsetSums A).filter (fun (x : ℕ) => ((x : ZMod m) = r))).Nonempty then
    ((subsetSums A).filter (fun (x : ℕ) => ((x : ZMod m) = r))).max' h
  else 0

/-- Properties of maxFiberElem: belongs to subsetSums A and projects to r modulo m. -/
lemma maxFiberElem_mem {A : Finset ℕ} {m : ℕ} {r : ZMod m}
    (hr : r ∈ subsetSumsMod m A) :
    maxFiberElem A m r ∈ subsetSums A ∧ ((maxFiberElem A m r : ℕ) : ZMod m) = r := by
  dsimp [maxFiberElem]
  have h_ne : ((subsetSums A).filter (fun (x : ℕ) => ((x : ZMod m) = r))).Nonempty := by
    simp only [subsetSumsMod, Finset.mem_image] at hr
    rcases hr with ⟨x, hx, rfl⟩
    refine ⟨x, ?_⟩
    simp only [Finset.mem_filter, hx, true_and]
  rw [dif_pos h_ne]
  have h_mem := Finset.max'_mem _ h_ne
  simp only [Finset.mem_filter] at h_mem
  exact h_mem

/-- Any element in subsetSums A with residue r is bounded by maxFiberElem. -/
lemma le_maxFiberElem {A : Finset ℕ} {m : ℕ} {r : ZMod m} (x : ℕ)
    (hx : x ∈ subsetSums A) (hxr : ((x : ℕ) : ZMod m) = r) :
    x ≤ maxFiberElem A m r := by
  dsimp [maxFiberElem]
  have h_ne : ((subsetSums A).filter (fun (y : ℕ) => ((y : ZMod m) = r))).Nonempty :=
    ⟨x, by simp only [Finset.mem_filter, hx, hxr, and_self]⟩
  rw [dif_pos h_ne]
  apply Finset.le_max'
  simp only [Finset.mem_filter, hx, hxr, and_self]

/-- Conlon–Fox–Pham (2021) Lemma 2.5 (Single-element subset sum growth from modular density):
    For any set of positive integers A and m ∉ A with m > 0,
      |Σ(A)| + |Σ_m(A)| ≤ |Σ(A ∪ {m})|. -/
theorem card_subsetSums_insert_ge (A : Finset ℕ) (m : ℕ) (hm : 0 < m) (hm_not : m ∉ A) :
    (subsetSums A).card + (subsetSumsMod m A).card ≤ (subsetSums (insert m A)).card := by
  let S := subsetSums A
  let R := subsetSumsMod m A
  let g : ZMod m → ℕ := fun r => maxFiberElem A m r + m
  let W : Finset ℕ := R.image g
  have hW_sub : W ⊆ subsetSums (insert m A) := by
    intro y hy
    simp only [W, Finset.mem_image] at hy
    rcases hy with ⟨r, hr, rfl⟩
    have hr_spec := (maxFiberElem_mem hr).1
    rw [subsetSums_insert A m hm_not]
    apply Finset.mem_union_right
    simp only [Finset.mem_image]
    exact ⟨maxFiberElem A m r, hr_spec, rfl⟩
  have hS_sub : S ⊆ subsetSums (insert m A) := by
    rw [subsetSums_insert A m hm_not]
    exact Finset.subset_union_left
  have h_disj : Disjoint S W := by
    rw [Finset.disjoint_right]
    intro y hy
    simp only [W, Finset.mem_image] at hy
    rcases hy with ⟨r, hr, rfl⟩
    intro hy_in_S
    have hr_mod := (maxFiberElem_mem hr).2
    have h_mod_y : ((maxFiberElem A m r + m : ℕ) : ZMod m) = r := by
      push_cast
      rw [hr_mod, CharP.cast_eq_zero (ZMod m) m, add_zero]
    have h_le := le_maxFiberElem (maxFiberElem A m r + m) hy_in_S h_mod_y
    omega
  have h_inj : ∀ r1 ∈ R, ∀ r2 ∈ R, g r1 = g r2 → r1 = r2 := by
    intro r1 hr1 r2 hr2 h_eq
    have h_mod1 : ((g r1 : ℕ) : ZMod m) = r1 := by
      dsimp [g]
      push_cast
      rw [(maxFiberElem_mem hr1).2, CharP.cast_eq_zero (ZMod m) m, add_zero]
    have h_mod2 : ((g r2 : ℕ) : ZMod m) = r2 := by
      dsimp [g]
      push_cast
      rw [(maxFiberElem_mem hr2).2, CharP.cast_eq_zero (ZMod m) m, add_zero]
    rw [← h_mod1, ← h_mod2, h_eq]
  have hW_card : W.card = R.card := Finset.card_image_of_injOn h_inj
  have h_union_sub : S ∪ W ⊆ subsetSums (insert m A) := Finset.union_subset hS_sub hW_sub
  have h_card_union := Finset.card_le_card h_union_sub
  rw [Finset.card_union_of_disjoint h_disj, hW_card] at h_card_union
  exact h_card_union

/-- Conlon–Fox–Pham (2021) Lemma 2.5 (Iterated subset sum growth over disjoint sets):
    For disjoint sets S, B ⊆ ℕ where all elements in B are strictly positive,
      |Σ(S)| + ∑ b ∈ B, |Σ_b(S)| ≤ |Σ(S ∪ B)|. -/
theorem card_subsetSums_union_ge_sum (S B : Finset ℕ) (h_disj : Disjoint S B) (hB_pos : ∀ b ∈ B, 0 < b) :
    (subsetSums S).card + ∑ b ∈ B, (subsetSumsMod b S).card ≤ (subsetSums (S ∪ B)).card := by
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, add_zero, Finset.union_empty, le_refl]
  | @insert b B' hb_not ih =>
    have hb_in : b ∈ insert b B' := Finset.mem_insert_self b B'
    have hb_pos : 0 < b := hB_pos b hb_in
    have hB'_pos : ∀ x ∈ B', 0 < x := fun x hx => hB_pos x (Finset.mem_insert_of_mem hx)
    have h_disj' : Disjoint S B' := by
      rw [Finset.disjoint_left] at h_disj ⊢
      intro x hxS hxB'
      exact h_disj hxS (Finset.mem_insert_of_mem hxB')
    have hb_not_S : b ∉ S := by
      intro hbS
      rw [Finset.disjoint_left] at h_disj
      exact h_disj hbS hb_in
    have hb_not_SB' : b ∉ S ∪ B' := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hb_not_S, hb_not⟩
    have ih_res := ih h_disj' hB'_pos
    have h_single := card_subsetSums_insert_ge (S ∪ B') b hb_pos hb_not_SB'
    have h_mono : subsetSumsMod b S ⊆ subsetSumsMod b (S ∪ B') :=
      subsetSumsMod_mono Finset.subset_union_left
    have h_card_mono : (subsetSumsMod b S).card ≤ (subsetSumsMod b (S ∪ B')).card :=
      Finset.card_le_card h_mono
    rw [Finset.sum_insert hb_not]
    have h_insert_eq : insert b (S ∪ B') = S ∪ insert b B' := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto
    rw [h_insert_eq] at h_single
    omega

/-- Uniform modular lower bound on disjoint addition:
    if |Σ_b(S)| ≥ L for all b ∈ B, then |Σ(S ∪ B)| ≥ |B| * L. -/
theorem card_subsetSums_union_ge_mul_min (S B : Finset ℕ) (h_disj : Disjoint S B)
    (hB_pos : ∀ b ∈ B, 0 < b) (L : ℕ) (hL : ∀ b ∈ B, L ≤ (subsetSumsMod b S).card) :
    B.card * L ≤ (subsetSums (S ∪ B)).card := by
  have h_sum_ge : B.card * L ≤ ∑ b ∈ B, (subsetSumsMod b S).card := by
    have : ∑ b ∈ B, L ≤ ∑ b ∈ B, (subsetSumsMod b S).card := Finset.sum_le_sum (fun b hb => hL b hb)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have h_main := card_subsetSums_union_ge_sum S B h_disj hB_pos
  omega

/-- Real version of uniform modular lower bound on disjoint addition. -/
theorem card_subsetSums_union_ge_mul_min_real (S B : Finset ℕ) (h_disj : Disjoint S B)
    (hB_pos : ∀ b ∈ B, 0 < b) (L : ℝ) (hL : ∀ b ∈ B, L ≤ ((subsetSumsMod b S).card : ℝ)) :
    (B.card : ℝ) * L ≤ ((subsetSums (S ∪ B)).card : ℝ) := by
  have h_sum_ge : (B.card : ℝ) * L ≤ ∑ b ∈ B, ((subsetSumsMod b S).card : ℝ) := by
    have : ∑ b ∈ B, L ≤ ∑ b ∈ B, ((subsetSumsMod b S).card : ℝ) := Finset.sum_le_sum (fun b hb => hL b hb)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have h_main := card_subsetSums_union_ge_sum S B h_disj hB_pos
  have h_main_real : ((subsetSums S).card : ℝ) + ∑ b ∈ B, ((subsetSumsMod b S).card : ℝ) ≤
      ((subsetSums (S ∪ B)).card : ℝ) := by
    have h_cast : (((subsetSums S).card + ∑ b ∈ B, (subsetSumsMod b S).card : ℕ) : ℝ) ≤
        (((subsetSums (S ∪ B)).card : ℕ) : ℝ) := Nat.cast_le.mpr h_main
    push_cast at h_cast
    exact h_cast
  have h_nonneg : 0 ≤ ((subsetSums S).card : ℝ) := by positivity
  linarith

/-- Conlon–Fox–Pham (2021) Lemma 5.5 (Integer Subset Sum Growth from Modular Density):
    Let A_1, A_2 ⊆ A be disjoint subsets where all elements in A_2 are positive,
    and satisfy the lower bound b ≥ y / v.
    Suppose that for all b ∈ A_2, the modular subset sums of A_1 satisfy the density bound:
      c * b ≤ |Σ_b(A_1)|.
    Then the integer subset sums of A satisfy the lower bound:
      |Σ(A)| ≥ |A_2| * c * (y / v). -/
theorem cfp_lemma_5_5 (A A1 A2 : Finset ℕ) (y v : ℕ) (c : ℝ)
    (hA1 : A1 ⊆ A) (hA2 : A2 ⊆ A) (h_disj : Disjoint A1 A2)
    (hA2_pos : ∀ b ∈ A2, 0 < b)
    (hA2_ge : ∀ b ∈ A2, (y : ℝ) / (v : ℝ) ≤ (b : ℝ))
    (hc_nonneg : 0 ≤ c)
    (h_mod_density : ∀ b ∈ A2, c * (b : ℝ) ≤ ((subsetSumsMod b A1).card : ℝ)) :
    (A2.card : ℝ) * c * ((y : ℝ) / (v : ℝ)) ≤ ((subsetSums A).card : ℝ) := by
  have h_bound : ∀ b ∈ A2, c * ((y : ℝ) / (v : ℝ)) ≤ ((subsetSumsMod b A1).card : ℝ) := by
    intro b hb
    have h1 := mul_le_mul_of_nonneg_left (hA2_ge b hb) hc_nonneg
    have h2 := h_mod_density b hb
    exact h1.trans h2
  have h_union := card_subsetSums_union_ge_mul_min_real A1 A2 h_disj hA2_pos (c * ((y : ℝ) / (v : ℝ))) h_bound
  have h_sub : A1 ∪ A2 ⊆ A := Finset.union_subset hA1 hA2
  have h_mono : subsetSums (A1 ∪ A2) ⊆ subsetSums A := subsetSums_mono h_sub
  have h_card_mono : ((subsetSums (A1 ∪ A2)).card : ℝ) ≤ ((subsetSums A).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_mono
  have h_assoc : (A2.card : ℝ) * c * ((y : ℝ) / (v : ℝ)) = (A2.card : ℝ) * (c * ((y : ℝ) / (v : ℝ))) := by ring
  rw [h_assoc]
  exact h_union.trans h_card_mono

/-- Specialized Conlon–Fox–Pham Lemma 5.5 on extracted diverse subsets:
    Combining Lemma 5.4 extraction (size s) with Lemma 5.6 modular density min(xi, 32/ell)
    yields integer subset sum lower bound s * min(xi, 32/ell) * (y/v) ≤ |Σ(A)|. -/
theorem cfp_lemma_5_5_scale (A A1 A2 : Finset ℕ) (y v s : ℕ) (xi : ℝ) (ell : ℕ)
    (hA1 : A1 ⊆ A) (hA2 : A2 ⊆ A) (h_disj : Disjoint A1 A2)
    (hA2_card : s ≤ A2.card)
    (hA2_pos : ∀ b ∈ A2, 0 < b)
    (hA2_ge : ∀ b ∈ A2, (y : ℝ) / (v : ℝ) ≤ (b : ℝ))
    (hxi_pos : 0 ≤ xi) (hell_pos : 0 < ell)
    (h_mod_density : ∀ b ∈ A2, min xi ((32 : ℝ) / (ell : ℝ)) * (b : ℝ) ≤ ((subsetSumsMod b A1).card : ℝ)) :
    (s : ℝ) * min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ)) ≤ ((subsetSums A).card : ℝ) := by
  have hc_nonneg : 0 ≤ min xi ((32 : ℝ) / (ell : ℝ)) := by
    apply le_min hxi_pos
    have : 0 < (ell : ℝ) := Nat.cast_pos.mpr hell_pos
    positivity
  have h_full := cfp_lemma_5_5 A A1 A2 y v (min xi ((32 : ℝ) / (ell : ℝ)))
                   hA1 hA2 h_disj hA2_pos hA2_ge hc_nonneg h_mod_density
  have hs_le : (s : ℝ) ≤ (A2.card : ℝ) := Nat.cast_le.mpr hA2_card
  have h_factor_nonneg : 0 ≤ min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ)) := by
    apply mul_nonneg hc_nonneg
    positivity
  have h_scale : (s : ℝ) * (min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ))) ≤
      (A2.card : ℝ) * (min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ))) :=
    mul_le_mul_of_nonneg_right hs_le h_factor_nonneg
  have h_assoc1 : (s : ℝ) * min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ)) =
      (s : ℝ) * (min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ))) := by ring
  have h_assoc2 : (A2.card : ℝ) * min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ)) =
      (A2.card : ℝ) * (min xi ((32 : ℝ) / (ell : ℝ)) * ((y : ℝ) / (v : ℝ))) := by ring
  rw [h_assoc1]
  rw [h_assoc2] at h_full
  exact h_scale.trans h_full

/-- Bridging lemma: mapping sumsets of integer-embedded subset sums back to natural subset sums. -/
lemma subsetSums_of_mem_sumset_image
    {A B : Finset ℕ} (h_disj : Disjoint A B)
    (z : ℤ) (hz : 0 ≤ z)
    (hz_mem : z ∈ sumset ((subsetSums A).image (fun (x : ℕ) => (x : ℤ)))
                         ((subsetSums B).image (fun (x : ℕ) => (x : ℤ)))) :
    z.toNat ∈ subsetSums (A ∪ B) := by
  rw [mem_sumset_iff] at hz_mem
  rcases hz_mem with ⟨x, hx, y, hy, rfl⟩
  simp only [Finset.mem_image] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  have hab : (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; rfl
  rw [hab, Int.toNat_natCast]
  exact subsetSums_add_of_disjoint h_disj ha hb

/-- Bounding the integer image of subset sums in an integer interval [0, L]. -/
lemma image_cast_subsetSums_subset_Icc (A : Finset ℕ) (L : ℕ) (hL : A.sum id ≤ L) :
    (subsetSums A).image (fun (x : ℕ) => (x : ℤ)) ⊆ Finset.Icc 0 (L : ℤ) := by
  intro z hz
  simp only [Finset.mem_image, mem_subsetSums_iff] at hz
  rcases hz with ⟨x, ⟨B, hB, rfl⟩, rfl⟩
  simp only [Finset.mem_Icc]
  constructor
  · omega
  · have h_le : B.sum id ≤ A.sum id := Finset.sum_le_sum_of_subset hB
    omega

/-- **Continuous Interval Generation from Lev (2010) Theorem**:
    If disjoint subsets A, B ⊆ ℕ have bounded sum (A.sum id ≤ L1, B.sum id ≤ L2)
    and satisfy the high density threshold max L1 L2 + 2 ≤ |Σ(A)| + |Σ(B)|,
    then the subset sums Σ(A ∪ B) contain the continuous integer interval
    [(L1 + L2 - K).toNat, K.toNat], where K = |Σ(A)| + |Σ(B)| - 2. -/
theorem subsetSums_contains_Icc_of_lev
    (A B : Finset ℕ) (h_disj : Disjoint A B)
    (L1 L2 : ℕ)
    (hL1 : A.sum id ≤ L1) (hL2 : B.sum id ≤ L2)
    (h_dense : max (L1 : ℤ) (L2 : ℤ) + 2 ≤ ((subsetSums A).card : ℤ) + ((subsetSums B).card : ℤ)) :
    let K : ℤ := ((subsetSums A).card : ℤ) + ((subsetSums B).card : ℤ) - 2
    Finset.Icc (L1 + L2 - K).toNat K.toNat ⊆ subsetSums (A ∪ B) := by
  intro K k hk
  simp only [Finset.mem_Icc] at hk
  rcases hk with ⟨hk_low, hk_high⟩
  set S1 := (subsetSums A).image (fun (x : ℕ) => (x : ℤ))
  set S2 := (subsetSums B).image (fun (x : ℕ) => (x : ℤ))
  have hS1_sub : S1 ⊆ Finset.Icc 0 (L1 : ℤ) := image_cast_subsetSums_subset_Icc A L1 hL1
  have hS2_sub : S2 ⊆ Finset.Icc 0 (L2 : ℤ) := image_cast_subsetSums_subset_Icc B L2 hL2
  have hS1_card : S1.card = (subsetSums A).card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have hS2_card : S2.card = (subsetSums B).card :=
    Finset.card_image_of_injective _ Nat.cast_injective
  have h_dense' : max (L1 : ℤ) (L2 : ℤ) + 2 ≤ (S1.card : ℤ) + (S2.card : ℤ) := by
    rw [hS1_card, hS2_card]; exact h_dense
  have h_lev := lev_pigeonhole_interval (L1 : ℤ) (L2 : ℤ) (by omega) (by omega)
                  S1 S2 hS1_sub hS2_sub h_dense'
  rw [hS1_card, hS2_card] at h_lev
  have hS1_le : (S1.card : ℤ) ≤ (L1 : ℤ) + 1 := by
    have h_cast : (S1.card : ℤ) ≤ ((Finset.Icc 0 (L1 : ℤ)).card : ℤ) :=
      Nat.cast_le.mpr (Finset.card_le_card hS1_sub)
    rw [Int.card_Icc_of_le 0 (L1 : ℤ) (by omega)] at h_cast
    omega
  have hS2_le : (S2.card : ℤ) ≤ (L2 : ℤ) + 1 := by
    have h_cast : (S2.card : ℤ) ≤ ((Finset.Icc 0 (L2 : ℤ)).card : ℤ) :=
      Nat.cast_le.mpr (Finset.card_le_card hS2_sub)
    rw [Int.card_Icc_of_le 0 (L2 : ℤ) (by omega)] at h_cast
    omega
  have hlow_nonneg : 0 ≤ L1 + L2 - K := by
    dsimp [K]
    rw [hS1_card] at hS1_le
    rw [hS2_card] at hS2_le
    omega
  have hk_int : (k : ℤ) ∈ Finset.Icc (L1 + L2 - K) K := by
    simp only [Finset.mem_Icc]
    constructor
    · have h_cast_k : ((L1 + L2 - K).toNat : ℤ) ≤ (k : ℤ) := Nat.cast_le.mpr hk_low
      rw [Int.toNat_of_nonneg hlow_nonneg] at h_cast_k
      exact h_cast_k
    · have h_cast_k : (k : ℤ) ≤ (K.toNat : ℤ) := Nat.cast_le.mpr hk_high
      have hK_nonneg : 0 ≤ K := by omega
      rw [Int.toNat_of_nonneg hK_nonneg] at h_cast_k
      exact h_cast_k
  have hk_mem_sumset := h_lev hk_int
  have hk_nonneg : 0 ≤ (k : ℤ) := by omega
  have h_hit := subsetSums_of_mem_sumset_image h_disj (k : ℤ) hk_nonneg hk_mem_sumset
  rwa [Int.toNat_natCast] at h_hit

/-- Extension of a continuous interval in V ⊆ Q across the remainder set Q \ V to hit target. -/
theorem mem_subsetSums_of_lev_interval_extend
    {Q V : Finset ℕ} (hVQ : V ⊆ Q)
    {a b : ℕ} (hab : a ≤ b)
    (h_interval : Finset.Icc a b ⊆ subsetSums V)
    (hQ_bound : ∀ t ∈ Q \ V, t ≤ b - a + 1)
    {target : ℕ}
    (ha_le : a ≤ target)
    (hle_b : target ≤ b + (Q \ V).sum id) :
    target ∈ subsetSums Q := by
  have h_disj : Disjoint V (Q \ V) := Finset.disjoint_sdiff
  have h_extend := subsetSums_interval_extend h_disj h_interval hQ_bound hab
  have h_union : V ∪ (Q \ V) = Q := Finset.union_sdiff_of_subset hVQ
  rw [h_union] at h_extend
  apply h_extend
  simp only [Finset.mem_Icc]
  exact ⟨ha_le, hle_b⟩

/-- **Master Target Hitting Theorem via Lev Dense Interval Extension**:
    If Q contains a disjoint pair V1, V2 satisfying the Lev density condition,
    producing an interval [a, b] ⊆ Σ(V1 ∪ V2) that extends across Q \ (V1 ∪ V2)
    to cover target, then target ∈ Σ(Q). -/
theorem target_hit_of_lev_diverse
    {Q V1 V2 : Finset ℕ} (hV1Q : V1 ⊆ Q) (hV2Q : V2 ⊆ Q) (h_disj : Disjoint V1 V2)
    (L1 L2 : ℕ) (hL1 : V1.sum id ≤ L1) (hL2 : V2.sum id ≤ L2)
    (h_dense : max (L1 : ℤ) (L2 : ℤ) + 2 ≤ ((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ))
    (target : ℕ)
    (h_step_bound : ∀ t ∈ Q \ (V1 ∪ V2),
      t ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat -
          (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat + 1)
    (ha_le : (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat ≤ target)
    (hle_b : target ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat + (Q \ (V1 ∪ V2)).sum id) :
    target ∈ subsetSums Q := by
  let V := V1 ∪ V2
  have hVQ : V ⊆ Q := Finset.union_subset hV1Q hV2Q
  have h_int := subsetSums_contains_Icc_of_lev V1 V2 h_disj L1 L2 hL1 hL2 h_dense
  set K : ℤ := ((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2
  have hab : (L1 + L2 - K).toNat ≤ K.toNat := by
    apply Int.toNat_le_toNat
    omega
  exact mem_subsetSums_of_lev_interval_extend hVQ hab h_int h_step_bound ha_le hle_b

/-- **Construction of CFPDiverseWitness from Lev Interval Coverage**:
    Given a base set S ⊆ [1, n), threshold M with k * M < |S|, and scaling factor v ∣ n with 0 < v,
    if every large subset A ⊆ S of size ≥ M + 1 has its quotient Q = (A ∩ vℕ)/v containing
    subsets V1, V2 satisfying the Lev condition such that n/v is covered,
    then CFPDiverseWitness n k is instantiated. -/
def CFPDiverseWitness.ofLevCoverage
    (n k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n)
    (M : ℕ) (h_card : k * M < S.card)
    (v : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (h_lev_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
      let Q := (A.filter (fun x => v ∣ x)).image (fun x => x / v)
      ∃ (V1 V2 : Finset ℕ) (_hV1Q : V1 ⊆ Q) (_hV2Q : V2 ⊆ Q) (_h_disj : Disjoint V1 V2)
        (L1 L2 : ℕ) (_hL1 : V1.sum id ≤ L1) (_hL2 : V2.sum id ≤ L2)
        (_h_dense : max (L1 : ℤ) (L2 : ℤ) + 2 ≤ ((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ))
        (_h_step_bound : ∀ t ∈ Q \ (V1 ∪ V2),
          t ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat -
              (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat + 1)
        (_ha_le : (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat ≤ n / v)
        (_hle_b : n / v ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat + (Q \ (V1 ∪ V2)).sum id),
        True) :
    CFPDiverseWitness n k where
  S := S
  hS := hS
  M := M
  h_card := h_card
  v := v
  hv := hv
  hvn := hvn
  h_hit := by
    intro A hA hM
    obtain ⟨V1, V2, hV1Q, hV2Q, h_disj, L1, L2, hL1, hL2, h_dense, h_step, ha_le, hle_b, _⟩ :=
      h_lev_hit A hA hM
    exact target_hit_of_lev_diverse hV1Q hV2Q h_disj L1 L2 hL1 hL2 h_dense (n / v) h_step ha_le hle_b

/-- Direct chromatic lower bound k + 1 ≤ f(n) from Lev interval coverage. -/
theorem minColors_ge_of_lev_coverage
    (n k : ℕ) (hn : 2 ≤ n) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n)
    (M : ℕ) (h_card : k * M < S.card)
    (v : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (h_lev_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
      let Q := (A.filter (fun x => v ∣ x)).image (fun x => x / v)
      ∃ (V1 V2 : Finset ℕ) (_hV1Q : V1 ⊆ Q) (_hV2Q : V2 ⊆ Q) (_h_disj : Disjoint V1 V2)
        (L1 L2 : ℕ) (_hL1 : V1.sum id ≤ L1) (_hL2 : V2.sum id ≤ L2)
        (_h_dense : max (L1 : ℤ) (L2 : ℤ) + 2 ≤ ((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ))
        (_h_step_bound : ∀ t ∈ Q \ (V1 ∪ V2),
          t ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat -
              (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat + 1)
        (_ha_le : (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat ≤ n / v)
        (_hle_b : n / v ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat + (Q \ (V1 ∪ V2)).sum id),
        True) :
    k + 1 ≤ minColors n hn :=
  minColors_ge_of_cfp_diverse_witness n k hn (CFPDiverseWitness.ofLevCoverage n k S hS M h_card v hv hvn h_lev_hit)

/-- Structured predicate for Lev interval coverage on a quotient set Q:
    Q contains a disjoint pair V1, V2 satisfying the Lev condition and
    extending to hit n / v. -/
def HasLevIntervalCoverage (n v : ℕ) (Q : Finset ℕ) : Prop :=
  ∃ (V1 V2 : Finset ℕ), V1 ⊆ Q ∧ V2 ⊆ Q ∧ Disjoint V1 V2 ∧
    ∃ (L1 L2 : ℕ), V1.sum id ≤ L1 ∧ V2.sum id ≤ L2 ∧
      max (L1 : ℤ) (L2 : ℤ) + 2 ≤ ((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) ∧
      (∀ t ∈ Q \ (V1 ∪ V2),
        t ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat -
            (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat + 1) ∧
      (L1 + L2 - (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2)).toNat ≤ n / v ∧
      n / v ≤ (((subsetSums V1).card : ℤ) + ((subsetSums V2).card : ℤ) - 2).toNat + (Q \ (V1 ∪ V2)).sum id

/-- Direct target hitting from HasLevIntervalCoverage. -/
theorem target_hit_of_hasLevIntervalCoverage
    {n v : ℕ} {Q : Finset ℕ} (h_cov : HasLevIntervalCoverage n v Q) :
    n / v ∈ subsetSums Q := by
  rcases h_cov with ⟨V1, V2, hV1Q, hV2Q, h_disj, L1, L2, hL1, hL2, h_dense, h_step, ha_le, hle_b⟩
  exact target_hit_of_lev_diverse hV1Q hV2Q h_disj L1 L2 hL1 hL2 h_dense (n / v) h_step ha_le hle_b

/-- Predicate form of CFPDiverseWitness from HasLevIntervalCoverage. -/
def CFPDiverseWitness.ofLevCoveragePred
    (n k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 1 n)
    (M : ℕ) (h_card : k * M < S.card)
    (v : ℕ) (hv : 0 < v) (hvn : v ∣ n)
    (h_lev_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
      HasLevIntervalCoverage n v ((A.filter (fun x => v ∣ x)).image (fun x => x / v))) :
    CFPDiverseWitness n k where
  S := S
  hS := hS
  M := M
  h_card := h_card
  v := v
  hv := hv
  hvn := hvn
  h_hit := by
    intro A hA hM
    exact target_hit_of_hasLevIntervalCoverage (h_lev_hit A hA hM)

/-- Global Asymptotic Lower Bound from Diverse Witnesses:
    If for all sufficiently large n, there exists a CFPDiverseWitness n k
    at scale k + 1 ≥ c * F(n), then f(n) satisfies HasChromaticLowerBound F c. -/
theorem hasChromaticLowerBound_of_diverse_witnesses (F : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (N0 : ℕ)
    (h_wit : ∀ n, 2 ≤ n → N0 ≤ n → ∃ k : ℕ, c * F n ≤ (k + 1 : ℝ) ∧ Nonempty (CFPDiverseWitness n k)) :
    HasChromaticLowerBound F c := by
  apply hasChromaticLowerBound_of_cfp_witnesses F c hc N0
  intro n hn hN
  obtain ⟨k, h_scale, ⟨w⟩⟩ := h_wit n hn hN
  exact ⟨k, h_scale, ⟨CFPLowerBoundWitness.ofDiverse n k w⟩⟩

/-- Global Asymptotic Lower Bound from Lev Interval Coverage:
    If for all sufficiently large n, there exists a Lev coverage witness at scale k + 1 ≥ c * F(n),
    then f(n) satisfies HasChromaticLowerBound F c. -/
theorem hasChromaticLowerBound_of_lev_coverage (F : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (N0 : ℕ)
    (h_wit : ∀ n, 2 ≤ n → N0 ≤ n → ∃ (k : ℕ) (S : Finset ℕ) (_hS : S ⊆ Finset.Ico 1 n)
      (M : ℕ) (_h_card : k * M < S.card) (v : ℕ) (_hv : 0 < v) (_hvn : v ∣ n)
      (_h_lev_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
        HasLevIntervalCoverage n v ((A.filter (fun x => v ∣ x)).image (fun x => x / v))),
      c * F n ≤ (k + 1 : ℝ)) :
    HasChromaticLowerBound F c := by
  apply hasChromaticLowerBound_of_diverse_witnesses F c hc N0
  intro n hn hN
  obtain ⟨k, S, hS, M, h_card, v, hv, hvn, h_lev_hit, h_scale⟩ := h_wit n hn hN
  have w := CFPDiverseWitness.ofLevCoveragePred n k S hS M h_card v hv hvn h_lev_hit
  exact ⟨k, h_scale, ⟨w⟩⟩

/-- Conlon–Fox–Pham (2021) Asymptotic Master Theorem with Diverse Witnesses:
    Uniting diverse lower bound witnesses with 4-layer upper bounds to yield the sharp
    asymptotic two-sided equivalence c * F(n) ≤ f(n) ≤ C * F(n). -/
theorem erdos_problem_360_asymptotic_master_of_diverse (F : ℕ → ℝ) {c C : ℝ} (hc : 0 < c)
    (N0 : ℕ)
    (h_wit : ∀ n, 2 ≤ n → N0 ≤ n → ∃ k : ℕ, c * F n ≤ (k + 1 : ℝ) ∧ Nonempty (CFPDiverseWitness n k))
    (h_upper : HasChromaticUpperBound F C) :
    ∃ N_final : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N_final ≤ n →
      c * F n ≤ (minColors n hn : ℝ) ∧
      (minColors n hn : ℝ) ≤ C * F n := by
  have h_lower := hasChromaticLowerBound_of_diverse_witnesses F c hc N0 h_wit
  exact conlon_fox_pham_bounds F h_lower h_upper

/-- Conlon–Fox–Pham (2021) Asymptotic Master Theorem with Lev Interval Coverage:
    Uniting Lev interval coverage with 4-layer upper bounds to yield the sharp
    asymptotic two-sided equivalence c * F(n) ≤ f(n) ≤ C * F(n). -/
theorem erdos_problem_360_asymptotic_master_of_lev (F : ℕ → ℝ) {c C : ℝ} (hc : 0 < c)
    (N0 : ℕ)
    (h_wit : ∀ n, 2 ≤ n → N0 ≤ n → ∃ (k : ℕ) (S : Finset ℕ) (_hS : S ⊆ Finset.Ico 1 n)
      (M : ℕ) (_h_card : k * M < S.card) (v : ℕ) (_hv : 0 < v) (_hvn : v ∣ n)
      (_h_lev_hit : ∀ A : Finset ℕ, A ⊆ S → M + 1 ≤ A.card →
        HasLevIntervalCoverage n v ((A.filter (fun x => v ∣ x)).image (fun x => x / v))),
      c * F n ≤ (k + 1 : ℝ))
    (h_upper : HasChromaticUpperBound F C) :
    ∃ N_final : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N_final ≤ n →
      c * F n ≤ (minColors n hn : ℝ) ∧
      (minColors n hn : ℝ) ≤ C * F n := by
  have h_lower := hasChromaticLowerBound_of_lev_coverage F c hc N0 h_wit
  exact conlon_fox_pham_bounds F h_lower h_upper

/-- Explicit Conlon–Fox–Pham Asymptotic Lower Bound Parameters:
    Encapsulates the explicit asymptotic parameter package (v, y, z, ell, W) for n:
    - Scaling divisor v ∣ n with 0 < v
    - Target scale factor k with c * F(n) ≤ k + 1
    - Instantiated CFPDiverseWitness n k via Lev interval coverage -/
structure CFPAsymptoticParams (n : ℕ) (F : ℕ → ℝ) (c : ℝ) : Type where
  k : ℕ
  h_scale : c * F n ≤ (k + 1 : ℝ)
  witness : CFPDiverseWitness n k

/-- Canonical realization of HasChromaticLowerBound from a family of asymptotic parameters. -/
theorem hasChromaticLowerBound_of_asymptotic_params (F : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (N0 : ℕ)
    (h_params : ∀ n, 2 ≤ n → N0 ≤ n → CFPAsymptoticParams n F c) :
    HasChromaticLowerBound F c := by
  apply hasChromaticLowerBound_of_diverse_witnesses F c hc N0
  intro n hn hN
  let p := h_params n hn hN
  exact ⟨p.k, p.h_scale, ⟨p.witness⟩⟩


/-!
### 24. Growth Steps Budget Infrastructure (Conlon–Fox–Pham 2021, Lemma 5.6 Claim 1 / Phase P16)

In §5.1 Claim 1, Conlon–Fox–Pham bound the total number of growth steps during the greedy iteration:
1. Subgroup index doubling chain: If g_0 | g_1 | ... | g_m with g_i < g_{i+1}, then 2^m ≤ g_m.
2. Uniform block bound: Any chain bounded by gMax has length at most L where gMax < 2^{L+1}.
3. Segment decomposition: The iteration is partitioned into at most L + 1 constant-g blocks.
4. Per-block growth budget: Multiplicative steps (T multiplies by ≥ 3/2) and linear steps (T grows by ≥ M/8).
5. Master growth budget bound: Total growth steps are bounded by B_growth = (L + 1) * (J_mult + 8U/M + 1).
-/

/-- Strict divisor doubling: if a ∣ b and a < b for positive integers, then 2 * a ≤ b. -/
lemma mul_two_le_of_dvd_of_lt {a b : ℕ} (ha : 0 < a) (h_dvd : a ∣ b) (h_lt : a < b) :
    2 * a ≤ b := by
  rcases h_dvd with ⟨c, rfl⟩
  have hc : 2 ≤ c := by
    by_contra h_not
    have : c ≤ 1 := by omega
    interval_cases c
    · omega
    · omega
  nlinarith

/-- Exponential lower bound on strictly increasing divisor chains:
    any chain g_0 | g_1 | ... | g_m of positive integers with g_i < g_{i+1}
    satisfies 2^m ≤ g_m. -/
lemma chain_doubling_le (g : ℕ → ℕ) (hg_pos : ∀ i, 0 < g i)
    (hg_dvd : ∀ i, g i ∣ g (i + 1)) (hg_lt : ∀ i, g i < g (i + 1)) (m : ℕ) :
    2 ^ m ≤ g m := by
  induction m with
  | zero =>
    simp only [Nat.pow_zero]
    exact hg_pos 0
  | succ m ih =>
    have h_step := mul_two_le_of_dvd_of_lt (hg_pos m) (hg_dvd m) (hg_lt m)
    have h_pow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [h_pow]
    nlinarith

/-- Bound on chain length from maximum subgroup index:
    if g_m ≤ gMax and gMax < 2^(L + 1), then m ≤ L. -/
lemma chain_length_le_of_le_gMax (g : ℕ → ℕ) (hg_pos : ∀ i, 0 < g i)
    (hg_dvd : ∀ i, g i ∣ g (i + 1)) (hg_lt : ∀ i, g i < g (i + 1))
    (gMax L m : ℕ) (hgMax : g m ≤ gMax) (hL : gMax < 2 ^ (L + 1)) :
    m ≤ L := by
  by_contra h_not
  have hm : L + 1 ≤ m := by omega
  have h_mono : 2 ^ (L + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_chain := chain_doubling_le g hg_pos hg_dvd hg_lt m
  omega

/-- Multiplicative growth step bound in natural numbers:
    if a quantity S starts at ≥ 1 and satisfies 3 * S j ≤ 2 * S (j + 1) on each multiplicative step,
    then 3^q ≤ 2^q * S q. -/
lemma multiplicative_growth_bound_nat (S : ℕ → ℕ) (hS0 : 1 ≤ S 0)
    (h_step : ∀ j, 3 * S j ≤ 2 * S (j + 1)) (q : ℕ) :
    3 ^ q ≤ 2 ^ q * S q := by
  induction q with
  | zero => simp [hS0]
  | succ q ih =>
    have h_pow3 : 3 ^ (q + 1) = 3 ^ q * 3 := by ring
    have h_pow2 : 2 ^ (q + 1) = 2 ^ q * 2 := by ring
    rw [h_pow3, h_pow2]
    have h1 : 3 ^ q * 3 ≤ (2 ^ q * S q) * 3 := Nat.mul_le_mul_right 3 ih
    have h2 : (2 ^ q * S q) * 3 = 2 ^ q * (3 * S q) := by ring
    have h3 : 2 ^ q * (3 * S q) ≤ 2 ^ q * (2 * S (q + 1)) :=
      Nat.mul_le_mul_left (2 ^ q) (h_step q)
    have h4 : 2 ^ q * (2 * S (q + 1)) = (2 ^ q * 2) * S (q + 1) := by ring
    rw [h2] at h1
    rw [h4] at h3
    exact h1.trans h3

/-- Multiplicative growth step bound in reals:
    (3/2)^q ≤ S q when 3 * S j ≤ 2 * S (j + 1) and 1 ≤ S 0. -/
lemma multiplicative_growth_bound_real (S : ℕ → ℕ) (hS0 : 1 ≤ S 0)
    (h_step : ∀ j, 3 * S j ≤ 2 * S (j + 1)) (q : ℕ) :
    (3 : ℝ) ^ q / (2 : ℝ) ^ q ≤ (S q : ℝ) := by
  have h_nat := multiplicative_growth_bound_nat S hS0 h_step q
  have h_cast : ((3 ^ q : ℕ) : ℝ) ≤ (((2 ^ q * S q : ℕ) : ℝ)) := Nat.cast_le.mpr h_nat
  push_cast at h_cast
  have h2 : 0 < (2 : ℝ) ^ q := by positivity
  exact (div_le_iff₀ h2).mpr (by linarith)

/-- Linear growth step bound:
    if a quantity increases by at least Δ on each step and remains bounded by U,
    the number of steps k satisfies k * Δ ≤ U. -/
lemma linear_growth_bound_step (T : ℕ → ℕ) (Δ U : ℕ)
    (h_step : ∀ j, T j + Δ ≤ T (j + 1)) (k : ℕ) (h_bound : T k ≤ U) :
    T 0 + k * Δ ≤ U := by
  have h_ind : ∀ j, T 0 + j * Δ ≤ T j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h_succ := h_step j
      have : T 0 + (j + 1) * Δ = (T 0 + j * Δ) + Δ := by ring
      rw [this]
      exact (Nat.add_le_add_right ih Δ).trans h_succ
  exact (h_ind k).trans h_bound

/-- Linear step count bound: k ≤ U / Δ when T 0 + k * Δ ≤ U. -/
lemma linear_step_count_le (T : ℕ → ℕ) (Δ U : ℕ) (hΔ : 0 < Δ)
    (h_step : ∀ j, T j + Δ ≤ T (j + 1)) (k : ℕ) (h_bound : T k ≤ U) :
    k ≤ U / Δ := by
  have h_le := linear_growth_bound_step T Δ U h_step k h_bound
  have h_mul : k * Δ ≤ U := (Nat.le_add_left (k * Δ) (T 0)).trans h_le
  exact (Nat.le_div_iff_mul_le hΔ).mpr h_mul

/-- Chain length bound using Nat.log2. -/
lemma chain_length_le_log2 (g : ℕ → ℕ) (hg_pos : ∀ i, 0 < g i)
    (hg_dvd : ∀ i, g i ∣ g (i + 1)) (hg_lt : ∀ i, g i < g (i + 1))
    (gMax m : ℕ) (hgMax_pos : 0 < gMax) (hgMax : g m ≤ gMax) :
    m ≤ Nat.log2 gMax := by
  have h_pow := chain_doubling_le g hg_pos hg_dvd hg_lt m
  have h_le : 2 ^ m ≤ gMax := h_pow.trans hgMax
  exact (Nat.le_log2 (by omega)).mpr h_le

/-- Number of constant-g blocks in any divisor chain bounded by gMax. -/
def maxSubgroupBlocks (gMax : ℕ) : ℕ :=
  Nat.log2 gMax + 1

/-- Multiplicative growth step budget per block (Conlon–Fox–Pham 2021, Claim 1 / Phase P16). -/
def p16MultBudget (t : ℕ) : ℕ :=
  2 * (Nat.log2 t + 1)

/-- Linear growth step budget per block. -/
def p16LinearBudget (U M : ℕ) : ℕ :=
  8 * U / M + 1

/-- Per-block growth budget: sum of multiplicative and linear budgets. -/
def p16BlockBudget (t U M : ℕ) : ℕ :=
  p16MultBudget t + p16LinearBudget U M

/-- Total growth budget: (Nat.log2 gMax + 1) * p16BlockBudget. -/
def p16TotalBudget (t gMax U M : ℕ) : ℕ :=
  (Nat.log2 gMax + 1) * p16BlockBudget t U M

/-- Legacy multiplicative growth step budget per block. -/
def multGrowthBudget (t : ℕ) : ℕ :=
  2 * t

/-- Legacy linear growth step budget per block. -/
def linearGrowthBudget (U M : ℕ) : ℕ :=
  8 * U / M + 1

/-- Legacy per-block growth budget. -/
def blockGrowthBudget (t U M : ℕ) : ℕ :=
  multGrowthBudget t + linearGrowthBudget U M

/-- Legacy Claim 1 growth bound. -/
def claim1GrowthBound (t gMax U M : ℕ) : ℕ :=
  maxSubgroupBlocks gMax * blockGrowthBudget t U M

/-!
### Abstract Sparse Marked-Step Counting Theorems (Phase D)
-/

lemma pow_eight_le_pow_nine (L : ℕ) : 8 ^ L ≤ 9 ^ L :=
  Nat.pow_le_pow_left (by omega) L

lemma eight_pow_eq (L : ℕ) : 8 ^ L = 2 ^ (3 * L) := by
  rw [show (8 : ℕ) = 2 ^ 3 by rfl, ← Nat.pow_mul]

lemma two_pow_split (L : ℕ) : 2 ^ (2 * L) * 2 ^ L = 2 ^ (3 * L) := by
  rw [← Nat.pow_add, show 2 * L + L = 3 * L by omega]

lemma two_pow_mul_t_lt_three_pow (L t : ℕ) (ht : t < 2 ^ L) :
    2 ^ (2 * L) * t < 3 ^ (2 * L) := by
  have h1 : 2 ^ (2 * L) * t < 2 ^ (2 * L) * 2 ^ L :=
    Nat.mul_lt_mul_of_pos_left ht (Nat.two_pow_pos (2 * L))
  rw [two_pow_split L, ← eight_pow_eq L] at h1
  have h2 : 8 ^ L ≤ 9 ^ L := pow_eight_le_pow_nine L
  have h3 : (9 : ℕ) ^ L = 3 ^ (2 * L) := by
    rw [show (9 : ℕ) = 3 ^ 2 by rfl, ← Nat.pow_mul, mul_comm 2 L]
  rw [h3] at h2
  exact h1.trans_le h2

lemma mult_step_count_bound (q t L : ℕ) (ht : t < 2 ^ L) (hq : 3 ^ q ≤ 2 ^ q * t) :
    q ≤ 2 * L := by
  by_contra h_gt
  have h_le : 2 * L + 1 ≤ q := by omega
  have h_pow3 : 3 ^ (2 * L + 1) ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) h_le
  have h_key := two_pow_mul_t_lt_three_pow L t ht
  have h_step : 2 ^ (2 * L + 1) * t < 3 ^ (2 * L + 1) := by
    calc 2 ^ (2 * L + 1) * t
      _ = 2 * (2 ^ (2 * L) * t) := by
        rw [pow_succ]
        ring
      _ < 3 * (3 ^ (2 * L)) := by
        have h_mul2 : 2 * (2 ^ (2 * L) * t) < 2 * (3 ^ (2 * L)) :=
          Nat.mul_lt_mul_of_pos_left h_key (by omega)
        have h_mul3 : 2 * (3 ^ (2 * L)) < 3 * (3 ^ (2 * L)) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
        exact h_mul2.trans h_mul3
      _ = 3 ^ (2 * L + 1) := by
        rw [pow_succ]
        ring
  let d := q - (2 * L + 1)
  have h_decomp : q = d + (2 * L + 1) := by omega
  have h_contra : 2 ^ q * t < 3 ^ q := by
    calc 2 ^ q * t
      _ = 2 ^ d * (2 ^ (2 * L + 1) * t) := by
        rw [h_decomp, pow_add]
        ring
      _ < 3 ^ d * 3 ^ (2 * L + 1) := by
        have hd_le : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by omega) d
        cases t with
        | zero =>
          exfalso
          have : 3 ^ q = 0 := by omega
          have : 0 < 3 ^ q := Nat.pow_pos (by omega)
          omega
        | succ t' =>
          exact Nat.mul_lt_mul_of_le_of_lt hd_le h_step (Nat.pow_pos (by omega))
      _ = 3 ^ q := by
        rw [← pow_add]
        congr 1
        omega
  omega

lemma lt_two_pow_succ_log2 (t : ℕ) : t < 2 ^ (Nat.log2 t + 1) :=
  Nat.lt_log2_self

lemma min'_erase_max' (J : Finset ℕ) (hJ : J.Nonempty) :
    let m := J.max' hJ
    let J' := J.erase m
    ∀ (hJ' : J'.Nonempty), J'.min' hJ' = J.min' hJ := by
  intro m J' hJ'
  have hm_in : m ∈ J := Finset.max'_mem J hJ
  have h_sub : J' ⊆ J := Finset.erase_subset m J
  have h_min_le : J.min' hJ ≤ J'.min' hJ' :=
    Finset.min'_le J (J'.min' hJ') (h_sub (Finset.min'_mem J' hJ'))
  have h_le_min : J'.min' hJ' ≤ J.min' hJ := by
    have h_min_in : J.min' hJ ∈ J := Finset.min'_mem J hJ
    by_cases h_eq_m : J.min' hJ = m
    · have h_non : ∃ y ∈ J', True := ⟨hJ'.choose, hJ'.choose_spec, trivial⟩
      rcases h_non with ⟨y, hy, _⟩
      have hy_in : y ∈ J := h_sub hy
      have hy_ne_m : y ≠ m := Finset.ne_of_mem_erase hy
      have hy_le_m : y ≤ m := Finset.le_max' J y hy_in
      have hy_lt_m : y < m := lt_of_le_of_ne hy_le_m hy_ne_m
      have hm_le_y : m ≤ y := by
        rw [← h_eq_m]
        exact Finset.min'_le J y hy_in
      omega
    · have h_min_in_J' : J.min' hJ ∈ J' := Finset.mem_erase.mpr ⟨h_eq_m, h_min_in⟩
      exact Finset.min'_le J' (J.min' hJ) h_min_in_J'
  exact le_antisymm h_le_min h_min_le

lemma finset_mult_growth (f : ℕ → ℕ) (hf_mono : ∀ a b, a ≤ b → f a ≤ f b)
    (J : Finset ℕ) (hJ : J.Nonempty)
    (hJ_step : ∀ j ∈ J, 3 * f j ≤ 2 * f (j + 1)) :
    3 ^ J.card * f (J.min' hJ) ≤ 2 ^ J.card * f ((J.max' hJ) + 1) := by
  generalize hk : J.card = k
  induction k using Nat.strong_induction_on generalizing J with
  | h n ih =>
    subst hk
    have hJ_pos : 0 < J.card := Finset.card_pos.mpr hJ
    by_cases hn1 : J.card = 1
    · rcases Finset.card_eq_one.mp hn1 with ⟨x, rfl⟩
      simp only [Finset.card_singleton, pow_one, Finset.min'_singleton, Finset.max'_singleton]
      exact hJ_step x (Finset.mem_singleton_self x)
    · have hn2 : 2 ≤ J.card := by omega
      let m := J.max' hJ
      have hm_in : m ∈ J := Finset.max'_mem J hJ
      let J' := J.erase m
      have hJ'_card : J'.card = J.card - 1 := Finset.card_erase_of_mem hm_in
      have hJ'_nonempty : J'.Nonempty := Finset.card_pos.mp (by rw [hJ'_card]; omega)
      let m' := J'.max' hJ'_nonempty
      have hm'_in' : m' ∈ J' := Finset.max'_mem J' hJ'_nonempty
      have hm'_in : m' ∈ J := Finset.mem_of_mem_erase hm'_in'
      have hm'_ne : m' ≠ m := Finset.ne_of_mem_erase hm'_in'
      have hm'_le_m : m' ≤ m := Finset.le_max' J m' hm'_in
      have hm'_lt_m : m' < m := lt_of_le_of_ne hm'_le_m hm'_ne
      have hm'_succ_le : m' + 1 ≤ m := hm'_lt_m
      have h_f_le_m : f (m' + 1) ≤ f m := hf_mono (m' + 1) m hm'_succ_le
      have h_step_m := hJ_step m hm_in
      have h_step_sub : ∀ j ∈ J', 3 * f j ≤ 2 * f (j + 1) := fun j hj =>
        hJ_step j (Finset.mem_of_mem_erase hj)
      have ih_app := ih J'.card (by omega) J' hJ'_nonempty h_step_sub rfl
      have h_min_eq := min'_erase_max' J hJ hJ'_nonempty
      rw [h_min_eq] at ih_app
      have h_mid : 3 ^ J'.card * f (J.min' hJ) ≤ 2 ^ J'.card * f m := by
        calc 3 ^ J'.card * f (J.min' hJ)
          _ ≤ 2 ^ J'.card * f (m' + 1) := ih_app
          _ ≤ 2 ^ J'.card * f m := Nat.mul_le_mul_left (2 ^ J'.card) h_f_le_m
      have h_mul3 : 3 * (3 ^ J'.card * f (J.min' hJ)) ≤ 3 * (2 ^ J'.card * f m) :=
        Nat.mul_le_mul_left 3 h_mid
      have h_step_ring : 3 * (2 ^ J'.card * f m) = 2 ^ J'.card * (3 * f m) := by ring
      have h_trans : 2 ^ J'.card * (3 * f m) ≤ 2 ^ J'.card * (2 * f (m + 1)) :=
        Nat.mul_le_mul_left (2 ^ J'.card) h_step_m
      have h_combined : 3 * (3 ^ J'.card * f (J.min' hJ)) ≤ 2 ^ J'.card * (2 * f (m + 1)) := by
        rw [h_step_ring] at h_mul3
        exact h_mul3.trans h_trans
      have h_pow3_succ : 3 * (3 ^ J'.card * f (J.min' hJ)) = 3 ^ J.card * f (J.min' hJ) := by
        have h_sub : J.card = J'.card + 1 := by omega
        conv_rhs => rw [h_sub]
        rw [pow_succ]
        ring
      have h_pow2_succ : 2 ^ J'.card * (2 * f (m + 1)) = 2 ^ J.card * f (m + 1) := by
        have h_sub : J.card = J'.card + 1 := by omega
        conv_rhs => rw [h_sub]
        rw [pow_succ]
        ring
      rw [h_pow3_succ, h_pow2_succ] at h_combined
      exact h_combined

/-- D1 Abstract Multiplicative Step Counting on Finset:
    Any set of marked steps where 3*f(j) ≤ 2*f(j+1) has cardinality bounded by p16MultBudget t. -/
theorem card_mult_growth_steps_le
    (f : ℕ → ℕ) (hf_mono : ∀ a b, a ≤ b → f a ≤ f b)
    (t : ℕ) (hf_pos : ∀ j, 1 ≤ f j) (hf_le : ∀ j, f j ≤ t)
    (J : Finset ℕ)
    (hJ_step : ∀ j ∈ J, 3 * f j ≤ 2 * f (j + 1)) :
    J.card ≤ p16MultBudget t := by
  by_cases hJ : J.Nonempty
  · have h_grow := finset_mult_growth f hf_mono J hJ hJ_step
    have hf_min_pos : 1 ≤ f (J.min' hJ) := hf_pos (J.min' hJ)
    have hf_max_le : f ((J.max' hJ) + 1) ≤ t := hf_le ((J.max' hJ) + 1)
    have h_3q : 3 ^ J.card ≤ 2 ^ J.card * t := by
      calc 3 ^ J.card
        _ ≤ 3 ^ J.card * f (J.min' hJ) := by
          have := Nat.mul_le_mul_left (3 ^ J.card) hf_min_pos
          omega
        _ ≤ 2 ^ J.card * f ((J.max' hJ) + 1) := h_grow
        _ ≤ 2 ^ J.card * t := Nat.mul_le_mul_left (2 ^ J.card) hf_max_le
    let L := Nat.log2 t + 1
    have ht_lt : t < 2 ^ L := lt_two_pow_succ_log2 t
    have h_q_le := mult_step_count_bound J.card t L ht_lt h_3q
    dsimp [p16MultBudget]
    omega
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hJ
    rw [hJ, Finset.card_empty]
    exact Nat.zero_le _

lemma finset_linear_growth (f : ℕ → ℕ) (hf_mono : ∀ a b, a ≤ b → f a ≤ f b)
    (M : ℕ) (J : Finset ℕ) (V : ℕ)
    (hJ_le : ∀ j ∈ J, 8 * f j ≤ V)
    (hJ_step : ∀ j ∈ J, 8 * f j + M ≤ 8 * f (j + 1)) :
    J.card * M ≤ V + M := by
  generalize hk : J.card = k
  induction k using Nat.strong_induction_on generalizing J V with
  | h n ih =>
    subst hk
    by_cases hJ : J.Nonempty
    · have hJ_pos : 0 < J.card := Finset.card_pos.mpr hJ
      by_cases hn1 : J.card = 1
      · rw [hn1, one_mul]
        exact Nat.le_add_left M V
      · have hn2 : 2 ≤ J.card := by omega
        let m := J.max' hJ
        have hm_in : m ∈ J := Finset.max'_mem J hJ
        let J' := J.erase m
        have hJ'_card : J'.card = J.card - 1 := Finset.card_erase_of_mem hm_in
        have hJ'_nonempty : J'.Nonempty := Finset.card_pos.mp (by rw [hJ'_card]; omega)
        let m' := J'.max' hJ'_nonempty
        have hm'_in' : m' ∈ J' := Finset.max'_mem J' hJ'_nonempty
        have hm'_in : m' ∈ J := Finset.mem_of_mem_erase hm'_in'
        have hm'_ne : m' ≠ m := Finset.ne_of_mem_erase hm'_in'
        have hm'_le_m : m' ≤ m := Finset.le_max' J m' hm'_in
        have hm'_lt_m : m' < m := lt_of_le_of_ne hm'_le_m hm'_ne
        have hm'_succ_le : m' + 1 ≤ m := hm'_lt_m
        have h_f_le_m : f (m' + 1) ≤ f m := hf_mono (m' + 1) m hm'_succ_le
        have h_step_m' := hJ_step m' hm'_in
        have hm_bound : 8 * f m ≤ V := hJ_le m hm_in
        have hm'_le_V_sub : 8 * f m' + M ≤ V := by
          calc 8 * f m' + M
            _ ≤ 8 * f (m' + 1) := h_step_m'
            _ ≤ 8 * f m := Nat.mul_le_mul_left 8 h_f_le_m
            _ ≤ V := hm_bound
        let V' := V - M
        have hJ'_le : ∀ j ∈ J', 8 * f j ≤ V' := by
          intro j hj
          have hj_in : j ∈ J := Finset.mem_of_mem_erase hj
          have hj_le_m' : j ≤ m' := Finset.le_max' J' j hj
          have h_f_le : f j ≤ f m' := hf_mono j m' hj_le_m'
          dsimp [V']
          omega
        have hJ'_step : ∀ j ∈ J', 8 * f j + M ≤ 8 * f (j + 1) := fun j hj =>
          hJ_step j (Finset.mem_of_mem_erase hj)
        have ih_app := ih J'.card (by omega) J' V' hJ'_le hJ'_step rfl
        have h_card_split : J.card * M = J'.card * M + M := by
          have h_sub : J.card = J'.card + 1 := by omega
          conv_lhs => rw [h_sub]
          ring
        rw [h_card_split]
        dsimp [V'] at ih_app
        omega
    · rw [Finset.nonempty_iff_ne_empty, not_not] at hJ
      rw [hJ, Finset.card_empty, Nat.zero_mul]
      exact Nat.zero_le _

/-- D2 Abstract Linear Step Counting on Finset:
    Any set of marked steps where f(j) ≤ U and 8*f(j) + M ≤ 8*f(j+1)
    has cardinality bounded by p16LinearBudget U M. -/
theorem card_linear_growth_steps_le
    (f : ℕ → ℕ) (hf_mono : ∀ a b, a ≤ b → f a ≤ f b)
    (U M : ℕ) (hM : 0 < M)
    (J : Finset ℕ)
    (hJ_le_U : ∀ j ∈ J, f j ≤ U)
    (hJ_step : ∀ j ∈ J, 8 * f j + M ≤ 8 * f (j + 1)) :
    J.card ≤ p16LinearBudget U M := by
  by_cases hq : J.card ≤ 1
  · have h_bud : 1 ≤ p16LinearBudget U M := by
      dsimp [p16LinearBudget]
      exact Nat.le_add_left 1 (8 * U / M)
    exact hq.trans h_bud
  have h_bound := finset_linear_growth f hf_mono M J (8 * U)
    (fun j hj => by have := hJ_le_U j hj; omega) hJ_step
  have h_split : J.card * M = (J.card - 1) * M + M := by
    have h_sub : J.card = (J.card - 1) + 1 := by omega
    conv_lhs => rw [h_sub]
    ring
  rw [h_split] at h_bound
  have h_sub : (J.card - 1) * M ≤ 8 * U := by omega
  have h_div : J.card - 1 ≤ 8 * U / M := (Nat.le_div_iff_mul_le hM).mpr h_sub
  dsimp [p16LinearBudget]
  omega

/-- Combined block budget bound: if J is partitioned into multiplicative and linear steps,
    its cardinality is bounded by p16BlockBudget t U M. -/
theorem card_partition_le_p16BlockBudget
    (t U M : ℕ) (J J_mult J_lin : Finset ℕ)
    (h_cover : J ⊆ J_mult ∪ J_lin)
    (h_mult : J_mult.card ≤ p16MultBudget t)
    (h_lin : J_lin.card ≤ p16LinearBudget U M) :
    J.card ≤ p16BlockBudget t U M := by
  have h_le := Finset.card_le_card h_cover
  have h_union := Finset.card_union_le J_mult J_lin
  dsimp [p16BlockBudget]
  omega

/-!
### Modulo Injectivity & Candidate Cardinality Preservation
-/

lemma injOn_scaled_of_injOn (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (A : Finset ℕ)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod t)) (A : Set ℕ))
    (B : Finset ℕ) (hBA : B ⊆ A) (hB_dvd : ∀ a ∈ B, g ∣ a) :
    Set.InjOn (fun a : ℕ => ((a / g : ℕ) : ZMod (t / g))) (B : Set ℕ) := by
  intro a ha b hb hab
  have ha_A : a ∈ (A : Set ℕ) := Finset.mem_coe.mpr (hBA (Finset.mem_coe.mp ha))
  have hb_A : b ∈ (A : Set ℕ) := Finset.mem_coe.mpr (hBA (Finset.mem_coe.mp hb))
  have ha_dvd : g ∣ a := hB_dvd a (Finset.mem_coe.mp ha)
  have hb_dvd : g ∣ b := hB_dvd b (Finset.mem_coe.mp hb)
  have htg_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd ht hdvd) hg
  have inst1 : NeZero (t / g) := ⟨by omega⟩
  have inst2 : NeZero t := ⟨by omega⟩
  rw [ZMod.natCast_eq_natCast_iff] at hab
  have h_mul := Nat.ModEq.mul_right' g hab
  rw [Nat.div_mul_cancel ha_dvd, Nat.div_mul_cancel hb_dvd, Nat.div_mul_cancel hdvd] at h_mul
  have hab_t : (a : ZMod t) = (b : ZMod t) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact h_mul
  exact h_inj ha_A hb_A hab_t

lemma card_image_scaled_of_injOn (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (A : Finset ℕ)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod t)) (A : Set ℕ))
    (B : Finset ℕ) (hBA : B ⊆ A) (hB_dvd : ∀ a ∈ B, g ∣ a) :
    (B.image (fun a => ((a / g : ℕ) : ZMod (t / g)))).card = B.card := by
  exact Finset.card_image_of_injOn (injOn_scaled_of_injOn t g ht hg hdvd A h_inj B hBA hB_dvd)

/-!
### Range 1 Single-Step Growth Bound
-/

lemma three_mul_le_two_mul_add_of_gt_half (s d : ℕ) (hd : s / 2 < d) :
    3 * s ≤ 2 * (s + d) := by
  have hd_ge : s / 2 + 1 ≤ d := hd
  have h_two_div : s ≤ 2 * (s / 2) + 1 := by
    have := (Nat.div_add_mod s 2).symm
    have h_mod : s % 2 < 2 := Nat.mod_lt s (by decide)
    omega
  calc 3 * s
    _ = 2 * s + s := by ring
    _ ≤ 2 * s + (2 * (s / 2) + 1) := by omega
    _ ≤ 2 * s + (2 * (s / 2) + 2) := by omega
    _ = 2 * s + 2 * (s / 2 + 1) := by ring
    _ ≤ 2 * s + 2 * d := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hd_ge) (2 * s)
    _ = 2 * (s + d) := by ring

lemma exists_candidate_range1_growth {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (hS_pos : 0 < S.card)
    (B : Finset ℕ) (f : ℕ → G) (h_inj : Set.InjOn f (B : Set ℕ))
    (h_range1 : 2 * S.card < B.card) :
    ∃ a ∈ B, 3 * S.card ≤ 2 * (S.card + delta S (f a)) := by
  have h_small := card_smallGrowth_half_le S hS_pos
  have h_img_card : (B.image f).card = B.card := Finset.card_image_of_injOn h_inj
  have h_not_sub : ¬ B.image f ⊆ smallGrowth S (S.card / 2) := by
    intro h_sub
    have h_le := Finset.card_le_card h_sub
    rw [h_img_card] at h_le
    omega
  rw [Finset.subset_iff] at h_not_sub
  push Not at h_not_sub
  rcases h_not_sub with ⟨x, hx_img, hx_not_small⟩
  rcases Finset.mem_image.mp hx_img with ⟨a, ha_B, rfl⟩
  simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at hx_not_small
  push Not at hx_not_small
  have h_step := three_mul_le_two_mul_add_of_gt_half S.card (delta S (f a)) hx_not_small
  exact ⟨a, ha_B, h_step⟩

/-!
### Monotonicity of Iterated Sumsets and Small Growth
-/

/-- Subset sum cardinality is bounded by the modulus t. -/
lemma card_subsetSumsMod_le_modulus (t : ℕ) (ht : 0 < t) (A : Finset ℕ) :
    (subsetSumsMod t A).card ≤ t := by
  have : NeZero t := ⟨by omega⟩
  have h_sub : subsetSumsMod t A ⊆ Finset.univ := Finset.subset_univ _
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_univ, ZMod.card t] at h_le
  exact h_le

lemma iterSum_mono_set {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} (hAB : A ⊆ B) (k : ℕ) :
    iterSum k A ⊆ iterSum k B := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    simp only [iterSum_succ]
    exact sumset_subset_sumset ih hAB

lemma smallGrowth_mono {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) {D1 D2 : ℕ} (hD : D1 ≤ D2) :
    smallGrowth S D1 ⊆ smallGrowth S D2 := by
  intro x hx
  simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.trans hD

/-!
### Range 2 Candidate Growth Arithmetic & Reduction (Phase U2)
-/

lemma k_mul_e_le_half_s (s b : ℕ) (hb_pos : 0 < b) (hb_le : b ≤ 2 * s) :
    (4 * s / b) * ((b - 1) / 8) ≤ s / 2 := by
  set k := 4 * s / b
  set e := (b - 1) / 8
  have he : 8 * e ≤ b - 1 := Nat.mul_div_le (b - 1) 8
  have hk : k * b ≤ 4 * s := Nat.div_mul_le_self (4 * s) b
  have hk2 : 2 ≤ k := by
    have : 2 * b ≤ 4 * s := by omega
    exact (Nat.le_div_iff_mul_le hb_pos).mpr this
  have hke : 8 * (k * e) ≤ 4 * s - 2 := by
    calc 8 * (k * e)
      _ = k * (8 * e) := by ring
      _ ≤ k * (b - 1) := Nat.mul_le_mul_left k he
      _ = k * b - k := by rw [Nat.mul_sub_left_distrib, mul_one]
      _ ≤ 4 * s - 2 := by omega
  have h_div : k * e ≤ (4 * s - 2) / 8 := Nat.le_div_iff_mul_le (by decide) |>.mpr (by omega)
  have h_div2 : (4 * s - 2) / 8 ≤ s / 2 := by omega
  exact h_div.trans h_div2

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Range 2 Single-Step Growth:
    For any candidate set Q with Q.card ≤ 2 * S.card, either some candidate a ∈ Q
    satisfies Q.card ≤ 8 * delta S a, or the iterated sumset yields an arithmetic contradiction. -/
theorem exists_candidate_range2_growth_of_iterSum_growth
    (N : ℕ) [NeZero N]
    (S Q : Finset (ZMod N))
    (hS : 0 < S.card)
    (hS_half : 2 * S.card < N)
    (hQ : 0 < Q.card)
    (hgen : AddSubgroup.closure (Q : Set (ZMod N)) = ⊤)
    (hrange : Q.card ≤ 2 * S.card)
    (h_u1 : ∀ (C : Finset (ZMod N)), (0 : ZMod N) ∈ C → AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k → (iterSum k C).card = N ∨ (k + 1) * C.card ≤ 2 * (iterSum k C).card) :
    ∃ a ∈ Q, Q.card ≤ 8 * delta S a := by
  by_contra! h_contra
  set s := S.card
  set b := Q.card
  set e := (b - 1) / 8
  set k := 4 * s / b
  have hk1 : 1 ≤ k := by
    have : 1 * b ≤ 4 * s := by omega
    exact (Nat.le_div_iff_mul_le hQ).mpr this
  set C : Finset (ZMod N) := insert 0 Q
  have h0 : (0 : ZMod N) ∈ C := Finset.mem_insert_self 0 Q
  have hQC : (Q : Set (ZMod N)) ⊆ (C : Set (ZMod N)) := by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    exact Finset.mem_insert_of_mem hx
  have hgenC : AddSubgroup.closure (C : Set (ZMod N)) = ⊤ := by
    rw [eq_top_iff]
    rw [← hgen]
    exact AddSubgroup.closure_mono hQC
  have hb_le_C : b ≤ C.card := by
    have : Q ⊆ C := Finset.subset_insert 0 Q
    exact Finset.card_le_card this
  have hC_sub : C ⊆ smallGrowth S e := by
    intro x hx
    have hx_ins : x ∈ insert 0 Q := hx
    rw [Finset.mem_insert] at hx_ins
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx_ins with rfl | hxQ
    · rw [delta_zero]
      omega
    · have h_lt := h_contra x hxQ
      omega
  have h_iter_sub : iterSum k C ⊆ smallGrowth S (k * e) := by
    have h1 := iterSum_mono_set hC_sub k
    have h2 := iterSum_smallGrowth_subset S e k
    exact h1.trans h2
  have h_ke : k * e ≤ s / 2 := k_mul_e_le_half_s s b hQ hrange
  have h_small_sub : smallGrowth S (k * e) ⊆ smallGrowth S (s / 2) :=
    smallGrowth_mono S h_ke
  have h_iter_in_half : iterSum k C ⊆ smallGrowth S (s / 2) :=
    h_iter_sub.trans h_small_sub
  have h_iter_card : (iterSum k C).card ≤ 2 * s := by
    have h_le := Finset.card_le_card h_iter_in_half
    have h_half := card_smallGrowth_half_le S hS
    exact h_le.trans h_half
  have h_not_full : (iterSum k C).card ≠ N := by
    omega
  have h_u1_res := h_u1 C h0 hgenC k hk1
  rcases h_u1_res with h_eq_N | h_bound
  · exact h_not_full h_eq_N
  · have h_contr : (k + 1) * b ≤ 4 * s := by
      calc (k + 1) * b
        _ ≤ (k + 1) * C.card := Nat.mul_le_mul_left (k + 1) hb_le_C
        _ ≤ 2 * (iterSum k C).card := h_bound
        _ ≤ 2 * (2 * s) := Nat.mul_le_mul_left 2 h_iter_card
        _ = 4 * s := by ring
    have h_gt : 4 * s < (k + 1) * b := floor_mul_succ_gt s b hQ
    omega

/-!
### Quotient Coordinates, Scaled Embedding and Delta Preservation (Phase U3)
-/

/-- Scaled embedding from ZMod (t / g) to ZMod t via multiplication by g. -/
def zmodScale (t g : ℕ) (x : ZMod (t / g)) : ZMod t :=
  (g * x.val : ℕ)

lemma zmodScale_zero (t g : ℕ) : zmodScale t g 0 = 0 := by
  dsimp [zmodScale]
  simp

lemma zmodScale_add (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (x y : ZMod (t / g)) :
    zmodScale t g (x + y) = zmodScale t g x + zmodScale t g y := by
  dsimp [zmodScale]
  have htg_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd ht hdvd) hg
  have inst1 : NeZero (t / g) := ⟨by omega⟩
  have inst2 : NeZero t := ⟨by omega⟩
  rw [← Nat.cast_add]
  rw [ZMod.natCast_eq_natCast_iff]
  have h_val : (x + y).val = (x.val + y.val) % (t / g) := ZMod.val_add x y
  rw [h_val]
  rw [← Nat.mul_mod_mul_left]
  rw [Nat.mul_div_cancel' hdvd]
  have h_ring : g * (x.val + y.val) = g * x.val + g * y.val := by ring
  rw [h_ring]
  exact Nat.mod_modEq (g * x.val + g * y.val) t

lemma zmodScale_injective (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) :
    Function.Injective (zmodScale t g) := by
  intro x y hxy
  dsimp [zmodScale] at hxy
  have htg_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd ht hdvd) hg
  have inst1 : NeZero (t / g) := ⟨by omega⟩
  have inst2 : NeZero t := ⟨by omega⟩
  rw [ZMod.natCast_eq_natCast_iff] at hxy
  have hg_ne : g ≠ 0 := by omega
  have ht_eq : t = (t / g) * g := (Nat.div_mul_cancel hdvd).symm
  set xv := x.val
  set yv := y.val
  rw [mul_comm g xv, mul_comm g yv, ht_eq] at hxy
  have h_cancel : xv ≡ yv [MOD t / g] := Nat.ModEq.mul_right_cancel' hg_ne hxy
  have hx_lt : xv < t / g := ZMod.val_lt x
  have hy_lt : yv < t / g := ZMod.val_lt y
  have h_eq : xv = yv := by
    rw [Nat.ModEq] at h_cancel
    rw [Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at h_cancel
    exact h_cancel
  exact ZMod.val_injective (t / g) h_eq

lemma zmodScale_natCast_div (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (a : ℕ) (ha : g ∣ a) :
    zmodScale t g ((a / g : ℕ) : ZMod (t / g)) = (a : ZMod t) := by
  dsimp [zmodScale]
  have htg_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd ht hdvd) hg
  have inst1 : NeZero (t / g) := ⟨by omega⟩
  have inst2 : NeZero t := ⟨by omega⟩
  rw [ZMod.natCast_eq_natCast_iff]
  rw [ZMod.val_natCast]
  rw [← Nat.mul_mod_mul_left]
  rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hdvd]
  exact Nat.mod_modEq a t

lemma translate_image_zmodScale (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t)
    (S : Finset (ZMod (t / g))) (x : ZMod (t / g)) :
    translate (S.image (zmodScale t g)) (zmodScale t g x) =
      (translate S x).image (zmodScale t g) := by
  dsimp [translate]
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro s _
  exact (zmodScale_add t g ht hg hdvd s x).symm

lemma delta_image_zmodScale (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t)
    (S : Finset (ZMod (t / g))) (x : ZMod (t / g)) :
    delta (S.image (zmodScale t g)) (zmodScale t g x) = delta S x := by
  dsimp [delta]
  have h_inj := zmodScale_injective t g ht hg hdvd
  rw [translate_image_zmodScale t g ht hg hdvd]
  rw [← Finset.image_sdiff _ _ h_inj]
  rw [Finset.card_image_of_injective _ h_inj]

lemma subsetSums_empty : subsetSums (∅ : Finset ℕ) = {0} := by
  dsimp [subsetSums]
  simp

lemma subsetSumsMod_empty (d : ℕ) : subsetSumsMod d (∅ : Finset ℕ) = {0} := by
  dsimp [subsetSumsMod]
  rw [subsetSums_empty]
  simp

/-- Scaling equality for tracked subset sums: the scaled set sums in ZMod (t/g)
    embed under zmodScale t g onto the unscaled subset sums in ZMod t. -/
theorem subsetSumsMod_image_zmodScale
    (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hgt : g ∣ t)
    (D : Finset ℕ) (hD : ∀ a ∈ D, g ∣ a) :
    (subsetSumsMod (t / g) (D.image (fun a => a / g))).image (zmodScale t g) =
      subsetSumsMod t D := by
  induction D using Finset.induction_on with
  | empty =>
    simp only [Finset.image_empty, subsetSumsMod_empty]
    ext x
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨y, rfl, rfl⟩
      exact zmodScale_zero t g
    · rintro rfl
      exact ⟨0, rfl, zmodScale_zero t g⟩
  | insert a D ha ih =>
    have ha_dvd : g ∣ a := hD a (Finset.mem_insert_self a D)
    have hD_dvd : ∀ x ∈ D, g ∣ x := fun x hx => hD x (Finset.mem_insert_of_mem hx)
    have ih_app := ih hD_dvd
    have ha_div_not : a / g ∉ D.image (fun x => x / g) := by
      intro h_mem
      rcases Finset.mem_image.mp h_mem with ⟨b, hb, h_eq⟩
      have hb_dvd : g ∣ b := hD_dvd b hb
      have h_ab : a = b := by
        calc a = (a / g) * g := (Nat.div_mul_cancel ha_dvd).symm
             _ = (b / g) * g := by rw [h_eq]
             _ = b := Nat.div_mul_cancel hb_dvd
      subst h_ab
      exact ha hb
    rw [Finset.image_insert]
    rw [subsetSumsMod_insert (t / g) (D.image (fun x => x / g)) (a / g) ha_div_not]
    rw [subsetSumsMod_insert t D a ha]
    rw [Finset.image_union]
    rw [ih_app]
    congr 1
    rw [← ih_app]
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro r _
    dsimp
    rw [zmodScale_add t g ht hg hgt r ((a / g : ℕ) : ZMod (t / g))]
    rw [zmodScale_natCast_div t g ht hg hgt a ha_dvd]

/-- Scaled tracked fiber multiples sums in quotient ring ZMod (t / g). -/
def scaledSelectedSums (t g : ℕ) (E : Finset ℕ) : Finset (ZMod (t / g)) :=
  subsetSumsMod (t / g)
    ((E.filter (fun a => g ∣ a)).image (fun a => a / g))

/-- Bridge 1: Image of scaledSelectedSums under zmodScale equals selectedMultiplesSums. -/
theorem scaledSelectedSums_image_zmodScale (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (E : Finset ℕ) :
    (scaledSelectedSums t g E).image (zmodScale t g) = selectedMultiplesSums t g E := by
  dsimp [scaledSelectedSums, selectedMultiplesSums]
  exact subsetSumsMod_image_zmodScale t g ht hg hdvd (E.filter (fun a => g ∣ a))
    (fun a ha => (Finset.mem_filter.mp ha).2)

/-- Bridge 2: Cardinality of scaledSelectedSums equals cardinality of selectedMultiplesSums. -/
theorem card_scaledSelectedSums_eq (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t) (E : Finset ℕ) :
    (scaledSelectedSums t g E).card = (selectedMultiplesSums t g E).card := by
  have h_img := scaledSelectedSums_image_zmodScale t g ht hg hdvd E
  have h_inj := zmodScale_injective t g ht hg hdvd
  rw [← h_img]
  exact (Finset.card_image_of_injective _ h_inj).symm

/-- Bridge 3: Delta preservation between quotient and full modulus for multiples of g. -/
theorem delta_scaledSelectedSums_eq (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hdvd : g ∣ t)
    (E : Finset ℕ) (a : ℕ) (ha : g ∣ a) :
    delta (scaledSelectedSums t g E) ((a / g : ℕ) : ZMod (t / g)) =
      delta (selectedMultiplesSums t g E) (a : ZMod t) := by
  have h_img := scaledSelectedSums_image_zmodScale t g ht hg hdvd E
  have h_delta := delta_image_zmodScale t g ht hg hdvd (scaledSelectedSums t g E) ((a / g : ℕ) : ZMod (t / g))
  rw [h_img, zmodScale_natCast_div t g ht hg hdvd a ha] at h_delta
  exact h_delta.symm

lemma closure_eq_top_of_one_mem {n : ℕ} [NeZero n] (s : Set (ZMod n))
    (h1 : (1 : ZMod n) ∈ AddSubgroup.closure s) :
    AddSubgroup.closure s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x.val • (1 : ZMod n) := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [hx]
  exact (AddSubgroup.closure s).nsmul_mem h1 x.val

/-!
### Modular GCD and Subgroup Generation (Phase B2)
-/

/-- The modular image of the greatest common divisor of two natural numbers
    belongs to any additive subgroup containing their modular images. -/
lemma nat_gcd_cast_mem_addSubgroup
    (N : ℕ) (H : AddSubgroup (ZMod N))
    (a b : ℕ) (ha : (a : ZMod N) ∈ H) (hb : (b : ZMod N) ∈ H) :
    (Nat.gcd a b : ZMod N) ∈ H := by
  have h_bezout := Nat.gcd_eq_gcd_ab a b
  have h_cast : ((Nat.gcd a b : ℤ) : ZMod N) =
      (((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) : ZMod N) := by
    rw [← h_bezout]
  push_cast at h_cast
  rw [h_cast]
  have ha_zsmul : Nat.gcdA a b • (a : ZMod N) ∈ H := H.zsmul_mem ha (Nat.gcdA a b)
  have hb_zsmul : Nat.gcdB a b • (b : ZMod N) ∈ H := H.zsmul_mem hb (Nat.gcdB a b)
  rw [zsmul_eq_mul, mul_comm] at ha_zsmul
  rw [zsmul_eq_mul, mul_comm] at hb_zsmul
  exact H.add_mem ha_zsmul hb_zsmul

/-- The modular image of the gcd of a finite set belongs to any additive subgroup
    containing the modular images of all its elements. -/
lemma finset_gcd_cast_mem_addSubgroup
    (N : ℕ) (H : AddSubgroup (ZMod N))
    (D : Finset ℕ) (hD : ∀ a ∈ D, (a : ZMod N) ∈ H) :
    ((D.gcd id : ℕ) : ZMod N) ∈ H := by
  induction D using Finset.induction_on with
  | empty =>
    rw [Finset.gcd_empty]
    simp only [Nat.cast_zero, H.zero_mem]
  | insert a D ha ih =>
    rw [Finset.gcd_insert]
    dsimp [id]
    have ha_mem : (a : ZMod N) ∈ H := hD a (Finset.mem_insert_self a D)
    have hD_mem : ∀ x ∈ D, (x : ZMod N) ∈ H := fun x hx => hD x (Finset.mem_insert_of_mem hx)
    have ih_app : ((D.gcd id : ℕ) : ZMod N) ∈ H := ih hD_mem
    exact nat_gcd_cast_mem_addSubgroup N H a (D.gcd id) ha_mem ih_app

/-- General generation theorem: if gcd(N, D.gcd id) = 1, then the modular image of D generates ZMod N. -/
theorem closure_natCast_image_eq_top_of_gcd_eq_one
    (N : ℕ) [NeZero N] (D : Finset ℕ)
    (hcop : Nat.gcd N (D.gcd id) = 1) :
    AddSubgroup.closure ((D.image (fun (a : ℕ) => (a : ZMod N))) : Set (ZMod N)) = ⊤ := by
  let H := AddSubgroup.closure ((D.image (fun (a : ℕ) => (a : ZMod N))) : Set (ZMod N))
  have h_elem : ∀ a ∈ D, (a : ZMod N) ∈ H := by
    intro a ha
    apply AddSubgroup.subset_closure
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have h_D_gcd : ((D.gcd id : ℕ) : ZMod N) ∈ H := finset_gcd_cast_mem_addSubgroup N H D h_elem
  have h_N : (N : ZMod N) ∈ H := by
    rw [CharP.cast_eq_zero (ZMod N) N]
    exact H.zero_mem
  have h_one_mod : ((Nat.gcd N (D.gcd id) : ℕ) : ZMod N) ∈ H :=
    nat_gcd_cast_mem_addSubgroup N H N (D.gcd id) h_N h_D_gcd
  rw [hcop] at h_one_mod
  simp only [Nat.cast_one] at h_one_mod
  exact closure_eq_top_of_one_mem ((D.image (fun (a : ℕ) => (a : ZMod N))) : Set (ZMod N)) h_one_mod

/-- Instantiation to the scaled candidate set:
    The quotient candidate set {a/g | a ∈ B} unconditionally generates ZMod (t / g). -/
theorem closure_scaled_candidate_eq_top
    (t : ℕ) (ht : 0 < t) (B : Finset ℕ) :
    let g := subgroupIndex t B
    let N := t / g
    AddSubgroup.closure ((B.image (fun (a : ℕ) => ((a / g : ℕ) : ZMod N))) : Set (ZMod N)) = ⊤ := by
  set g := subgroupIndex t B
  set N := t / g
  have hg_pos := subgroupIndex_pos t B ht
  have hg_dvd := subgroupIndex_dvd_modulus t B
  have hN_pos : 0 < N := Nat.div_pos (Nat.le_of_dvd ht hg_dvd) hg_pos
  have inst : NeZero N := ⟨by omega⟩
  have hcop := subgroupIndex_scaled_coprime t B ht
  have h_eq_image : (B.image (fun a => a / g)).image (fun (a : ℕ) => (a : ZMod N)) =
      B.image (fun a => ((a / g : ℕ) : ZMod N)) := by
    rw [Finset.image_image]
    rfl
  have h_gen := @closure_natCast_image_eq_top_of_gcd_eq_one N inst (B.image (fun a => a / g)) hcop
  rwa [h_eq_image] at h_gen

/-!
### Real Trajectory Potential & Growth Steps (Phase U4)
-/

/-- Sequence of chosen subsets is monotonic along the greedy iteration. -/
lemma greedySeq_E_mono (fc : FiniteConditions) {j1 j2 : ℕ} (hj : j1 ≤ j2) :
    (greedySeq fc j1).E ⊆ (greedySeq fc j2).E := by
  induction j2, hj using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n hjn ih =>
    have hn_step : (greedySeq fc n).E ⊆ (greedySeq fc (n + 1)).E := by
      dsimp [greedySeq]
      split_ifs with hn_lt hB
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
      · exact Finset.Subset.refl _
    exact ih.trans hn_step

/-- Trajectory potential: cardinality of selected multiples sums at step j. -/
noncomputable def f_g (fc : FiniteConditions) (g : ℕ) (j : ℕ) : ℕ :=
  (selectedMultiplesSums fc.t g (greedySeq fc j).E).card

lemma f_g_mono (fc : FiniteConditions) (g : ℕ) {j1 j2 : ℕ} (hj : j1 ≤ j2) :
    f_g fc g j1 ≤ f_g fc g j2 :=
  card_selectedMultiplesSums_le_of_subset fc.t g (greedySeq_E_mono fc hj)

lemma one_le_f_g (fc : FiniteConditions) (g : ℕ) (j : ℕ) :
    1 ≤ f_g fc g j :=
  one_le_card_selectedMultiplesSums fc.t g _

lemma f_g_le_t (fc : FiniteConditions) (g : ℕ) (j : ℕ) :
    f_g fc g j ≤ fc.t := by
  dsimp [f_g, selectedMultiplesSums]
  exact card_subsetSumsMod_le_modulus fc.t fc.ht_pos _

lemma f_g_succ_eq (fc : FiniteConditions) (j : ℕ) (hj : j ∈ growthSteps fc) :
    f_g fc ((greedySeq fc j).g fc.t) (j + 1) =
      f_g fc ((greedySeq fc j).g fc.t) j +
      delta (selectedMultiplesSums fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E)
        (greedyChoice fc.t fc.U (greedySeq fc j) ((greedySeq fc j).B_nonempty (by
          rw [card_greedySeq_E fc j (by
            simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
            omega)]
          have hj_lt : j < fc.K := by
            simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
            exact hj.1
          have : fc.K + fc.M ≤ fc.A.card := fc.hK_add_M_le
          omega)) : ZMod fc.t) := by
  have hj_lt : j < fc.K := by
    simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
    exact hj.1
  have h_grow : isGrowthStage fc.t fc.U (greedySeq fc j) := by
    simp only [growthSteps, Finset.mem_filter] at hj
    exact hj.2
  have hB : (greedySeq fc j).B.Nonempty := by
    apply (greedySeq fc j).B_nonempty
    rw [card_greedySeq_E fc j (by omega)]
    have : fc.K + fc.M ≤ fc.A.card := fc.hK_add_M_le
    omega
  dsimp [f_g, greedySeq]
  rw [if_pos hj_lt, dif_pos hB]
  dsimp [nextState]
  have ha_dvd : (greedySeq fc j).g fc.t ∣ greedyChoice fc.t fc.U (greedySeq fc j) hB := by
    apply subgroupIndex_dvd_mem fc.t (greedySeq fc j).B
    exact greedyChoice_mem fc.t fc.U (greedySeq fc j) hB
  have ha_not : greedyChoice fc.t fc.U (greedySeq fc j) hB ∉ (greedySeq fc j).E := by
    have h_mem := greedyChoice_mem fc.t fc.U (greedySeq fc j) hB
    exact (Finset.mem_sdiff.mp h_mem).2
  exact card_selectedMultiplesSums_insert_eq fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E
    (greedyChoice fc.t fc.U (greedySeq fc j) hB) ha_not ha_dvd

lemma trajectory_growth_step_range1 (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (j : ℕ) (hj : j ∈ growthSteps fc)
    (hrange1 : 2 * f_g fc ((greedySeq fc j).g fc.t) j < (greedySeq fc j).B.card) :
    3 * f_g fc ((greedySeq fc j).g fc.t) j ≤ 2 * f_g fc ((greedySeq fc j).g fc.t) (j + 1) := by
  have : NeZero fc.t := ⟨by have := fc.ht_pos; omega⟩
  have h_grow : isGrowthStage fc.t fc.U (greedySeq fc j) := by
    simp only [growthSteps, Finset.mem_filter] at hj; exact hj.2
  have hB : (greedySeq fc j).B.Nonempty := by
    apply (greedySeq fc j).B_nonempty
    rw [card_greedySeq_E fc j (by
      simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj; omega)]
    have : fc.K + fc.M ≤ fc.A.card := fc.hK_add_M_le
    simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
    omega
  have h_inj_B : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) ((greedySeq fc j).B : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have ha_A : a ∈ fc.A := (Finset.mem_sdiff.mp ha).1
    have hb_A : b ∈ fc.A := (Finset.mem_sdiff.mp hb).1
    exact h_inj (Finset.mem_coe.mpr ha_A) (Finset.mem_coe.mpr hb_A) hab
  have h_step1 := exists_candidate_range1_growth
    (selectedMultiplesSums fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E)
    (card_selectedMultiplesSums_pos fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E)
    (greedySeq fc j).B (fun a => (a : ZMod fc.t)) h_inj_B hrange1
  rcases h_step1 with ⟨a, ha_B, h_growth_a⟩
  have h_choice_max := greedyChoice_growth_max fc.t fc.U (greedySeq fc j) hB h_grow a ha_B
  have h_step2 : 3 * f_g fc ((greedySeq fc j).g fc.t) j ≤
      2 * (f_g fc ((greedySeq fc j).g fc.t) j +
        delta (selectedMultiplesSums fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E)
          (greedyChoice fc.t fc.U (greedySeq fc j) hB : ZMod fc.t)) := by
    dsimp [f_g] at h_growth_a ⊢
    omega
  rw [f_g_succ_eq fc j hj]
  exact h_step2

lemma trajectory_growth_step_range2 (fc : FiniteConditions)
    (j : ℕ) (hj : j ∈ growthSteps fc)
    (_hrange2 : (greedySeq fc j).B.card ≤ 2 * f_g fc ((greedySeq fc j).g fc.t) j)
    (h_u2_growth : ∃ a ∈ (greedySeq fc j).B,
      (greedySeq fc j).B.card ≤ 8 * delta (selectedMultiplesSums fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E) (a : ZMod fc.t)) :
    8 * f_g fc ((greedySeq fc j).g fc.t) j + fc.M ≤ 8 * f_g fc ((greedySeq fc j).g fc.t) (j + 1) := by
  have h_grow : isGrowthStage fc.t fc.U (greedySeq fc j) := by
    simp only [growthSteps, Finset.mem_filter] at hj; exact hj.2
  have hB : (greedySeq fc j).B.Nonempty := by
    apply (greedySeq fc j).B_nonempty
    rw [card_greedySeq_E fc j (by
      simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj; omega)]
    have : fc.K + fc.M ≤ fc.A.card := fc.hK_add_M_le
    simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
    omega
  rcases h_u2_growth with ⟨a, ha_B, ha_bound⟩
  have h_choice_max := greedyChoice_growth_max fc.t fc.U (greedySeq fc j) hB h_grow a ha_B
  have h_M_le : fc.M ≤ (greedySeq fc j).B.card := by
    rw [(greedySeq fc j).card_B]
    rw [card_greedySeq_E fc j (by
      simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj; omega)]
    have : fc.K + fc.M ≤ fc.A.card := fc.hK_add_M_le
    simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj
    omega
  rw [f_g_succ_eq fc j hj]
  omega

/-- Scaled fiber bound: strictly less than quotient modulus N = t / g. -/
lemma small_fiber_card_mul_two_lt (fc : FiniteConditions) (g : ℕ) (hg_pos : 0 < g) (hg_le : g ≤ fc.gMax)
    (S_card : ℕ) (hS_le : S_card ≤ fc.U) :
    2 * S_card < fc.t / g := by
  have hU_lt := fc.h_small_fiber_bound
  have h_2gmax_pos : 0 < 2 * fc.gMax := by
    have := fc.hgMax_pos
    omega
  have hU_le : fc.U + 1 ≤ fc.t / (2 * fc.gMax) := hU_lt
  have h_mul : (fc.U + 1) * (2 * fc.gMax) ≤ fc.t :=
    (Nat.le_div_iff_mul_le h_2gmax_pos).mp hU_le
  have h_le_g : (2 * S_card + 2) * g ≤ (fc.U + 1) * (2 * fc.gMax) := by
    calc (2 * S_card + 2) * g
      _ ≤ (2 * fc.U + 2) * g := Nat.mul_le_mul_right g (by omega)
      _ = (fc.U + 1) * (2 * g) := by ring
      _ ≤ (fc.U + 1) * (2 * fc.gMax) := Nat.mul_le_mul_left (fc.U + 1) (by omega)
  have h_le_t : (2 * S_card + 2) * g ≤ fc.t := h_le_g.trans h_mul
  have h_div : 2 * S_card + 2 ≤ fc.t / g :=
    (Nat.le_div_iff_mul_le hg_pos).mpr h_le_t
  omega

/-- Deriving real Range 2 candidate from iterated sumset growth hypothesis U1. -/
theorem exists_trajectory_range2_candidate_of_iterSum_growth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card)
    (j : ℕ) (hj : j ∈ growthSteps fc)
    (hrange : (greedySeq fc j).B.card ≤ 2 * f_g fc ((greedySeq fc j).g fc.t) j) :
    ∃ a ∈ (greedySeq fc j).B,
      (greedySeq fc j).B.card ≤
        8 * delta (selectedMultiplesSums fc.t ((greedySeq fc j).g fc.t) (greedySeq fc j).E) (a : ZMod fc.t) := by
  have hj_growth : isGrowthStage fc.t fc.U (greedySeq fc j) := by
    simp only [growthSteps, Finset.mem_filter] at hj; exact hj.2
  have hj_lt : j < fc.K := by
    simp only [growthSteps, Finset.mem_filter, Finset.mem_range] at hj; exact hj.1
  have hj_card : (greedySeq fc j).E.card ≤ fc.K := by
    rw [card_greedySeq_E fc j (by omega)]
    omega
  have hM_le_B : fc.M ≤ (greedySeq fc j).B.card := (greedySeq fc j).B_card_ge hj_card
  have hB_sub_A : (greedySeq fc j).B ⊆ fc.A := Finset.sdiff_subset
  set g := (greedySeq fc j).g fc.t
  have hg_pos : 0 < g := subgroupIndex_pos fc.t (greedySeq fc j).B fc.ht_pos
  have hg_dvd : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t (greedySeq fc j).B
  have hg_le : g ≤ fc.gMax := fc.h_subgroup_le (greedySeq fc j).B hB_sub_A hM_le_B
  set N := fc.t / g
  have hN_pos : 0 < N := Nat.div_pos (Nat.le_of_dvd fc.ht_pos hg_dvd) hg_pos
  have instN : NeZero N := ⟨by omega⟩
  set S := scaledSelectedSums fc.t g (greedySeq fc j).E
  set Q := (greedySeq fc j).B.image (fun a => ((a / g : ℕ) : ZMod N))
  have hS_card_eq : S.card = (selectedMultiplesSums fc.t g (greedySeq fc j).E).card :=
    card_scaledSelectedSums_eq fc.t g fc.ht_pos hg_pos hg_dvd _
  have hS_pos : 0 < S.card := by
    rw [hS_card_eq]
    exact card_selectedMultiplesSums_pos fc.t g _
  have hS_le_U : (selectedMultiplesSums fc.t g (greedySeq fc j).E).card ≤ fc.U :=
    card_selectedMultiplesSums_le_U fc.t fc.U (greedySeq fc j) fc.ht_pos hj_growth
  have hS_half : 2 * S.card < N := by
    rw [hS_card_eq]
    exact small_fiber_card_mul_two_lt fc g hg_pos hg_le
      (selectedMultiplesSums fc.t g (greedySeq fc j).E).card hS_le_U
  have hB_dvd : ∀ a ∈ (greedySeq fc j).B, g ∣ a :=
    fun a ha => subgroupIndex_dvd_mem fc.t (greedySeq fc j).B ha
  have hQ_card_eq : Q.card = (greedySeq fc j).B.card :=
    card_image_scaled_of_injOn fc.t g fc.ht_pos hg_pos hg_dvd fc.A h_inj (greedySeq fc j).B hB_sub_A hB_dvd
  have hQ_pos : 0 < Q.card := by
    rw [hQ_card_eq]
    have := fc.hM_pos
    omega
  have hgen : AddSubgroup.closure (Q : Set (ZMod N)) = ⊤ :=
    closure_scaled_candidate_eq_top fc.t fc.ht_pos (greedySeq fc j).B
  have h_fg : f_g fc g j = S.card := by
    dsimp [f_g]
    rw [hS_card_eq]
  have hrange_Q : Q.card ≤ 2 * S.card := by
    rw [hQ_card_eq]
    rwa [h_fg] at hrange
  have h_u1_N : ∀ (C : Finset (ZMod N)), (0 : ZMod N) ∈ C → AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k → (iterSum k C).card = N ∨ (k + 1) * C.card ≤ 2 * (iterSum k C).card :=
    fun C h0 hgenC k hk => h_u1 N hN_pos C h0 hgenC k hk
  have h_cand := exists_candidate_range2_growth_of_iterSum_growth N S Q hS_pos hS_half hQ_pos hgen hrange_Q h_u1_N
  rcases h_cand with ⟨q, hq_Q, hq_bound⟩
  rcases Finset.mem_image.mp hq_Q with ⟨a, ha_B, rfl⟩
  use a, ha_B
  have ha_dvd : g ∣ a := hB_dvd a ha_B
  have h_delta_eq : delta S ((a / g : ℕ) : ZMod N) =
      delta (selectedMultiplesSums fc.t g (greedySeq fc j).E) (a : ZMod fc.t) :=
    delta_scaledSelectedSums_eq fc.t g fc.ht_pos hg_pos hg_dvd (greedySeq fc j).E a ha_dvd
  rw [hQ_card_eq] at hq_bound
  rw [h_delta_eq] at hq_bound
  exact hq_bound

/-- Range 2 trajectory growth step closed using the iterated sumset growth hypothesis U1. -/
lemma trajectory_growth_step_range2_of_iterSum_growth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card)
    (j : ℕ) (hj : j ∈ growthSteps fc)
    (hrange2 : (greedySeq fc j).B.card ≤ 2 * f_g fc ((greedySeq fc j).g fc.t) j) :
    8 * f_g fc ((greedySeq fc j).g fc.t) j + fc.M ≤ 8 * f_g fc ((greedySeq fc j).g fc.t) (j + 1) := by
  have h_cand := exists_trajectory_range2_candidate_of_iterSum_growth fc h_inj h_u1 j hj hrange2
  exact trajectory_growth_step_range2 fc j hj hrange2 h_cand

/-- Double counting fiber bound for finite sets. -/
lemma card_le_mul_of_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (N_blocks N_per_block : ℕ)
    (h_blocks : (S.image f).card ≤ N_blocks)
    (h_fibers : ∀ y ∈ S.image f, (S.filter (fun x => f x = y)).card ≤ N_per_block) :
    S.card ≤ N_blocks * N_per_block := by
  have h_sum := Finset.card_eq_sum_card_image f S
  rw [h_sum]
  have h_le : ∑ y ∈ S.image f, (S.filter (fun x => f x = y)).card ≤ ∑ y ∈ S.image f, N_per_block := by
    apply Finset.sum_le_sum
    intro y hy
    exact h_fibers y hy
  rw [Finset.sum_const, nsmul_eq_mul] at h_le
  have h_mul : (S.image f).card * N_per_block ≤ N_blocks * N_per_block :=
    Nat.mul_le_mul_right N_per_block h_blocks
  exact h_le.trans h_mul

/-- Subgroup index is monotone under divisibility along greedySeq:
    for any j ≤ k ≤ K, g(j) ∣ g(k). -/
lemma greedySeq_g_dvd (fc : FiniteConditions) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ fc.K) :
    (greedySeq fc j).g fc.t ∣ (greedySeq fc k).g fc.t := by
  induction k, hjk using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n hjn ih =>
    have hn_lt : n < fc.K := by omega
    have ih_n := ih (by omega)
    dsimp [greedySeq]
    rw [if_pos hn_lt]
    split_ifs with hB
    · exact ih_n.trans (nextState_g_dvd fc.t (greedySeq fc n) _ _)
    · exact ih_n

/-- Subgroup index is monotone in ≤ along greedySeq. -/
lemma greedySeq_g_le (fc : FiniteConditions) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ fc.K) :
    (greedySeq fc j).g fc.t ≤ (greedySeq fc k).g fc.t := by
  have hdvd := greedySeq_g_dvd fc j k hjk hk
  have hpos := subgroupIndex_pos fc.t (greedySeq fc k).B fc.ht_pos
  exact Nat.le_of_dvd hpos hdvd

/-- Strict increases in the subgroup index image double at each step. -/
lemma greedySeq_g_image_doubling (fc : FiniteConditions) (a b : ℕ)
    (ha : a ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t))
    (hb : b ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t))
    (h_lt : a < b) : 2 * a ≤ b := by
  simp only [Finset.mem_image, growthSteps, Finset.mem_filter, Finset.mem_range] at ha hb
  rcases ha with ⟨j1, ⟨hj1_lt, _⟩, rfl⟩
  rcases hb with ⟨j2, ⟨hj2_lt, _⟩, rfl⟩
  have hj : j1 < j2 := by
    by_contra h_not
    have : j2 ≤ j1 := by omega
    have h_le := greedySeq_g_le fc j2 j1 this (by omega)
    omega
  have hdvd := greedySeq_g_dvd fc j1 j2 (by omega) (by omega)
  have hpos := subgroupIndex_pos fc.t (greedySeq fc j1).B fc.ht_pos
  exact mul_two_le_of_dvd_of_lt hpos hdvd h_lt

/-- Every element in the subgroup index image is bounded by gMax. -/
lemma greedySeq_g_image_le_gMax (fc : FiniteConditions) (a : ℕ)
    (ha : a ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t)) :
    a ≤ fc.gMax := by
  simp only [Finset.mem_image, growthSteps, Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨j, ⟨hj_lt, _⟩, rfl⟩
  have hj_card : (greedySeq fc j).E.card ≤ fc.K := by
    rw [card_greedySeq_E fc j (by omega)]
    omega
  have hM := (greedySeq fc j).B_card_ge hj_card
  have hB_sub : (greedySeq fc j).B ⊆ fc.A := Finset.sdiff_subset
  exact fc.h_subgroup_le (greedySeq fc j).B hB_sub hM

/-- Bounding the cardinality of a finite set of positive integers with strict doubling. -/
lemma doubling_chain_finset_card_le (Y : Finset ℕ)
    (hY_pos : ∀ y ∈ Y, 0 < y)
    (h_doubling : ∀ a ∈ Y, ∀ b ∈ Y, a < b → 2 * a ≤ b)
    (gMax : ℕ) (hgMax : 0 < gMax) (hY_le : ∀ y ∈ Y, y ≤ gMax) :
    Y.card ≤ Nat.log2 gMax + 1 := by
  have h_ind : ∀ k, ∀ (Y : Finset ℕ), Y.card = k →
      (∀ y ∈ Y, 0 < y) →
      (∀ a ∈ Y, ∀ b ∈ Y, a < b → 2 * a ≤ b) →
      ∀ G, 0 < G → (∀ y ∈ Y, y ≤ G) →
      Y.card ≤ Nat.log2 G + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro Y hY_card hY_pos h_doubling G hG hY_le
      by_cases hk1 : Y.card ≤ 1
      · have : 0 ≤ Nat.log2 G := Nat.zero_le _
        omega
      · have hk2 : 2 ≤ Y.card := by omega
        have h_nonempty : Y.Nonempty := Finset.card_pos.mp (by omega)
        let m := Y.max' h_nonempty
        have hm_in : m ∈ Y := Finset.max'_mem Y h_nonempty
        have hm_le : m ≤ G := hY_le m hm_in
        let Y' := Y.erase m
        have hY'_card : Y'.card = Y.card - 1 := Finset.card_erase_of_mem hm_in
        have hY'_nonempty : Y'.Nonempty := Finset.card_pos.mp (by omega)
        let m' := Y'.max' hY'_nonempty
        have hm'_in' : m' ∈ Y' := Finset.max'_mem Y' hY'_nonempty
        have hm'_in : m' ∈ Y := Finset.mem_of_mem_erase hm'_in'
        have hm'_ne : m' ≠ m := Finset.ne_of_mem_erase hm'_in'
        have hm'_le_m : m' ≤ m := Finset.le_max' Y m' hm'_in
        have hm'_lt_m : m' < m := lt_of_le_of_ne hm'_le_m hm'_ne
        have h_double := h_doubling m' hm'_in m hm_in hm'_lt_m
        have hm'_le_div : m' ≤ G / 2 := by
          have : 2 * m' ≤ G := h_double.trans hm_le
          omega
        have hY'_le : ∀ y ∈ Y', y ≤ G / 2 := by
          intro y hy
          have hy_le_m' : y ≤ m' := Finset.le_max' Y' y hy
          exact hy_le_m'.trans hm'_le_div
        have h_sub_doubling : ∀ a ∈ Y', ∀ b ∈ Y', a < b → 2 * a ≤ b := by
          intro a ha b hb hlt
          exact h_doubling a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hlt
        have hY'_pos : ∀ y ∈ Y', 0 < y := fun y hy => hY_pos y (Finset.mem_of_mem_erase hy)
        have hm'_pos : 0 < m' := hY_pos m' hm'_in
        have h_double_G : 2 * m' ≤ G := h_double.trans hm_le
        have hG2 : 2 ≤ G := (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hm'_pos)).trans h_double_G
        have h_div_pos : 0 < G / 2 := Nat.div_pos hG2 (by decide)
        have ih_app := ih Y'.card (by omega) Y' rfl hY'_pos h_sub_doubling (G / 2) h_div_pos hY'_le
        have h_log : Nat.log2 G = Nat.log2 (G / 2) + 1 := by
          rw [Nat.log2_def G, if_pos hG2]
        omega
  exact h_ind Y.card Y rfl hY_pos h_doubling gMax hgMax hY_le

/-- Number of distinct subgroup indices in growthSteps is bounded by maxSubgroupBlocks. -/
lemma growthSteps_g_image_card_le (fc : FiniteConditions) :
    ((growthSteps fc).image (fun j => (greedySeq fc j).g fc.t)).card ≤ maxSubgroupBlocks fc.gMax := by
  dsimp [maxSubgroupBlocks]
  let Y := (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t)
  have hY_pos : ∀ y ∈ Y, 0 < y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, _, rfl⟩
    exact subgroupIndex_pos fc.t (greedySeq fc j).B fc.ht_pos
  have hY_le : ∀ y ∈ Y, y ≤ fc.gMax := fun y hy => greedySeq_g_image_le_gMax fc y hy
  have hY_doubling : ∀ a ∈ Y, ∀ b ∈ Y, a < b → 2 * a ≤ b := fun a ha b hb hlt =>
    greedySeq_g_image_doubling fc a b ha hb hlt
  exact doubling_chain_finset_card_le Y hY_pos hY_doubling fc.gMax fc.hgMax_pos hY_le

/-- Universal bound: growth steps count cannot exceed K. -/
lemma growthSteps_card_le_K (fc : FiniteConditions) :
    (growthSteps fc).card ≤ fc.K := by
  dsimp [growthSteps]
  have h_sub : (Finset.range fc.K).filter (fun j => isGrowthStage fc.t fc.U (greedySeq fc j)) ⊆ Finset.range fc.K :=
    Finset.filter_subset _ _
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_range] at h_le
  exact h_le

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Per-Block Budget Bound (Phase U5):
    Each subgroup index block in growthSteps has cardinality bounded by p16BlockBudget. -/
theorem growthSteps_block_card_le_p16BlockBudget
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (y : ℕ)
    (_hy : y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t))
    (h_range2 : ∀ j ∈ (growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y),
      (greedySeq fc j).B.card ≤ 2 * f_g fc y j →
      8 * f_g fc y j + fc.M ≤ 8 * f_g fc y (j + 1)) :
    ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤
      p16BlockBudget fc.t fc.U fc.M := by
  set J_y := (growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)
  set J_mult := J_y.filter (fun j => 2 * f_g fc y j < (greedySeq fc j).B.card)
  set J_lin := J_y.filter (fun j => ¬ (2 * f_g fc y j < (greedySeq fc j).B.card))
  have h_cover : J_y ⊆ J_mult ∪ J_lin := by
    intro j hj
    by_cases h : 2 * f_g fc y j < (greedySeq fc j).B.card
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hj, h⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hj, h⟩
  have h_mult_bound : J_mult.card ≤ p16MultBudget fc.t := by
    apply card_mult_growth_steps_le (f_g fc y) (fun a b hab => f_g_mono fc y hab) fc.t
      (one_le_f_g fc y) (f_g_le_t fc y) J_mult
    intro j hj
    have hj_Jy : j ∈ J_y := (Finset.mem_filter.mp hj).1
    have hj_r1 : 2 * f_g fc y j < (greedySeq fc j).B.card := (Finset.mem_filter.mp hj).2
    have hj_growth : j ∈ growthSteps fc := (Finset.mem_filter.mp hj_Jy).1
    have hj_g : (greedySeq fc j).g fc.t = y := (Finset.mem_filter.mp hj_Jy).2
    rw [← hj_g]
    exact trajectory_growth_step_range1 fc h_inj j hj_growth (by rwa [hj_g])
  have h_lin_bound : J_lin.card ≤ p16LinearBudget fc.U fc.M := by
    apply card_linear_growth_steps_le (f_g fc y) (fun a b hab => f_g_mono fc y hab)
      fc.U fc.M fc.hM_pos J_lin
    · intro j hj
      have hj_Jy : j ∈ J_y := (Finset.mem_filter.mp hj).1
      have hj_growth : j ∈ growthSteps fc := (Finset.mem_filter.mp hj_Jy).1
      have hj_g : (greedySeq fc j).g fc.t = y := (Finset.mem_filter.mp hj_Jy).2
      have h_grow : isGrowthStage fc.t fc.U (greedySeq fc j) := by
        simp only [growthSteps, Finset.mem_filter] at hj_growth; exact hj_growth.2
      dsimp [f_g]
      rw [← hj_g]
      exact card_selectedMultiplesSums_le_U fc.t fc.U (greedySeq fc j) fc.ht_pos h_grow
    · intro j hj
      have hj_Jy : j ∈ J_y := (Finset.mem_filter.mp hj).1
      have hj_not_r1 : ¬ (2 * f_g fc y j < (greedySeq fc j).B.card) := (Finset.mem_filter.mp hj).2
      have hj_le : (greedySeq fc j).B.card ≤ 2 * f_g fc y j := by omega
      exact h_range2 j hj_Jy hj_le
  exact card_partition_le_p16BlockBudget fc.t fc.U fc.M J_y J_mult J_lin h_cover h_mult_bound h_lin_bound

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Total Budget Master Theorem (Phase U6):
    Total growth steps are bounded by p16TotalBudget without h_fibers. -/
theorem growthSteps_card_le_p16Budget
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_range2 : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ∀ j ∈ (growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y),
        (greedySeq fc j).B.card ≤ 2 * f_g fc y j →
        8 * f_g fc y j + fc.M ≤ 8 * f_g fc y (j + 1)) :
    (growthSteps fc).card ≤ p16TotalBudget fc.t fc.gMax fc.U fc.M := by
  have h_blocks := growthSteps_g_image_card_le fc
  have h_fiber : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ p16BlockBudget fc.t fc.U fc.M := by
    intro y hy
    exact growthSteps_block_card_le_p16BlockBudget fc h_inj y hy (h_range2 y hy)
  exact card_le_mul_of_fiber_bound (growthSteps fc) (fun j => (greedySeq fc j).g fc.t)
    (maxSubgroupBlocks fc.gMax) (p16BlockBudget fc.t fc.U fc.M)
    h_blocks h_fiber

/-- Master derivation: Connecting p16TotalBudget to fc.B_growth via explicit numeric bound. -/
theorem growthSteps_card_le_budget_of_p16
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_range2 : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ∀ j ∈ (growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y),
        (greedySeq fc j).B.card ≤ 2 * f_g fc y j →
        8 * f_g fc y j + fc.M ≤ 8 * f_g fc y (j + 1)) :
    (growthSteps fc).card ≤ fc.B_growth :=
  (growthSteps_card_le_p16Budget fc h_inj h_range2).trans h_numeric

/-- CFP Lemma 5.6 Finite Core with p16 Logarithmic Budget (Phase U6 Master Theorem):
    The ad-hoc h_fibers bound is eliminated, replaced by the proven block budget. -/
theorem cfp_lemma_5_6_finite_core_of_p16 (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_range2 : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ∀ j ∈ (growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y),
        (greedySeq fc j).B.card ≤ 2 * f_g fc y j →
        8 * f_g fc y j + fc.M ≤ 8 * f_g fc y (j + 1))
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) :=
  cfp_lemma_5_6_finite_core fc (growthSteps_card_le_budget_of_p16 fc h_inj h_numeric h_range2) h_unsaturated_step_growth

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Per-Block Budget Bound (Closing U5 under U1):
    Each subgroup index block in growthSteps has cardinality bounded by p16BlockBudget,
    derived directly from the iterated sumset growth hypothesis U1. -/
theorem growthSteps_block_card_le_p16BlockBudget_of_iterSum_growth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card)
    (y : ℕ)
    (hy : y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t)) :
    ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤
      p16BlockBudget fc.t fc.U fc.M := by
  apply growthSteps_block_card_le_p16BlockBudget fc h_inj y hy
  intro j hj_Jy hj_le
  have hj_growth : j ∈ growthSteps fc := (Finset.mem_filter.mp hj_Jy).1
  have hj_g : (greedySeq fc j).g fc.t = y := (Finset.mem_filter.mp hj_Jy).2
  rw [← hj_g] at hj_le ⊢
  exact trajectory_growth_step_range2_of_iterSum_growth fc h_inj h_u1 j hj_growth hj_le

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Total Budget Master Theorem (Closing U6 under U1):
    Total growth steps are bounded by p16TotalBudget without any external h_fibers or h_range2. -/
theorem growthSteps_card_le_p16Budget_of_iterSum_growth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card) :
    (growthSteps fc).card ≤ p16TotalBudget fc.t fc.gMax fc.U fc.M := by
  have h_blocks := growthSteps_g_image_card_le fc
  have h_fiber : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ p16BlockBudget fc.t fc.U fc.M := by
    intro y hy
    exact growthSteps_block_card_le_p16BlockBudget_of_iterSum_growth fc h_inj h_u1 y hy
  exact card_le_mul_of_fiber_bound (growthSteps fc) (fun j => (greedySeq fc j).g fc.t)
    (maxSubgroupBlocks fc.gMax) (p16BlockBudget fc.t fc.U fc.M)
    h_blocks h_fiber

/-- Master derivation: Connecting p16TotalBudget to fc.B_growth via explicit numeric bound under U1. -/
theorem growthSteps_card_le_budget_of_iterSum_growth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card) :
    (growthSteps fc).card ≤ fc.B_growth :=
  (growthSteps_card_le_p16Budget_of_iterSum_growth fc h_inj h_u1).trans h_numeric

/-- CFP Lemma 5.6 Finite Core with p16 Logarithmic Budget (Master Theorem under U1):
    The ad-hoc h_fibers bound is eliminated, and finite Claim 1 is strictly reduced to U1. -/
theorem cfp_lemma_5_6_finite_core_of_iterSum_growth (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) :=
  cfp_lemma_5_6_finite_core fc
    (growthSteps_card_le_budget_of_iterSum_growth fc h_inj h_numeric h_u1)
    h_unsaturated_step_growth

/-- CFP Lemma 5.6 Specialized to m = n Closed under U1:
    The growth budget bound hypothesis is eliminated by invoking the U1-derived Claim 1 budget bound. -/
theorem cfp_lemma_5_6_m_eq_n_of_iterSum_growth (p : CFPArithParams)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod p.t)) (p.A : Set ℕ))
    (h_numeric : p16TotalBudget p.t p.gMax p.U p.M ≤ p.B_growth)
    (h_u1 : ∀ (N : ℕ) (_hN : 0 < N) (C : Finset (ZMod N)),
      (0 : ZMod N) ∈ C →
      AddSubgroup.closure (C : Set (ZMod N)) = ⊤ →
      ∀ (k : ℕ), 1 ≤ k →
        (iterSum k C).card = N ∨
          (k + 1) * C.card ≤ 2 * (iterSum k C).card)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps p.toFiniteConditions, p.D ≤ greedyDelta p.toFiniteConditions j) :
    min p.xi ((32 : ℝ) / (p.ell : ℝ)) * (p.t : ℝ) ≤ ((subsetSumsMod p.t p.A).card : ℝ) :=
  cfp_lemma_5_6_m_eq_n p
    (growthSteps_card_le_budget_of_iterSum_growth p.toFiniteConditions h_inj h_numeric h_u1)
    h_unsaturated_step_growth

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 (Phase P16 Unbundled Master Theorem, Legacy Interface):
    Total growth steps during the greedy iteration bounded under fiber hypothesis. -/
theorem growthSteps_card_le_p16TotalBudget (fc : FiniteConditions)
    (h_fibers : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ p16BlockBudget fc.t fc.U fc.M) :
    (growthSteps fc).card ≤ p16TotalBudget fc.t fc.gMax fc.U fc.M := by
  exact card_le_mul_of_fiber_bound (growthSteps fc) (fun j => (greedySeq fc j).g fc.t)
    (maxSubgroupBlocks fc.gMax) (p16BlockBudget fc.t fc.U fc.M)
    (growthSteps_g_image_card_le fc) h_fibers

/-- Master derivation: Connecting p16TotalBudget to fc.B_growth via explicit numeric bound (Legacy Interface). -/
theorem growthSteps_card_le_budget_of_numeric_bound (fc : FiniteConditions)
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_fibers : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ p16BlockBudget fc.t fc.U fc.M) :
    (growthSteps fc).card ≤ fc.B_growth :=
  (growthSteps_card_le_p16TotalBudget fc h_fibers).trans h_numeric

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1:
    Total growth steps during the greedy iteration are bounded by claim1GrowthBound. -/
theorem growthSteps_card_le_claim1 (fc : FiniteConditions)
    (h_fibers : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ blockGrowthBudget fc.t fc.U fc.M) :
    (growthSteps fc).card ≤ claim1GrowthBound fc.t fc.gMax fc.U fc.M := by
  exact card_le_mul_of_fiber_bound (growthSteps fc) (fun j => (greedySeq fc j).g fc.t)
    (maxSubgroupBlocks fc.gMax) (blockGrowthBudget fc.t fc.U fc.M)
    (growthSteps_g_image_card_le fc) h_fibers

/-- Master derivation: Closing the growth budget bound via Claim 1. -/
theorem claim1_growth_bound_of_budget (fc : FiniteConditions)
    (hB : claim1GrowthBound fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_fibers : ∀ y ∈ (growthSteps fc).image (fun j => (greedySeq fc j).g fc.t),
      ((growthSteps fc).filter (fun j => (greedySeq fc j).g fc.t = y)).card ≤ blockGrowthBudget fc.t fc.U fc.M) :
    (growthSteps fc).card ≤ fc.B_growth :=
  (growthSteps_card_le_claim1 fc h_fibers).trans hB

lemma u1_iterSum_growth (N : ℕ) (hN : 0 < N) (C : Finset (ZMod N))
    (h0 : (0 : ZMod N) ∈ C)
    (hgen : AddSubgroup.closure (C : Set (ZMod N)) = ⊤)
    (k : ℕ) (hk : 1 ≤ k) :
    (iterSum k C).card = N ∨
      (k + 1) * C.card ≤ 2 * (iterSum k C).card := by
  have : NeZero N := ⟨by omega⟩
  exact iterSum_card_ge_of_zero_mem_of_generates N C h0 hgen k hk

/-- Conlon–Fox–Pham (2021) Lemma 5.6 Claim 1 Total Budget Closed Master Theorem:
    Total growth steps are bounded by p16TotalBudget unconditionally (no h_u1, no h_fibers). -/
theorem growthSteps_card_le_p16Budget_closed
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ)) :
    (growthSteps fc).card ≤ p16TotalBudget fc.t fc.gMax fc.U fc.M :=
  growthSteps_card_le_p16Budget_of_iterSum_growth fc h_inj u1_iterSum_growth

/-- Master derivation: Connecting p16TotalBudget to fc.B_growth via explicit numeric bound unconditionally. -/
theorem growthSteps_card_le_budget_closed
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth) :
    (growthSteps fc).card ≤ fc.B_growth :=
  growthSteps_card_le_budget_of_iterSum_growth fc h_inj h_numeric u1_iterSum_growth

/-- CFP Lemma 5.6 Finite Core with p16 Logarithmic Budget (Closed Master Theorem):
    The ad-hoc h_fibers bound and h_u1 are eliminated unconditionally. -/
theorem cfp_lemma_5_6_finite_core_closed (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) :=
  cfp_lemma_5_6_finite_core_of_iterSum_growth fc h_inj h_numeric u1_iterSum_growth h_unsaturated_step_growth

/-- CFP Lemma 5.6 Specialized to m = n Closed Master Theorem:
    Unconditionally closed under U1 and Claim 1. -/
theorem cfp_lemma_5_6_m_eq_n_closed (p : CFPArithParams)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod p.t)) (p.A : Set ℕ))
    (h_numeric : p16TotalBudget p.t p.gMax p.U p.M ≤ p.B_growth)
    (h_unsaturated_step_growth : ∀ j ∈ unsaturatedSteps p.toFiniteConditions, p.D ≤ greedyDelta p.toFiniteConditions j) :
    min p.xi ((32 : ℝ) / (p.ell : ℝ)) * (p.t : ℝ) ≤ ((subsetSumsMod p.t p.A).card : ℝ) :=
  cfp_lemma_5_6_m_eq_n_of_iterSum_growth p h_inj h_numeric u1_iterSum_growth h_unsaturated_step_growth

/-!
### 24. Phase P17: Candidate Injectivity, Fiber Pullback, and Unsaturated Step Growth

Formalization of Phase P17 for Conlon–Fox–Pham (2021) Lemma 5.6:
- Group A1: Modulo t injectivity derived from candidate membership in Y_v (`injOn_of_inY_v`).
- Group B2: Fiber centering, quotient scale retraction (`zmodScale_val_div`), and exact pullback (`centerFiberPullback`, `delta_fiber_pullback_le_delta_S`).
- Group B3: Medium fiber extraction and reduction to smallGrowth (`unsaturated_step_medium_fiber_and_smallGrowth`).
- P17 Finite Arithmetic Conditions: Explicit raw parameters and numerical thresholds (`P17FiniteArithConditions`).
- Integration Master Theorem: Conditional elimination of `h_unsaturated_step_growth` and `h_inj` (`cfp_lemma_5_6_finite_core_of_arith_conditional`).
-/

lemma injOn_of_inY_v_aux {y m W v t : ℕ} (hv : 0 < v) (_ht : 0 < t) (hyt : y ≤ v * t)
    {A : Finset ℕ} (hA : ∀ a ∈ A, inY_v y m W v a)
    {a1 a2 : ℕ} (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (heq : (a1 : ZMod t) = (a2 : ZMod t))
    (hle : a1 ≤ a2) : a1 = a2 := by
  have h1 := hA a1 ha1
  have h2 := hA a2 ha2
  rcases h1 with ⟨hy1, hlt1, -⟩
  rcases h2 with ⟨hy2, hlt2, -⟩
  have hdiff : v * (a2 - a1) < v * t := by
    calc v * (a2 - a1) = v * a2 - v * a1 := Nat.mul_sub_left_distrib v a2 a1
    _ < 2 * y - y := by omega
    _ = y := by omega
    _ ≤ v * t := hyt
  have hlt_t : a2 - a1 < t := (Nat.mul_lt_mul_left hv).mp hdiff
  have h_sub_zero : ((a2 - a1 : ℕ) : ZMod t) = 0 := by
    rw [Nat.cast_sub hle, heq.symm, sub_self]
  have hdvd : t ∣ a2 - a1 := (CharP.cast_eq_zero_iff (ZMod t) t (a2 - a1)).mp h_sub_zero
  have hzero : a2 - a1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt_t
  omega

/-- Group A1: Modulo t injectivity derived unconditionally from candidate membership in Y_v. -/
lemma injOn_of_inY_v {y m W v t : ℕ} (hv : 0 < v) (ht : 0 < t) (hyt : y ≤ v * t)
    {A : Finset ℕ} (hA : ∀ a ∈ A, inY_v y m W v a) :
    Set.InjOn (fun a : ℕ => (a : ZMod t)) (A : Set ℕ) := by
  intro a1 ha1 a2 ha2 heq
  rw [Finset.mem_coe] at ha1 ha2
  rcases le_total a1 a2 with hle | hle
  · exact injOn_of_inY_v_aux hv ht hyt hA ha1 ha2 heq hle
  · exact (injOn_of_inY_v_aux hv ht hyt hA ha2 ha1 heq.symm hle).symm

/-- Group B2: Every element in the kernel of zmodProj hd is in the image of zmodScale t g. -/
lemma zmodScale_val_div (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hd : g ∣ t)
    (y : ZMod t) (hy : zmodProj hd y = 0) :
    zmodScale t g ((y.val / g : ℕ) : ZMod (t / g)) = y := by
  have htg_pos : 0 < t / g := Nat.div_pos (Nat.le_of_dvd ht hd) hg
  have inst1 : NeZero (t / g) := ⟨by omega⟩
  have inst2 : NeZero t := ⟨by omega⟩
  have hdvd : g ∣ y.val := by
    have h_proj := ZMod.natCast_zmod_val y
    rw [← h_proj] at hy
    rw [zmodProj_natCast hd] at hy
    exact (CharP.cast_eq_zero_iff (ZMod g) g y.val).mp hy
  dsimp [zmodScale]
  have hval_lt : (y.val / g) < t / g := by
    have h_y_lt : y.val < t := ZMod.val_lt y
    rcases hdvd with ⟨q1, hq1⟩
    rcases hd with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
    rw [hq1, hq2] at h_y_lt
    exact (Nat.mul_lt_mul_left hg).mp h_y_lt
  have h_val_eq : (((y.val / g : ℕ) : ZMod (t / g)).val) = y.val / g := ZMod.val_natCast_of_lt hval_lt
  rw [h_val_eq, Nat.mul_div_cancel' hdvd, ZMod.natCast_zmod_val y]

/-- Definition of pulling back a centered fiber C (which lies in the kernel of zmodProj)
    to a subset of ZMod (t / g). -/
def centerFiberPullback (t g : ℕ) (C : Finset (ZMod t)) : Finset (ZMod (t / g)) :=
  C.image (fun y => ((y.val / g : ℕ) : ZMod (t / g)))

lemma image_zmodScale_centerFiberPullback (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hd : g ∣ t)
    (C : Finset (ZMod t)) (hC : ∀ y ∈ C, zmodProj hd y = 0) :
    (centerFiberPullback t g C).image (zmodScale t g) = C := by
  ext x
  simp only [centerFiberPullback, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [zmodScale_val_div t g ht hg hd y (hC y hy)]
    exact hy
  · intro hx
    refine ⟨((x.val / g : ℕ) : ZMod (t / g)), ?_, zmodScale_val_div t g ht hg hd x (hC x hx)⟩
    exact ⟨x, hx, rfl⟩

lemma card_centerFiberPullback (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hd : g ∣ t)
    (C : Finset (ZMod t)) (hC : ∀ y ∈ C, zmodProj hd y = 0) :
    (centerFiberPullback t g C).card = C.card := by
  have h_inj := zmodScale_injective t g ht hg hd
  have h_img := image_zmodScale_centerFiberPullback t g ht hg hd C hC
  nth_rw 2 [← h_img]
  rw [Finset.card_image_of_injective _ h_inj]

lemma delta_centerFiberPullback (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hd : g ∣ t)
    (C : Finset (ZMod t)) (hC : ∀ y ∈ C, zmodProj hd y = 0)
    (a : ℕ) (ha : g ∣ a) :
    delta (centerFiberPullback t g C) ((a / g : ℕ) : ZMod (t / g)) = delta C (a : ZMod t) := by
  have h_delta := delta_image_zmodScale t g ht hg hd (centerFiberPullback t g C) ((a / g : ℕ) : ZMod (t / g))
  rw [image_zmodScale_centerFiberPullback t g ht hg hd C hC] at h_delta
  rw [zmodScale_natCast_div t g ht hg hd a ha] at h_delta
  exact h_delta.symm

lemma delta_fiber_pullback_le_delta_S (t g : ℕ) (ht : 0 < t) (hg : 0 < g) (hd : g ∣ t)
    (S : Finset (ZMod t)) (r : ZMod g) (x0 : ZMod t) (hx0 : zmodProj hd x0 = r)
    (a : ℕ) (ha : g ∣ a) :
    let C := centerFiber hd S r x0
    let T := centerFiberPullback t g C
    T.card = (fiber hd S r).card ∧
    delta T ((a / g : ℕ) : ZMod (t / g)) ≤ delta S (a : ZMod t) := by
  intro C T
  have hC : ∀ y ∈ C, zmodProj hd y = 0 := centerFiber_subset_kernel hd S r x0 hx0
  have h_card : T.card = (fiber hd S r).card := by
    rw [card_centerFiberPullback t g ht hg hd C hC, card_centerFiber]
  have h_delta : delta T ((a / g : ℕ) : ZMod (t / g)) = delta (fiber hd S r) (a : ZMod t) := by
    rw [delta_centerFiberPullback t g ht hg hd C hC a ha, delta_centerFiber_eq]
  have ha_ker : zmodProj hd (a : ZMod t) = 0 := by
    rw [zmodProj_natCast hd]
    exact (CharP.cast_eq_zero_iff (ZMod g) g a).mpr ha
  have h_le : delta (fiber hd S r) (a : ZMod t) ≤ delta S (a : ZMod t) :=
    delta_fiber_le_delta hd S (a : ZMod t) ha_ker r
  exact ⟨h_card, h_delta.trans_le h_le⟩

lemma unsaturatedSteps_div_neZero (fc : FiniteConditions) (j : ℕ) (hj : j ∈ unsaturatedSteps fc) :
    NeZero (fc.t / (greedySeq fc j).g fc.t) := by
  classical
  have hj_range : j ∈ Finset.range fc.K := (Finset.mem_filter.mp hj).1
  have hj_lt : j < fc.K := Finset.mem_range.mp hj_range
  let st := greedySeq fc j
  have hg_pos : 0 < st.g fc.t := subgroupIndex_pos fc.t st.B fc.ht_pos
  have hd : st.g fc.t ∣ fc.t := subgroupIndex_dvd_modulus fc.t st.B
  have hN_pos : 0 < fc.t / st.g fc.t := Nat.div_pos (Nat.le_of_dvd fc.ht_pos hd) hg_pos
  exact ⟨ne_of_gt hN_pos⟩

/-- Group B Complete Bridge:
    At an unsaturated step j with greedyDelta fc j ≤ fc.D,
    there exists a fiber pullback T in ZMod (fc.t / g) and scaled candidate set Q such that:
    1. U < |T|
    2. |T| < xi * (t / g)
    3. Q ⊆ smallGrowth T fc.D
    4. M ≤ |Q|
    5. AddSubgroup.closure Q = ⊤ -/
theorem unsaturated_step_medium_fiber_and_smallGrowth
    (fc : FiniteConditions)
    (h_inj : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ))
    (j : ℕ) (hj : j ∈ unsaturatedSteps fc)
    (h_delta_le : greedyDelta fc j ≤ fc.D) :
    let st := greedySeq fc j
    let g := st.g fc.t
    let N := fc.t / g
    letI : NeZero N := unsaturatedSteps_div_neZero fc j hj
    let Q := st.B.image (fun a => ((a / g : ℕ) : ZMod N))
    ∃ (T : Finset (ZMod N)),
      fc.U < T.card ∧
      (T.card : ℝ) < fc.xi * (fc.t : ℝ) / (g : ℝ) ∧
      Q ⊆ smallGrowth T fc.D ∧
      fc.M ≤ Q.card ∧
      AddSubgroup.closure (Q : Set (ZMod N)) = ⊤ := by
  intro st g N Q
  classical
  have hj_range : j ∈ Finset.range fc.K := (Finset.mem_filter.mp hj).1
  have hj_lt : j < fc.K := Finset.mem_range.mp hj_range
  have hj_unsat : isUnsaturatedStage fc.t fc.U fc.xi st := (Finset.mem_filter.mp hj).2
  rcases hj_unsat with ⟨h_not_grow, h_not_sat⟩
  have hg_pos : 0 < g := subgroupIndex_pos fc.t st.B fc.ht_pos
  have hd : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t st.B
  have hN_pos : 0 < N := Nat.div_pos (Nat.le_of_dvd fc.ht_pos hd) hg_pos
  have instN : NeZero N := ⟨ne_of_gt hN_pos⟩
  have h_card_E : st.E.card = j := card_greedySeq_E fc j (by omega)
  have hB_card : fc.M ≤ st.B.card := st.B_card_ge (by omega)
  have hB_nonempty : st.B.Nonempty := st.B_nonempty (by omega)
  have hB_sub_A : st.B ⊆ fc.A := Finset.sdiff_subset
  have hB_dvd : ∀ a ∈ st.B, g ∣ a := fun a ha => subgroupIndex_dvd_mem fc.t st.B ha

  -- From ¬ isSaturatedStage, obtain medium residue r
  have h_not_sat_ex : ∃ r ∈ (st.S fc.t).image (zmodProj hd), ((fiber hd (st.S fc.t) r).card : ℝ) < fc.xi * (fc.t : ℝ) / (g : ℝ) := by
    by_contra! h_all
    apply h_not_sat
    dsimp [isSaturatedStage]
    exact h_all
  rcases h_not_sat_ex with ⟨r, hr_img, hr_lt⟩

  -- From ¬ isGrowthStage, every fiber has card > U
  have hr_gt_U : fc.U < (fiber hd (st.S fc.t) r).card := by
    by_contra! hle
    apply h_not_grow
    dsimp [isGrowthStage]
    exact ⟨r, hr_img, hle⟩

  -- Since r is in image, fiber is non-empty, pick x0 in fiber
  have hr_fib_nonempty : (fiber hd (st.S fc.t) r).Nonempty := by
    have := fc.hU_pos
    exact Finset.card_pos.mp (by omega)
  rcases hr_fib_nonempty with ⟨x0, hx0_fib⟩
  have hx0_proj : zmodProj hd x0 = r := (Finset.mem_filter.mp hx0_fib).2

  -- Construct T via centerFiberPullback
  set C := centerFiber hd (st.S fc.t) r x0
  set T := centerFiberPullback fc.t g C
  use T

  have h_pullback := delta_fiber_pullback_le_delta_S fc.t g fc.ht_pos hg_pos hd (st.S fc.t) r x0 hx0_proj
  have hT_card : T.card = (fiber hd (st.S fc.t) r).card := (h_pullback 0 (dvd_zero g)).1

  have hT_gt_U : fc.U < T.card := by rwa [hT_card]
  have hT_lt_xi : (T.card : ℝ) < fc.xi * (fc.t : ℝ) / (g : ℝ) := by rwa [hT_card]

  -- Q ⊆ smallGrowth T fc.D
  have hQ_sub : Q ⊆ smallGrowth T fc.D := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨a, ha_B, rfl⟩
    have ha_dvd := hB_dvd a ha_B
    have h_delta_le_S := (h_pullback a ha_dvd).2
    have h_delta_S_le : delta (st.S fc.t) (a : ZMod fc.t) ≤ greedyDelta fc j := by
      dsimp [greedyDelta]
      rw [dif_pos hj_lt]
      exact greedyChoice_ordinary_max fc.t fc.U st hB_nonempty h_not_grow a ha_B
    have h_delta_le_D : delta T ((a / g : ℕ) : ZMod N) ≤ fc.D :=
      h_delta_le_S.trans (h_delta_S_le.trans h_delta_le)
    simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_delta_le_D

  -- M ≤ Q.card
  have hQ_card : Q.card = st.B.card :=
    card_image_scaled_of_injOn fc.t g fc.ht_pos hg_pos hd fc.A h_inj st.B hB_sub_A hB_dvd
  have hM_le_Q : fc.M ≤ Q.card := by omega

  -- closure Q = ⊤
  have hgen : AddSubgroup.closure (Q : Set (ZMod N)) = ⊤ :=
    closure_scaled_candidate_eq_top fc.t fc.ht_pos st.B

  exact ⟨hT_gt_U, hT_lt_xi, hQ_sub, hM_le_Q, hgen⟩

/-- Finite Arithmetic Conditions for Phase P17 (CFP Lemma 5.6 Unsaturated Step Growth).
    Separates the raw arithmetic candidate membership and explicit numerical bounds
    from the discrete greedy state machine. -/
structure P17FiniteArithConditions (fc : FiniteConditions) where
  n : ℕ
  hn_pos : 0 < n
  hn_ge_three : 3 ≤ n
  r : ℕ
  hr_pos : 0 < r
  hr_gt_one : 1 < r
  y : ℕ
  hy_pos : 0 < y
  W : ℕ
  hW_pos : 0 < W
  hv_dvd_n : fc.v ∣ n
  h_y_le_vt : y ≤ fc.v * fc.t
  h_t_le_n : fc.t ≤ n
  hA_inY : ∀ a ∈ fc.A, inY_v y n W fc.v a

  -- Explicit numerical conditions E1, E2, E3 from CFP §5.1 / P17 specification:
  -- E1: small cardinality branch contradiction bound
  hE1 : 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / (fc.U : ℝ) ^ ((1 : ℝ) / 50) < (fc.M : ℝ)
  -- E2: AP branch length threshold
  hE2 : r ^ 3 ≤ fc.M ^ 16
  -- E3: AP branch final contradiction bound
  hE3 : 98304 * (fc.D : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ) < (fc.M : ℝ)

  -- Deshouillers–Freiman small density condition from CFP §5.1 (xi ≤ min(xi_DF/4, 1/20) ≤ 1/20):
  h_xi_le : fc.xi ≤ (1 / 20 : ℝ)

/-- Deriving modulo t injectivity of the candidate set fc.A directly from P17 arithmetic conditions. -/
lemma P17FiniteArithConditions.injOn_A (fc : FiniteConditions) (p : P17FiniteArithConditions fc) :
    Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ) :=
  injOn_of_inY_v fc.hv_pos fc.ht_pos p.h_y_le_vt p.hA_inY

/-- Cardinality bound on candidate subsets from coset AP coverage:
    For any candidate subset B ⊆ fc.A and coset AP R in ZMod (t / g) containing
    the scaled projection of B, the cardinality |B| is bounded by R.ell * |R.H|. -/
theorem card_le_card_cosetAP_of_image_subset
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (B : Finset ℕ) (hBA : B ⊆ fc.A)
    [instN : NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset) :
    B.card ≤ R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card := by
  let g := subgroupIndex fc.t B
  let N := fc.t / g
  let f : ℕ → ZMod N := fun a => ((a / g : ℕ) : ZMod N)
  have h_inj_A : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (fc.A : Set ℕ) := p.injOn_A fc
  have h_inj_B : Set.InjOn (fun a : ℕ => (a : ZMod fc.t)) (B : Set ℕ) :=
    h_inj_A.mono hBA
  have hg_dvd : ∀ a ∈ B, g ∣ a := fun a ha => subgroupIndex_dvd_mem fc.t B ha
  have hg_dvd_t : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t B
  have hg_mul_N : g * N = fc.t := Nat.mul_div_cancel' hg_dvd_t
  have hf_inj : Set.InjOn f (B : Set ℕ) := by
    intro a1 ha1 a2 ha2 heq
    dsimp [f] at heq
    rw [ZMod.natCast_eq_natCast_iff] at heq
    have h_mul := Nat.ModEq.mul_left' g heq
    rw [Nat.mul_div_cancel' (hg_dvd a1 ha1), Nat.mul_div_cancel' (hg_dvd a2 ha2)] at h_mul
    rw [hg_mul_N] at h_mul
    rw [← ZMod.natCast_eq_natCast_iff] at h_mul
    exact h_inj_B ha1 ha2 h_mul
  have h_card_img : (B.image f).card = B.card := Finset.card_image_of_injOn hf_inj
  have h_sub_card := Finset.card_le_card hQR
  rw [h_card_img] at h_sub_card
  have h_R_card := R.card_toFinset_le
  exact h_sub_card.trans h_R_card

/-- Subgroup generated by {0, x} when 2x = 0. -/
lemma closure_pair_zero_order_two {G : Type*} [AddCommGroup G] (x : G) (h2x : x + x = 0) :
    (AddSubgroup.closure ({0, x} : Set G) : Set G) = {0, x} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl <;> simp
    | zero => simp
    | add a b ha hb ha_ih hb_ih =>
      rcases ha_ih with ha0 | hax <;> rcases hb_ih with hb0 | hbx
      · rw [ha0, hb0, add_zero]; left; rfl
      · rw [ha0, hbx, zero_add]; right; rfl
      · rw [hax, hb0, add_zero]; right; rfl
      · rw [hax, hbx, h2x]; left; rfl
    | neg a ha ha_ih =>
      rcases ha_ih with ha0 | hax
      · rw [ha0, neg_zero]; left; rfl
      · rw [hax]
        have : -x = x := by
          rw [neg_eq_iff_add_eq_zero]
          exact h2x
        rw [this]; right; rfl
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.subset_closure (by simp)

/-- Subgroup generated by {0, x} when 3x = 0. -/
lemma closure_pair_zero_order_three {G : Type*} [AddCommGroup G] (x : G) (h3x : x + x + x = 0) :
    (AddSubgroup.closure ({0, x} : Set G) : Set G) = {0, x, x + x} := by
  have h3x' : x + (x + x) = 0 := by
    calc x + (x + x) = (x + x + x) := by abel
    _ = 0 := h3x
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl <;> simp
    | zero => simp
    | add a b ha hb ha_ih hb_ih =>
      rcases ha_ih with ha0 | hax | ha2x <;> rcases hb_ih with hb0 | hbx | hb2x
      · rw [ha0, hb0, add_zero]; left; rfl
      · rw [ha0, hbx, zero_add]; right; left; rfl
      · rw [ha0, hb2x, zero_add]; right; right; rfl
      · rw [hax, hb0, add_zero]; right; left; rfl
      · rw [hax, hbx]; right; right; rfl
      · rw [hax, hb2x, h3x']; left; rfl
      · rw [ha2x, hb0, add_zero]; right; right; rfl
      · rw [ha2x, hbx, h3x]; left; rfl
      · rw [ha2x, hb2x]
        have : (x + x) + (x + x) = x := by
          calc (x + x) + (x + x) = (x + x + x) + x := by abel
          _ = 0 + x := by rw [h3x]
          _ = x := zero_add x
        rw [this]; right; left; rfl
    | neg a ha ha_ih =>
      rcases ha_ih with ha0 | hax | ha2x
      · rw [ha0, neg_zero]; left; rfl
      · rw [hax]
        have : -x = x + x := by
          rw [neg_eq_iff_add_eq_zero]
          exact h3x'
        rw [this]; right; right; rfl
      · rw [ha2x]
        have : -(x + x) = x := by
          rw [neg_eq_iff_add_eq_zero]
          exact h3x
        rw [this]; right; left; rfl
  · rintro (rfl | rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.subset_closure (by simp)
    · have hx : x ∈ AddSubgroup.closure ({0, x} : Set G) :=
        AddSubgroup.subset_closure (by simp)
      exact add_mem hx hx

/-- Small set rigidity: If 0 ∈ S and S = {0, x} with 2x = 0,
    the subgroup generated by S has cardinality at most 2. -/
lemma closure_card_le_two_of_order_two {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (h2x : x + x = 0) :
    ∃ (H : AddSubgroup G), (({0, x} : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 2) := by
  use AddSubgroup.closure ({0, x} : Set G)
  refine ⟨AddSubgroup.subset_closure, ?_⟩
  use {0, x}
  have hs : (({0, x} : Finset G) : Set G) = ({0, x} : Set G) := by simp
  refine ⟨by rw [closure_pair_zero_order_two x h2x, hs], ?_⟩
  exact Finset.card_insert_le 0 {x}

/-- Small set rigidity: If 0 ∈ S and S = {0, x} with 3x = 0,
    the subgroup generated by S has cardinality at most 3. -/
lemma closure_card_le_three_of_order_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (h3x : x + x + x = 0) :
    ∃ (H : AddSubgroup G), (({0, x} : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 3) := by
  use AddSubgroup.closure ({0, x} : Set G)
  refine ⟨AddSubgroup.subset_closure, ?_⟩
  use {0, x, x + x}
  have hs : (({0, x, x + x} : Finset G) : Set G) = ({0, x, x + x} : Set G) := by simp
  refine ⟨by rw [closure_pair_zero_order_three x h3x, hs], ?_⟩
  have h1 : ({x, x + x} : Finset G).card ≤ 2 := Finset.card_insert_le x {x + x}
  have h2 : ({0, x, x + x} : Finset G).card ≤ ({x, x + x} : Finset G).card + 1 :=
    Finset.card_insert_le 0 {x, x + x}
  omega

/-- If S has 3 elements {0, x, y} and S is closed under addition, then 3x = 0 and y = x + x. -/
lemma order_three_of_card_three_add_self_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x y : G) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y)
    (h_add : ∀ a ∈ ({0, x, y} : Finset G), ∀ b ∈ ({0, x, y} : Finset G),
      a + b ∈ ({0, x, y} : Finset G)) :
    x + x + x = 0 ∧ y = x + x := by
  have hx_mem : x ∈ ({0, x, y} : Finset G) := by simp
  have hy_mem : y ∈ ({0, x, y} : Finset G) := by simp
  have h2x_mem := h_add x hx_mem x hx_mem
  have hxy_mem := h_add x hx_mem y hy_mem
  simp only [mem_insert, mem_singleton] at h2x_mem hxy_mem
  -- First prove x + x ≠ 0
  have h2x_ne_zero : x + x ≠ 0 := by
    intro h2x0
    rcases hxy_mem with hxy0 | hxyx | hxyy
    · -- x + y = 0 => y = -x = x (since 2x = 0)
      have : y = x := by
        calc y = -x := by rw [← add_eq_zero_iff_neg_eq.mp hxy0]
        _ = x := by rw [neg_eq_iff_add_eq_zero.mpr h2x0]
      exact hxy this.symm
    · -- x + y = x => y = 0
      have : y = 0 := by
        calc y = (x + y) - x := by abel
        _ = x - x := by rw [hxyx]
        _ = 0 := sub_self x
      exact hy0 this
    · -- x + y = y => x = 0
      have : x = 0 := by
        calc x = (x + y) - y := by abel
        _ = y - y := by rw [hxyy]
        _ = 0 := sub_self y
      exact hx0 this
  -- Since 2x ∈ {0, x, y} and 2x ≠ 0 and 2x ≠ x, we must have 2x = y
  have h2x_ne_x : x + x ≠ x := by
    intro h
    have : x = 0 := by
      calc x = (x + x) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := sub_self x
    exact hx0 this
  have hy_eq : y = x + x := by
    rcases h2x_mem with h | h | h
    · exact False.elim (h2x_ne_zero h)
    · exact False.elim (h2x_ne_x h)
    · exact h.symm
  -- Now x + (x + x) ∈ {0, x, y} = {0, x, x + x}
  have h3x_mem : (x + x + x) ∈ ({0, x, y} : Finset G) := by
    have h_assoc : x + x + x = x + y := by
      calc x + x + x = x + (x + x) := by abel
      _ = x + y := by rw [hy_eq]
    rw [h_assoc]
    simp only [mem_insert, mem_singleton]
    exact hxy_mem
  simp only [mem_insert, mem_singleton] at h3x_mem
  have h3x_zero : x + x + x = 0 := by
    rcases h3x_mem with h | h | h
    · exact h
    · -- 3x = x => 2x = 0, contradiction
      have h2x0 : x + x = 0 := by
        calc x + x = (x + x + x) - x := by abel
        _ = x - x := by rw [h]
        _ = 0 := sub_self x
      exact False.elim (h2x_ne_zero h2x0)
    · -- 3x = y = 2x => x = 0, contradiction
      rw [hy_eq] at h
      have hx0' : x = 0 := by
        calc x = (x + x + x) - (x + x) := by abel
        _ = (x + x) - (x + x) := by rw [h]
        _ = 0 := sub_self (x + x)
      exact False.elim (hx0 hx0')
  exact ⟨h3x_zero, hy_eq⟩

/-- Small set rigidity: If 0 ∈ S and S = {0, x, y} with S closed under addition,
    the subgroup generated by S has cardinality at most 3. -/
lemma closure_card_le_three_of_card_three_add_self_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x y : G)
    (h_add : ∀ a ∈ ({0, x, y} : Finset G), ∀ b ∈ ({0, x, y} : Finset G),
      a + b ∈ ({0, x, y} : Finset G)) :
    ∃ (H : AddSubgroup G), (({0, x, y} : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 3) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hs : ({0, (0 : G), y} : Set G) = {0, y} := by ext z; aesop
    by_cases hy0 : y = 0
    · subst hy0
      use ⊥
      refine ⟨by simp, ?_⟩
      use {0}
      simp
    · have hy_mem : y ∈ ({0, (0 : G), y} : Finset G) := by simp
      have h2y_mem := h_add y hy_mem y hy_mem
      simp only [mem_insert, mem_singleton] at h2y_mem
      rcases h2y_mem with h2y0 | h2y0 | h2yy
      · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two y h2y0
        use H
        refine ⟨by rw [hs]; exact hsub, ⟨s, hs_eq, by omega⟩⟩
      · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two y h2y0
        use H
        refine ⟨by rw [hs]; exact hsub, ⟨s, hs_eq, by omega⟩⟩
      · have : y = 0 := by
          calc y = (y + y) - y := by abel
          _ = y - y := by rw [h2yy]
          _ = 0 := sub_self y
        exact False.elim (hy0 this)
  · by_cases hy0 : y = 0
    · subst hy0
      have hs : ({0, x, (0 : G)} : Set G) = {0, x} := by ext z; aesop
      have hx_mem : x ∈ ({0, x, (0 : G)} : Finset G) := by simp
      have h2x_mem := h_add x hx_mem x hx_mem
      simp only [mem_insert, mem_singleton] at h2x_mem
      rcases h2x_mem with h2x0 | h2xx | h2x0
      · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two x h2x0
        use H
        refine ⟨by rw [hs]; exact hsub, ⟨s, hs_eq, by omega⟩⟩
      · have : x = 0 := by
          calc x = (x + x) - x := by abel
          _ = x - x := by rw [h2xx]
          _ = 0 := sub_self x
        exact False.elim (hx0 this)
      · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two x h2x0
        use H
        refine ⟨by rw [hs]; exact hsub, ⟨s, hs_eq, by omega⟩⟩
    · by_cases hxy : x = y
      · subst hxy
        have hs : ({0, x, x} : Set G) = {0, x} := by ext z; aesop
        have hx_mem : x ∈ ({0, x, x} : Finset G) := by simp
        have h2x_mem := h_add x hx_mem x hx_mem
        simp only [mem_insert, mem_singleton] at h2x_mem
        rcases h2x_mem with h2x0 | h2xx | h2xx
        · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two x h2x0
          use H
          refine ⟨by rw [hs]; exact hsub, ⟨s, hs_eq, by omega⟩⟩
        · have : x = 0 := by
            calc x = (x + x) - x := by abel
            _ = x - x := by rw [h2xx]
            _ = 0 := sub_self x
          exact False.elim (hx0 this)
        · have : x = 0 := by
            calc x = (x + x) - x := by abel
            _ = x - x := by rw [h2xx]
            _ = 0 := sub_self x
          exact False.elim (hx0 this)
      · have ⟨h3x, hy_eq⟩ := order_three_of_card_three_add_self_eq x y hx0 hy0 hxy h_add
        have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_order_three x h3x
        use H
        refine ⟨?_, ⟨s, hs_eq, hcard⟩⟩
        rw [hy_eq]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
        rcases hz with rfl | rfl | rfl
        · exact zero_mem H
        · exact hsub (by simp)
        · have hx : x ∈ H := hsub (by simp)
          exact add_mem hx hx

/-- Containment of multiples 0, x, 2x, 3x in the 4-fold sumset iterSum 4 S when x ∈ S and 0 ∈ S. -/
lemma elements_in_iterSum_four {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (h0 : 0 ∈ S) (x : G) (hx : x ∈ S) :
    0 ∈ iterSum 4 S ∧ x ∈ iterSum 4 S ∧ x + x ∈ iterSum 4 S ∧ x + x + x ∈ iterSum 4 S := by
  have h1 : x ∈ iterSum 1 S := by
    rw [iterSum_succ, mem_sumset_iff]
    exact ⟨0, by simp [iterSum_zero], x, hx, zero_add x⟩
  have h2 : x + x ∈ iterSum 2 S := by
    rw [iterSum_succ, mem_sumset_iff]
    exact ⟨x, h1, x, hx, rfl⟩
  have h3 : x + x + x ∈ iterSum 3 S := by
    rw [iterSum_succ, mem_sumset_iff]
    exact ⟨x + x, h2, x, hx, rfl⟩
  have h0_4 : 0 ∈ iterSum 4 S := by
    have : 0 ∈ iterSum 0 S := by simp [iterSum_zero]
    exact iterSum_mono_of_zero_mem S h0 (by omega) this
  have h1_4 : x ∈ iterSum 4 S :=
    iterSum_mono_of_zero_mem S h0 (by omega) h1
  have h2_4 : x + x ∈ iterSum 4 S :=
    iterSum_mono_of_zero_mem S h0 (by omega) h2
  have h3_4 : x + x + x ∈ iterSum 4 S :=
    iterSum_mono_of_zero_mem S h0 (by omega) h3
  exact ⟨h0_4, h1_4, h2_4, h3_4⟩

/-- When 0 ∈ S and S = {0, x}, if |4S| ≤ 3, then 2x = 0 or 3x = 0 (orders dividing 2 or 3). -/
lemma order_two_or_three_of_pair_iterSum_four_le_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (hx0 : x ≠ 0)
    (h_iter : (iterSum 4 ({0, x} : Finset G)).card ≤ 3) :
    x + x = 0 ∨ x + x + x = 0 := by
  have h0 : (0 : G) ∈ ({0, x} : Finset G) := by simp
  have hx : x ∈ ({0, x} : Finset G) := by simp
  have ⟨h0_4, hx_4, h2x_4, h3x_4⟩ := elements_in_iterSum_four ({0, x} : Finset G) h0 x hx
  have h_sub : ({0, x, x + x, x + x + x} : Finset G) ⊆ iterSum 4 {0, x} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact h0_4
    · exact hx_4
    · exact h2x_4
    · exact h3x_4
  have h_card_le := Finset.card_le_card h_sub
  by_contra! h_contra
  have ⟨h2x_ne, h3x_ne⟩ := h_contra
  have h0_ne_x : (0 : G) ≠ x := ne_of_apply_ne id (Ne.symm hx0)
  have h0_ne_2x : (0 : G) ≠ x + x := Ne.symm h2x_ne
  have h0_ne_3x : (0 : G) ≠ x + x + x := Ne.symm h3x_ne
  have hx_ne_2x : x ≠ x + x := by
    intro h
    have : x = 0 := by
      calc x = (x + x) - x := by abel
      _ = x - x := by rw [← h]
      _ = 0 := sub_self x
    exact hx0 this
  have hx_ne_3x : x ≠ x + x + x := by
    intro h
    have : x + x = 0 := by
      calc x + x = (x + x + x) - x := by abel
      _ = x - x := by rw [← h]
      _ = 0 := sub_self x
    exact h2x_ne this
  have h2x_ne_3x : x + x ≠ x + x + x := by
    intro h
    have : x = 0 := by
      calc x = (x + x + x) - (x + x) := by abel
      _ = (x + x) - (x + x) := by rw [← h]
      _ = 0 := sub_self (x + x)
    exact hx0 this
  have h_card_4 : ({0, x, x + x, x + x + x} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h; aesop
    · intro h; aesop
    · intro h; aesop
  omega

/-- When S = {0, x} and |4S| ≤ 3, the subgroup generated by S has order at most 3. -/
lemma closure_card_le_three_of_pair_iterSum_four_le_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (h_iter : (iterSum 4 ({0, x} : Finset G)).card ≤ 3) :
    ∃ (H : AddSubgroup G), (({0, x} : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 3) := by
  by_cases hx0 : x = 0
  · subst hx0
    use ⊥
    refine ⟨by simp, ?_⟩
    use {0}
    simp
  · have h_or := order_two_or_three_of_pair_iterSum_four_le_three x hx0 h_iter
    rcases h_or with h2x | h3x
    · have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_two_of_order_two x h2x
      use H
      refine ⟨hsub, ⟨s, hs_eq, by omega⟩⟩
    · exact closure_card_le_three_of_order_three x h3x

/-- Small set rigidity for 3 elements: If 0 ∈ S and S = {0, x, y} with |4S| ≤ 3,
    the subgroup generated by S has cardinality at most 3. -/
lemma closure_card_le_three_of_card_three_iterSum_four_le_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x y : G)
    (h_iter : (iterSum 4 ({0, x, y} : Finset G)).card ≤ 3) :
    ∃ (H : AddSubgroup G), (({0, x, y} : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 3) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hs : ({0, (0 : G), y} : Finset G) = {0, y} := by ext z; aesop
    have hs_set : ({0, (0 : G), y} : Set G) = {0, y} := by ext z; aesop
    have h_iter' : (iterSum 4 ({0, y} : Finset G)).card ≤ 3 := by
      rw [← hs]
      exact h_iter
    have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_pair_iterSum_four_le_three y h_iter'
    use H
    refine ⟨by rw [hs_set]; exact hsub, ⟨s, hs_eq, hcard⟩⟩
  · by_cases hy0 : y = 0
    · subst hy0
      have hs : ({0, x, (0 : G)} : Finset G) = {0, x} := by ext z; aesop
      have hs_set : ({0, x, (0 : G)} : Set G) = {0, x} := by ext z; aesop
      have h_iter' : (iterSum 4 ({0, x} : Finset G)).card ≤ 3 := by
        rw [← hs]
        exact h_iter
      have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_pair_iterSum_four_le_three x h_iter'
      use H
      refine ⟨by rw [hs_set]; exact hsub, ⟨s, hs_eq, hcard⟩⟩
    · by_cases hxy : x = y
      · subst hxy
        have hs : ({0, x, x} : Finset G) = {0, x} := by ext z; aesop
        have hs_set : ({0, x, x} : Set G) = {0, x} := by ext z; aesop
        have h_iter' : (iterSum 4 ({0, x} : Finset G)).card ≤ 3 := by
          rw [← hs]
          exact h_iter
        have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_pair_iterSum_four_le_three x h_iter'
        use H
        refine ⟨by rw [hs_set]; exact hsub, ⟨s, hs_eq, hcard⟩⟩
      · have h0 : (0 : G) ∈ ({0, x, y} : Finset G) := by simp
        have h1_sub_2 : iterSum 1 ({0, x, y} : Finset G) ⊆ iterSum 2 ({0, x, y} : Finset G) :=
          iterSum_subset_succ _ h0 1
        have h2_sub_4 : iterSum 2 ({0, x, y} : Finset G) ⊆ iterSum 4 ({0, x, y} : Finset G) :=
          iterSum_mono_of_zero_mem _ h0 (by omega)
        have h_S_sub_1 : ({0, x, y} : Finset G) ⊆ iterSum 1 ({0, x, y} : Finset G) := by
          intro z hz
          rw [iterSum_succ, mem_sumset_iff]
          exact ⟨0, by simp [iterSum_zero], z, hz, zero_add z⟩
        have h_S_sub_2 : ({0, x, y} : Finset G) ⊆ iterSum 2 ({0, x, y} : Finset G) :=
          h_S_sub_1.trans h1_sub_2
        have h_card_3 : ({0, x, y} : Finset G).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · intro h; aesop
          · intro h; aesop
        have h_card_2_le : (iterSum 2 ({0, x, y} : Finset G)).card ≤ 3 :=
          (Finset.card_le_card h2_sub_4).trans h_iter
        have h_card_2_ge : 3 ≤ (iterSum 2 ({0, x, y} : Finset G)).card := by
          rw [← h_card_3]
          exact Finset.card_le_card h_S_sub_2
        have h_card_2_eq : (iterSum 2 ({0, x, y} : Finset G)).card = 3 := by omega
        have h_eq : iterSum 2 ({0, x, y} : Finset G) = {0, x, y} :=
          (Finset.eq_of_subset_of_card_le h_S_sub_2 (by rw [h_card_2_eq, h_card_3])).symm
        have h_add : ∀ a ∈ ({0, x, y} : Finset G), ∀ b ∈ ({0, x, y} : Finset G),
            a + b ∈ ({0, x, y} : Finset G) := by
          intro a ha b hb
          have ha_1 : a ∈ iterSum 1 ({0, x, y} : Finset G) := h_S_sub_1 ha
          have hab : a + b ∈ iterSum 2 ({0, x, y} : Finset G) := by
            rw [iterSum_succ, mem_sumset_iff]
            exact ⟨a, ha_1, b, hb, rfl⟩
          rw [h_eq] at hab
          exact hab
        exact closure_card_le_three_of_card_three_add_self_eq x y h_add

/-- Structural classification of small sets containing 0 into singletons, pairs, or triples. -/
lemma exists_eq_pair_or_three_of_zero_mem_card_le_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (h0 : 0 ∈ S) (hS_card : S.card ≤ 3) :
    (S = {0}) ∨ (∃ x, S = {0, x}) ∨ (∃ x y, S = {0, x, y}) := by
  let S' := S \ {0}
  have hS_eq : S = insert (0 : G) S' := (Finset.insert_sdiff_self_of_mem h0).symm
  have h0_not_mem : (0 : G) ∉ S' := by simp [S']
  have hS'_card : S'.card ≤ 2 := by
    have : S.card = S'.card + 1 := by
      rw [hS_eq, Finset.card_insert_of_notMem h0_not_mem]
    omega
  interval_cases h : S'.card
  · have : S' = ∅ := Finset.card_eq_zero.mp h
    left
    rw [hS_eq, this, Finset.insert_empty]
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
    right; left
    use x
    rw [hS_eq, hx]
  · obtain ⟨x, y, _, hxy⟩ := Finset.card_eq_two.mp h
    right; right
    use x, y
    rw [hS_eq, hxy]

/-- Subgroup bound for any set S containing 0 with |S| ≤ 3 and |4S| ≤ 3:
    The additive subgroup generated by S has cardinality at most 3. -/
lemma closure_card_le_three_of_iterSum_four_le_three {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (h0 : 0 ∈ S) (hS_card : S.card ≤ 3)
    (h_iter : (iterSum 4 S).card ≤ 3) :
    ∃ (H : AddSubgroup G), ((S : Set G) ⊆ H) ∧
      (∃ (s : Finset G), (H : Set G) = (s : Set G) ∧ s.card ≤ 3) := by
  rcases exists_eq_pair_or_three_of_zero_mem_card_le_three S h0 hS_card with h1 | ⟨x, h2⟩ | ⟨x, y, h3⟩
  · subst h1
    use ⊥
    refine ⟨by simp, ⟨{0}, by simp, by simp⟩⟩
  · subst h2
    have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_pair_iterSum_four_le_three x h_iter
    use H
    refine ⟨?_, ⟨s, hs_eq, hcard⟩⟩
    intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    exact hsub hz
  · subst h3
    have ⟨H, hsub, s, hs_eq, hcard⟩ := closure_card_le_three_of_card_three_iterSum_four_le_three x y h_iter
    use H
    refine ⟨?_, ⟨s, hs_eq, hcard⟩⟩
    intro z hz
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    exact hsub hz

/-- Reducing the cardinality bound on B from an AP cover and Selberg sieve rough count. -/
lemma card_le_sieve_bound_of_cover
    (B : Finset ℕ) (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (Q : ℕ) (hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
    (R_card d : ℕ) (hR_card : R_card ≤ 128 * d)
    (cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ))) R_card fc.t p.n)
    (C_sieve : ℝ) (hC_nonneg : 0 ≤ C_sieve)
    (h_sieve : ∀ i ∈ cov.I, (roughCount (cov.APs i) Q : ℝ) ≤ ((cov.APs i).k : ℝ) * C_sieve) :
    (B.card : ℝ) ≤ 384 * (d : ℝ) * C_sieve := by
  let B_int := B.image (fun (a : ℕ) => (a : ℤ))
  have hB_card : B_int.card = B.card :=
    Finset.card_image_of_injective B Nat.cast_injective
  have hB_int_rough : ∀ z ∈ B_int, Nat.Coprime z.natAbs Q := by
    intro z hz
    simp only [B_int, Finset.mem_image] at hz
    rcases hz with ⟨a, ha, rfl⟩
    rw [Int.natAbs_natCast]
    exact hB_rough a ha
  have h_sum_real : (∑ i ∈ cov.I, (cov.APs i).k : ℝ) ≤ 384 * (d : ℝ) := by
    have h1 : ∑ i ∈ cov.I, (cov.APs i).k ≤ 3 * R_card := cov.h_sum_len
    have h2 : 3 * R_card ≤ 384 * d := by omega
    have h_le : ∑ i ∈ cov.I, (cov.APs i).k ≤ 384 * d := h1.trans h2
    exact_mod_cast h_le
  have h_bound := card_le_sieve_bound_of_ap_family
    B_int Q hB_int_rough cov.I cov.APs cov.h_cov d p.n p.r C_sieve hC_nonneg h_sieve h_sum_real
  rw [hB_card] at h_bound
  exact h_bound

/-- Pure Structural Trichotomy for smallGrowth (CFP Lemma 2.4 / Deshouillers–Freiman):
    For a generating set with small growth and small density (xi ≤ 1/20), G is either:
    1. Contained in a proper additive subgroup H < ZMod N;
    2. Has small cardinality bounded by 20 * (2d)^(51/50) / |T|^(1/50);
    3. Contained in a coset AP R with length at most 128 * d. -/
def SmallGrowthTrichotomy (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) : Prop :=
  let G := smallGrowth T d
  -- Branch 1: G is contained in a proper additive subgroup
  (∃ (H : AddSubgroup (ZMod N)) (_hH : H ≠ ⊤), (G : Set (ZMod N)) ⊆ (H : Set (ZMod N))) ∨
  -- Branch 2: G has small cardinality bounded by the Deshouillers–Freiman bound
  (((G.card : ℝ)) ≤ 20 * (2 * (d : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50)) ∨
  -- Branch 3: G is covered by a coset AP R with length at most 128 * d
  (∃ (R : CosetAP N), G ⊆ R.toFinset ∧ R.ell * (R.H : Set (ZMod N)).toFinset.card ≤ 128 * d)

/-- Full-group inputs can never satisfy the small density condition xi ≤ 1/20
    (mathematically blocking the diagnostic counterexample). -/
theorem univ_cannot_satisfy_small_density (N : ℕ) [NeZero N] (xi : ℝ)
    (h_xi_le : xi ≤ (1 / 20 : ℝ))
    (h_dense : ((Finset.univ : Finset (ZMod N)).card : ℝ) < xi * (N : ℝ)) : False := by
  have h_card : (Finset.univ : Finset (ZMod N)).card = N := ZMod.card N
  rw [h_card] at h_dense
  have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := NeZero.one_le
    exact_mod_cast this
  have h_le : xi * (N : ℝ) ≤ (1 / 20 : ℝ) * (N : ℝ) := by
    have : 0 ≤ (N : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right h_xi_le this
  have h_lt : (N : ℝ) < (1 / 20 : ℝ) * (N : ℝ) := h_dense.trans_le h_le
  linarith

/-- Arithmetic density inequality: Under xi ≤ 1/20 and 8d < |T| < xi * N,
    we have 128 * d < N. -/
lemma mul_128_lt_of_density (N : ℕ) [NeZero N] (d : ℕ) (T : Finset (ZMod N)) (xi : ℝ)
    (h_xi_le : xi ≤ (1 / 20 : ℝ))
    (hd_lt : 8 * d < T.card)
    (h_dense : (T.card : ℝ) < xi * (N : ℝ)) :
    128 * d < N := by
  have hd_real : 8 * (d : ℝ) < (T.card : ℝ) := by exact_mod_cast hd_lt
  have h_le : xi * (N : ℝ) ≤ (1 / 20 : ℝ) * (N : ℝ) := by
    have : 0 ≤ (N : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right h_xi_le this
  have h_T_lt : (T.card : ℝ) < (1 / 20 : ℝ) * (N : ℝ) := h_dense.trans_le h_le
  have h_128 : (128 * d : ℝ) = 16 * (8 * (d : ℝ)) := by ring
  have h_lt_real : (128 * d : ℝ) < (N : ℝ) := by
    calc (128 * d : ℝ) = 16 * (8 * (d : ℝ)) := h_128
    _ < 16 * (T.card : ℝ) := by linarith
    _ < 16 * ((1 / 20 : ℝ) * (N : ℝ)) := by linarith
    _ = (4 / 5 : ℝ) * (N : ℝ) := by ring
    _ < (N : ℝ) := by
      have hN_pos : 0 < (N : ℝ) := by
        have : 0 < N := NeZero.pos N
        exact_mod_cast this
      linarith
  exact_mod_cast h_lt_real

/-- An additive subgroup of ZMod N whose cardinality is strictly less than N is proper (H ≠ ⊤). -/
lemma proper_subgroup_of_card_lt (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N))
    (h_card : (H : Set (ZMod N)).toFinset.card < N) : H ≠ ⊤ := by
  intro h_top
  have h_finset : (H : Set (ZMod N)).toFinset = Finset.univ := by
    ext x
    simp [h_top]
  have h_eq : (H : Set (ZMod N)).toFinset.card = N := by
    rw [h_finset, Finset.card_univ, ZMod.card N]
  omega

/-- An additive subgroup of ZMod N whose cardinality is bounded by 128 * d is proper
    under the small density condition xi ≤ 1/20 and 8d < |T| < xi * N. -/
lemma proper_subgroup_of_card_le_128d (N : ℕ) [NeZero N] (d : ℕ) (T : Finset (ZMod N)) (xi : ℝ)
    (h_xi_le : xi ≤ (1 / 20 : ℝ))
    (hd_lt : 8 * d < T.card)
    (h_dense : (T.card : ℝ) < xi * (N : ℝ))
    (H : AddSubgroup (ZMod N))
    (hH_card : (H : Set (ZMod N)).toFinset.card ≤ 128 * d) :
    H ≠ ⊤ := by
  have h_128_lt : 128 * d < N := mul_128_lt_of_density N d T xi h_xi_le hd_lt h_dense
  have h_card_lt : (H : Set (ZMod N)).toFinset.card < N := hH_card.trans_lt h_128_lt
  exact proper_subgroup_of_card_lt N H h_card_lt

/-- The cardinality of the join of two additive subgroups in ZMod N is bounded
    by the product of their cardinalities. -/
lemma card_sup_subgroup_le (N : ℕ) [NeZero N] (H K : AddSubgroup (ZMod N)) :
    ((H ⊔ K : AddSubgroup (ZMod N)) : Set (ZMod N)).toFinset.card ≤
    (H : Set (ZMod N)).toFinset.card * (K : Set (ZMod N)).toFinset.card := by
  let s := (H : Set (ZMod N)).toFinset
  let t := (K : Set (ZMod N)).toFinset
  let U := t.biUnion (fun k => s.image (fun h => h + k))
  have h_sub : ((H ⊔ K : AddSubgroup (ZMod N)) : Set (ZMod N)).toFinset ⊆ U := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    rw [SetLike.mem_coe] at hx
    rw [AddSubgroup.mem_sup] at hx
    rcases hx with ⟨h, hh, k, hk, rfl⟩
    rw [Finset.mem_biUnion]
    refine ⟨k, ?_, ?_⟩
    · rw [Set.mem_toFinset, SetLike.mem_coe]
      exact hk
    · rw [Finset.mem_image]
      refine ⟨h, ?_, rfl⟩
      rw [Set.mem_toFinset, SetLike.mem_coe]
      exact hh
  have h_le_U : ((H ⊔ K : AddSubgroup (ZMod N)) : Set (ZMod N)).toFinset.card ≤ U.card :=
    Finset.card_le_card h_sub
  have h_biUnion := Finset.card_biUnion_le (s := t) (t := fun k => s.image (fun h => h + k))
  have h_img : ∀ k ∈ t, (s.image (fun h => h + k)).card ≤ s.card := by
    intro k _hk
    exact Finset.card_image_le
  have h_sum : ∑ k ∈ t, (s.image (fun h => h + k)).card ≤ ∑ _k ∈ t, s.card :=
    Finset.sum_le_sum h_img
  rw [Finset.sum_const, smul_eq_mul] at h_sum
  have h_U_le : U.card ≤ t.card * s.card := h_biUnion.trans h_sum
  rw [mul_comm] at h_U_le
  exact h_le_U.trans h_U_le

/-- 3-Coset Absorption into Proper Subgroup:
    If a subset T ⊆ ZMod N is covered by at most 3 cosets C + H_0 of a subgroup H_0,
    where 0 ∈ C, |C| ≤ 3, |4C| ≤ 3, and 3 * |H_0| ≤ 128 * d,
    then under the small density condition (8d < |T| < xi * N with xi ≤ 1/20),
    T is contained in a PROPER additive subgroup H < ⊤. -/
lemma proper_subgroup_of_three_coset_absorption
    (N : ℕ) [NeZero N] (d : ℕ) (T : Finset (ZMod N)) (xi : ℝ)
    (h_xi_le : xi ≤ (1 / 20 : ℝ))
    (hd_lt : 8 * d < T.card)
    (h_dense : (T.card : ℝ) < xi * (N : ℝ))
    (H_0 : AddSubgroup (ZMod N))
    (C : Finset (ZMod N)) (h0 : 0 ∈ C) (hC_card : C.card ≤ 3)
    (hC_iter : (iterSum 4 C).card ≤ 3)
    (hH0_card : 3 * (H_0 : Set (ZMod N)).toFinset.card ≤ 128 * d)
    (hT_cov : ∀ t ∈ T, ∃ c ∈ C, ∃ h ∈ H_0, t = c + h) :
    ∃ (H : AddSubgroup (ZMod N)) (_hH : H ≠ ⊤), (T : Set (ZMod N)) ⊆ (H : Set (ZMod N)) := by
  have ⟨K, hCK, s, hs_eq, hs_card⟩ :=
    closure_card_le_three_of_iterSum_four_le_three C h0 hC_card hC_iter
  let H := H_0 ⊔ K
  have hT_sub : (T : Set (ZMod N)) ⊆ (H : Set (ZMod N)) := by
    intro t ht
    rcases hT_cov t (Finset.mem_coe.mp ht) with ⟨c, hc, h, hh, rfl⟩
    have hcK : c ∈ (K : Set (ZMod N)) := hCK (Finset.mem_coe.mpr hc)
    have hcK' : c ∈ K := SetLike.mem_coe.mp hcK
    have hcH : c ∈ H := AddSubgroup.mem_sup_right hcK'
    have hhH : h ∈ H := AddSubgroup.mem_sup_left hh
    have h_add : c + h ∈ H := H.add_mem hcH hhH
    exact SetLike.mem_coe.mpr h_add
  have hK_card : (K : Set (ZMod N)).toFinset.card ≤ 3 := by
    have h_eq : (K : Set (ZMod N)).toFinset = s := by
      ext z
      simp only [Set.mem_toFinset, hs_eq, Finset.mem_coe]
    rw [h_eq]
    exact hs_card
  have hH_card_le : (H : Set (ZMod N)).toFinset.card ≤ 128 * d := by
    have h_prod := card_sup_subgroup_le N H_0 K
    have h_mul_3 : (H_0 : Set (ZMod N)).toFinset.card * (K : Set (ZMod N)).toFinset.card ≤
        (H_0 : Set (ZMod N)).toFinset.card * 3 :=
      Nat.mul_le_mul_left (H_0 : Set (ZMod N)).toFinset.card hK_card
    rw [mul_comm (H_0 : Set (ZMod N)).toFinset.card 3] at h_mul_3
    exact h_prod.trans (h_mul_3.trans hH0_card)
  have hH_proper : H ≠ ⊤ :=
    proper_subgroup_of_card_le_128d N d T xi h_xi_le hd_lt h_dense H hH_card_le
  exact ⟨H, hH_proper, hT_sub⟩

/-- If T is contained in an additive subgroup H and d < |T|,
    then smallGrowth T d is also contained in H. -/
lemma smallGrowth_subset_subgroup {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (T : Finset G) (d : ℕ) (hd_lt : d < T.card)
    (H : AddSubgroup G) (hTH : (T : Set G) ⊆ (H : Set G)) :
    (smallGrowth T d : Set G) ⊆ (H : Set G) := by
  intro x hx
  rw [Finset.mem_coe] at hx
  simp only [smallGrowth, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  by_contra hxH
  have h_disj : Disjoint (translate T x) T := by
    rw [Finset.disjoint_left]
    intro y hy_trans hy_T
    rw [translate, Finset.mem_image] at hy_trans
    rcases hy_trans with ⟨t, ht, rfl⟩
    have htH : t ∈ H := hTH (Finset.mem_coe.mpr ht)
    have htxH : t + x ∈ H := hTH (Finset.mem_coe.mpr hy_T)
    have hx_sub : x = (t + x) - t := by abel
    have hx_in_H : x ∈ H := by
      rw [hx_sub]
      exact H.sub_mem htxH htH
    exact hxH hx_in_H
  have h_sdiff : translate T x \ T = translate T x :=
    Finset.sdiff_eq_self_iff_disjoint.mpr h_disj
  have h_delta : delta T x = T.card := by
    dsimp [delta]
    rw [h_sdiff, card_translate]
  rw [h_delta] at hx
  omega

/-- Upgraded 3-Coset Absorption into Proper Subgroup for smallGrowth:
    If T is covered by at most 3 cosets of H_0 satisfying the small doubling and size bounds,
    then smallGrowth T d is contained in a PROPER additive subgroup H < ⊤. -/
lemma proper_subgroup_smallGrowth_of_three_coset_absorption
    (N : ℕ) [NeZero N] (d : ℕ) (T : Finset (ZMod N)) (xi : ℝ)
    (h_xi_le : xi ≤ (1 / 20 : ℝ))
    (hd_lt : 8 * d < T.card)
    (h_dense : (T.card : ℝ) < xi * (N : ℝ))
    (H_0 : AddSubgroup (ZMod N))
    (C : Finset (ZMod N)) (h0 : 0 ∈ C) (hC_card : C.card ≤ 3)
    (hC_iter : (iterSum 4 C).card ≤ 3)
    (hH0_card : 3 * (H_0 : Set (ZMod N)).toFinset.card ≤ 128 * d)
    (hT_cov : ∀ t ∈ T, ∃ c ∈ C, ∃ h ∈ H_0, t = c + h) :
    ∃ (H : AddSubgroup (ZMod N)) (_hH : H ≠ ⊤), (smallGrowth T d : Set (ZMod N)) ⊆ (H : Set (ZMod N)) := by
  have ⟨H, hH_proper, hT_sub⟩ := proper_subgroup_of_three_coset_absorption N d T xi h_xi_le hd_lt h_dense H_0 C h0 hC_card hC_iter hH0_card hT_cov
  have hd_lt_card : d < T.card := by omega
  have hG_sub := smallGrowth_subset_subgroup T d hd_lt_card H hT_sub
  exact ⟨H, hH_proper, hG_sub⟩

/-- If smallGrowth T d does not generate the full group, it is contained in a proper subgroup. -/
lemma smallGrowth_proper_subgroup_of_closure_ne_top (N : ℕ) [NeZero N]
    (T : Finset (ZMod N)) (d : ℕ)
    (h_not_top : AddSubgroup.closure (smallGrowth T d : Set (ZMod N)) ≠ ⊤) :
    ∃ (H : AddSubgroup (ZMod N)) (_hH : H ≠ ⊤), (smallGrowth T d : Set (ZMod N)) ⊆ (H : Set (ZMod N)) :=
  ⟨AddSubgroup.closure (smallGrowth T d : Set (ZMod N)), h_not_top, AddSubgroup.subset_closure⟩

/-- Arithmetic progression coset lifting and sieve interface for Phase P17 (CFP Lemma 5.10):
    For any candidate subset B ⊆ fc.A with |B| ≥ M whose quotient image is covered by a coset AP
    R with R.ell * |R.H| ≤ 128 * D, the sieve bound holds. -/
def APCoverSieveBridge (fc : FiniteConditions) (p : P17FiniteArithConditions fc) : Prop :=
  ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
    [NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D),
    (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset →
    (B.card : ℝ) ≤ 98304 * (fc.D : ℝ) * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)

/-- Proving the APCoverSieveBridge from an IntAPCover and Selberg sieve rough count bound:
    For any candidate subset B ⊆ fc.A, if B is covered by an IntAPCover whose APs
    satisfy the Selberg rough count bound, then B satisfies the 98304 sieve bound. -/
theorem apCoverSieveBridge_of_cover_and_sieve
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (h_cov_sieve : ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
      [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
      (R : CosetAP (fc.t / subgroupIndex fc.t B))
      (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
      (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset),
      ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
        (cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
          (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n)
        (C_sieve : ℝ) (_hC_nonneg : 0 ≤ C_sieve)
        (_h_sieve : ∀ i ∈ cov.I, (roughCount (cov.APs i) Q : ℝ) ≤ ((cov.APs i).k : ℝ) * C_sieve)
        (_hC_eq : C_sieve = 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)),
        True) :
    APCoverSieveBridge fc p := by
  intro B hBA hB_card instN R hR_card hQR
  rcases h_cov_sieve B hBA hB_card R hR_card hQR with ⟨Q, hB_rough, cov, C_sieve, hC_nonneg, h_sieve, hC_eq, _⟩
  have h_bound := card_le_sieve_bound_of_cover B fc p Q hB_rough
    (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card)
    fc.D hR_card cov C_sieve hC_nonneg h_sieve
  rw [hC_eq] at h_bound
  have h_ring : 384 * (fc.D : ℝ) * (256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)) =
      98304 * (fc.D : ℝ) * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ) := by ring
  rwa [h_ring] at h_bound

/-- P17 Step Growth Master Contradiction:
    Under P17 finite arithmetic conditions, the structural trichotomy (under xi ≤ 1/20),
    and the AP sieve bridge, every unsaturated step satisfies fc.D ≤ greedyDelta fc j. -/
theorem unsaturated_step_growth_of_arith_conditional
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_trichotomy : ∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) (xi : ℝ),
      8 * d < T.card → 0 < xi → xi ≤ (1 / 20 : ℝ) → (T.card : ℝ) < xi * (N : ℝ) →
      SmallGrowthTrichotomy N T d)
    (h_sieve : APCoverSieveBridge fc p)
    (j : ℕ) (hj : j ∈ unsaturatedSteps fc) :
    fc.D ≤ greedyDelta fc j := by
  have h_inj := p.injOn_A fc
  by_contra! h_lt
  have h_le : greedyDelta fc j ≤ fc.D := by omega
  have h_med := unsaturated_step_medium_fiber_and_smallGrowth fc h_inj j hj h_le
  let st := greedySeq fc j
  let g := st.g fc.t
  let N := fc.t / g
  have instN : NeZero N := unsaturatedSteps_div_neZero fc j hj
  have : NeZero (fc.t / subgroupIndex fc.t st.B) := instN
  let Q := st.B.image (fun a => ((a / g : ℕ) : ZMod N))
  rcases h_med with ⟨T, hT_U, hT_xi, hQ_sub, hM_Q, hQ_gen⟩

  have h8D_T : 8 * fc.D < T.card := by
    have h8D_U := fc.h_growth_threshold
    omega

  have h_div_real : (fc.t : ℝ) / (g : ℝ) = (N : ℝ) := by
    have hd : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t st.B
    have hg_pos : 0 < g := subgroupIndex_pos fc.t st.B fc.ht_pos
    have h_div_mul := Nat.div_mul_cancel hd
    rw [← h_div_mul]
    push_cast
    have : (g : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_right₀ (N : ℝ) this

  have hT_xi_N : (T.card : ℝ) < fc.xi * (N : ℝ) := by
    calc (T.card : ℝ) < fc.xi * (fc.t : ℝ) / (g : ℝ) := hT_xi
    _ = fc.xi * ((fc.t : ℝ) / (g : ℝ)) := by ring
    _ = fc.xi * (N : ℝ) := by rw [h_div_real]

  have h_trich := h_trichotomy N T fc.D fc.xi h8D_T fc.hxi_pos p.h_xi_le hT_xi_N
  let G := smallGrowth T fc.D

  rcases h_trich with ⟨H, hH_ne, hGH⟩ | h_small | ⟨R, hGR, hR_card⟩
  -- Branch 1: Proper subgroup containment
  · have hQH : (Q : Set (ZMod N)) ⊆ (H : Set (ZMod N)) := by
      intro x hx
      exact hGH (hQ_sub (Finset.mem_coe.mp hx))
    have h_clos_le : AddSubgroup.closure (Q : Set (ZMod N)) ≤ H := by
      rw [AddSubgroup.closure_le]
      exact hQH
    rw [hQ_gen] at h_clos_le
    have hH_top : H = ⊤ := top_le_iff.mp h_clos_le
    exact hH_ne hH_top

  -- Branch 2: Small cardinality bound
  · have hU_pos : (0 : ℝ) < (fc.U : ℝ) := Nat.cast_pos.mpr fc.hU_pos
    have hT_pos_nat : 0 < T.card := by omega
    have hT_pos : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.mpr hT_pos_nat
    have h_exp_pos : (0 : ℝ) < (1 : ℝ) / 50 := by norm_num
    have h_rpow_lt : (fc.U : ℝ) ^ ((1 : ℝ) / 50) < ((T.card : ℝ)) ^ ((1 : ℝ) / 50) := by
      apply Real.rpow_lt_rpow (le_of_lt hU_pos) (by exact_mod_cast hT_U) h_exp_pos
    have h_bound_lt : 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50) <
        20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / (fc.U : ℝ) ^ ((1 : ℝ) / 50) := by
      have hD_pos : (0 : ℝ) < (fc.D : ℝ) := Nat.cast_pos.mpr fc.hD_pos
      have h_num_pos : (0 : ℝ) < 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) := by
        have : (0 : ℝ) < 2 * (fc.D : ℝ) := by linarith
        have h_pow := Real.rpow_pos_of_pos this ((51 : ℝ) / 50)
        linarith
      have h_den_pos : (0 : ℝ) < (fc.U : ℝ) ^ ((1 : ℝ) / 50) := Real.rpow_pos_of_pos hU_pos _
      exact div_lt_div_of_pos_left h_num_pos h_den_pos h_rpow_lt
    have hE1 := p.hE1
    have hG_card_lt_M : (G.card : ℝ) < (fc.M : ℝ) :=
      h_small.trans_lt (h_bound_lt.trans hE1)
    have hQ_le_G : Q.card ≤ G.card := Finset.card_le_card hQ_sub
    have hM_le_Q_real : (fc.M : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hM_Q
    have hQ_le_G_real : (Q.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hQ_le_G
    linarith

  -- Branch 3: AP cover & sieve bound
  · have hQR : Q ⊆ R.toFinset := hQ_sub.trans hGR
    have hB_sub : st.B ⊆ fc.A := Finset.sdiff_subset
    have hB_card : fc.M ≤ st.B.card := by
      classical
      apply st.B_card_ge
      have hj_range : j ∈ Finset.range fc.K := (Finset.mem_filter.mp hj).1
      have hj_lt : j < fc.K := Finset.mem_range.mp hj_range
      rw [card_greedySeq_E fc j (by omega)]
      omega
    have h_bound := @h_sieve st.B hB_sub hB_card instN R hR_card hQR
    have hE3 := p.hE3
    have hB_lt_M : (st.B.card : ℝ) < (fc.M : ℝ) := h_bound.trans_lt hE3
    have hM_le_B : (fc.M : ℝ) ≤ (st.B.card : ℝ) := by exact_mod_cast hB_card
    linarith

/-- All unsaturated steps satisfy greedyDelta ≥ D under P17 conditions, trichotomy, and sieve bridge. -/
theorem unsaturatedSteps_growth_of_arith_conditional
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_trichotomy : ∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) (xi : ℝ),
      8 * d < T.card → 0 < xi → xi ≤ (1 / 20 : ℝ) → (T.card : ℝ) < xi * (N : ℝ) →
      SmallGrowthTrichotomy N T d)
    (h_sieve : APCoverSieveBridge fc p) :
    ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j :=
  fun j hj => unsaturated_step_growth_of_arith_conditional fc p h_trichotomy h_sieve j hj

/-- CFP Lemma 5.6 Finite Core with P17 Arithmetic Integration:
    Unconditionally closes both h_inj and h_unsaturated_step_growth under
    explicit P17 arithmetic conditions, the structural trichotomy, and the sieve bridge. -/
theorem cfp_lemma_5_6_finite_core_of_arith_conditional
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_trichotomy : ∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) (xi : ℝ),
      8 * d < T.card → 0 < xi → xi ≤ (1 / 20 : ℝ) → (T.card : ℝ) < xi * (N : ℝ) →
      SmallGrowthTrichotomy N T d)
    (h_sieve : APCoverSieveBridge fc p) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  have h_inj := p.injOn_A fc
  have h_unsat := unsaturatedSteps_growth_of_arith_conditional fc p h_trichotomy h_sieve
  exact cfp_lemma_5_6_finite_core_closed fc h_inj h_numeric h_unsat

/-!
#### Guarded Coset-AP Cover Interface (Branch 3 of the Trichotomy, Isolated)

The earlier "pure AP cover" hypothesis

  `∀ N [NeZero N] (T : Finset (ZMod N)) (d : ℕ), ∃ R : CosetAP N,
     smallGrowth T d ⊆ R.toFinset ∧ R.ell * |R.H| ≤ 128 * d`

is **false** (`not_unguarded_ap_cover`): for `T = univ` the small growth set is the whole group,
which no coset AP with `R.ell * |R.H| ≤ 128 * d` can cover once `N > 128 * d`. Every theorem that
assumed it was therefore vacuous. The interface `GuardedAPCover` below keeps exactly the guards
under which the structure theorem is invoked at an unsaturated step, and is provably equivalent
to the guarded trichotomy hypothesis `GuardedTrichotomy` (`guardedAPCover_iff_trichotomy`):
Branch 1 is excluded by requiring that the small growth set generates `ZMod N`, Branch 2 by
requiring that it exceeds the Deshouillers–Freiman cardinality threshold.
-/

/-- The guarded structural trichotomy hypothesis, exactly as consumed by
    `unsaturated_step_growth_of_arith_conditional`. -/
def GuardedTrichotomy : Prop :=
  ∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) (xi : ℝ),
    8 * d < T.card → 0 < xi → xi ≤ (1 / 20 : ℝ) → (T.card : ℝ) < xi * (N : ℝ) →
    SmallGrowthTrichotomy N T d

/-- Guarded coset-AP cover hypothesis: Branch 3 of `SmallGrowthTrichotomy`, restricted to the
    situation in which Branches 1 and 2 are excluded by the hypotheses themselves:
    * density window `8 * d < |T| < xi * N` with `0 < xi ≤ 1/20` (excludes `T = univ`);
    * the small growth set generates `ZMod N` (excludes Branch 1, proper subgroup);
    * the small growth set exceeds the Deshouillers–Freiman threshold (excludes Branch 2). -/
def GuardedAPCover : Prop :=
  ∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ) (xi : ℝ),
    8 * d < T.card → 0 < xi → xi ≤ (1 / 20 : ℝ) → (T.card : ℝ) < xi * (N : ℝ) →
    AddSubgroup.closure (smallGrowth T d : Set (ZMod N)) = ⊤ →
    20 * (2 * (d : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50) < ((smallGrowth T d).card : ℝ) →
    ∃ (R : CosetAP N), smallGrowth T d ⊆ R.toFinset ∧
      R.ell * (R.H : Set (ZMod N)).toFinset.card ≤ 128 * d

/-- The guarded trichotomy yields the guarded AP cover: under the two extra guards, Branch 1 and
    Branch 2 of the trichotomy are impossible, so Branch 3 must hold. -/
theorem guardedAPCover_of_trichotomy (h : GuardedTrichotomy) : GuardedAPCover := by
  intro N _ T d xi h8 hxi_pos hxi_le h_dense h_gen h_big
  rcases h N T d xi h8 hxi_pos hxi_le h_dense with ⟨H, hH_ne, hGH⟩ | h_small | h_cover
  · have h_le : AddSubgroup.closure (smallGrowth T d : Set (ZMod N)) ≤ H :=
      (AddSubgroup.closure_le H).mpr hGH
    rw [h_gen] at h_le
    exact absurd (top_le_iff.mp h_le) hH_ne
  · exact absurd h_small (not_le.mpr h_big)
  · exact h_cover

/-- The guarded AP cover yields the guarded trichotomy: if the small growth set does not generate
    `ZMod N` we are in Branch 1, if it is below the threshold we are in Branch 2, and otherwise
    the guarded cover provides Branch 3. -/
theorem trichotomy_of_guardedAPCover (h : GuardedAPCover) : GuardedTrichotomy := by
  intro N _ T d xi h8 hxi_pos hxi_le h_dense
  simp only [SmallGrowthTrichotomy]
  by_cases h_gen : AddSubgroup.closure (smallGrowth T d : Set (ZMod N)) = ⊤
  · by_cases h_small : ((smallGrowth T d).card : ℝ) ≤
        20 * (2 * (d : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50)
    · exact Or.inr (Or.inl h_small)
    · exact Or.inr (Or.inr (h N T d xi h8 hxi_pos hxi_le h_dense h_gen (not_le.mp h_small)))
  · exact Or.inl (smallGrowth_proper_subgroup_of_closure_ne_top N T d h_gen)

/-- The guarded AP cover interface is equivalent to the guarded structural trichotomy. -/
theorem guardedAPCover_iff_trichotomy : GuardedAPCover ↔ GuardedTrichotomy :=
  ⟨trichotomy_of_guardedAPCover, guardedAPCover_of_trichotomy⟩

/-- The unguarded "pure AP cover" statement is false for every `d`: in `ZMod (128 * d + 1)` take
    `T = univ`; then `smallGrowth T d = univ` has `128 * d + 1` elements, while any coset AP `R`
    with `R.ell * |R.H| ≤ 128 * d` has at most `128 * d` elements. -/
theorem not_unguarded_ap_cover (d : ℕ) :
    ¬ (∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)),
      ∃ (R : CosetAP N), smallGrowth T d ⊆ R.toFinset ∧
        R.ell * (R.H : Set (ZMod N)).toFinset.card ≤ 128 * d) := by
  intro h
  have : NeZero (128 * d + 1) := ⟨by omega⟩
  obtain ⟨R, h_sub, h_card⟩ := h (128 * d + 1) (Finset.univ : Finset (ZMod (128 * d + 1)))
  have h_delta : ∀ x : ZMod (128 * d + 1),
      delta (Finset.univ : Finset (ZMod (128 * d + 1))) x = 0 := by
    intro x
    simp only [delta, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact Finset.subset_univ _
  have h_univ : smallGrowth (Finset.univ : Finset (ZMod (128 * d + 1))) d = Finset.univ := by
    ext x
    simp [smallGrowth, h_delta]
  have h_le : (Finset.univ : Finset (ZMod (128 * d + 1))).card ≤ R.toFinset.card := by
    rw [← h_univ]
    exact Finset.card_le_card h_sub
  rw [Finset.card_univ, ZMod.card] at h_le
  exact absurd (h_le.trans (R.card_toFinset_le.trans h_card)) (by omega)

/-- Consequently the original unguarded hypothesis (quantified over `d` as well) is refutable;
    any theorem assuming it is vacuous. This is the reason for the guards in `GuardedAPCover`. -/
theorem not_unguarded_ap_cover' :
    ¬ (∀ (N : ℕ) [NeZero N] (T : Finset (ZMod N)) (d : ℕ),
      ∃ (R : CosetAP N), smallGrowth T d ⊆ R.toFinset ∧
        R.ell * (R.H : Set (ZMod N)).toFinset.card ≤ 128 * d) := by
  intro h
  apply not_unguarded_ap_cover 0
  intro N _ T
  exact h N T 0

/-- Guarded AP Cover Step Growth Contradiction (Branch 3 interface):
    Under P17 finite arithmetic conditions and the guarded coset-AP cover `GuardedAPCover`
    (Branch 3 of the structural trichotomy, with the guards that exclude Branches 1 and 2 supplied
    here from `closure Q = ⊤` and condition E1), every unsaturated step satisfies greedyDelta fc j ≥ D.
    `GuardedAPCover` is equivalent to the guarded trichotomy (`guardedAPCover_iff_trichotomy`);
    the unguarded form is false (`not_unguarded_ap_cover'`). -/
theorem unsaturated_step_growth_of_ap_cover
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_ap_cover : GuardedAPCover)
    (h_sieve : APCoverSieveBridge fc p)
    (j : ℕ) (hj : j ∈ unsaturatedSteps fc) :
    fc.D ≤ greedyDelta fc j := by
  have h_inj := p.injOn_A fc
  by_contra! h_lt
  have h_le : greedyDelta fc j ≤ fc.D := by omega
  have h_med := unsaturated_step_medium_fiber_and_smallGrowth fc h_inj j hj h_le
  let st := greedySeq fc j
  let g := st.g fc.t
  let N := fc.t / g
  have instN : NeZero N := unsaturatedSteps_div_neZero fc j hj
  have : NeZero (fc.t / subgroupIndex fc.t st.B) := instN
  let Q := st.B.image (fun a => ((a / g : ℕ) : ZMod N))
  rcases h_med with ⟨T, hT_U, hT_xi, hQ_sub, hM_Q, hQ_gen⟩

  have h8D_T : 8 * fc.D < T.card := by
    have h8D_U := fc.h_growth_threshold
    omega

  have h_div_real : (fc.t : ℝ) / (g : ℝ) = (N : ℝ) := by
    have hd : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t st.B
    have hg_pos : 0 < g := subgroupIndex_pos fc.t st.B fc.ht_pos
    have h_div_mul := Nat.div_mul_cancel hd
    rw [← h_div_mul]
    push_cast
    have : (g : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_right₀ (N : ℝ) this

  have hT_xi_N : (T.card : ℝ) < fc.xi * (N : ℝ) := by
    calc (T.card : ℝ) < fc.xi * (fc.t : ℝ) / (g : ℝ) := hT_xi
    _ = fc.xi * ((fc.t : ℝ) / (g : ℝ)) := by ring
    _ = fc.xi * (N : ℝ) := by rw [h_div_real]

  -- Guard 1 (excludes Branch 1): Q ⊆ smallGrowth T D and Q generates ZMod N.
  have h_gen : AddSubgroup.closure (smallGrowth T fc.D : Set (ZMod N)) = ⊤ := by
    have h_mono : AddSubgroup.closure (Q : Set (ZMod N)) ≤
        AddSubgroup.closure (smallGrowth T fc.D : Set (ZMod N)) :=
      AddSubgroup.closure_mono (Finset.coe_subset.mpr hQ_sub)
    rw [hQ_gen] at h_mono
    exact top_le_iff.mp h_mono

  -- Guard 2 (excludes Branch 2): M ≤ |Q| ≤ |smallGrowth T D| and E1 with U < |T|.
  have h_big : 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50) <
      ((smallGrowth T fc.D).card : ℝ) := by
    have hU_pos : (0 : ℝ) < (fc.U : ℝ) := Nat.cast_pos.mpr fc.hU_pos
    have h_exp_pos : (0 : ℝ) < (1 : ℝ) / 50 := by norm_num
    have h_rpow_lt : (fc.U : ℝ) ^ ((1 : ℝ) / 50) < ((T.card : ℝ)) ^ ((1 : ℝ) / 50) := by
      apply Real.rpow_lt_rpow (le_of_lt hU_pos) (by exact_mod_cast hT_U) h_exp_pos
    have h_bound_lt : 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / ((T.card : ℝ)) ^ ((1 : ℝ) / 50) <
        20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) / (fc.U : ℝ) ^ ((1 : ℝ) / 50) := by
      have hD_pos : (0 : ℝ) < (fc.D : ℝ) := Nat.cast_pos.mpr fc.hD_pos
      have h_num_pos : (0 : ℝ) < 20 * (2 * (fc.D : ℝ)) ^ ((51 : ℝ) / 50) := by
        have : (0 : ℝ) < 2 * (fc.D : ℝ) := by linarith
        have h_pow := Real.rpow_pos_of_pos this ((51 : ℝ) / 50)
        linarith
      have h_den_pos : (0 : ℝ) < (fc.U : ℝ) ^ ((1 : ℝ) / 50) := Real.rpow_pos_of_pos hU_pos _
      exact div_lt_div_of_pos_left h_num_pos h_den_pos h_rpow_lt
    have hQ_le_G : Q.card ≤ (smallGrowth T fc.D).card := Finset.card_le_card hQ_sub
    have hM_le_Q_real : (fc.M : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hM_Q
    have hQ_le_G_real : (Q.card : ℝ) ≤ ((smallGrowth T fc.D).card : ℝ) := by exact_mod_cast hQ_le_G
    exact lt_of_lt_of_le (h_bound_lt.trans p.hE1) (hM_le_Q_real.trans hQ_le_G_real)

  rcases h_ap_cover N T fc.D fc.xi h8D_T fc.hxi_pos p.h_xi_le hT_xi_N h_gen h_big
    with ⟨R, hGR, hR_card⟩
  have hQR : Q ⊆ R.toFinset := hQ_sub.trans hGR
  have hB_sub : st.B ⊆ fc.A := Finset.sdiff_subset
  have hB_card : fc.M ≤ st.B.card := by
    classical
    apply st.B_card_ge
    have hj_range : j ∈ Finset.range fc.K := (Finset.mem_filter.mp hj).1
    have hj_lt : j < fc.K := Finset.mem_range.mp hj_range
    rw [card_greedySeq_E fc j (by omega)]
    omega
  have h_bound := @h_sieve st.B hB_sub hB_card instN R hR_card hQR
  have hE3 := p.hE3
  have hB_lt_M : (st.B.card : ℝ) < (fc.M : ℝ) := h_bound.trans_lt hE3
  have hM_le_B : (fc.M : ℝ) ≤ (st.B.card : ℝ) := by exact_mod_cast hB_card
  linarith

/-- All unsaturated steps satisfy greedyDelta ≥ D under P17 conditions, guarded AP cover, and sieve bridge. -/
theorem unsaturatedSteps_growth_of_ap_cover
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_ap_cover : GuardedAPCover)
    (h_sieve : APCoverSieveBridge fc p) :
    ∀ j ∈ unsaturatedSteps fc, fc.D ≤ greedyDelta fc j :=
  fun j hj => unsaturated_step_growth_of_ap_cover fc p h_ap_cover h_sieve j hj

/-- CFP Lemma 5.6 Finite Core with Guarded AP Cover and Sieve Bridge:
    Closes both h_inj and h_unsaturated_step_growth under explicit P17 arithmetic conditions,
    the guarded AP cover `GuardedAPCover` (equivalent to the guarded trichotomy), and the sieve bridge. -/
theorem cfp_lemma_5_6_finite_core_of_ap_cover
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_sieve : APCoverSieveBridge fc p) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  have h_inj := p.injOn_A fc
  have h_unsat := unsaturatedSteps_growth_of_ap_cover fc p h_ap_cover h_sieve
  exact cfp_lemma_5_6_finite_core_closed fc h_inj h_numeric h_unsat

/-- CFP Lemma 5.6 Master Theorem Specialized to m = n with Guarded AP Cover:
    Closes both h_inj and h_unsaturated_step_growth under explicit P17 arithmetic conditions,
    the guarded AP cover `GuardedAPCover` (equivalent to the guarded trichotomy), and the sieve bridge. -/
theorem cfp_lemma_5_6_m_eq_n_of_ap_cover
    (p_cf : CFPArithParams)
    (p : P17FiniteArithConditions p_cf.toFiniteConditions)
    (h_numeric : p16TotalBudget p_cf.t p_cf.gMax p_cf.U p_cf.M ≤ p_cf.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_sieve : APCoverSieveBridge p_cf.toFiniteConditions p) :
    min p_cf.xi ((32 : ℝ) / (p_cf.ell : ℝ)) * (p_cf.t : ℝ) ≤ ((subsetSumsMod p_cf.t p_cf.A).card : ℝ) := by
  have h_inj : Set.InjOn (fun a : ℕ => (a : ZMod p_cf.t)) (p_cf.A : Set ℕ) := by
    have h := p.injOn_A p_cf.toFiniteConditions
    exact h
  have h_unsat := unsaturatedSteps_growth_of_ap_cover p_cf.toFiniteConditions p h_ap_cover h_sieve
  exact cfp_lemma_5_6_m_eq_n_closed p_cf h_inj h_numeric h_unsat

/-- CFP Lemma 5.6 Finite Core with Guarded AP Cover and Per-AP Sieve Rough Count:
    Uses the guarded AP cover interface and reduces the sieve bridge to explicit per-AP Selberg rough count bounds. -/
theorem cfp_lemma_5_6_finite_core_of_rough_count
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_cov_sieve : ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
      [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
      (R : CosetAP (fc.t / subgroupIndex fc.t B))
      (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
      (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset),
      ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
        (cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
          (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n)
        (C_sieve : ℝ) (_hC_nonneg : 0 ≤ C_sieve)
        (_h_sieve : ∀ i ∈ cov.I, (roughCount (cov.APs i) Q : ℝ) ≤ ((cov.APs i).k : ℝ) * C_sieve)
        (_hC_eq : C_sieve = 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)),
        True) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  have h_sieve := apCoverSieveBridge_of_cover_and_sieve fc p h_cov_sieve
  exact cfp_lemma_5_6_finite_core_of_ap_cover fc p h_numeric h_ap_cover h_sieve

/-- CFP Lemma 5.6 (m = n) Master Theorem with Guarded AP Cover and Per-AP Sieve Rough Count:
    Uses the guarded AP cover interface and reduces the sieve bridge to explicit per-AP Selberg rough count bounds. -/
theorem cfp_lemma_5_6_m_eq_n_of_rough_count
    (p_cf : CFPArithParams)
    (p : P17FiniteArithConditions p_cf.toFiniteConditions)
    (h_numeric : p16TotalBudget p_cf.t p_cf.gMax p_cf.U p_cf.M ≤ p_cf.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_cov_sieve : ∀ (B : Finset ℕ) (_hBA : B ⊆ p_cf.toFiniteConditions.A) (_hB_card : p_cf.toFiniteConditions.M ≤ B.card)
      [_instN : NeZero (p_cf.toFiniteConditions.t / subgroupIndex p_cf.toFiniteConditions.t B)]
      (R : CosetAP (p_cf.toFiniteConditions.t / subgroupIndex p_cf.toFiniteConditions.t B))
      (_hR_card : R.ell * (R.H : Set (ZMod (p_cf.toFiniteConditions.t / subgroupIndex p_cf.toFiniteConditions.t B))).toFinset.card ≤ 128 * p_cf.toFiniteConditions.D)
      (_hQR : (B.image (fun a => ((a / (subgroupIndex p_cf.toFiniteConditions.t B) : ℕ) : ZMod (p_cf.toFiniteConditions.t / subgroupIndex p_cf.toFiniteConditions.t B)))) ⊆ R.toFinset),
      ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
        (cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
          (R.ell * (R.H : Set (ZMod (p_cf.toFiniteConditions.t / subgroupIndex p_cf.toFiniteConditions.t B))).toFinset.card) p_cf.toFiniteConditions.t p.n)
        (C_sieve : ℝ) (_hC_nonneg : 0 ≤ C_sieve)
        (_h_sieve : ∀ i ∈ cov.I, (roughCount (cov.APs i) Q : ℝ) ≤ ((cov.APs i).k : ℝ) * C_sieve)
        (_hC_eq : C_sieve = 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)),
        True) :
    min p_cf.xi ((32 : ℝ) / (p_cf.ell : ℝ)) * (p_cf.t : ℝ) ≤ ((subsetSumsMod p_cf.t p_cf.A).card : ℝ) := by
  have h_sieve := apCoverSieveBridge_of_cover_and_sieve p_cf.toFiniteConditions p h_cov_sieve
  exact cfp_lemma_5_6_m_eq_n_of_ap_cover p_cf p h_numeric h_ap_cover h_sieve

/-- Phase P08 Branch A: Existence of an integer AP cover when |R.H|^3 ≥ R_card. -/
def HasIntAPCoverBranchA (fc : FiniteConditions) (p : P17FiniteArithConditions fc) : Prop :=
  ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
    [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
    (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset)
    (_h_branchA : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤
      (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ^ 3),
    ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
      (_cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
        (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n),
      True

/-- Every candidate a ∈ fc.A satisfies a < 2 * fc.t. -/
lemma candidate_lt_two_mul_t (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (a : ℕ) (ha : a ∈ fc.A) : a < 2 * fc.t := by
  have h_inY := p.hA_inY a ha
  rcases h_inY with ⟨_hy_le, h_va_lt, -⟩
  have h_y_le := p.h_y_le_vt
  have hv_pos := fc.hv_pos
  have h_lt : fc.v * a < fc.v * (2 * fc.t) := by
    calc fc.v * a < 2 * p.y := h_va_lt
    _ ≤ 2 * (fc.v * fc.t) := Nat.mul_le_mul_left 2 h_y_le
    _ = fc.v * (2 * fc.t) := by ring
  exact (Nat.mul_lt_mul_left hv_pos).mp h_lt

/-- Cardinality of an additive subgroup in ZMod N is strictly positive. -/
lemma subgroup_card_pos (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) :
    0 < (H : Set (ZMod N)).toFinset.card := by
  have h0 : (0 : ZMod N) ∈ (H : Set (ZMod N)).toFinset := by
    rw [Set.mem_toFinset]
    exact H.zero_mem
  exact Finset.card_pos.mpr ⟨0, h0⟩

/-- The order of an additive subgroup H ≤ ZMod N divides the scaled modulus t = g * N. -/
lemma subgroup_card_dvd_t (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N))
    (t g : ℕ) (hgN : g * N = t) :
    (H : Set (ZMod N)).toFinset.card ∣ t := by
  let h := (H : Set (ZMod N)).toFinset.card
  have h_card : (H : Set (ZMod N)).toFinset.card = Fintype.card H := Set.toFinset_card (H : Set (ZMod N))
  have h_lag := AddSubgroup.card_addSubgroup_dvd_card H
  rw [Nat.card_zmod N, Nat.card_eq_fintype_card, ← h_card] at h_lag
  have h_Ndvd : N ∣ t := ⟨g, by rw [mul_comm, hgN]⟩
  exact h_lag.trans h_Ndvd

/-- Constructing the lifted integer arithmetic progression for Branch A.
    For each coset j < R.ell and parity s ∈ {0, 1}, we lift c_j + H to an integer AP
    of length h with common difference t / h. -/
def branchA_AP (t : ℕ) (ht_pos : 0 < t) (g : ℕ) (N : ℕ) [NeZero N]
    (R : CosetAP N) (h : ℕ) (hh_pos : 0 < h) (hh_dvd : h ∣ t)
    (i : Fin (2 * R.ell)) : IntAP where
  a := ((g * (R.c + ((i.val / 2 : ℕ) : ZMod N) * R.v).val % (t / h) : ℕ) : ℤ) +
       ((i.val % 2 : ℕ) : ℤ) * (t : ℤ)
  b := t / h
  hb := Nat.div_pos (Nat.le_of_dvd ht_pos hh_dvd) hh_pos
  k := h

/-- Length of each lifted AP in Branch A is exactly the subgroup order h. -/
lemma branchA_AP_k (t : ℕ) (ht_pos : 0 < t) (g : ℕ) (N : ℕ) [NeZero N]
    (R : CosetAP N) (h : ℕ) (hh_pos : 0 < h) (hh_dvd : h ∣ t)
    (i : Fin (2 * R.ell)) :
    (branchA_AP t ht_pos g N R h hh_pos hh_dvd i).k = h := rfl

/-- Common difference of each lifted AP in Branch A is bounded by t. -/
lemma branchA_AP_b_le (t : ℕ) (ht_pos : 0 < t) (g : ℕ) (N : ℕ) [NeZero N]
    (R : CosetAP N) (h : ℕ) (hh_pos : 0 < h) (hh_dvd : h ∣ t)
    (i : Fin (2 * R.ell)) :
    (branchA_AP t ht_pos g N R h hh_pos hh_dvd i).b ≤ t :=
  Nat.div_le_self t h

/-- The lifted Branch A AP family covers the integer image of B. -/
lemma branchA_AP_cover
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (B : Finset ℕ) (hBA : B ⊆ fc.A)
    [instN : NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset) :
    let g := subgroupIndex fc.t B
    let N := fc.t / g
    let h := (R.H : Set (ZMod N)).toFinset.card
    have hh_pos : 0 < h := subgroup_card_pos N R.H
    have hg_dvd_t : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t B
    have hg_mul_N : g * N = fc.t := Nat.mul_div_cancel' hg_dvd_t
    have hh_dvd_t : h ∣ fc.t := subgroup_card_dvd_t N R.H fc.t g hg_mul_N
    (B.image (fun (a : ℕ) => (a : ℤ))) ⊆
      (Finset.univ : Finset (Fin (2 * R.ell))).biUnion
        (fun i => (branchA_AP fc.t fc.ht_pos g N R h hh_pos hh_dvd_t i).toFinset) := by
  intro g N h hh_pos hg_dvd_t hg_mul_N hh_dvd_t z hz
  simp only [Finset.mem_image] at hz
  rcases hz with ⟨a, ha, rfl⟩
  have ha_A : a ∈ fc.A := hBA ha
  have ha_lt_two_t : a < 2 * fc.t := candidate_lt_two_mul_t fc p a ha_A
  have hg_dvd_a : g ∣ a := subgroupIndex_dvd_mem fc.t B ha
  have ha_img : ((a / g : ℕ) : ZMod N) ∈ B.image (fun a => ((a / g : ℕ) : ZMod N)) := by
    simp only [Finset.mem_image]
    exact ⟨a, ha, rfl⟩
  have ha_R := hQR ha_img
  dsimp [CosetAP.toFinset] at ha_R
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at ha_R
  rcases ha_R with ⟨j, hj_lt, h_elem, hh_elem, heq_elem⟩
  rw [Set.mem_toFinset] at hh_elem
  let c_j : ZMod N := R.c + (j : ZMod N) * R.v
  have heq : ((a / g : ℕ) : ZMod N) = c_j + h_elem := heq_elem.symm
  have heq_val : ((a / g : ℕ) : ZMod N) = ((c_j.val + h_elem.val : ℕ) : ZMod N) := by
    calc ((a / g : ℕ) : ZMod N) = c_j + h_elem := heq
    _ = (c_j.val : ZMod N) + (h_elem.val : ZMod N) := by rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ = ((c_j.val + h_elem.val : ℕ) : ZMod N) := by push_cast; rfl
  rw [ZMod.natCast_eq_natCast_iff] at heq_val
  have h_mul := Nat.ModEq.mul_left' g heq_val
  rw [Nat.mul_div_cancel' hg_dvd_a] at h_mul
  rw [hg_mul_N] at h_mul
  have h_distrib : g * (c_j.val + h_elem.val) = g * c_j.val + g * h_elem.val := Nat.mul_add g c_j.val h_elem.val
  rw [h_distrib] at h_mul
  let d := fc.t / h
  have hd_dvd : d ∣ fc.t := ⟨h, (Nat.div_mul_cancel hh_dvd_t).symm⟩
  have h_mod_d := h_mul.of_dvd hd_dvd
  have hd_dvd_gh : d ∣ g * h_elem.val := zmod_subgroup_scaled_val_dvd N R.H fc.t g hg_mul_N h_elem hh_elem
  have h_zero : g * h_elem.val ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hd_dvd_gh
  have h_modeq_add : g * c_j.val + g * h_elem.val ≡ g * c_j.val + 0 [MOD d] :=
    Nat.ModEq.add (Nat.ModEq.refl (g * c_j.val)) h_zero
  rw [add_zero] at h_modeq_add
  have h_modeq_c : a ≡ g * c_j.val [MOD d] := h_mod_d.trans h_modeq_add
  let r_j := (g * c_j.val) % d
  have h_rj_modeq : g * c_j.val ≡ r_j [MOD d] := (Nat.mod_modEq (g * c_j.val) d).symm
  have h_modeq_rj : a ≡ r_j [MOD d] := h_modeq_c.trans h_rj_modeq
  have h_a_mod : a % d = r_j % d := h_modeq_rj
  have hr_j_lt : r_j < d := Nat.mod_lt _ (Nat.div_pos (Nat.le_of_dvd fc.ht_pos hh_dvd_t) hh_pos)
  rw [Nat.mod_eq_of_lt hr_j_lt] at h_a_mod
  let s := a / fc.t
  have hs_lt : s < 2 := by
    have ha_lt_t2 : a < fc.t * 2 := by linarith
    exact Nat.div_lt_of_lt_mul ha_lt_t2
  let a' := a % fc.t
  have ha_decomp : a = s * fc.t + a' := by
    have h := (Nat.div_add_mod a fc.t).symm
    dsimp [s, a']
    rw [Nat.mul_comm fc.t (a / fc.t)] at h
    exact h
  have ha'_modeq : a' ≡ a [MOD d] := by
    have h_mod_t : a' ≡ a [MOD fc.t] := Nat.mod_modEq a fc.t
    exact h_mod_t.of_dvd hd_dvd
  have ha'_mod_d : a' % d = r_j := by
    have h_trans : a' ≡ r_j [MOD d] := ha'_modeq.trans h_modeq_rj
    have h_mod : a' % d = r_j % d := h_trans
    rwa [Nat.mod_eq_of_lt hr_j_lt] at h_mod
  have h_d_mul_h : d * h = fc.t := Nat.div_mul_cancel hh_dvd_t
  have ha'_lt : a' < fc.t := Nat.mod_lt a fc.ht_pos
  have ha'_lt_dh : a' < d * h := by rwa [h_d_mul_h]
  let m := a' / d
  have hm_lt : m < h := Nat.div_lt_of_lt_mul ha'_lt_dh
  have ha'_eq : a' = r_j + m * d := by
    have h_div_add : a' = d * (a' / d) + a' % d := (Nat.div_add_mod a' d).symm
    rw [ha'_mod_d] at h_div_add
    dsimp [m]
    rw [Nat.add_comm (d * (a' / d)) r_j, Nat.mul_comm d (a' / d)] at h_div_add
    exact h_div_add
  have ha_eq : a = r_j + s * fc.t + m * d := by
    rw [ha_decomp, ha'_eq]
    ring
  let i_val := 2 * j + s
  have hi_lt : i_val < 2 * R.ell := by
    dsimp [i_val]
    omega
  let i : Fin (2 * R.ell) := ⟨i_val, hi_lt⟩
  have hi_div : i_val / 2 = j := by
    dsimp [i_val]
    interval_cases s <;> omega
  have hi_mod : i_val % 2 = s := by
    dsimp [i_val]
    interval_cases s <;> omega
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  use i
  simp only [IntAP.toFinset, Finset.mem_image, Finset.mem_range]
  use m
  refine ⟨hm_lt, ?_⟩
  have h_AP_a : (branchA_AP fc.t fc.ht_pos g N R h hh_pos hh_dvd_t i).a = (r_j : ℤ) + (s : ℤ) * (fc.t : ℤ) := by
    change ((g * (R.c + ((i_val / 2 : ℕ) : ZMod N) * R.v).val % (fc.t / h) : ℕ) : ℤ) +
           ((i_val % 2 : ℕ) : ℤ) * (fc.t : ℤ) = (r_j : ℤ) + (s : ℤ) * (fc.t : ℤ)
    rw [hi_div, hi_mod]
  have h_AP_b : (branchA_AP fc.t fc.ht_pos g N R h hh_pos hh_dvd_t i).b = d := rfl
  rw [h_AP_a, h_AP_b]
  have ha_cast : (a : ℤ) = (r_j : ℤ) + (s : ℤ) * (fc.t : ℤ) + (m : ℤ) * (d : ℤ) := by
    exact_mod_cast ha_eq
  exact ha_cast.symm

/-- Formally closing Phase P08 Branch A: HasIntAPCoverBranchA holds unconditionally. -/
theorem hasIntAPCoverBranchA
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc) :
    HasIntAPCoverBranchA fc p := by
  intro B hBA _hB_card instN R _hR_card hQR h_branchA
  let g := subgroupIndex fc.t B
  let N := fc.t / g
  let h := (R.H : Set (ZMod N)).toFinset.card
  let R_card := R.ell * h
  have hh_pos : 0 < h := subgroup_card_pos N R.H
  have hg_dvd_t : g ∣ fc.t := subgroupIndex_dvd_modulus fc.t B
  have hg_mul_N : g * N = fc.t := Nat.mul_div_cancel' hg_dvd_t
  have hh_dvd_t : h ∣ fc.t := subgroup_card_dvd_t N R.H fc.t g hg_mul_N
  let APs := branchA_AP fc.t fc.ht_pos g N R h hh_pos hh_dvd_t
  have h_cov := branchA_AP_cover fc p B hBA R hQR
  have h_len : ∀ i, (APs i).k = h := fun i => branchA_AP_k fc.t fc.ht_pos g N R h hh_pos hh_dvd_t i
  have h_sum_le : (2 * R.ell) * h ≤ 3 * R_card := by
    calc (2 * R.ell) * h = 2 * (R.ell * h) := by ring
    _ = 2 * R_card := rfl
    _ ≤ 3 * R_card := by omega
  have h_step_le : ∀ i, (APs i).b ≤ fc.t :=
    fun i => branchA_AP_b_le fc.t fc.ht_pos g N R h hh_pos hh_dvd_t i
  have cov := intAPCover_of_coset_family
    (B.image (fun (a : ℕ) => (a : ℤ))) R_card fc.t p.n p.h_t_le_n
    (2 * R.ell) h APs h_cov h_len h_sum_le h_branchA h_step_le
  refine ⟨1, fun a _ha => Nat.coprime_one_right a, cov, trivial⟩
/-- Phase P08 Branch B: Existence of an integer AP cover when |R.H|^3 < R_card. -/
def HasIntAPCoverBranchB (fc : FiniteConditions) (p : P17FiniteArithConditions fc) : Prop :=
  ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
    [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
    (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset)
    (_h_branchB : (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ^ 3 <
      R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card),
    ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
      (_cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
        (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n),
      True

/-- Phase P08 Component: Existence of an integer AP cover for any candidate subset B
    covered by a coset AP R with R.ell * |R.H| ≤ 128 * D. -/
def HasIntAPCover (fc : FiniteConditions) (p : P17FiniteArithConditions fc) : Prop :=
  ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
    [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
    (R : CosetAP (fc.t / subgroupIndex fc.t B))
    (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
    (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset),
    ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
      (_cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
        (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n),
      True

/-- Master Branch Reduction for Phase P08:
    Combines Branch A (|R.H|^3 ≥ R_card) and Branch B (|R.H|^3 < R_card)
    into the full HasIntAPCover theorem. -/
theorem hasIntAPCover_of_branchA_and_branchB
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (hA : HasIntAPCoverBranchA fc p)
    (hB : HasIntAPCoverBranchB fc p) :
    HasIntAPCover fc p := by
  intro B hBA hB_card instN R hR_card hQR
  let R_card := R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card
  let h_card := (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card
  by_cases h_cases : R_card ≤ h_card ^ 3
  · exact hA B hBA hB_card R hR_card hQR h_cases
  · have h_gt : h_card ^ 3 < R_card := by omega
    exact hB B hBA hB_card R hR_card hQR h_gt

/-- Phase P09 Component: Selberg rough count bound for arithmetic progressions.
    Any arithmetic progression P in an IntAPCover satisfies the Selberg rough count bound. -/
def HasAPRoughCountBound (fc : FiniteConditions) (p : P17FiniteArithConditions fc) : Prop :=
  0 ≤ 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ) ∧
  ∀ (P : IntAP) (Q : ℕ) (R_card : ℕ)
    (_h_min_len : R_card ≤ P.k ^ 3) (_h_step_le : P.b ≤ fc.t),
    (roughCount P Q : ℝ) ≤ (P.k : ℝ) * (256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ))

/-- Decoupled Master Reduction: Reduces h_cov_sieve to P08 AP Lifting and P09 Sieve Bound. -/
theorem h_cov_sieve_of_lifting_and_sieve
    (fc : FiniteConditions) (p : P17FiniteArithConditions fc)
    (h_lift : HasIntAPCover fc p)
    (h_sieve_bound : HasAPRoughCountBound fc p) :
    ∀ (B : Finset ℕ) (_hBA : B ⊆ fc.A) (_hB_card : fc.M ≤ B.card)
      [_instN : NeZero (fc.t / subgroupIndex fc.t B)]
      (R : CosetAP (fc.t / subgroupIndex fc.t B))
      (_hR_card : R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card ≤ 128 * fc.D)
      (_hQR : (B.image (fun a => ((a / (subgroupIndex fc.t B) : ℕ) : ZMod (fc.t / subgroupIndex fc.t B)))) ⊆ R.toFinset),
      ∃ (Q : ℕ) (_hB_rough : ∀ a ∈ B, Nat.Coprime a Q)
        (cov : IntAPCover (B.image (fun (a : ℕ) => (a : ℤ)))
          (R.ell * (R.H : Set (ZMod (fc.t / subgroupIndex fc.t B))).toFinset.card) fc.t p.n)
        (C_sieve : ℝ) (_hC_nonneg : 0 ≤ C_sieve)
        (_h_sieve : ∀ i ∈ cov.I, (roughCount (cov.APs i) Q : ℝ) ≤ ((cov.APs i).k : ℝ) * C_sieve)
        (_hC_eq : C_sieve = 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)),
        True := by
  intro B hBA hB_card instN R hR_card hQR
  rcases h_lift B hBA hB_card R hR_card hQR with ⟨Q, hB_rough, cov, _⟩
  let C_sieve := 256 * Real.log (Real.log (p.n : ℝ)) / Real.log (p.r : ℝ)
  have hC_nonneg := h_sieve_bound.1
  refine ⟨Q, hB_rough, cov, C_sieve, hC_nonneg, ?_, rfl, trivial⟩
  intro i hi
  exact h_sieve_bound.2 (cov.APs i) Q _ (cov.h_min_len i hi) (cov.h_step_le_t i hi)

/-- CFP Lemma 5.6 Finite Core with Decoupled AP Lifting and Sieve Bound:
    Completely decouples the AP lifting geometry (P08) from the Selberg rough count bound (P09). -/
theorem cfp_lemma_5_6_finite_core_of_lifting_and_sieve
    (fc : FiniteConditions)
    (p : P17FiniteArithConditions fc)
    (h_numeric : p16TotalBudget fc.t fc.gMax fc.U fc.M ≤ fc.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_lift : HasIntAPCover fc p)
    (h_sieve_bound : HasAPRoughCountBound fc p) :
    min fc.xi ((32 : ℝ) / (fc.ell : ℝ)) * (fc.t : ℝ) ≤ ((subsetSumsMod fc.t fc.A).card : ℝ) := by
  have h_cov_sieve := h_cov_sieve_of_lifting_and_sieve fc p h_lift h_sieve_bound
  exact cfp_lemma_5_6_finite_core_of_rough_count fc p h_numeric h_ap_cover h_cov_sieve

/-- CFP Lemma 5.6 (m = n) Master Theorem with Decoupled AP Lifting and Sieve Bound:
    Specializes Lemma 5.6 to m = n with guarded AP cover, decoupled AP lifting (P08),
    and Selberg sieve rough count bound (P09). -/
theorem cfp_lemma_5_6_m_eq_n_of_lifting_and_sieve
    (p_cf : CFPArithParams)
    (p : P17FiniteArithConditions p_cf.toFiniteConditions)
    (h_numeric : p16TotalBudget p_cf.t p_cf.gMax p_cf.U p_cf.M ≤ p_cf.B_growth)
    (h_ap_cover : GuardedAPCover)
    (h_lift : HasIntAPCover p_cf.toFiniteConditions p)
    (h_sieve_bound : HasAPRoughCountBound p_cf.toFiniteConditions p) :
    min p_cf.xi ((32 : ℝ) / (p_cf.ell : ℝ)) * (p_cf.t : ℝ) ≤ ((subsetSumsMod p_cf.t p_cf.A).card : ℝ) := by
  have h_cov_sieve := h_cov_sieve_of_lifting_and_sieve p_cf.toFiniteConditions p h_lift h_sieve_bound
  exact cfp_lemma_5_6_m_eq_n_of_rough_count p_cf p h_numeric h_ap_cover h_cov_sieve

/-- CFP Lemma 5.6 (m = n) Master Theorem with Branch-Decoupled AP Lifting and Sieve Bound:
    Specializes Lemma 5.6 to m = n with guarded AP cover, Branch A (|R.H|^3 ≥ R_card) /
    Branch B (|R.H|^3 < R_card) decoupled AP lifting (P08), and Selberg sieve rough count bound (P09). -/
theorem cfp_lemma_5_6_m_eq_n_of_branches_and_sieve
    (p_cf : CFPArithParams)
    (p : P17FiniteArithConditions p_cf.toFiniteConditions)
    (h_numeric : p16TotalBudget p_cf.t p_cf.gMax p_cf.U p_cf.M ≤ p_cf.B_growth)
    (h_ap_cover : GuardedAPCover)
    (hA : HasIntAPCoverBranchA p_cf.toFiniteConditions p)
    (hB : HasIntAPCoverBranchB p_cf.toFiniteConditions p)
    (h_sieve_bound : HasAPRoughCountBound p_cf.toFiniteConditions p) :
    min p_cf.xi ((32 : ℝ) / (p_cf.ell : ℝ)) * (p_cf.t : ℝ) ≤ ((subsetSumsMod p_cf.t p_cf.A).card : ℝ) := by
  have h_lift := hasIntAPCover_of_branchA_and_branchB p_cf.toFiniteConditions p hA hB
  exact cfp_lemma_5_6_m_eq_n_of_lifting_and_sieve p_cf p h_numeric h_ap_cover h_lift h_sieve_bound



/-- Unconditional Two-Sided Master Theorem for Erdős Problem JSP-000298:

    For all n ≥ 3, the chromatic number f(n) is unconditionally non-trivial (f(n) ≥ 2)
    and bounded from above by the Conlon–Fox–Pham (2021) 4-layer upper bound:
      2 ≤ f(n) ≤ s1 + |P| + 2 * |reducedResidues d| + ⌈|R_cfp| / s_rem⌉. -/
theorem erdos_problem_360_unconditional_master (n : ℕ) (hn : 3 ≤ n)
    (s1 : ℕ) (hs1 : 1 ≤ s1) (P : Finset ℕ) (d s_rem : ℕ)
    (hd : 1 ≤ d) (hs_rem : 1 ≤ s_rem) (h_srem_le : s_rem ≤ s1)
    (hP : ∀ p ∈ P, ¬ p ∣ n) :
    let T := reducedResidues d
    let R := cfpRemainder n s1 d P
    2 ≤ minColors n (by omega) ∧
    minColors n (by omega) ≤ s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem := by
  refine ⟨minColors_ge_two n hn,
          minColors_le_conlon_fox_pham n s1 P d s_rem (by omega) hs1 hd hs_rem h_srem_le hP⟩

/-- Canonical Conlon–Fox–Pham asymptotic growth scale:
    F(n) = n^(1/3) * (n / φ(n)) / ((log n)^(1/3) * (log log n)^(2/3)). -/
noncomputable def cfpScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) / (Nat.totient n : ℝ)) /
    ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) * (Real.log (Real.log (n : ℝ))) ^ ((2 : ℝ) / 3))

/-- Strict positivity of the canonical CFP growth scale for sufficiently large n. -/
lemma cfpScale_pos_of_hyp (n : ℕ) (hn : (1 : ℝ) < Real.log (n : ℝ))
    (h_tot : 0 < (Nat.totient n : ℝ)) (hn_pos : 0 < (n : ℝ)) : 0 < cfpScale n := by
  dsimp [cfpScale]
  apply _root_.div_pos
  · apply mul_pos
    · exact Real.rpow_pos_of_pos hn_pos _
    · exact _root_.div_pos hn_pos h_tot
  · apply mul_pos
    · exact Real.rpow_pos_of_pos (by linarith) _
    · have : (0 : ℝ) < Real.log (Real.log (n : ℝ)) := Real.log_pos hn
      exact Real.rpow_pos_of_pos this _

/-- Conlon–Fox–Pham (2021) Asymptotic Master Theorem:
    Given matching lower and upper bound witnesses with respect to a growth scale F,
    the chromatic number f(n) satisfies the sharp asymptotic two-sided equivalence:
      c * F(n) ≤ f(n) ≤ C * F(n)
    for all sufficiently large n. -/
theorem erdos_problem_360_asymptotic_master (F : ℕ → ℝ) {c C : ℝ}
    (h_lower : HasChromaticLowerBound F c)
    (h_upper : HasChromaticUpperBound F C) :
    ∃ N0 : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N0 ≤ n →
      c * F n ≤ (minColors n hn : ℝ) ∧
      (minColors n hn : ℝ) ≤ C * F n :=
  conlon_fox_pham_bounds F h_lower h_upper

/-- Grand Unified Master Theorem for Erdős Problem JSP-000298 (Erdős Problem #360):
    Unifies all three historical generations of solutions:
    1. Generation 1 (Alon–Erdős 1996 Elementary):
       Cubic-root bound f(n) ≤ 2s when n ≤ s^3.
    2. Generation 2 (Alon–Erdős 1996 Sieve):
       Quantitative finite Selberg sieve remainder bound and prime reciprocal sum bound.
    3. Generation 3 (Conlon–Fox–Pham 2021 Upper Bound):
       4-layer coloring bound with reduced residues modulo d.
    4. Generation 3 (Conlon–Fox–Pham 2021 Lower Bound):
       Additive combinatorics lower bound witness theorem f(n) ≥ k + 1.
    5. Generation 3 (Conlon–Fox–Pham 2021 Asymptotic Synthesis):
       Two-sided growth scale equivalence c * F(n) ≤ f(n) ≤ C * F(n). -/
theorem erdos_problem_360_unified_solution :
    -- 1. Generation 1: Cubic-root bound
    (∀ n s : ℕ, (hn : 2 ≤ n) → (hs : 1 ≤ s) → n ≤ s ^ 3 → minColors n hn ≤ 2 * s) ∧
    -- 2. Generation 2: Selberg prime reciprocal sum bound
    (∀ n s z : ℕ, (hn : 2 ≤ n) → (hs : 1 ≤ s) → (hz : 1 ≤ z) →
      minColors n hn ≤ 2 * s +
        Nat.ceil (((n - 1 : ℝ) / ((s : ℝ) * (s + 1 : ℝ) *
          (1 + ∑ p ∈ (sievePrimes n s).filter (fun p => p ≤ z), (1 / ((p : ℝ) - 1))))) +
          (z : ℝ) ^ 4 / (s : ℝ))) ∧
    -- 3. Generation 3: Conlon–Fox–Pham 4-layer upper bound
    (∀ n s1 : ℕ, (P : Finset ℕ) → (d s_rem : ℕ) →
      (hn : 2 ≤ n) → (hs1 : 1 ≤ s1) → (hd : 1 ≤ d) → (hs_rem : 1 ≤ s_rem) → (h_srem_le : s_rem ≤ s1) →
      (hP : ∀ p ∈ P, ¬ p ∣ n) →
      let T := reducedResidues d
      let R := cfpRemainder n s1 d P
      minColors n hn ≤ s1 + P.card + 2 * T.card + (R.card + s_rem - 1) / s_rem) ∧
    -- 4. Generation 3: Conlon–Fox–Pham lower bound witness theorem
    (∀ n k : ℕ, (hn : 2 ≤ n) → (w : CFPLowerBoundWitness n k) → k + 1 ≤ minColors n hn) ∧
    -- 5. Generation 3: Conlon–Fox–Pham asymptotic growth equivalence
    (∀ F : ℕ → ℝ, ∀ c C : ℝ,
      HasChromaticLowerBound F c → HasChromaticUpperBound F C →
      ∃ N0 : ℕ, ∀ n (hn : 2 ≤ n), N0 ≤ n → c * F n ≤ (minColors n hn : ℝ) ∧ (minColors n hn : ℝ) ≤ C * F n) := by
  refine ⟨minColors_le_two_mul_s,
          minColors_le_of_sum_primes,
          minColors_le_conlon_fox_pham,
          minColors_ge_of_cfp_witness,
          conlon_fox_pham_bounds⟩

/-!
### Concrete Non-Vacuity Witness for `CFPArithParams`, `P17FiniteArithConditions` and `h_numeric`

The structures `CFPArithParams` and `P17FiniteArithConditions` bundle several numerical
conditions (E1, E2, E3, the small-fiber and growth-budget bounds, and the growth-step budget
`h_numeric` consumed by the master theorems). None of the master theorems can be applied unless
these conditions are jointly satisfiable, so we exhibit an explicit witness:

* `n = t = 16411` (prime), `v = 1`, `W = 1`, `y = 8192`, `A = [8192, 16383]` (8192 elements);
* `K = 32`, `M = 8160`, `k_div = 1`, `U = 9`, `D = 1`, `gMax = 1`, `ξ = 1/128`, `ℓ = 2^20`,
  `B_growth = 31`, `r = 8160^5`.

Every element of `A` is coprime to the prime modulus, which gives `subgroupIndex t B = 1` for every
non-empty `B ⊆ A`, and the consecutive elements `8192, 8193 ∈ A` give 1-diversity. The analytic
conditions E1 and E3 are verified from `0 < log 2 ≤ 1` and monotonicity of `log` only.

The witness is deliberately small: for it the conclusion `min(ξ, 32/ℓ) · t ≤ |Σ_t(A)|` of the
master theorems is trivial (`32 t / ℓ < 1`). Its purpose is solely to certify that the parameter
side of the Lemma 5.6 reduction chain is consistent, i.e. that no theorem of the chain is vacuous
for lack of admissible parameters.
-/

/-- The prime modulus of the witness. -/
theorem witness_prime : Nat.Prime 16411 := by norm_num

/-- Every element of the witness candidate set is coprime to the modulus. -/
lemma witness_coprime {a : ℕ} (ha : a ∈ Finset.Icc 8192 16383) : Nat.Coprime a 16411 := by
  rw [Finset.mem_Icc] at ha
  have h_not_dvd : ¬ 16411 ∣ a := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact ((Nat.Prime.coprime_iff_not_dvd witness_prime).mpr h_not_dvd).symm

/-- For every non-empty `B ⊆ [8192, 16383]`, the subgroup index modulo `16411` is `1`. -/
lemma witness_subgroupIndex_le_one (B : Finset ℕ) (hB : B ⊆ Finset.Icc 8192 16383)
    (hM : 8160 ≤ B.card) : subgroupIndex 16411 B ≤ 1 := by
  have h_nonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  rcases h_nonempty with ⟨b, hb⟩
  have hb_A := hB hb
  have hb_cop : Nat.Coprime b 16411 := witness_coprime hb_A
  dsimp [subgroupIndex]
  have h_dvd_gcd : Finset.gcd B id ∣ b := Finset.gcd_dvd hb
  have h_gcd_dvd_b : Nat.gcd 16411 (Finset.gcd B id) ∣ Nat.gcd 16411 b :=
    Nat.dvd_gcd (Nat.gcd_dvd_left 16411 _) (dvd_trans (Nat.gcd_dvd_right 16411 _) h_dvd_gcd)
  have h1 : Nat.gcd 16411 b = 1 := hb_cop.symm
  rw [h1] at h_gcd_dvd_b
  exact Nat.le_of_dvd (by decide) h_gcd_dvd_b

/-- The witness candidate set is `1`-diverse (it contains the consecutive integers `8192, 8193`). -/
lemma witness_isDiverse : IsDiverse (Finset.Icc 8192 16383) 1 := by
  intro d hd
  have h_mem_of : ∀ x, x ∈ Finset.Icc 8192 16383 → ¬ d ∣ x →
      0 < ((Finset.Icc 8192 16383).filter (fun x => ¬ d ∣ x)).card := by
    intro x hx hdx
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hdx⟩⟩
  by_cases h1 : d ∣ 8192
  · have h2 : ¬ d ∣ 8193 := by
      intro h2
      have h_one : d ∣ 8193 - 8192 := Nat.dvd_sub h2 h1
      have : d ∣ 1 := by simpa using h_one
      have := Nat.le_of_dvd (by decide) this
      omega
    exact h_mem_of 8193 (by simp) h2
  · exact h_mem_of 8192 (by simp) h1

/-- Explicit arithmetic parameter configuration (see the section docstring). -/
noncomputable def concreteCFPArithParams : CFPArithParams where
  n := 16411
  hn := by decide
  t := 16411
  ht_pos := by decide
  A := Finset.Icc 8192 16383
  hA_pos := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    omega
  v := 1
  hv_pos := by decide
  hvn := one_dvd _
  K := 32
  M := 8160
  hM_pos := by decide
  k_div := 1
  U := 9
  hU_pos := by decide
  D := 1
  hD_pos := by decide
  gMax := 1
  hgMax_pos := by decide
  xi := (1 : ℝ) / 128
  hxi_pos := by norm_num
  ell := 2 ^ 20
  hell_pos := by decide
  B_growth := 31
  hB_le_K := by decide
  hK_add_M_le := by simp
  hA_diverse := witness_isDiverse
  h_subgroup_le := witness_subgroupIndex_le_one
  h_subgroup_diverse := by
    intro B hB hM
    have := witness_subgroupIndex_le_one B hB hM
    omega
  h_small_fiber_bound := by decide
  h_growth_threshold := by decide
  h_growth_budget := by norm_num

/-- `Nat.log2 16411 = 14`. -/
lemma witness_log2 : Nat.log2 16411 = 14 := by
  have h1 : 14 ≤ Nat.log2 16411 := (Nat.le_log2 (by decide)).mpr (by decide)
  have h2 : Nat.log2 16411 < 15 := (Nat.log2_lt (by decide)).mpr (by decide)
  omega

/-- The growth-step budget condition `h_numeric` holds for the witness. -/
theorem concreteCFPArithParams_numeric :
    p16TotalBudget concreteCFPArithParams.t concreteCFPArithParams.gMax
      concreteCFPArithParams.U concreteCFPArithParams.M ≤ concreteCFPArithParams.B_growth := by
  show p16TotalBudget 16411 1 9 8160 ≤ 31
  simp only [p16TotalBudget, p16BlockBudget, p16MultBudget, p16LinearBudget, witness_log2]
  decide

/-- Condition E1 for the witness. -/
lemma witness_E1 :
    20 * (2 * ((1 : ℕ) : ℝ)) ^ ((51 : ℝ) / 50) / ((9 : ℕ) : ℝ) ^ ((1 : ℝ) / 50) < ((8160 : ℕ) : ℝ) := by
  have h_base : (2 * ((1 : ℕ) : ℝ)) = 2 := by norm_num
  have h1 : (2 * ((1 : ℕ) : ℝ)) ^ ((51 : ℝ) / 50) ≤ 4 := by
    rw [h_base]
    calc (2 : ℝ) ^ ((51 : ℝ) / 50) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have h2 : (1 : ℝ) ≤ ((9 : ℕ) : ℝ) ^ ((1 : ℝ) / 50) := Real.one_le_rpow (by norm_num) (by norm_num)
  have h_num_nonneg : (0 : ℝ) ≤ 20 * (2 * ((1 : ℕ) : ℝ)) ^ ((51 : ℝ) / 50) := by positivity
  calc 20 * (2 * ((1 : ℕ) : ℝ)) ^ ((51 : ℝ) / 50) / ((9 : ℕ) : ℝ) ^ ((1 : ℝ) / 50)
      ≤ 20 * (2 * ((1 : ℕ) : ℝ)) ^ ((51 : ℝ) / 50) := div_le_self h_num_nonneg h2
    _ ≤ 20 * 4 := by linarith
    _ < ((8160 : ℕ) : ℝ) := by norm_num

/-- `log (log 16411) ≤ 4 log 2`. -/
lemma witness_loglog_le : Real.log (Real.log ((16411 : ℕ) : ℝ)) ≤ 4 * Real.log 2 := by
  have h_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_two_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h_log_le : Real.log ((16411 : ℕ) : ℝ) ≤ 15 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < ((16411 : ℕ) : ℝ))
      (by norm_num : ((16411 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (15 : ℕ))
    rwa [Real.log_pow] at h
    -- `Real.log_pow : Real.log (x ^ n) = n * Real.log x`
  have h_log_pos : 0 < Real.log ((16411 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have h_log_le_16 : Real.log ((16411 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 : ℕ) := by
    have h16 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    rw [h16]
    linarith
  have h := Real.log_le_log h_log_pos h_log_le_16
  rwa [Real.log_pow] at h

/-- `60 log 2 ≤ log (8160^5)`. -/
lemma witness_logr_ge : 60 * Real.log 2 ≤ Real.log (((8160 ^ 5 : ℕ) : ℝ)) := by
  have h_cast : (((8160 ^ 5 : ℕ) : ℝ)) = ((8160 : ℕ) : ℝ) ^ (5 : ℕ) := by push_cast; ring
  rw [h_cast, Real.log_pow]
  have h : Real.log ((2 : ℝ) ^ (12 : ℕ)) ≤ Real.log ((8160 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h ⊢
  linarith

/-- Condition E3 for the witness. -/
lemma witness_E3 :
    98304 * ((1 : ℕ) : ℝ) * Real.log (Real.log ((16411 : ℕ) : ℝ)) / Real.log (((8160 ^ 5 : ℕ) : ℝ))
      < ((8160 : ℕ) : ℝ) := by
  have h_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := witness_loglog_le
  have hR := witness_logr_ge
  have hR_pos : 0 < Real.log (((8160 ^ 5 : ℕ) : ℝ)) := by linarith
  rw [div_lt_iff₀ hR_pos]
  norm_num at hL hR ⊢
  linarith

/-- Explicit P17 arithmetic conditions on the witness parameters. -/
noncomputable def concreteP17Conditions :
    P17FiniteArithConditions concreteCFPArithParams.toFiniteConditions where
  n := 16411
  hn_pos := by decide
  hn_ge_three := by decide
  r := 8160 ^ 5
  hr_pos := by norm_num
  hr_gt_one := by norm_num
  y := 8192
  hy_pos := by decide
  W := 1
  hW_pos := by decide
  hv_dvd_n := one_dvd _
  h_y_le_vt := by decide
  h_t_le_n := le_refl _
  hA_inY := by
    intro a ha
    have ha' : a ∈ Finset.Icc 8192 16383 := ha
    have hcop := witness_coprime ha'
    rw [Finset.mem_Icc] at ha'
    show inY_v 8192 16411 1 1 a
    refine ⟨by omega, by omega, a, 1, (mul_one a).symm, by norm_num, by norm_num, ?_⟩
    simpa using hcop
  hE1 := witness_E1
  hE2 := by
    show (8160 ^ 5) ^ 3 ≤ 8160 ^ 16
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by decide)
  hE3 := witness_E3
  h_xi_le := by
    show (1 : ℝ) / 128 ≤ 1 / 20
    norm_num

/-- `CFPArithParams` is non-vacuous. -/
theorem cfpArithParams_realizable : Nonempty CFPArithParams := ⟨concreteCFPArithParams⟩

/-- `P17FiniteArithConditions` is non-vacuous. -/
theorem p17FiniteArithConditions_realizable :
    Nonempty (P17FiniteArithConditions concreteCFPArithParams.toFiniteConditions) :=
  ⟨concreteP17Conditions⟩

/-- The parameter-side hypotheses of the Lemma 5.6 master reductions
    (`CFPArithParams`, `P17FiniteArithConditions`, `h_numeric`) are jointly satisfiable. -/
theorem lemma_5_6_parameter_hypotheses_satisfiable :
    ∃ (p_cf : CFPArithParams) (_p : P17FiniteArithConditions p_cf.toFiniteConditions),
      p16TotalBudget p_cf.t p_cf.gMax p_cf.U p_cf.M ≤ p_cf.B_growth :=
  ⟨concreteCFPArithParams, concreteP17Conditions, concreteCFPArithParams_numeric⟩

end Erdos298

#print axioms Erdos298.exists_coloring_of_le_cube
#print axioms Erdos298.minColors_le_two_mul_s
#print axioms Erdos298.exists_coloring_sieve
#print axioms Erdos298.minColors_le_sieve
#print axioms Erdos298.minColors_le_two_s_add_remainder
#print axioms Erdos298.siftedSum_eq_card_remainder
#print axioms Erdos298.card_remainder_le_mainSum_errSum
#print axioms Erdos298.erdos_rem_bound_of_mem_divisors
#print axioms Erdos298.sieveG_ge_one
#print axioms Erdos298.selbergWeight_one
#print axioms Erdos298.selbergWeight_isUpperMoebius
#print axioms Erdos298.mainSum_selbergWeight_eq
#print axioms Erdos298.errSum_selbergWeight_le
#print axioms Erdos298.selberg_remainder_bound
#print axioms Erdos298.selbergTerms_prime
#print axioms Erdos298.sieveG_ge_one_add_sum_primes
#print axioms Erdos298.minColors_le_of_sieveG_lower_bound
#print axioms Erdos298.minColors_le_of_sum_primes
#print axioms Erdos298.minColors_le_of_prime_subset
#print axioms Erdos298.minColors_ge_two
#print axioms Erdos298.conlon_fox_pham_bounds

#print axioms Erdos298.exists_coloring_conlon_fox_pham
#print axioms Erdos298.minColors_le_conlon_fox_pham
#print axioms Erdos298.minColors_le_conlon_fox_pham_coarse

#print axioms Erdos298.hasValidColoring_of_le
#print axioms Erdos298.minColors_gt_of_not_hasValidColoring
#print axioms Erdos298.minColors_ge_of_not_hasValidColoring
#print axioms Erdos298.monochromatic_fiber_sum_eq
#print axioms Erdos298.exists_monochromatic_fiber_strict
#print axioms Erdos298.not_avoids_of_arithProg_subset
#print axioms Erdos298.denseSubsetSumHitting_of_ap
#print axioms Erdos298.not_avoidsMonoSubsetSum_of_dense
#print axioms Erdos298.not_hasValidColoring_of_dense
#print axioms Erdos298.minColors_gt_of_dense
#print axioms Erdos298.minColors_ge_of_dense
#print axioms Erdos298.minColors_ge_of_cfp_witness
#print axioms Erdos298.minColors_ge_of_cfp_ap_witness
#print axioms Erdos298.hasChromaticLowerBound_of_cfp_witnesses
#print axioms Erdos298.cfpWitness_two
#print axioms Erdos298.minColors_ge_two_via_cfp

#print axioms Erdos298.subsetSums_add_of_disjoint
#print axioms Erdos298.subsetSums_interval_extend_single
#print axioms Erdos298.subsetSums_interval_extend
#print axioms Erdos298.subsetSums_scale
#print axioms Erdos298.mem_subsetSums_of_scaled
#print axioms Erdos298.cfpScale_pos_of_hyp

#print axioms Erdos298.erdos_problem_360_finite_master
#print axioms Erdos298.erdos_problem_360_unconditional_master
#print axioms Erdos298.erdos_problem_360_asymptotic_master
#print axioms Erdos298.erdos_problem_360_unified_solution


#print axioms Erdos298.subsetSums_Icc_zero
#print axioms Erdos298.mem_subsetSums_Icc_of_le
#print axioms Erdos298.mem_subsetSums_scaled_Icc_of_le
#print axioms Erdos298.cfpLowerBoundSet_subset
#print axioms Erdos298.cfpLowerBoundSet_card
#print axioms Erdos298.mem_subsetSums_cfpLowerBoundSet
#print axioms Erdos298.cfpWitness_scaled
#print axioms Erdos298.minColors_ge_two_via_cfp_scaled

#print axioms Erdos298.isDiverse_of_le
#print axioms Erdos298.isDiverse_of_subset
#print axioms Erdos298.quotient_scale_subset
#print axioms Erdos298.mem_subsetSums_of_quotient_hit
#print axioms Erdos298.mem_subsetSums_of_quotient_Icc_subset
#print axioms Erdos298.mem_subsetSums_of_scaled_Icc_subset
#print axioms Erdos298.minColors_ge_of_cfp_diverse_witness

#print axioms Erdos298.not_isDiverse_iff
#print axioms Erdos298.card_le_card_filter_dvd_add
#print axioms Erdos298.card_image_div_eq_card_filter_dvd
#print axioms Erdos298.div_step_bounds
#print axioms Erdos298.exists_diverse_scaled_subset
#print axioms Erdos298.scale_factor_le_of_mem_bounds

#print axioms Erdos298.subsetSumsMod_eq_univ_of_divisor_counts
#print axioms Erdos298.subsetSumsMod_eq_univ_of_isDiverse
#print axioms Erdos298.exists_diverse_scaled_subset_mod_coverage
#print axioms Erdos298.sanity_mod_coverage_empty
#print axioms Erdos298.sanity_mod_coverage_4
#print axioms Erdos298.sanity_mod_coverage_6

#print axioms Erdos298.card_subsetSumsMod_dvd_le_fiber
#print axioms Erdos298.subsetSumsMod_image_zmodProj
#print axioms Erdos298.card_subsetSumsMod_dvd_mul_card_le
#print axioms Erdos298.card_mul_card_subsetSumsMod_dvd_le_of_isDiverse

#print axioms Erdos298.delta_add_le
#print axioms Erdos298.delta_sum_le_mul_of_forall_le
#print axioms Erdos298.delta_sum_le_mul_of_forall_le_real
#print axioms Erdos298.card_smallGrowth_mul_le
#print axioms Erdos298.card_smallGrowth_le_div
#print axioms Erdos298.card_smallGrowthR_mul_le
#print axioms Erdos298.card_smallGrowthR_le_div
#print axioms Erdos298.exists_mem_large_growth
#print axioms Erdos298.exists_mem_large_growth_real
#print axioms Erdos298.card_subsetSumsMod_insert_eq
#print axioms Erdos298.natCast_zmod_injOn_Ico
#print axioms Erdos298.card_image_natCast_zmod_of_Ico

#print axioms Erdos298.cochrane_ostergaard_spencer_arith_le
#print axioms Erdos298.iterSum_growth_bound_of_kneser_data
#print axioms Erdos298.iterSum_card_ge_of_kneser_hyp
#print axioms Erdos298.iterSum_card_ge_of_kneser_hyp_real
#print axioms Erdos298.subgroupIndex_pos
#print axioms Erdos298.subgroupIndex_dvd_modulus
#print axioms Erdos298.subgroupIndex_dvd_mem
#print axioms Erdos298.subgroupIndex_mono
#print axioms Erdos298.subgroupIndex_doubles_of_lt
#print axioms Erdos298.subgroupIndex_le_of_mem
#print axioms Erdos298.subgroupIndex_le_modulus
#print axioms Erdos298.subgroupIndex_scaled_coprime
#print axioms Erdos298.natCast_zmod_div_injOn_Ico
#print axioms Erdos298.card_image_natCast_zmod_div_of_Ico
#print axioms Erdos298.card_eq_sum_image_fibers
#print axioms Erdos298.delta_fiber_le_delta
#print axioms Erdos298.card_centerFiber
#print axioms Erdos298.centerFiber_subset_kernel
#print axioms Erdos298.delta_centerFiber_eq

#print axioms Erdos298.IntAP.card_toFinset
#print axioms Erdos298.cosetAPLift_card
#print axioms Erdos298.coset_family_length_sum_eq
#print axioms Erdos298.coset_family_length_sum_le_three_mul
#print axioms Erdos298.GreedyState.card_B
#print axioms Erdos298.GreedyState.B_card_ge
#print axioms Erdos298.GreedyState.B_nonempty
#print axioms Erdos298.exists_greedy_element
#print axioms Erdos298.nextState_card
#print axioms Erdos298.nextState_S_mono
#print axioms Erdos298.nextState_g_dvd
#print axioms Erdos298.subsetSumsMod_eq_of_compl_dvd
#print axioms Erdos298.card_ge_of_fibers_ge
#print axioms Erdos298.mul_div_cancel_of_pos
#print axioms Erdos298.card_subsetSumsMod_ge_of_saturated

#print axioms Erdos298.card_smallGrowth_half_le
#print axioms Erdos298.exists_large_growth_of_two_mul_lt
#print axioms Erdos298.floor_mul_succ_gt
#print axioms Erdos298.range2_arith_contradiction
#print axioms Erdos298.card_greedySeq_E
#print axioms Erdos298.greedySeq_S_subset
#print axioms Erdos298.card_greedySeq_S_succ
#print axioms Erdos298.sum_delta_le_card_final
#print axioms Erdos298.sum_delta_le_total
#print axioms Erdos298.disjoint_growth_unsaturated
#print axioms Erdos298.steps_partition
#print axioms Erdos298.card_unsaturatedSteps_ge
#print axioms Erdos298.cfp_lemma_5_6_finite_core

#print axioms Erdos298.concreteFiniteConditions
#print axioms Erdos298.finiteConditions_realizable
#print axioms Erdos298.primorialProd
#print axioms Erdos298.cfpTau
#print axioms Erdos298.cfpTau_pos
#print axioms Erdos298.mem_Y_of_mem_Y_v
#print axioms Erdos298.CFPArithParams.toFiniteConditions
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n
#print axioms Erdos298.chromatic_lower_bound_of_diverse_density

#print axioms Erdos298.filter_not_dvd_sdiff_subset
#print axioms Erdos298.card_sdiff_of_subset
#print axioms Erdos298.card_filter_not_dvd_le_card_add_sdiff
#print axioms Erdos298.isDiverse_subset_of_card_diff_le
#print axioms Erdos298.isDiverse_sdiff_singleton
#print axioms Erdos298.isDiverse_sdiff_finset
#print axioms Erdos298.GreedyState.isDiverse_B
#print axioms Erdos298.exists_diverse_subset_of_card_eq
#print axioms Erdos298.cfp_lemma_5_4_of_deterministic
#print axioms Erdos298.isDiverse_gcd_le_one
#print axioms Erdos298.isDiverse_gcd_eq_one
#print axioms Erdos298.subgroupIndex_eq_one_of_isDiverse
#print axioms Erdos298.exists_disjoint_diverse_subsets
#print axioms Erdos298.exists_scaled_diverse_candidate
#print axioms Erdos298.diverse_candidate_satisfies_finiteConditions
#print axioms Erdos298.cfp_lemma_5_4_full_of_deterministic
#print axioms Erdos298.cfp_lemma_5_4_all_subsets_diverse
#print axioms Erdos298.card_CFPLemma54Subsets_eq

#print axioms Erdos298.subsetSums_mono
#print axioms Erdos298.maxFiberElem_mem
#print axioms Erdos298.le_maxFiberElem
#print axioms Erdos298.card_subsetSums_insert_ge
#print axioms Erdos298.card_subsetSums_union_ge_sum
#print axioms Erdos298.card_subsetSums_union_ge_mul_min
#print axioms Erdos298.card_subsetSums_union_ge_mul_min_real
#print axioms Erdos298.cfp_lemma_5_5
#print axioms Erdos298.cfp_lemma_5_5_scale

#print axioms Erdos298.mul_two_le_of_dvd_of_lt
#print axioms Erdos298.chain_doubling_le
#print axioms Erdos298.chain_length_le_of_le_gMax
#print axioms Erdos298.multiplicative_growth_bound_nat
#print axioms Erdos298.multiplicative_growth_bound_real
#print axioms Erdos298.linear_growth_bound_step
#print axioms Erdos298.linear_step_count_le

#print axioms Erdos298.greedyChoice_mem
#print axioms Erdos298.greedyChoice_growth_max
#print axioms Erdos298.greedyChoice_ordinary_max
#print axioms Erdos298.chain_length_le_log2
#print axioms Erdos298.doubling_chain_finset_card_le
#print axioms Erdos298.growthSteps_g_image_card_le
#print axioms Erdos298.growthSteps_card_le_K
#print axioms Erdos298.card_subsetSumsMod_le_modulus
#print axioms Erdos298.growthSteps_card_le_claim1
#print axioms Erdos298.claim1_growth_bound_of_budget
#print axioms Erdos298.cfp_lemma_5_6_finite_core_closed
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_closed
#print axioms Erdos298.growthSteps_card_le_p16Budget_closed
#print axioms Erdos298.growthSteps_card_le_budget_closed
#print axioms Erdos298.card_selectedMultiplesSums_le_U
#print axioms Erdos298.card_selectedMultiplesSums_insert_eq
#print axioms Erdos298.card_mult_growth_steps_le
#print axioms Erdos298.card_linear_growth_steps_le
#print axioms Erdos298.card_partition_le_p16BlockBudget
#print axioms Erdos298.card_image_scaled_of_injOn
#print axioms Erdos298.exists_candidate_range1_growth
#print axioms Erdos298.growthSteps_card_le_p16TotalBudget
#print axioms Erdos298.growthSteps_card_le_budget_of_numeric_bound
#print axioms Erdos298.exists_candidate_range2_growth_of_iterSum_growth
#print axioms Erdos298.zmodScale_add
#print axioms Erdos298.zmodScale_injective
#print axioms Erdos298.zmodScale_natCast_div
#print axioms Erdos298.translate_image_zmodScale
#print axioms Erdos298.delta_image_zmodScale
#print axioms Erdos298.closure_eq_top_of_one_mem
#print axioms Erdos298.greedySeq_E_mono
#print axioms Erdos298.f_g_mono
#print axioms Erdos298.f_g_succ_eq
#print axioms Erdos298.trajectory_growth_step_range1
#print axioms Erdos298.trajectory_growth_step_range2
#print axioms Erdos298.growthSteps_block_card_le_p16BlockBudget
#print axioms Erdos298.growthSteps_card_le_p16Budget
#print axioms Erdos298.growthSteps_card_le_budget_of_p16
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_p16
#print axioms Erdos298.small_fiber_card_mul_two_lt
#print axioms Erdos298.exists_trajectory_range2_candidate_of_iterSum_growth
#print axioms Erdos298.trajectory_growth_step_range2_of_iterSum_growth
#print axioms Erdos298.growthSteps_block_card_le_p16BlockBudget_of_iterSum_growth
#print axioms Erdos298.growthSteps_card_le_p16Budget_of_iterSum_growth
#print axioms Erdos298.growthSteps_card_le_budget_of_iterSum_growth
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_iterSum_growth
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_of_iterSum_growth
#print axioms Erdos298.injOn_of_inY_v
#print axioms Erdos298.zmodScale_val_div
#print axioms Erdos298.card_centerFiberPullback
#print axioms Erdos298.delta_centerFiberPullback
#print axioms Erdos298.delta_fiber_pullback_le_delta_S
#print axioms Erdos298.unsaturatedSteps_div_neZero
#print axioms Erdos298.unsaturated_step_medium_fiber_and_smallGrowth
#print axioms Erdos298.P17FiniteArithConditions.injOn_A
#print axioms Erdos298.unsaturated_step_growth_of_arith_conditional
#print axioms Erdos298.unsaturatedSteps_growth_of_arith_conditional
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_arith_conditional
#print axioms Erdos298.closure_card_le_three_of_card_three_iterSum_four_le_three
#print axioms Erdos298.exists_eq_pair_or_three_of_zero_mem_card_le_three
#print axioms Erdos298.closure_card_le_three_of_iterSum_four_le_three
#print axioms Erdos298.CosetAP.card_toFinset_le
#print axioms Erdos298.mul_128_lt_of_density
#print axioms Erdos298.proper_subgroup_of_card_lt
#print axioms Erdos298.proper_subgroup_of_card_le_128d
#print axioms Erdos298.card_sup_subgroup_le
#print axioms Erdos298.proper_subgroup_of_three_coset_absorption
#print axioms Erdos298.scaledCosetAPLift_k
#print axioms Erdos298.scaledCosetAPLift_b_le
#print axioms Erdos298.intAPCover_of_family
#print axioms Erdos298.intAPCover_of_single
#print axioms Erdos298.intAPCover_of_coset_family
#print axioms Erdos298.apCoverSieveBridge_of_cover_and_sieve
#print axioms Erdos298.subsetSums_of_mem_sumset_image
#print axioms Erdos298.image_cast_subsetSums_subset_Icc
#print axioms Erdos298.subsetSums_contains_Icc_of_lev
#print axioms Erdos298.mem_subsetSums_of_lev_interval_extend
#print axioms Erdos298.target_hit_of_lev_diverse
#print axioms Erdos298.CFPDiverseWitness.ofLevCoverage
#print axioms Erdos298.minColors_ge_of_lev_coverage

#print axioms Erdos298.exists_disjoint_subsets_list
#print axioms Erdos298.exists_disjoint_diverse_list
#print axioms Erdos298.pairwise_get_of_pairwise
#print axioms Erdos298.exists_disjoint_diverse_family
#print axioms Erdos298.exists_disjoint_diverse_pair_of_family
#print axioms Erdos298.exists_disjoint_diverse_partition_of_div
#print axioms Erdos298.target_hit_of_hasLevIntervalCoverage
#print axioms Erdos298.CFPDiverseWitness.ofLevCoveragePred
#print axioms Erdos298.hasChromaticLowerBound_of_diverse_witnesses
#print axioms Erdos298.hasChromaticLowerBound_of_lev_coverage
#print axioms Erdos298.erdos_problem_360_asymptotic_master_of_diverse
#print axioms Erdos298.erdos_problem_360_asymptotic_master_of_lev
#print axioms Erdos298.hasChromaticLowerBound_of_asymptotic_params

#print axioms Erdos298.smallGrowth_subset_subgroup
#print axioms Erdos298.proper_subgroup_smallGrowth_of_three_coset_absorption
#print axioms Erdos298.smallGrowth_proper_subgroup_of_closure_ne_top
#print axioms Erdos298.guardedAPCover_of_trichotomy
#print axioms Erdos298.trichotomy_of_guardedAPCover
#print axioms Erdos298.guardedAPCover_iff_trichotomy
#print axioms Erdos298.not_unguarded_ap_cover
#print axioms Erdos298.not_unguarded_ap_cover'
#print axioms Erdos298.unsaturated_step_growth_of_ap_cover
#print axioms Erdos298.unsaturatedSteps_growth_of_ap_cover
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_ap_cover
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_of_ap_cover
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_rough_count
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_of_rough_count

#print axioms Erdos298.IntAP.inj_of_hb
#print axioms Erdos298.linear_dvd_sub_ge_d
#print axioms Erdos298.card_le_div_add_one_of_separated
#print axioms Erdos298.card_filter_range_dvd_le
#print axioms Erdos298.card_filter_dvd_toFinset_le
#print axioms Erdos298.dvd_natAbs_iff
#print axioms Erdos298.card_filter_natAbs_dvd_toFinset_le
#print axioms Erdos298.roughCount_eq_card_filter_range


#print axioms Erdos298.h_cov_sieve_of_lifting_and_sieve
#print axioms Erdos298.cfp_lemma_5_6_finite_core_of_lifting_and_sieve
#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_of_lifting_and_sieve

#print axioms Erdos298.coprime_q_W_of_inY_v
#print axioms Erdos298.card_le_card_cosetAP_of_image_subset

#print axioms Erdos298.card_filter_natAbs_dvd_toFinset_real_le
#print axioms Erdos298.roughCount_one
#print axioms Erdos298.roughCount_mono
#print axioms Erdos298.roughCount_le_card

#print axioms Erdos298.hasIntAPCover_of_branchA_and_branchB

#print axioms Erdos298.zmod_subgroup_val_dvd
#print axioms Erdos298.zmod_subgroup_scaled_val_dvd

#print axioms Erdos298.cfp_lemma_5_6_m_eq_n_of_branches_and_sieve
#print axioms Erdos298.hasIntAPCoverBranchA
#print axioms Erdos298.concreteCFPArithParams_numeric
#print axioms Erdos298.cfpArithParams_realizable
#print axioms Erdos298.p17FiniteArithConditions_realizable
#print axioms Erdos298.lemma_5_6_parameter_hypotheses_satisfiable

#print axioms Erdos298.selbergTerms_of_squarefree
#print axioms Erdos298.sieveG_ge_half_totient_ratio_mul_log
#print axioms Erdos298.minColors_le_of_totient_log
