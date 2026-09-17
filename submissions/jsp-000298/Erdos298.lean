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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic


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

