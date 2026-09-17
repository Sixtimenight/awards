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

/-!
# Erdős Problem 360 / JSP-000298: Monochromatic Subset Sums

Let (n) denote the minimum number of colors needed to color {1, ..., n-1}
such that no color class contains a subset whose elements sum to 
.

Alon and Erdős (1996, *Acta Arithmetica* 74(3), pp. 269-272) studied this problem:
1. Cubic-root baseline: partitioning into interval blocks A_k for 
 ≤ (k+1)x
   and remainder blocks gives (n) ≤ 2⌈n^(1/3)⌉.
2. Sieve-remainder bound: sieving multiples of primes p ≤ s with p ∤ n
   leaves a remainder set R. Partitioning R by element counts into blocks
   of size at most s yields:
   (n) ≤ s + |P| + ⌈|R| / s⌉.
3. Lower bound: (n) ≥ 2 for all 
 ≥ 3 (since {1, n-1} sums to 
).
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
  simp only [Finsupp.coe_finsetSum, sum_apply]
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
#print axioms Erdos298.minColors_ge_two