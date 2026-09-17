import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

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
#print axioms Erdos298.minColors_ge_two