import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

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

/-- Small remainder set R: elements x with (s + 1) * x < n. -/
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

/-- Small block C_j: subset of R in the interval [j*s, (j+1)*s - 1]. -/
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

lemma small_block_avoids_subset_sum (n s j : ℕ) (hn : 2 ≤ n) :
    AvoidsSubsetSum (smallBlock n s j) n := by
  intro ⟨T, hTsub, hTsum⟩
  by_cases h0 : T.card = 0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp at hTsum
    omega
  · have h_elem : ∀ x ∈ T, (s + 1) * x ≤ n - 1 := by
      intro x hx
      have := hTsub hx
      simp only [smallBlock, smallRemainder, Finset.mem_filter, Finset.mem_Ico] at this
      omega
    have h_card_T : T.card ≤ s := (Finset.card_le_card hTsub).trans (small_block_card_le n s j)
    have h_sum_le : (s + 1) * T.sum id ≤ s * (n - 1) := by
      rw [Finset.mul_sum]
      dsimp
      have h_sum := Finset.sum_le_sum (fun x hx => h_elem x hx)
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

/-- Main theorem: For any n ≥ 2 and s ≥ 1 with n ≤ s^3,
    there exists a coloring of {1, ..., n-1} with 2*s colors avoiding monochromatic subset sum n. -/
theorem exists_coloring_of_le_cube (n s : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) (hns : n ≤ s ^ 3) :
    ∃ c : ℕ → Fin (2 * s), AvoidsMonoSubsetSum n (2 * s) c := by
  use explicitColoring n s hn hs hns
  intro color
  let class_set := (Finset.Ico 1 n).filter (fun x => explicitColoring n s hn hs hns x = color)
  by_cases h_col : color.val < s
  · -- Case: color in [0, s - 1], belongs to intervalBlock
    let k := color.val + 1
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
  · -- Case: color in [s, 2s - 1], belongs to smallBlock
    have h_col_ge : s ≤ color.val := by omega
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
#print axioms Erdos298.minColors_ge_two