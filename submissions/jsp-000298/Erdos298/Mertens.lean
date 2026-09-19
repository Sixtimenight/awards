import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting

open Real

namespace Erdos298

lemma inv_sq_le_inv_sub (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / ((k : ℝ) ^ 2) ≤ (1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ) := by
  have hk_cast : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have h1le : 1 ≤ k := by omega
    rw [Nat.cast_sub h1le, Nat.cast_one]
  rw [hk1_cast]
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (k : ℝ) ≠ 0 := by linarith
  have h_eq : (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) = (1 : ℝ) / (((k : ℝ) - 1) * (k : ℝ)) := by
    field_simp
    ring
  rw [h_eq]
  have h_prod_pos : (0 : ℝ) < ((k : ℝ) - 1) * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have : (0 : ℝ) < (k : ℝ) := by linarith
    positivity
  have h_sq_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < (k : ℝ) := by linarith
    positivity
  have h_le : ((k : ℝ) - 1) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith
  exact (one_div_le_one_div h_sq_pos h_prod_pos).mpr h_le

lemma sum_Icc_sub_tele (f : ℕ → ℝ) (z : ℕ) (hz : 2 ≤ z) :
    (∑ k ∈ Finset.Icc 2 z, (f (k - 1) - f k)) = f 1 - f z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hz
  clear hz
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have h_assoc : 2 + (d + 1) = (2 + d) + 1 := by omega
    rw [h_assoc]
    have h_split : Finset.Icc 2 ((2 + d) + 1) = insert ((2 + d) + 1) (Finset.Icc 2 (2 + d)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not : (2 + d) + 1 ∉ Finset.Icc 2 (2 + d) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro; omega
    rw [h_split, Finset.sum_insert h_not, ih]
    have hz_sub : (2 + d) + 1 - 1 = 2 + d := by omega
    rw [hz_sub]
    ring

lemma sum_inv_sq_le_two (z : ℕ) :
    (∑ k ∈ Finset.Icc 1 z, (1 : ℝ) / ((k : ℝ) ^ 2)) ≤ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hz1 : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr hz
  by_cases hz2 : z = 1
  · subst hz2
    simp
  have hz_ge_2 : 2 ≤ z := by omega
  have h_split : Finset.Icc 1 z = insert 1 (Finset.Icc 2 z) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1_not : 1 ∉ Finset.Icc 2 z := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro; omega
  rw [h_split, Finset.sum_insert h1_not]
  simp only [Nat.cast_one, one_pow, div_one]
  have h_term_le : ∀ k ∈ Finset.Icc 2 z, (1 : ℝ) / ((k : ℝ) ^ 2) ≤ (1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact inv_sq_le_inv_sub k hk.1
  have h_sum_le := Finset.sum_le_sum h_term_le
  have h_tele := sum_Icc_sub_tele (fun k => (1 : ℝ) / (k : ℝ)) z hz_ge_2
  simp only [Nat.cast_one, div_one] at h_tele
  have hz_pos : (0 : ℝ) < (z : ℝ) := by
    have : 0 < z := by omega
    exact Nat.cast_pos.mpr this
  have hz_inv_pos : (0 : ℝ) ≤ (1 : ℝ) / (z : ℝ) := by positivity
  linarith

lemma harmonic_le_two_mul_sum_squarefree_inv (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ)) ≤
      2 * (∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (a : ℝ)) := by
  let S := (Finset.Icc 1 z).filter Squarefree
  let B := Finset.Icc 1 z
  choose! a b hab_eq ha_sq using Nat.sq_mul_squarefree
  let f : ℕ → ℕ × ℕ := fun n => (a n, b n)
  have hf_inj : Set.InjOn f (Finset.Icc 1 z) := by
    intro n1 hn1 n2 hn2 h_eq
    dsimp [f] at h_eq
    have ha_eq : a n1 = a n2 := (Prod.ext_iff.mp h_eq).1
    have hb_eq : b n1 = b n2 := (Prod.ext_iff.mp h_eq).2
    have e1 := hab_eq n1
    have e2 := hab_eq n2
    rw [← e1, ← e2, ha_eq, hb_eq]
  have hf_mem : ∀ n ∈ Finset.Icc 1 z, f n ∈ S ×ˢ B := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn_pos : 0 < n := by omega
    dsimp [f]
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, S, B]
    have e := hab_eq n
    have ha_pos : 0 < a n := by
      by_contra! h0
      have : a n = 0 := by omega
      rw [this, mul_zero] at e
      omega
    have hb_pos : 0 < b n := by
      by_contra! h0
      have : b n = 0 := by omega
      rw [this, zero_pow (by omega), zero_mul] at e
      omega
    refine ⟨⟨⟨ha_pos, ?_⟩, ha_sq n⟩, ⟨hb_pos, ?_⟩⟩
    · have hb_ge : 1 ≤ b n := hb_pos
      have hb2_ge : 1 ≤ (b n) ^ 2 := by nlinarith
      have : a n ≤ (b n) ^ 2 * a n := by nlinarith
      omega
    · have ha_ge : 1 ≤ a n := ha_pos
      have : (b n) ^ 2 ≤ (b n) ^ 2 * a n := by nlinarith
      have : b n ≤ (b n) ^ 2 := by nlinarith
      omega
  have h_sum_map : (∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ)) =
      ∑ p ∈ (Finset.Icc 1 z).image f, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2)) := by
    rw [Finset.sum_image hf_inj]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f]
    congr 1
    have h_prod : (a n : ℝ) * (b n : ℝ) ^ 2 = ((b n ^ 2 * a n : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h_prod, hab_eq n]
  have h_sub : (Finset.Icc 1 z).image f ⊆ S ×ˢ B := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    exact hf_mem n hn
  have h_le_prod : (∑ p ∈ (Finset.Icc 1 z).image f, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2))) ≤
      ∑ p ∈ S ×ˢ B, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (by intros; positivity)
  have h_prod_split : (∑ p ∈ S ×ˢ B, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2))) =
      (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) * (∑ b ∈ B, (1 : ℝ) / ((b : ℝ) ^ 2)) := by
    rw [Finset.sum_product]
    have h_inner : ∀ x ∈ S, (∑ y ∈ B, (1 : ℝ) / ((x : ℝ) * (y : ℝ) ^ 2)) =
        ((1 : ℝ) / (x : ℝ)) * ∑ y ∈ B, (1 : ℝ) / ((y : ℝ) ^ 2) := by
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [Finset.sum_congr rfl h_inner, ← Finset.sum_mul]
  have h_B_le_2 := sum_inv_sq_le_two z
  have h_S_nonneg : 0 ≤ ∑ a ∈ S, (1 : ℝ) / (a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    positivity
  calc ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ)
    _ = ∑ p ∈ (Finset.Icc 1 z).image f, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2)) := h_sum_map
    _ ≤ ∑ p ∈ S ×ˢ B, (1 : ℝ) / (((p.1 : ℝ) * (p.2 : ℝ) ^ 2)) := h_le_prod
    _ = (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) * (∑ b ∈ B, (1 : ℝ) / ((b : ℝ) ^ 2)) := h_prod_split
    _ ≤ (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) * 2 := by gcongr
    _ = 2 * (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) := by ring




lemma log_le_harmonic (z : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) ≤ ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
  have h1 : Real.log (z : ℝ) ≤ Real.log (↑(z + 1) : ℝ) := by
    apply Real.log_le_log
    · exact Nat.cast_pos.mpr (by omega)
    · exact_mod_cast (by omega)
  have h2 := log_add_one_le_harmonic z
  have h3 : (harmonic z : ℝ) = ∑ n ∈ Finset.Icc 1 z, (1 : ℝ) / (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  rw [h3] at h2
  exact h1.trans h2

lemma sum_squarefree_inv_ge_half_log (z : ℕ) (hz : 1 ≤ z) :
    (1 / 2 : ℝ) * Real.log (z : ℝ) ≤ ∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (a : ℝ) := by
  have h_harm := log_le_harmonic z hz
  have h_sq := harmonic_le_two_mul_sum_squarefree_inv z
  linarith

lemma sum_squarefree_inv_totient_ge_half_log (z : ℕ) (hz : 1 ≤ z) :
    (1 / 2 : ℝ) * Real.log (z : ℝ) ≤ ∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / ((Nat.totient a : ℝ)) := by
  have h_le : (∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (a : ℝ)) ≤
      ∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / ((Nat.totient a : ℝ)) := by
    apply Finset.sum_le_sum
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    have ha_pos : 0 < a := by omega
    have ht_pos : 0 < Nat.totient a := Nat.totient_pos.mpr ha_pos
    have ht_le : Nat.totient a ≤ a := Nat.totient_le a
    have ha_cast_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha_pos
    have ht_cast_pos : (0 : ℝ) < (Nat.totient a : ℝ) := Nat.cast_pos.mpr ht_pos
    have ht_cast_le : (Nat.totient a : ℝ) ≤ (a : ℝ) := by exact_mod_cast ht_le
    exact (one_div_le_one_div ha_cast_pos ht_cast_pos).mpr ht_cast_le
  have h_base := sum_squarefree_inv_ge_half_log z hz
  linarith




lemma totient_of_squarefree {d : ℕ} (hd : Squarefree d) :
    Nat.totient d = ∏ p ∈ d.primeFactors, (p - 1) := by
  have hd_pos : 0 < d := hd.ne_zero.bot_lt
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hd,
      Nat.div_self hd_pos, one_mul]

lemma primeFactors_inj_of_squarefree {d1 d2 : ℕ}
    (h1 : Squarefree d1) (h2 : Squarefree d2)
    (h : d1.primeFactors = d2.primeFactors) : d1 = d2 := by
  rw [← Nat.prod_primeFactors_of_squarefree h1, ← Nat.prod_primeFactors_of_squarefree h2, h]


lemma cast_totient_of_squarefree {d : ℕ} (hd : Squarefree d) :
    ((Nat.totient d : ℝ)) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have e := totient_of_squarefree hd
  have h_cast : ((Nat.totient d : ℝ)) = ((∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast e
  rw [h_cast, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have : 1 ≤ p := hp_prime.one_le
  rw [Nat.cast_sub (R := ℝ) this, Nat.cast_one]

lemma inv_totient_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (1 : ℝ) / ((Nat.totient d : ℝ)) = ∏ p ∈ d.primeFactors, ((1 : ℝ) / ((p : ℝ) - 1)) := by
  rw [cast_totient_of_squarefree hd, one_div, ← Finset.prod_inv_distrib]
  simp only [one_div]


lemma one_add_inv_sub_one (p : ℝ) (hp : 1 < p) :
    1 + 1 / (p - 1) = p / (p - 1) := by
  have : p - 1 ≠ 0 := by linarith
  field_simp
  ring

lemma sum_divisors_squarefree_inv_totient_le (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter Squarefree, (1 : ℝ) / ((Nat.totient d : ℝ))) ≤
      (n : ℝ) / ((Nat.totient n : ℝ)) := by
  let f : ℕ → Finset ℕ := fun d => d.primeFactors
  let S := n.divisors.filter Squarefree
  let P := n.primeFactors
  have hf_inj : Set.InjOn f S := by
    intro d1 hd1 d2 hd2 h_eq
    have hd1_sq : Squarefree d1 := (Finset.mem_filter.mp hd1).2
    have hd2_sq : Squarefree d2 := (Finset.mem_filter.mp hd2).2
    exact primeFactors_inj_of_squarefree hd1_sq hd2_sq h_eq
  have hf_sub : S.image f ⊆ P.powerset := by
    intro s hs
    simp only [Finset.mem_image, S] at hs
    obtain ⟨d, hd, rfl⟩ := hs
    simp only [Finset.mem_powerset, P]
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact Nat.primeFactors_mono hd_dvd hn.ne'
  have h_sum_map : (∑ d ∈ S, (1 : ℝ) / ((Nat.totient d : ℝ))) =
      ∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.sum_image hf_inj]
    apply Finset.sum_congr rfl
    intro d hd
    have hd_sq : Squarefree d := (Finset.mem_filter.mp hd).2
    exact inv_totient_of_squarefree hd_sq
  have h_nonneg : ∀ s ∈ P.powerset, 0 ≤ ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1)) := by
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    simp only [Finset.mem_powerset, P] at hs
    have hp_P : p ∈ P := hs hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_P
    have hp_lt : 1 < p := hp_prime.one_lt
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_lt
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have h_sub_le : (∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1))) ≤
      ∑ s ∈ P.powerset, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hf_sub (fun s hs _ => h_nonneg s hs)
  have h_prod_one_add : (∑ s ∈ P.powerset, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1))) =
      ∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) - 1)) :=
    (Finset.prod_one_add P).symm
  have h_term_eq : ∀ p ∈ P, 1 + (1 : ℝ) / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_lt : 1 < p := hp_prime.one_lt
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_lt
    exact one_add_inv_sub_one (p : ℝ) this
  have h_prod_eq : (∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) - 1))) =
      ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) :=
    Finset.prod_congr rfl h_term_eq
  have h_prod_div : (∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) =
      (∏ p ∈ P, (p : ℝ)) / (∏ p ∈ P, ((p : ℝ) - 1)) := by
    rw [Finset.prod_div_distrib]
  have h_totient_prod := Nat.totient_mul_prod_primeFactors n
  have h_tot_cast : ((Nat.totient n : ℝ)) * (∏ p ∈ P, (p : ℝ)) =
      (n : ℝ) * (∏ p ∈ P, ((p : ℝ) - 1)) := by
    have h_c : (((Nat.totient n * ∏ p ∈ P, p : ℕ) : ℝ)) = (((n * ∏ p ∈ P, (p - 1) : ℕ) : ℝ)) := by
      exact_mod_cast h_totient_prod
    push_cast at h_c
    rw [h_c]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have : 1 ≤ p := hp_prime.one_le
    rw [Nat.cast_sub (R := ℝ) this, Nat.cast_one]
  have h_denom_pos : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_lt : 1 < p := hp_prime.one_lt
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_lt
    linarith
  have h_tot_pos : (0 : ℝ) < ((Nat.totient n : ℝ)) := by
    have : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    exact Nat.cast_pos.mpr this
  have h_ratio_eq : (∏ p ∈ P, (p : ℝ)) / (∏ p ∈ P, ((p : ℝ) - 1)) =
      (n : ℝ) / ((Nat.totient n : ℝ)) := by
    rw [div_eq_div_iff h_denom_pos.ne' h_tot_pos.ne']
    linarith
  calc (∑ d ∈ S, (1 : ℝ) / ((Nat.totient d : ℝ)))
    _ = ∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1)) := h_sum_map
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, ((1 : ℝ) / ((p : ℝ) - 1)) := h_sub_le
    _ = ∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) - 1)) := h_prod_one_add
    _ = ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) := h_prod_eq
    _ = (∏ p ∈ P, (p : ℝ)) / (∏ p ∈ P, ((p : ℝ) - 1)) := h_prod_div
    _ = (n : ℝ) / ((Nat.totient n : ℝ)) := h_ratio_eq



lemma sum_squarefree_inv_totient_le_mul (n z : ℕ) (hn : 0 < n) :
    (∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / ((Nat.totient a : ℝ))) ≤
      (∑ d ∈ n.divisors.filter Squarefree, (1 : ℝ) / ((Nat.totient d : ℝ))) *
      (∑ c ∈ (Finset.Icc 1 z).filter (fun c => Squarefree c ∧ c.Coprime n), (1 : ℝ) / ((Nat.totient c : ℝ))) := by
  let S := (Finset.Icc 1 z).filter Squarefree
  let D := n.divisors.filter Squarefree
  let C := (Finset.Icc 1 z).filter (fun c => Squarefree c ∧ c.Coprime n)
  let g : ℕ → ℕ × ℕ := fun a => (a.gcd n, a / a.gcd n)
  have hg_inj : Set.InjOn g S := by
    intro a1 ha1 a2 ha2 h_eq
    dsimp [g] at h_eq
    have h1 : a1.gcd n = a2.gcd n := (Prod.ext_iff.mp h_eq).1
    have h2 : a1 / a1.gcd n = a2 / a2.gcd n := (Prod.ext_iff.mp h_eq).2
    have e1 : a1 = a1.gcd n * (a1 / a1.gcd n) := by
      have := Nat.gcd_dvd_left a1 n
      exact (Nat.mul_div_cancel' this).symm
    have e2 : a2 = a2.gcd n * (a2 / a2.gcd n) := by
      have := Nat.gcd_dvd_left a2 n
      exact (Nat.mul_div_cancel' this).symm
    rw [e1, e2, h2]
    congr 1
  have hg_mem : ∀ a ∈ S, g a ∈ D ×ˢ C := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc, S] at ha
    obtain ⟨⟨ha1, haz⟩, ha_sq⟩ := ha
    dsimp [g]
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, D, C]
    have hd_dvd : a.gcd n ∣ n := Nat.gcd_dvd_right a n
    have hd_sq : Squarefree (a.gcd n) := ha_sq.squarefree_of_dvd (Nat.gcd_dvd_left a n)
    have hc_cop : (a / a.gcd n).Coprime n := Nat.coprime_div_gcd_of_squarefree ha_sq hn.ne'
    have ha_eq : a = a.gcd n * (a / a.gcd n) := by
      have := Nat.gcd_dvd_left a n
      exact (Nat.mul_div_cancel' this).symm
    have hc_sq : Squarefree (a / a.gcd n) := by
      rw [ha_eq] at ha_sq
      exact ha_sq.of_mul_right
    have hd_pos : 0 < a.gcd n := Nat.gcd_pos_of_pos_left n ha1
    have ha_pos : 0 < a := by omega
    have hc_pos : 0 < a / a.gcd n := Nat.div_pos (Nat.gcd_le_left n ha_pos) hd_pos
    have hc_le_a : a / a.gcd n ≤ a := Nat.div_le_self a (a.gcd n)
    have hc_le_z : a / a.gcd n ≤ z := hc_le_a.trans haz
    refine ⟨⟨⟨hd_dvd, hn.ne'⟩, hd_sq⟩, ⟨⟨hc_pos, hc_le_z⟩, hc_sq, hc_cop⟩⟩
  have h_sub : S.image g ⊆ D ×ˢ C := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hg_mem a ha
  have h_term : ∀ a ∈ S, (1 : ℝ) / ((Nat.totient a : ℝ)) =
      ((1 : ℝ) / ((Nat.totient (g a).1 : ℝ))) * ((1 : ℝ) / ((Nat.totient (g a).2 : ℝ))) := by
    intro a ha
    simp only [Finset.mem_filter, S] at ha
    have ha_sq : Squarefree a := ha.2
    dsimp [g]
    have ha_eq : a = a.gcd n * (a / a.gcd n) := by
      have := Nat.gcd_dvd_left a n
      exact (Nat.mul_div_cancel' this).symm
    have h_cop : (a.gcd n).Coprime (a / a.gcd n) := by
      rw [ha_eq] at ha_sq
      exact Nat.coprime_of_squarefree_mul ha_sq
    have h_tot : Nat.totient a = Nat.totient (a.gcd n) * Nat.totient (a / a.gcd n) := by
      nth_rw 1 [ha_eq]
      exact Nat.totient_mul h_cop
    have h_tot_cast : ((Nat.totient a : ℝ)) = ((Nat.totient (a.gcd n) : ℝ)) * ((Nat.totient (a / a.gcd n) : ℝ)) := by
      exact_mod_cast h_tot
    rw [h_tot_cast, one_div_mul_one_div]
  have h_sum_map : (∑ a ∈ S, (1 : ℝ) / ((Nat.totient a : ℝ))) =
      ∑ p ∈ S.image g, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ))) := by
    rw [Finset.sum_image hg_inj]
    apply Finset.sum_congr rfl
    intro a ha
    exact h_term a ha
  have h_le_prod : (∑ p ∈ S.image g, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ)))) ≤
      ∑ p ∈ D ×ˢ C, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro p _ _
    positivity
  have h_prod_split : (∑ p ∈ D ×ˢ C, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ)))) =
      (∑ d ∈ D, (1 : ℝ) / ((Nat.totient d : ℝ))) *
      (∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ))) := by
    rw [Finset.sum_product]
    have h_inner : ∀ d ∈ D, (∑ c ∈ C, ((1 : ℝ) / ((Nat.totient d : ℝ))) * ((1 : ℝ) / ((Nat.totient c : ℝ)))) =
        ((1 : ℝ) / ((Nat.totient d : ℝ))) * ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := by
      intro d hd
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl h_inner, ← Finset.sum_mul]
  calc (∑ a ∈ S, (1 : ℝ) / ((Nat.totient a : ℝ)))
    _ = ∑ p ∈ S.image g, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ))) := h_sum_map
    _ ≤ ∑ p ∈ D ×ˢ C, ((1 : ℝ) / ((Nat.totient p.1 : ℝ))) * ((1 : ℝ) / ((Nat.totient p.2 : ℝ))) := h_le_prod
    _ = (∑ d ∈ D, (1 : ℝ) / ((Nat.totient d : ℝ))) * (∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ))) := h_prod_split



lemma sum_coprime_squarefree_inv_totient_ge_half (n z : ℕ) (hn : 0 < n) (hz : 1 ≤ z) :
    (1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ) ≤
      ∑ c ∈ (Finset.Icc 1 z).filter (fun c => Squarefree c ∧ c.Coprime n), (1 : ℝ) / ((Nat.totient c : ℝ)) := by
  let C := (Finset.Icc 1 z).filter (fun c => Squarefree c ∧ c.Coprime n)
  let D := n.divisors.filter Squarefree
  let S := (Finset.Icc 1 z).filter Squarefree
  have h_base := sum_squarefree_inv_totient_ge_half_log z hz
  have h_mul := sum_squarefree_inv_totient_le_mul n z hn
  have h_div := sum_divisors_squarefree_inv_totient_le n hn
  have h_C_nonneg : 0 ≤ ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := by
    apply Finset.sum_nonneg
    intro c hc
    positivity
  have h_trans : (1 / 2 : ℝ) * Real.log (z : ℝ) ≤
      ((n : ℝ) / ((Nat.totient n : ℝ))) * ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := by
    calc (1 / 2 : ℝ) * Real.log (z : ℝ)
      _ ≤ ∑ a ∈ S, (1 : ℝ) / ((Nat.totient a : ℝ)) := h_base
      _ ≤ (∑ d ∈ D, (1 : ℝ) / ((Nat.totient d : ℝ))) * ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := h_mul
      _ ≤ ((n : ℝ) / ((Nat.totient n : ℝ))) * ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := by gcongr
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have htot_pos : (0 : ℝ) < ((Nat.totient n : ℝ)) := by
    have : 0 < Nat.totient n := Nat.totient_pos.mpr hn
    exact Nat.cast_pos.mpr this
  have h_ratio_pos : (0 : ℝ) < (Nat.totient n : ℝ) / (n : ℝ) := div_pos htot_pos hn_pos
  have h_cancel : ((Nat.totient n : ℝ) / (n : ℝ)) * (((n : ℝ) / ((Nat.totient n : ℝ))) * ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ))) =
      ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := by
    have h_inv : ((Nat.totient n : ℝ) / (n : ℝ)) * ((n : ℝ) / ((Nat.totient n : ℝ))) = 1 := by
      field_simp
    rw [← mul_assoc, h_inv, one_mul]
  have h_mul_le := mul_le_mul_of_nonneg_left h_trans (le_of_lt h_ratio_pos)
  rw [h_cancel] at h_mul_le
  calc (1 / 2 : ℝ) * ((Nat.totient n : ℝ) / (n : ℝ)) * Real.log (z : ℝ)
    _ = ((Nat.totient n : ℝ) / (n : ℝ)) * ((1 / 2 : ℝ) * Real.log (z : ℝ)) := by ring
    _ ≤ ∑ c ∈ C, (1 : ℝ) / ((Nat.totient c : ℝ)) := h_mul_le

lemma primeFactors_subset_primesLE {a z : ℕ} (haz : a ≤ z) :
    a.primeFactors ⊆ Nat.primesLE z := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  rw [Nat.mem_primesLE]
  have ha_pos : 1 ≤ a := by
    obtain ⟨_, _, ha_ne⟩ := hp
    exact Nat.pos_of_ne_zero ha_ne
  have hp_le_a : p ≤ a := Nat.le_of_dvd ha_pos hp.2.1
  exact ⟨hp_le_a.trans haz, hp.1⟩

lemma prod_primesLE_one_add (z : ℕ) :
    ∏ p ∈ Nat.primesLE z, (1 + (1 : ℝ) / (p : ℝ)) =
      ∑ S ∈ (Nat.primesLE z).powerset, ∏ p ∈ S, ((1 : ℝ) / (p : ℝ)) := by
  exact Finset.prod_one_add (Nat.primesLE z)

lemma prod_one_add_le_exp_sum (z : ℕ) :
    ∏ p ∈ Nat.primesLE z, (1 + (1 : ℝ) / (p : ℝ)) ≤ exp (∑ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    positivity
  · intro p _
    rw [add_comm]
    exact add_one_le_exp ((1 : ℝ) / (p : ℝ))

lemma cast_prod_primeFactors_of_squarefree {a : ℕ} (ha : Squarefree a) :
    (a : ℝ) = ∏ p ∈ a.primeFactors, (p : ℝ) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree ha]
  rw [Nat.cast_prod]

lemma inv_prod_primeFactors_of_squarefree {a : ℕ} (ha : Squarefree a) :
    (1 : ℝ) / (a : ℝ) = ∏ p ∈ a.primeFactors, ((1 : ℝ) / (p : ℝ)) := by
  rw [cast_prod_primeFactors_of_squarefree ha, one_div, ← Finset.prod_inv_distrib]
  simp only [one_div]

lemma sum_squarefree_inv_le_prod_primesLE (z : ℕ) :
    (∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (a : ℝ)) ≤
      ∏ p ∈ Nat.primesLE z, (1 + (1 : ℝ) / (p : ℝ)) := by
  let S := (Finset.Icc 1 z).filter Squarefree
  let P := Nat.primesLE z
  let f : ℕ → Finset ℕ := fun a => a.primeFactors
  have h_inj : Set.InjOn f S := by
    intro a1 ha1 a2 ha2 heq
    have ha1_sq : Squarefree a1 := (Finset.mem_filter.mp ha1).2
    have ha2_sq : Squarefree a2 := (Finset.mem_filter.mp ha2).2
    exact primeFactors_inj_of_squarefree ha1_sq ha2_sq heq
  have h_im_sub : S.image f ⊆ P.powerset := by
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_Icc, S] at ha
    rw [Finset.mem_powerset]
    exact primeFactors_subset_primesLE ha.1.2
  have h_sum_map : (∑ a ∈ S, (1 : ℝ) / (a : ℝ)) =
      ∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / (p : ℝ)) := by
    rw [Finset.sum_image h_inj]
    apply Finset.sum_congr rfl
    intro a ha
    have ha_sq : Squarefree a := (Finset.mem_filter.mp ha).2
    exact inv_prod_primeFactors_of_squarefree ha_sq
  have h_sub_le : (∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / (p : ℝ))) ≤
      ∑ s ∈ P.powerset, ∏ p ∈ s, ((1 : ℝ) / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_im_sub
    intro s _ _
    apply Finset.prod_nonneg
    intro p _
    positivity
  calc (∑ a ∈ S, (1 : ℝ) / (a : ℝ))
    _ = ∑ s ∈ S.image f, ∏ p ∈ s, ((1 : ℝ) / (p : ℝ)) := h_sum_map
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, ((1 : ℝ) / (p : ℝ)) := h_sub_le
    _ = ∏ p ∈ P, (1 + (1 : ℝ) / (p : ℝ)) := (prod_primesLE_one_add z).symm

/-- (M2) Elementary lower bound on the sum of prime reciprocals:
    ∑_{p ≤ z} 1/p ≥ log(log z) - log 2 for all z ≥ 3. -/
theorem sum_primesLE_inv_ge_log_log (z : ℕ) (hz : 3 ≤ z) :
    Real.log (Real.log (z : ℝ)) - Real.log 2 ≤ ∑ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ) := by
  have h_log_pos : 0 < Real.log (z : ℝ) := by
    have : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
    exact Real.log_pos this
  have h_half_log_pos : 0 < (1 / 2 : ℝ) * Real.log (z : ℝ) := by positivity
  have h1z : 1 ≤ z := by omega
  have h_sq_ge : (1 / 2 : ℝ) * Real.log (z : ℝ) ≤
      ∑ a ∈ (Finset.Icc 1 z).filter Squarefree, (1 : ℝ) / (a : ℝ) :=
    sum_squarefree_inv_ge_half_log z h1z
  have h_prod_ge : (1 / 2 : ℝ) * Real.log (z : ℝ) ≤
      ∏ p ∈ Nat.primesLE z, (1 + (1 : ℝ) / (p : ℝ)) :=
    h_sq_ge.trans (sum_squarefree_inv_le_prod_primesLE z)
  have h_exp_ge : (1 / 2 : ℝ) * Real.log (z : ℝ) ≤
      exp (∑ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ)) :=
    h_prod_ge.trans (prod_one_add_le_exp_sum z)
  have h_log_le : Real.log ((1 / 2 : ℝ) * Real.log (z : ℝ)) ≤
      ∑ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ) := by
    rw [← Real.log_exp (∑ p ∈ Nat.primesLE z, (1 : ℝ) / (p : ℝ))]
    exact Real.log_le_log h_half_log_pos h_exp_ge
  have h_log_mul : Real.log ((1 / 2 : ℝ) * Real.log (z : ℝ)) =
      Real.log (Real.log (z : ℝ)) - Real.log 2 := by
    rw [Real.log_mul (by norm_num) h_log_pos.ne']
    have : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [this]
    ring
  rw [h_log_mul] at h_log_le
  exact h_log_le

end Erdos298

