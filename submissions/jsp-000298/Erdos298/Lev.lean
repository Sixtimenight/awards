/-
Copyright (c) 2026 The Justin Sun Prize Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Justin Sun Prize Authors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Erdos298.Basic

/-!
# Lev (2010) Integer Sumset Interval Theorems

This module formalizes the core sumset interval theorems of V. F. Lev (2010),
*Consecutive integers in high-multiplicity sumsets*, Acta Math. Hungar. 129, 245–253,
cited as Lemma 2.2 in Conlon–Fox–Pham (2021, arXiv:2104.14766):

1. `mem_Icc_max_min_iff`: Characterization of candidate pairs summing to `g`.
2. `min_sub_max_ge`: Pigeonhole pair-count lower bound across all geometric cases.
3. `card_Icc_max_min_ge`: Finite integer interval cardinality bound.
4. `lev_pigeonhole_interval`: Lev (2010) Lemma 1 (Two-Set Pigeonhole Interval Theorem).
   For finite sets `S1 ⊆ [0, L1]` and `S2 ⊆ [0, L2]` with `max(L1, L2) + 2 ≤ |S1| + |S2|`,
   the sumset `S1 + S2` contains the continuous integer interval:
     `[L1 + L2 - K, K] ⊆ S1 + S2`, where `K = |S1| + |S2| - 2`.
5. `sumset_Icc`: Exact Minkowski sum of two integer intervals:
     `[a1, b1] + [a2, b2] = [a1 + a2, b1 + b2]`.
6. `lev_interval_length`: Evaluation of the interval length `2K - (L1 + L2)`.
-/

namespace Erdos298

open Classical

/-- Characterization of candidate pairs summing to `g`:
    an integer `x` satisfies `0 ≤ x ≤ L1` and `0 ≤ g - x ≤ L2` if and only if
    `max 0 (g - L2) ≤ x ≤ min L1 g`. -/
lemma mem_Icc_max_min_iff (L1 L2 g x : ℤ) :
    x ∈ Finset.Icc (max 0 (g - L2)) (min L1 g) ↔
      x ∈ Finset.Icc 0 L1 ∧ g - x ∈ Finset.Icc 0 L2 := by
  simp only [Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- Pigeonhole pair-count lower bound:
    for any `g` in `[L1 + L2 - K, K]` where `max L1 L2 ≤ K`,
    `min L1 g - max 0 (g - L2) ≥ L1 + L2 - K`. -/
lemma min_sub_max_ge (L1 L2 K g : ℤ)
    (hL1 : L1 ≤ K) (hL2 : L2 ≤ K)
    (hg_low : L1 + L2 - K ≤ g) (hg_high : g ≤ K) :
    L1 + L2 - K ≤ min L1 g - max 0 (g - L2) := by
  omega

/-- Finite integer interval cardinality bound for the candidate set `X_g`. -/
lemma card_Icc_max_min_ge (L1 L2 K g : ℤ)
    (hL1 : L1 ≤ K) (hL2 : L2 ≤ K)
    (hK : 0 ≤ L1 + L2 - K)
    (hg_low : L1 + L2 - K ≤ g) (hg_high : g ≤ K) :
    L1 + L2 - K + 1 ≤ ((Finset.Icc (max 0 (g - L2)) (min L1 g)).card : ℤ) := by
  have h_le : max 0 (g - L2) ≤ min L1 g + 1 := by
    have := min_sub_max_ge L1 L2 K g hL1 hL2 hg_low hg_high
    omega
  rw [Int.card_Icc_of_le _ _ h_le]
  have := min_sub_max_ge L1 L2 K g hL1 hL2 hg_low hg_high
  omega

/-- **Lev (2010) Lemma 1 (Two-Set Pigeonhole Interval Theorem)**:
    Let `S1 ⊆ [0, L1]` and `S2 ⊆ [0, L2]` be finite sets of integers.
    If `max(L1, L2) + 2 ≤ |S1| + |S2|`, then the sumset `S1 + S2` contains the
    continuous integer interval `[L1 + L2 - K, K]`, where `K = |S1| + |S2| - 2`. -/
theorem lev_pigeonhole_interval
    (L1 L2 : ℤ) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (S1 S2 : Finset ℤ)
    (hS1 : S1 ⊆ Finset.Icc 0 L1)
    (hS2 : S2 ⊆ Finset.Icc 0 L2)
    (h_dense : max L1 L2 + 2 ≤ (S1.card : ℤ) + (S2.card : ℤ)) :
    Finset.Icc (L1 + L2 - ((S1.card : ℤ) + (S2.card : ℤ) - 2))
               ((S1.card : ℤ) + (S2.card : ℤ) - 2) ⊆ sumset S1 S2 := by
  set K : Int := (S1.card : Int) + (S2.card : Int) - 2
  have hK_ge : max L1 L2 ≤ K := by omega
  have hL1_le_K : L1 ≤ K := (le_max_left L1 L2).trans hK_ge
  have hL2_le_K : L2 ≤ K := (le_max_right L1 L2).trans hK_ge
  set U1 := Finset.Icc 0 L1
  set U2 := Finset.Icc 0 L2
  have hU1_card : (U1.card : Int) = L1 + 1 := by
    rw [Int.card_Icc_of_le 0 L1 (by omega)]
    omega
  have hU2_card : (U2.card : Int) = L2 + 1 := by
    rw [Int.card_Icc_of_le 0 L2 (by omega)]
    omega
  have hS1_card_le : S1.card ≤ U1.card := Finset.card_le_card hS1
  have hS2_card_le : S2.card ≤ U2.card := Finset.card_le_card hS2
  have hK_le_sum : 0 ≤ L1 + L2 - K := by omega
  have hU1_sdiff : (U1 \ S1).card = U1.card - S1.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS1]
  have hU2_sdiff : (U2 \ S2).card = U2.card - S2.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS2]
  intro g hg
  simp only [Finset.mem_Icc] at hg
  rcases hg with ⟨hg_low, hg_high⟩
  have hX_card_ge : L1 + L2 - K + 1 ≤ ((Finset.Icc (max 0 (g - L2)) (min L1 g)).card : Int) :=
    card_Icc_max_min_ge L1 L2 K g hL1_le_K hL2_le_K hK_le_sum hg_low hg_high
  by_contra h_not_mem
  have h_no_pair : ∀ x ∈ Finset.Icc (max 0 (g - L2)) (min L1 g), ¬ (x ∈ S1 ∧ g - x ∈ S2) := by
    intro x hx ⟨hx1, hx2⟩
    apply h_not_mem
    rw [mem_sumset_iff]
    refine ⟨x, hx1, g - x, hx2, by ring⟩
  let X := Finset.Icc (max 0 (g - L2)) (min L1 g)
  have hX_card_ge' : L1 + L2 - K + 1 ≤ (X.card : Int) := hX_card_ge
  let E1 := X \ S1
  let E2 := X.filter (fun x => g - x ∉ S2)
  have hX_sub : X ⊆ E1 ∪ E2 := by
    intro x hx
    by_cases hxS1 : x ∈ S1
    · apply Finset.mem_union_right
      simp only [E2, Finset.mem_filter, hx, true_and]
      intro h_gx
      exact h_no_pair x hx ⟨hxS1, h_gx⟩
    · apply Finset.mem_union_left
      simp only [E1, Finset.mem_sdiff, hx, hxS1, not_false_eq_true, and_self]
  have hE1_sub : E1 ⊆ U1 \ S1 := by
    intro x hx
    simp only [E1, Finset.mem_sdiff] at hx
    have hxU1 : x ∈ U1 := by
      have hxX := hx.1
      rw [mem_Icc_max_min_iff] at hxX
      exact hxX.1
    simp only [Finset.mem_sdiff, hxU1, hx.2, not_false_eq_true, and_self]
  have hE1_card : (E1.card : Int) ≤ (U1.card : Int) - (S1.card : Int) := by
    have h1 := Finset.card_le_card hE1_sub
    rw [hU1_sdiff] at h1
    have h_cast : ((U1.card - S1.card : Nat) : Int) = (U1.card : Int) - (S1.card : Int) :=
      Nat.cast_sub hS1_card_le
    omega
  let f : Int → Int := fun x => g - x
  have hf_inj : ∀ a ∈ E2, ∀ b ∈ E2, f a = f b → a = b := by
    intro a _ b _ hab
    dsimp [f] at hab
    omega
  have hE2_img_sub : E2.image f ⊆ U2 \ S2 := by
    intro y hy
    simp only [Finset.mem_image, E2, Finset.mem_filter] at hy
    rcases hy with ⟨x, ⟨hxX, hx_not⟩, rfl⟩
    have hxU2 : g - x ∈ U2 := by
      rw [mem_Icc_max_min_iff] at hxX
      exact hxX.2
    simp only [Finset.mem_sdiff]
    exact ⟨hxU2, hx_not⟩
  have hE2_card : (E2.card : Int) ≤ (U2.card : Int) - (S2.card : Int) := by
    have h1 : (E2.image f).card = E2.card := Finset.card_image_of_injOn hf_inj
    have h2 := Finset.card_le_card hE2_img_sub
    rw [h1, hU2_sdiff] at h2
    have h_cast : ((U2.card - S2.card : Nat) : Int) = (U2.card : Int) - (S2.card : Int) :=
      Nat.cast_sub hS2_card_le
    omega
  have hX_le : (X.card : Int) ≤ (E1.card : Int) + (E2.card : Int) := by
    have h_sub := Finset.card_le_card hX_sub
    have h_un := Finset.card_union_le E1 E2
    omega
  omega

/-- Exact Minkowski sum of two integer intervals:
    `[a1, b1] + [a2, b2] = [a1 + a2, b1 + b2]`. -/
theorem sumset_Icc (a1 b1 a2 b2 : ℤ) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) :
    sumset (Finset.Icc a1 b1) (Finset.Icc a2 b2) = Finset.Icc (a1 + a2) (b1 + b2) := by
  ext z
  simp only [mem_sumset_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, y, ⟨hya, hyb⟩, rfl⟩
    constructor <;> omega
  · rintro ⟨hza, hzb⟩
    refine ⟨max a1 (z - b2), ?_, z - max a1 (z - b2), ?_, by ring⟩
    · constructor <;> omega
    · constructor <;> omega

/-- Algebraic length evaluation of the Lev pigeonhole interval:
    `K - (L1 + L2 - K) = 2K - (L1 + L2)`. -/
lemma lev_interval_length (L1 L2 K : ℤ) :
    K - (L1 + L2 - K) = 2 * K - (L1 + L2) := by ring

/-- Monotone containment: sumset of sub-intervals is contained in sumset of outer sets. -/
lemma sumset_subset_of_subset {S1 S2 : Finset ℤ} {J1 J2 : Finset ℤ}
    (h1 : J1 ⊆ S1) (h2 : J2 ⊆ S2) :
    sumset J1 J2 ⊆ sumset S1 S2 :=
  sumset_subset_sumset h1 h2

/-- An interval in `S1` combined with an interval in `S2` yields a larger continuous interval. -/
theorem sumset_Icc_subset_sumset {S1 S2 : Finset ℤ} {a1 b1 a2 b2 : ℤ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (hS1 : Finset.Icc a1 b1 ⊆ S1) (hS2 : Finset.Icc a2 b2 ⊆ S2) :
    Finset.Icc (a1 + a2) (b1 + b2) ⊆ sumset S1 S2 := by
  rw [← sumset_Icc a1 b1 a2 b2 h1 h2]
  exact sumset_subset_of_subset hS1 hS2

end Erdos298