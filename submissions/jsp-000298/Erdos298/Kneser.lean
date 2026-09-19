import Erdos298.DeVos

set_option linter.unusedSectionVars false

open scoped Pointwise
open Classical

namespace Erdos298

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def iterSum : ℕ → Finset G → Finset G
  | 0, _ => {0}
  | k + 1, T => sumset (iterSum k T) T

@[simp]
lemma iterSum_zero (T : Finset G) : iterSum 0 T = {0} := rfl

@[simp]
lemma iterSum_succ (k : ℕ) (T : Finset G) :
    iterSum (k + 1) T = sumset (iterSum k T) T := rfl

lemma iterSum_add (a b : ℕ) (T : Finset G) :
    iterSum (a + b) T = sumset (iterSum a T) (iterSum b T) := by
  induction b with
  | zero =>
    simp only [Nat.add_zero, iterSum_zero, sumset_zero_right]
  | succ b ih =>
    rw [Nat.add_succ, iterSum_succ, ih, iterSum_succ, sumset_assoc]

variable [Fintype G]

lemma finsetAddStab_iterSum_mono (C : Finset G) {j k : ℕ} (hjk : j ≤ k) :
    finsetAddStab (iterSum j C) ≤ finsetAddStab (iterSum k C) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hjk
  intro x (hx : x +ᵥ iterSum j C = iterSum j C)
  change x +ᵥ iterSum (j + d) C = iterSum (j + d) C
  rw [iterSum_add, vadd_sumset_left, hx]

lemma finsetAddStab_iterSum_eq_bot_of_le (C : Finset G) {j k : ℕ} (_hj : 1 ≤ j) (hjk : j ≤ k)
    (h_bot : finsetAddStab (iterSum k C) = ⊥) :
    finsetAddStab (iterSum j C) = ⊥ := by
  have h_le := finsetAddStab_iterSum_mono C hjk
  rw [h_bot] at h_le
  exact le_bot_iff.mp h_le

lemma zero_mem_iterSum (C : Finset G) (h0 : 0 ∈ C) (k : ℕ) :
    (0 : G) ∈ iterSum k C := by
  induction k with
  | zero => simp only [iterSum_zero, Finset.mem_singleton]
  | succ k ih =>
    simp only [iterSum_succ, mem_sumset_iff]
    exact ⟨0, ih, 0, h0, add_zero 0⟩

lemma card_ge_two_of_closure_eq_top_of_ne_top
    {H : AddSubgroup G} (hH : H ≠ ⊤)
    (C : Finset G) (h0 : 0 ∈ C) (hgen : AddSubgroup.closure (C : Set G) = ⊤) :
    2 ≤ (C.image (QuotientAddGroup.mk' H)).card := by
  by_contra! hq
  have h_zero_mem : (0 : G ⧸ H) ∈ C.image (QuotientAddGroup.mk' H) := by
    rw [← map_zero (QuotientAddGroup.mk' H)]
    exact Finset.mem_image_of_mem _ h0
  have h_sing : C.image (QuotientAddGroup.mk' H) = {0} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra h_ne
      have h_sub : {0, x} ⊆ C.image (QuotientAddGroup.mk' H) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact h_zero_mem
        · exact hx
      have h2 : 2 ≤ (C.image (QuotientAddGroup.mk' H)).card := by
        have : ({0, x} : Finset (G ⧸ H)).card = 2 := Finset.card_pair (Ne.symm h_ne)
        rw [← this]
        exact Finset.card_le_card h_sub
      omega
    · rintro rfl
      exact h_zero_mem
  have hC_sub_H : (C : Set G) ⊆ (H : Set G) := by
    intro c hc
    have : QuotientAddGroup.mk' H c ∈ C.image (QuotientAddGroup.mk' H) :=
      Finset.mem_image_of_mem _ hc
    rw [h_sing, Finset.mem_singleton] at this
    exact (QuotientAddGroup.eq_zero_iff (x := c)).mp this
  have h_top_sub : (⊤ : AddSubgroup G) ≤ H := by
    rw [← hgen]
    exact (AddSubgroup.closure_le H).mpr hC_sub_H
  have : H = ⊤ := top_le_iff.mp h_top_sub
  exact hH this

lemma image_mk_iterSum (H : AddSubgroup G) (k : ℕ) (C : Finset G) :
    (iterSum k C).image (QuotientAddGroup.mk' H) =
      iterSum k (C.image (QuotientAddGroup.mk' H)) := by
  induction k with
  | zero =>
    simp only [iterSum_zero, Finset.image_singleton, map_zero]
  | succ k ih =>
    simp only [iterSum_succ]
    rw [image_mk_sumset, ih]

theorem iterSum_card_ge_linear_of_k3
    (h_k3 : ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty → finsetAddStab (sumset X Y) = ⊥ →
      X.card + Y.card ≤ (sumset X Y).card + 1)
    (C : Finset G) (h0 : 0 ∈ C) (hq : 2 ≤ C.card)
    (k : ℕ) (hk : 1 ≤ k)
    (h_bot : finsetAddStab (iterSum k C) = ⊥) :
    k * (C.card - 1) + 1 ≤ (iterSum k C).card := by
  induction k using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | m
    · omega
    rcases m with _ | m
    · -- m = 1
      simp only [zero_add, iterSum_succ, iterSum_zero, sumset_zero_left]
      omega
    · -- m ≥ 2, so m = m' + 2
      set j := m + 1
      have hj_ge : 1 ≤ j := by omega
      have hj_lt : j < m + 2 := by omega
      have hj_le : j ≤ m + 2 := by omega
      have h_bot_j : finsetAddStab (iterSum j C) = ⊥ :=
        finsetAddStab_iterSum_eq_bot_of_le C hj_ge hj_le h_bot
      have ih_j := ih j hj_lt hj_ge h_bot_j
      have hX_ne : (iterSum j C).Nonempty := ⟨0, zero_mem_iterSum C h0 j⟩
      have hY_ne : C.Nonempty := ⟨0, h0⟩
      have h_succ : iterSum (m + 2) C = sumset (iterSum j C) C := rfl
      have h_k3_step := h_k3 (iterSum j C) C hX_ne hY_ne (by rwa [← h_succ])
      rw [← h_succ] at h_k3_step
      have h_step : (iterSum j C).card + (C.card - 1) ≤ (iterSum (m + 2) C).card := by
        omega
      calc (m + 2) * (C.card - 1) + 1
        _ = j * (C.card - 1) + 1 + (C.card - 1) := by
          have : (m + 2) * (C.card - 1) = (j + 1) * (C.card - 1) := rfl
          rw [this, add_mul, one_mul, add_right_comm]
        _ ≤ (iterSum j C).card + (C.card - 1) := by omega
        _ ≤ (iterSum (m + 2) C).card := h_step

lemma arith_growth_le (k d : ℕ) (hk : 1 ≤ k) (hd : 2 ≤ d) :
    (k + 1) * d ≤ 2 * (k * (d - 1) + 1) := by
  have h_sub : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  have h_prod : 0 ≤ ((k : ℤ) - 1) * ((d : ℤ) - 2) := by
    have h1 : 0 ≤ (k : ℤ) - 1 := by omega
    have h2 : 0 ≤ (d : ℤ) - 2 := by omega
    exact mul_nonneg h1 h2
  have h_eq : 2 * ((k : ℤ) * ((d : ℤ) - 1) + 1) - ((k : ℤ) + 1) * (d : ℤ) = ((k : ℤ) - 1) * ((d : ℤ) - 2) := by
    ring
  have h_le : ((k : ℤ) + 1) * (d : ℤ) ≤ 2 * ((k : ℤ) * (((d - 1 : ℕ) : ℤ)) + 1) := by
    rw [h_sub]
    linarith
  exact_mod_cast h_le

theorem iterSum_card_ge_of_zero_mem_of_generates_of_k3
    (h_k3 : ∀ (G' : Type) [AddCommGroup G'] [Fintype G'] [DecidableEq G']
      (X Y : Finset G'), X.Nonempty → Y.Nonempty → finsetAddStab (sumset X Y) = ⊥ →
      X.card + Y.card ≤ (sumset X Y).card + 1)
    (N : ℕ) [NeZero N]
    (C : Finset (ZMod N))
    (h0 : (0 : ZMod N) ∈ C)
    (hgen : AddSubgroup.closure (C : Set (ZMod N)) = ⊤)
    (k : ℕ) (hk : 1 ≤ k) :
    (iterSum k C).card = N ∨
      (k + 1) * C.card ≤ 2 * (iterSum k C).card := by
  set S := iterSum k C
  set H := finsetAddStab S
  by_cases hH : H = ⊤
  · left
    have h0_S : (0 : ZMod N) ∈ S := zero_mem_iterSum C h0 k
    have h_univ : S = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      have hx_H : x ∈ H := by simp [hH]
      have h_eq : x +ᵥ S = S := hx_H
      have h_mem : x + 0 ∈ x +ᵥ S := Finset.mem_vadd_finset.mpr ⟨0, h0_S, rfl⟩
      rw [h_eq] at h_mem
      rwa [add_zero] at h_mem
    rw [h_univ, Finset.card_univ, ZMod.card]
  · right
    set π := QuotientAddGroup.mk' H
    set Cbar := C.image π
    set Sbar := S.image π
    have h0_bar : (0 : (ZMod N) ⧸ H) ∈ Cbar := by
      rw [← map_zero π]
      exact Finset.mem_image_of_mem _ h0
    have hCbar_ge : 2 ≤ Cbar.card := card_ge_two_of_closure_eq_top_of_ne_top hH C h0 hgen
    have hSbar_eq : Sbar = iterSum k Cbar := image_mk_iterSum H k C
    have h_bot : finsetAddStab (iterSum k Cbar) = ⊥ := by
      rw [← hSbar_eq]
      exact finsetAddStab_image_mk_eq_bot S
    have h_linear := iterSum_card_ge_linear_of_k3 (h_k3 ((ZMod N) ⧸ H)) Cbar h0_bar hCbar_ge k hk h_bot
    have h_arith := arith_growth_le k Cbar.card hk hCbar_ge
    have h_Cbar_le : (k + 1) * Cbar.card ≤ 2 * (iterSum k Cbar).card := by
      omega
    have h_mul : (k + 1) * Cbar.card * Fintype.card H ≤ 2 * (iterSum k Cbar).card * Fintype.card H :=
      Nat.mul_le_mul_right (Fintype.card H) h_Cbar_le
    have h_left : (k + 1) * C.card ≤ (k + 1) * Cbar.card * Fintype.card H := by
      have := card_le_card_image_mul_subgroup_card H C
      calc (k + 1) * C.card
        _ ≤ (k + 1) * (Cbar.card * Fintype.card H) := Nat.mul_le_mul_left _ this
        _ = (k + 1) * Cbar.card * Fintype.card H := by rw [mul_assoc]
    have h_right : 2 * (iterSum k Cbar).card * Fintype.card H = 2 * S.card := by
      rw [← hSbar_eq]
      have h_card_S : S.card = Sbar.card * Fintype.card H :=
        card_eq_card_image_mul_subgroup_card_of_stab_le (le_refl H)
      rw [mul_assoc, ← h_card_S]
    omega

/-- CFP Lemma 2.3: Unconditional iterated sumset growth on arbitrary positive modulus
    (composite allowed, arbitrary finite cyclic / abelian group). -/
theorem iterSum_card_ge_of_zero_mem_of_generates
    (N : ℕ) [NeZero N]
    (C : Finset (ZMod N))
    (h0 : (0 : ZMod N) ∈ C)
    (hgen : AddSubgroup.closure (C : Set (ZMod N)) = ⊤)
    (k : ℕ) (hk : 1 ≤ k) :
    (iterSum k C).card = N ∨
      (k + 1) * C.card ≤ 2 * (iterSum k C).card :=
  iterSum_card_ge_of_zero_mem_of_generates_of_k3 aperiodic_sumset_bound N C h0 hgen k hk

end Erdos298
