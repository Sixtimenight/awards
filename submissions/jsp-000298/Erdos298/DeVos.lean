import Erdos298.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Pointwise
open Classical

namespace Erdos298

universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def stabFinset (S : Finset G) : Finset G :=
  (finsetAddStab S : Set G).toFinset

lemma zero_mem_stabFinset (S : Finset G) : (0 : G) ∈ stabFinset S := by
  simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, AddSubgroup.zero_mem]

lemma stabFinset_nonempty (S : Finset G) : (stabFinset S).Nonempty :=
  ⟨0, zero_mem_stabFinset S⟩

lemma subset_sumset_stabFinset (T S : Finset G) :
    T ⊆ sumset T (stabFinset S) := by
  intro x hx
  rw [mem_sumset_iff]
  exact ⟨x, hx, 0, zero_mem_stabFinset S, add_zero x⟩

lemma card_le_card_sumset_stabFinset (T S : Finset G) :
    T.card ≤ (sumset T (stabFinset S)).card :=
  Finset.card_le_card (subset_sumset_stabFinset T S)

noncomputable def cosetFinset (a : G) (H : AddSubgroup G) : Finset G :=
  Finset.image (fun h => a + h) (Finset.filter (fun h => h ∈ H) Finset.univ)

lemma mem_cosetFinset_iff (a : G) (H : AddSubgroup G) (x : G) :
    x ∈ cosetFinset a H ↔ x - a ∈ H := by
  simp only [cosetFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : a + h - a = h := add_sub_cancel_left a h
    rwa [this]
  · intro hx
    refine ⟨x - a, hx, ?_⟩
    abel

lemma self_mem_cosetFinset (a : G) (H : AddSubgroup G) :
    a ∈ cosetFinset a H := by
  rw [mem_cosetFinset_iff]
  simp only [sub_self, H.zero_mem]

lemma card_cosetFinset (a : G) (H : AddSubgroup G) :
    (cosetFinset a H).card = Fintype.card H := by
  have h_inj : Set.InjOn (fun h : G => a + h) (Finset.filter (fun h => h ∈ H) Finset.univ) := by
    intro x _ y _ heq
    dsimp at heq
    exact add_left_cancel heq
  rw [cosetFinset, Finset.card_image_of_injOn h_inj]
  exact (Fintype.card_subtype (fun h => h ∈ H)).symm

lemma cosetFinset_disjoint_of_sub_not_mem {a b : G} {H : AddSubgroup G} (h : a - b ∉ H) :
    Disjoint (cosetFinset a H) (cosetFinset b H) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [mem_cosetFinset_iff] at hxa hxb
  have : a - b = (x - b) - (x - a) := by abel
  rw [this] at h
  exact h (H.sub_mem hxb hxa)

lemma disjoint_cosetFinset_of_stab
    {C : Finset G} {H : AddSubgroup G} (hH : H ≤ finsetAddStab C)
    {x : G} (h_not : ¬ cosetFinset x H ⊆ C) :
    Disjoint (cosetFinset x H) C := by
  rcases Finset.not_subset.mp h_not with ⟨y, hy, hyC⟩
  rw [mem_cosetFinset_iff] at hy
  rw [Finset.disjoint_left]
  intro z hz hzC
  rw [mem_cosetFinset_iff] at hz
  have h_diff : y - z ∈ H := by
    have : y - z = (y - x) - (z - x) := by abel
    rw [this]
    exact H.sub_mem hy hz
  have h_stab : y - z ∈ finsetAddStab C := hH h_diff
  have h_eq : (y - z) +ᵥ C = C := h_stab
  have h_mem : (y - z) + z ∈ (y - z) +ᵥ C :=
    Finset.mem_vadd_finset.mpr ⟨z, hzC, rfl⟩
  rw [h_eq] at h_mem
  have : (y - z) + z = y := sub_add_cancel y z
  rw [this] at h_mem
  exact hyC h_mem

lemma sumset_subset_cosetFinset_add {a b : G} {H : AddSubgroup G}
    {A1 B1 : Finset G} (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H) :
    sumset A1 B1 ⊆ cosetFinset (a + b) H := by
  intro x hx
  rcases (mem_sumset_iff A1 B1 x).mp hx with ⟨u, hu, v, hv, rfl⟩
  rw [mem_cosetFinset_iff]
  have hu' := hA1 hu
  have hv' := hB1 hv
  rw [mem_cosetFinset_iff] at hu' hv'
  have : u + v - (a + b) = (u - a) + (v - b) := by abel
  rw [this]
  exact H.add_mem hu' hv'

lemma H1_le_H {a b : G} {H : AddSubgroup G} {A1 B1 : Finset G}
    (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H)
    (hne : (sumset A1 B1).Nonempty) :
    finsetAddStab (sumset A1 B1) ≤ H := by
  intro h hh
  rcases hne with ⟨x, hx⟩
  have hx_coset := sumset_subset_cosetFinset_add hA1 hB1 hx
  rw [mem_cosetFinset_iff] at hx_coset
  rw [mem_finsetAddStab_iff] at hh
  have h_mem : h + x ∈ h +ᵥ sumset A1 B1 := Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
  rw [hh] at h_mem
  have h_coset := sumset_subset_cosetFinset_add hA1 hB1 h_mem
  rw [mem_cosetFinset_iff] at h_coset
  have : h = (h + x - (a + b)) - (x - (a + b)) := by abel
  rw [this]
  exact H.sub_mem h_coset hx_coset

lemma H1_lt_H {a b : G} {H : AddSubgroup G} {A1 B1 A B : Finset G}
    (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H)
    (hne : (sumset A1 B1).Nonempty)
    (h_sub : sumset A1 B1 ⊆ sumset A B)
    (h_not : ¬ cosetFinset (a + b) H ⊆ sumset A B) :
    finsetAddStab (sumset A1 B1) < H := by
  have h_le := H1_le_H hA1 hB1 hne
  refine lt_of_le_of_ne h_le ?_
  intro heq
  apply h_not
  intro y hy
  rw [mem_cosetFinset_iff] at hy
  rcases hne with ⟨x, hx⟩
  have hx_coset := sumset_subset_cosetFinset_add hA1 hB1 hx
  rw [mem_cosetFinset_iff] at hx_coset
  have h_diff : y - x ∈ H := by
    have : y - x = (y - (a + b)) - (x - (a + b)) := by abel
    rw [this]
    exact H.sub_mem hy hx_coset
  have h_in_H1 : y - x ∈ finsetAddStab (sumset A1 B1) := by
    rw [heq]
    exact h_diff
  have h_eq : (y - x) +ᵥ sumset A1 B1 = sumset A1 B1 := h_in_H1
  have h_mem : (y - x) + x ∈ (y - x) +ᵥ sumset A1 B1 :=
    Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
  rw [h_eq] at h_mem
  have : (y - x) + x = y := sub_add_cancel y x
  rw [this] at h_mem
  exact h_sub h_mem

def is_convergent (A B C : Finset G) : Prop :=
  C ⊆ sumset A B ∧
  (A ∩ B).card + (sumset (A ∪ B) (stabFinset C)).card ≤
    C.card + (stabFinset C).card

lemma exists_min_convergent {A B : Finset G} {C0 : Finset G} (hC0 : is_convergent A B C0) :
    ∃ C : Finset G, is_convergent A B C ∧
      ∀ D : Finset G, is_convergent A B D → (stabFinset C).card ≤ (stabFinset D).card := by
  set convs := (Finset.powerset (sumset A B)).filter (fun C => is_convergent A B C)
  have h_mem : C0 ∈ convs := by
    simp only [convs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hC0.1, hC0⟩
  have h_ne : convs.Nonempty := ⟨C0, h_mem⟩
  rcases Finset.exists_min_image convs (fun C => (stabFinset C).card) h_ne with ⟨C, hC, hmin⟩
  simp only [convs, Finset.mem_filter, Finset.mem_powerset] at hC
  refine ⟨C, hC.2, ?_⟩
  intro D hD
  have hD_mem : D ∈ convs := by
    simp only [convs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD.1, hD⟩
  exact hmin D hD_mem

lemma aperiodic_of_min_convergent_bot {A B C : Finset G}
    (hC : is_convergent A B C) (h_bot : finsetAddStab C = ⊥) :
    A.card + B.card ≤ (sumset A B).card + 1 := by
  have h_stab_eq : stabFinset C = {0} := by
    ext x
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, mem_finsetAddStab_iff,
      Finset.mem_singleton]
    constructor
    · intro hx
      have : x ∈ finsetAddStab C := hx
      rw [h_bot] at this
      exact (AddSubgroup.mem_bot (G := G)).mp this
    · rintro rfl
      simp
  have h_stab_card : (stabFinset C).card = 1 := by
    rw [h_stab_eq, Finset.card_singleton]
  have h_sumset_eq : sumset (A ∪ B) (stabFinset C) = A ∪ B := by
    rw [h_stab_eq, sumset_zero_right]
  have h_conv := hC.2
  rw [h_sumset_eq, h_stab_card] at h_conv
  have h_union : (A ∩ B).card + (A ∪ B).card = A.card + B.card := by
    rw [add_comm]
    exact Finset.card_union_add_card_inter A B
  have h_C_le : C.card ≤ (sumset A B).card := Finset.card_le_card hC.1
  omega

lemma devos_arith_contradiction_le
    (H H1 H2 A1 B1 A2 B2 S T : ℕ)
    (h2_1 : H1 + A1 + B1 ≤ H)
    (h2_2 : H2 + A2 + B2 ≤ H)
    (h3_1 : S + T + A1 + B1 < H + H1)
    (h3_2 : S + T + A2 + B2 < H + H2)
    (h_coset_a : H ≤ S + A1 + B2)
    (h_coset_b : H ≤ T + A2 + B1) :
    False := by
  omega

lemma sub_mul_ge_of_pos
    (H A B H1 kH kA kB : ℕ)
    (hH : H = kH * H1)
    (hA : A = kA * H1)
    (hB : kB * H1 = B)
    (hpos : (A : ℤ) + (B : ℤ) < (H : ℤ))
    (hH1 : 1 ≤ H1) :
    A + B + H1 ≤ H := by
  have : (kA : ℤ) * H1 + (kB : ℤ) * H1 < (kH : ℤ) * H1 := by
    linarith
  have h_k : (kA : ℤ) + (kB : ℤ) < (kH : ℤ) := by
    have h_pos : 0 < (H1 : ℤ) := by omega
    nlinarith
  have h_le : (kA : ℤ) + (kB : ℤ) + 1 ≤ (kH : ℤ) := by omega
  have h_mul : ((kA : ℤ) + (kB : ℤ) + 1) * (H1 : ℤ) ≤ (kH : ℤ) * (H1 : ℤ) := by
    have : 0 ≤ (H1 : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h_le this
  have h_distrib : ((kA : ℤ) + (kB : ℤ) + 1) * (H1 : ℤ) = (kA : ℤ) * H1 + (kB : ℤ) * H1 + H1 := by
    ring
  rw [h_distrib] at h_mul
  omega

lemma eq3_arith
    (S T A_union_B A_inter_B A_union_B_H C H A_card B_card AB A1_B1 A1 B1 H1 : ℕ)
    (h_disj : S + T + A_union_B ≤ A_union_B_H)
    (h_conv : A_inter_B + A_union_B_H ≤ C + H)
    (h_union : A_union_B + A_inter_B = A_card + B_card)
    (h_not_conv_AB : AB + 1 < A_inter_B + A_union_B)
    (h_sub_AB : C + A1_B1 ≤ AB)
    (h_ih_A1B1 : A1 + B1 ≤ A1_B1 + H1) :
    S + T + A1 + B1 < H + H1 := by
  omega

lemma card_vadd_finset (x : G) (S : Finset G) : (x +ᵥ S).card = S.card :=
  Finset.card_vadd_finset x S

lemma sumset_vadd_right (A B : Finset G) (x : G) :
    sumset A (x +ᵥ B) = x +ᵥ (sumset A B) := by
  ext z
  simp only [mem_sumset_iff, Finset.mem_vadd_finset]
  constructor
  · rintro ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    exact (add_left_comm a x b).symm
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨a, ha, x + b, ⟨b, hb, rfl⟩, ?_⟩
    exact add_left_comm a x b

lemma finsetAddStab_vadd (x : G) (S : Finset G) :
    finsetAddStab (x +ᵥ S) = finsetAddStab S := by
  ext y
  simp only [mem_finsetAddStab_iff]
  constructor
  · intro hy
    have h1 : y +ᵥ (x +ᵥ S) = x +ᵥ (y +ᵥ S) := by
      rw [← add_vadd, add_comm y x, add_vadd]
    rw [h1] at hy
    have h2 : -x +ᵥ (x +ᵥ (y +ᵥ S)) = -x +ᵥ (x +ᵥ S) := by rw [hy]
    rw [neg_vadd_vadd, neg_vadd_vadd] at h2
    exact h2
  · intro hy
    have h1 : y +ᵥ (x +ᵥ S) = x +ᵥ (y +ᵥ S) := by
      rw [← add_vadd, add_comm y x, add_vadd]
    rw [h1, hy]

lemma finsetAddStab_sumset_right_sub (A B : Finset G) (_hA : A.Nonempty) :
    finsetAddStab B ≤ finsetAddStab (sumset A B) := by
  intro x hx
  simp only [mem_finsetAddStab_iff] at hx ⊢
  rw [← sumset_vadd_right, hx]

lemma exists_translate_inter_nonempty_and_psubset
    (A B : Finset G) (hA : 2 ≤ A.card) (hB : B.Nonempty)
    (h_bot : finsetAddStab (sumset A B) = ⊥) :
    ∃ x : G,
      (x +ᵥ B).card = B.card ∧
      (sumset A (x +ᵥ B)).card = (sumset A B).card ∧
      finsetAddStab (sumset A (x +ᵥ B)) = ⊥ ∧
      (A ∩ (x +ᵥ B)).Nonempty ∧
      (A ∩ (x +ᵥ B)).card < A.card := by
  rcases Finset.one_lt_card_iff.mp hA with ⟨a, a', ha, ha', h_ne⟩
  have h_diff_ne : a' - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h_ne)
  have h_diff_not_stab : a' - a ∉ finsetAddStab (sumset A B) := by
    rw [h_bot, AddSubgroup.mem_bot]
    exact h_diff_ne
  have h_diff_not_stab_B : a' - a ∉ finsetAddStab B := by
    intro h_in
    have h_sub := finsetAddStab_sumset_right_sub A B ⟨a, ha⟩
    exact h_diff_not_stab (h_sub h_in)
  have h_vadd_ne : (a' - a) +ᵥ B ≠ B := by
    rwa [mem_finsetAddStab_iff] at h_diff_not_stab_B
  have h_not_sub : ¬ ((a' - a) +ᵥ B ⊆ B) := by
    intro h_sub
    have : (a' - a) +ᵥ B = B :=
      Finset.eq_of_subset_of_card_le h_sub (by rw [card_vadd_finset])
    exact h_vadd_ne this
  rcases Finset.not_subset.mp h_not_sub with ⟨b_out, hb_out, hb_not_in⟩
  rcases Finset.mem_vadd_finset.mp hb_out with ⟨b, hb, rfl⟩
  set x := a - b
  refine ⟨x, card_vadd_finset x B, ?_, ?_, ?_, ?_⟩
  · rw [sumset_vadd_right, Finset.card_vadd_finset]
  · rw [sumset_vadd_right, finsetAddStab_vadd, h_bot]
  · refine ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩⟩
    simp only [Finset.mem_vadd_finset, x]
    refine ⟨b, hb, ?_⟩
    change (a - b) + b = a
    exact sub_add_cancel a b
  · have ha'_not : a' ∉ x +ᵥ B := by
      intro ha'_in
      rcases Finset.mem_vadd_finset.mp ha'_in with ⟨b0, hb0, heq⟩
      dsimp [x] at heq
      have : (a' - a) + b = b0 := by
        rw [← heq]
        abel
      apply hb_not_in
      change (a' - a) + b ∈ B
      rwa [this]
    have h_sub : A ∩ (x +ᵥ B) ⊆ A := Finset.inter_subset_left
    have h_ne_A : A ∩ (x +ᵥ B) ≠ A := by
      intro h_eq
      have : a' ∈ A ∩ (x +ᵥ B) := by rw [h_eq]; exact ha'
      exact ha'_not (Finset.mem_inter.mp this).2
    have h_psub : A ∩ (x +ᵥ B) ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, h_ne_A⟩
    exact Finset.card_lt_card h_psub



lemma exists_not_subset_coset_of_stab_eq_bot
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (h_bot : finsetAddStab (sumset A B) = ⊥)
    {H : AddSubgroup G} (hH : H ≠ ⊥) :
    ∃ a ∈ A, ∃ b ∈ B, ¬ cosetFinset (a + b) H ⊆ sumset A B := by
  by_contra! h_all
  have h_stab : H ≤ finsetAddStab (sumset A B) := by
    intro h hh
    rw [mem_finsetAddStab_iff]
    have h_sub : h +ᵥ sumset A B ⊆ sumset A B := by
      intro x hx
      rcases Finset.mem_vadd_finset.mp hx with ⟨y, hy, rfl⟩
      rcases (mem_sumset_iff A B y).mp hy with ⟨a, ha, b, hb, rfl⟩
      have h_mem_coset : (a + b) + h ∈ cosetFinset (a + b) H := by
        rw [mem_cosetFinset_iff]
        have : (a + b) + h - (a + b) = h := add_sub_cancel_left (a + b) h
        rwa [this]
      have h_in : (a + b) + h ∈ sumset A B := h_all a ha b hb h_mem_coset
      have : h +ᵥ (a + b) = (a + b) + h := by
        change h + (a + b) = (a + b) + h
        abel
      rwa [this]
    have h_card : (h +ᵥ sumset A B).card = (sumset A B).card := Finset.card_vadd_finset h _
    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_card])
  rw [h_bot] at h_stab
  exact hH (le_bot_iff.mp h_stab)

lemma vadd_finset_subset_vadd_finset {S T : Finset G} (h : S ⊆ T) (x : G) :
    x +ᵥ S ⊆ x +ᵥ T := by
  intro z hz
  rcases Finset.mem_vadd_finset.mp hz with ⟨s, hs, rfl⟩
  exact Finset.mem_vadd_finset.mpr ⟨s, h hs, rfl⟩

lemma cosetFinset_subset_of_mem_stab {C : Finset G} {H : AddSubgroup G}
    (hH : H ≤ finsetAddStab C) {c : G} (hc : c ∈ C) :
    cosetFinset c H ⊆ C := by
  intro x hx
  rw [mem_cosetFinset_iff] at hx
  have h_in_stab : x - c ∈ finsetAddStab C := hH hx
  have h_eq : (x - c) +ᵥ C = C := h_in_stab
  have h_mem : (x - c) + c ∈ (x - c) +ᵥ C := Finset.mem_vadd_finset.mpr ⟨c, hc, rfl⟩
  rw [h_eq] at h_mem
  have : (x - c) + c = x := sub_add_cancel x c
  rwa [this] at h_mem

lemma cosetFinset_eq_of_mem {a : G} {H : AddSubgroup G} {x : G} (hx : x ∈ cosetFinset a H) :
    cosetFinset x H = cosetFinset a H := by
  ext y
  rw [mem_cosetFinset_iff, mem_cosetFinset_iff]
  rw [mem_cosetFinset_iff] at hx
  constructor
  · intro hy
    have : y - a = (y - x) + (x - a) := by abel
    rw [this]
    exact H.add_mem hy hx
  · intro hy
    have : y - x = (y - a) - (x - a) := by abel
    rw [this]
    exact H.sub_mem hy hx

lemma vadd_cosetFinset (x : G) (a : G) (H : AddSubgroup G) :
    x +ᵥ cosetFinset a H = cosetFinset (x + a) H := by
  ext y
  simp only [Finset.mem_vadd_finset, mem_cosetFinset_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x + z - (x + a) ∈ H
    have : x + z - (x + a) = z - a := by abel
    rwa [this]
  · intro hy
    refine ⟨y - x, ?_, ?_⟩
    · have : (y - x) - a = y - (x + a) := by abel
      rwa [this]
    · change x + (y - x) = y
      abel

lemma c1_stab_le {A B C : Finset G} {H : AddSubgroup G} (hH : H = finsetAddStab C)
    {a b : G} {A1 B1 : Finset G}
    (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H)
    (h_sub_AB : sumset A1 B1 ⊆ sumset A B)
    (h_not : ¬ cosetFinset (a + b) H ⊆ sumset A B)
    (hC_sub : C ⊆ sumset A B) :
    finsetAddStab (C ∪ sumset A1 B1) ≤ finsetAddStab (sumset A1 B1) := by
  set X := sumset A1 B1
  have hX_coset : X ⊆ cosetFinset (a + b) H := sumset_subset_cosetFinset_add hA1 hB1
  have h_not_C : ¬ cosetFinset (a + b) H ⊆ C := by
    intro h_sub
    exact h_not (h_sub.trans hC_sub)
  have h_disj : Disjoint (cosetFinset (a + b) H) C :=
    disjoint_cosetFinset_of_stab (by rw [hH]) h_not_C
  have h_disj_X : Disjoint C X := (h_disj.mono_left hX_coset).symm
  intro x hx
  rw [mem_finsetAddStab_iff] at hx ⊢
  have hx_in_H : x ∈ H := by
    by_contra hx_not_H
    have hx_not_stab : x ∉ finsetAddStab C := by
      intro h_in
      apply hx_not_H
      rwa [hH]
    have h_ne : x +ᵥ C ≠ C := by
      intro h_eq
      exact hx_not_stab (mem_finsetAddStab_iff C x |>.mpr h_eq)
    have h_inter : ((x +ᵥ C) ∩ X).Nonempty := by
      by_contra h_empty
      have h_empty' : (x +ᵥ C) ∩ X = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
      have h_sub_C : x +ᵥ C ⊆ C := by
        intro y hy
        have hy_union : y ∈ x +ᵥ (C ∪ X) := by
          rw [Finset.vadd_finset_union]
          exact Finset.mem_union_left _ hy
        rw [hx] at hy_union
        rcases Finset.mem_union.mp hy_union with hyC | hyX
        · exact hyC
        · exfalso
          have : y ∈ (x +ᵥ C) ∩ X := Finset.mem_inter.mpr ⟨hy, hyX⟩
          rw [h_empty'] at this
          simp at this
      have h_card_eq : (x +ᵥ C).card = C.card := Finset.card_vadd_finset x C
      exact h_ne (Finset.eq_of_subset_of_card_le h_sub_C (by rw [h_card_eq]))
    rcases h_inter with ⟨z, hz_inter⟩
    rcases Finset.mem_inter.mp hz_inter with ⟨hz_vadd, hz_X⟩
    rcases Finset.mem_vadd_finset.mp hz_vadd with ⟨c, hc_C, rfl⟩
    have hc_coset_C : cosetFinset c H ⊆ C :=
      cosetFinset_subset_of_mem_stab (by rw [hH]) hc_C
    have h_vadd_coset : x +ᵥ cosetFinset c H ⊆ C ∪ X := by
      calc x +ᵥ cosetFinset c H
        _ ⊆ x +ᵥ C := vadd_finset_subset_vadd_finset hc_coset_C x
        _ ⊆ x +ᵥ (C ∪ X) := vadd_finset_subset_vadd_finset (Finset.subset_union_left) x
        _ = C ∪ X := hx
    have h_coset_eq : cosetFinset (x + c) H = cosetFinset (a + b) H :=
      cosetFinset_eq_of_mem (hX_coset hz_X)
    rw [vadd_cosetFinset] at h_vadd_coset
    rw [h_coset_eq] at h_vadd_coset
    have h_sub_X : cosetFinset (a + b) H ⊆ X := by
      intro y hy
      have hy_union := h_vadd_coset hy
      rcases Finset.mem_union.mp hy_union with hyC | hyX
      · exfalso
        exact Finset.disjoint_left.mp h_disj hy hyC
      · exact hyX
    exact h_not (h_sub_X.trans h_sub_AB)
  have h_x_stab_C : x +ᵥ C = C := by
    have : x ∈ finsetAddStab C := by rwa [← hH]
    exact mem_finsetAddStab_iff C x |>.mp this
  have h_vadd_union : C ∪ (x +ᵥ X) = C ∪ X := by
    calc C ∪ (x +ᵥ X)
      _ = (x +ᵥ C) ∪ (x +ᵥ X) := by rw [h_x_stab_C]
      _ = x +ᵥ (C ∪ X) := (Finset.vadd_finset_union).symm
      _ = C ∪ X := hx
  have h_disj_vadd : Disjoint C (x +ᵥ X) := by
    rw [Finset.disjoint_right]
    intro y hy
    rcases Finset.mem_vadd_finset.mp hy with ⟨u, hu, rfl⟩
    have hu_coset := hX_coset hu
    rw [mem_cosetFinset_iff] at hu_coset
    have : x + u - (a + b) = x + (u - (a + b)) := by abel
    have h_in_H : (x + u) - (a + b) ∈ H := by
      rw [this]
      exact H.add_mem hx_in_H hu_coset
    have h_in_coset : x + u ∈ cosetFinset (a + b) H := by
      rwa [mem_cosetFinset_iff]
    intro hyC
    exact Finset.disjoint_left.mp h_disj h_in_coset hyC
  ext y
  constructor
  · intro hy
    have : y ∈ C ∪ (x +ᵥ X) := Finset.mem_union_right C hy
    rw [h_vadd_union] at this
    rcases Finset.mem_union.mp this with hyC | hyX
    · exfalso; exact Finset.disjoint_right.mp h_disj_vadd hy hyC
    · exact hyX
  · intro hy
    have : y ∈ C ∪ X := Finset.mem_union_right C hy
    rw [← h_vadd_union] at this
    rcases Finset.mem_union.mp this with hyC | hyX
    · exfalso; exact Finset.disjoint_right.mp h_disj_X hy hyC
    · exact hyX

lemma card_stabFinset_lt_of_lt {S1 S2 : Finset G}
    (h : finsetAddStab S1 < finsetAddStab S2) :
    (stabFinset S1).card < (stabFinset S2).card := by
  have h_ssub : (finsetAddStab S1 : Set G).toFinset ⊂ (finsetAddStab S2 : Set G).toFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro x hx
      simp only [Set.mem_toFinset] at hx ⊢
      exact h.1 hx
    · intro heq
      apply h.2
      intro x hx
      have h1 : x ∈ (finsetAddStab S2 : Set G).toFinset := by
        rw [Set.mem_toFinset]
        exact hx
      rw [← heq] at h1
      exact Set.mem_toFinset.mp h1
  exact Finset.card_lt_card h_ssub

lemma card_stabFinset_le_of_le {S1 S2 : Finset G}
    (h : finsetAddStab S1 ≤ finsetAddStab S2) :
    (stabFinset S1).card ≤ (stabFinset S2).card := by
  have h_sub : (finsetAddStab S1 : Set G).toFinset ⊆ (finsetAddStab S2 : Set G).toFinset := by
    intro x hx
    simp only [Set.mem_toFinset] at hx ⊢
    exact h hx
  exact Finset.card_le_card h_sub

lemma card_stabFinset_lt_of_le_of_lt {S1 S2 S3 : Finset G}
    (h1 : finsetAddStab S1 ≤ finsetAddStab S2)
    (h2 : finsetAddStab S2 < finsetAddStab S3) :
    (stabFinset S1).card < (stabFinset S3).card :=
  (card_stabFinset_le_of_le h1).trans_lt (card_stabFinset_lt_of_lt h2)

lemma c1_not_convergent {A B C : Finset G} {H : AddSubgroup G} (hH : H = finsetAddStab C)
    {a b : G} {A1 B1 : Finset G}
    (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H)
    (hne : (sumset A1 B1).Nonempty)
    (h_sub_AB : sumset A1 B1 ⊆ sumset A B)
    (h_not : ¬ cosetFinset (a + b) H ⊆ sumset A B)
    (hC_sub : C ⊆ sumset A B)
    (h_min : ∀ D : Finset G, is_convergent A B D → (stabFinset C).card ≤ (stabFinset D).card) :
    ¬ is_convergent A B (C ∪ sumset A1 B1) := by
  intro h_conv
  have h_le := h_min (C ∪ sumset A1 B1) h_conv
  have h_c1_stab := c1_stab_le hH hA1 hB1 h_sub_AB h_not hC_sub
  have h_lt := H1_lt_H hA1 hB1 hne h_sub_AB h_not
  rw [hH] at h_lt
  have h_card_lt := card_stabFinset_lt_of_le_of_lt h_c1_stab h_lt
  omega

lemma sumset_inter_union_subset (A B : Finset G) :
    sumset (A ∩ B) (A ∪ B) ⊆ sumset A B := by
  intro x hx
  rcases (mem_sumset_iff (A ∩ B) (A ∪ B) x).mp hx with ⟨u, hu, v, hv, rfl⟩
  rw [Finset.mem_inter] at hu
  rw [Finset.mem_union] at hv
  rw [mem_sumset_iff]
  rcases hv with hvA | hvB
  · exact ⟨v, hvA, u, hu.2, add_comm v u⟩
  · exact ⟨u, hu.1, v, hvB, rfl⟩

lemma image_mk_stabFinset (K : AddSubgroup G) (hK_ne : (stabFinset (sumset A B)).Nonempty)
    (hK : K = finsetAddStab (sumset A B)) :
    (stabFinset (sumset A B)).image (QuotientAddGroup.mk' K) = {0} := by
  ext y
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hx
    rw [hK]
    exact (QuotientAddGroup.eq_zero_iff (x := x)).mpr hx
  · rintro rfl
    rcases hK_ne with ⟨x, hx⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hx
    refine ⟨0, ?_, map_zero _⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, AddSubgroup.zero_mem]

lemma kneser_of_aperiodic_bound
    (h_aperiodic : ∀ (G' : Type u) [AddCommGroup G'] [Fintype G'] [DecidableEq G']
      (X Y : Finset G'), X.Nonempty → Y.Nonempty → finsetAddStab (sumset X Y) = ⊥ →
      X.card + Y.card ≤ (sumset X Y).card + 1)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (sumset A (stabFinset (sumset A B))).card + (sumset B (stabFinset (sumset A B))).card ≤
      (sumset A B).card + (stabFinset (sumset A B)).card := by
  set K := finsetAddStab (sumset A B)
  by_cases hK : K = ⊥
  · have h_stab_eq : stabFinset (sumset A B) = {0} := by
      ext x
      simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, mem_finsetAddStab_iff,
        Finset.mem_singleton]
      constructor
      · intro hx
        have : x ∈ K := hx
        rw [hK] at this
        exact (AddSubgroup.mem_bot (G := G)).mp this
      · rintro rfl
        simp
    rw [h_stab_eq, sumset_zero_right, sumset_zero_right, Finset.card_singleton]
    exact h_aperiodic G A B hA hB hK
  · -- K ≠ ⊥, quotient reduction
    set π := QuotientAddGroup.mk' K
    set Abar := A.image π
    set Bbar := B.image π
    have hAbar_ne : Abar.Nonempty := hA.image π
    have hBbar_ne : Bbar.Nonempty := hB.image π
    have h_sumset_bar : sumset Abar Bbar = (sumset A B).image π := (image_mk_sumset K A B).symm
    have h_bot_bar : finsetAddStab (sumset Abar Bbar) = ⊥ := by
      rw [h_sumset_bar]
      exact finsetAddStab_image_mk_eq_bot (sumset A B)
    have h_ap := h_aperiodic (G ⧸ K) Abar Bbar hAbar_ne hBbar_ne h_bot_bar
    have h_mul := Nat.mul_le_mul_right (Fintype.card K) h_ap
    have h_sumset_card : (sumset A B).card = (sumset Abar Bbar).card * Fintype.card K := by
      rw [h_sumset_bar]
      exact card_eq_card_image_mul_subgroup_card_of_stab_le (le_refl K)
    have h_stab_card : (stabFinset (sumset A B)).card = Fintype.card K := by
      simp [stabFinset, K]
    have h_im_stab : (stabFinset (sumset A B)).image π = {0} :=
      image_mk_stabFinset K (stabFinset_nonempty (sumset A B)) rfl
    have hA_im : (sumset A (stabFinset (sumset A B))).image π = Abar := by
      rw [image_mk_sumset, h_im_stab, sumset_zero_right]
    have hA_le : (sumset A (stabFinset (sumset A B))).card ≤ Abar.card * Fintype.card K := by
      have := card_le_card_image_mul_subgroup_card K (sumset A (stabFinset (sumset A B)))
      rwa [hA_im] at this
    have hB_im : (sumset B (stabFinset (sumset A B))).image π = Bbar := by
      rw [image_mk_sumset, h_im_stab, sumset_zero_right]
    have hB_le : (sumset B (stabFinset (sumset A B))).card ≤ Bbar.card * Fintype.card K := by
      have := card_le_card_image_mul_subgroup_card K (sumset B (stabFinset (sumset A B)))
      rwa [hB_im] at this
    have h_distrib : (Abar.card + Bbar.card) * Fintype.card K =
        Abar.card * Fintype.card K + Bbar.card * Fintype.card K := add_mul Abar.card Bbar.card (Fintype.card K)
    have h_distrib_rhs : ((sumset Abar Bbar).card + 1) * Fintype.card K =
        (sumset Abar Bbar).card * Fintype.card K + Fintype.card K := by
      rw [add_mul, one_mul]
    omega



def kneser_bound_le (n : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G), A.Nonempty → B.Nonempty →
    (sumset A B).card + A.card ≤ n →
    (sumset A (stabFinset (sumset A B))).card + (sumset B (stabFinset (sumset A B))).card ≤
      (sumset A B).card + (stabFinset (sumset A B)).card

lemma aperiodic_of_kneser_bound {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (_hA : A.Nonempty) (_hB : B.Nonempty)
    (h_bot : finsetAddStab (sumset A B) = ⊥)
    (h_kb : (sumset A (stabFinset (sumset A B))).card + (sumset B (stabFinset (sumset A B))).card ≤
      (sumset A B).card + (stabFinset (sumset A B)).card) :
    A.card + B.card ≤ (sumset A B).card + 1 := by
  have h_stab_eq : stabFinset (sumset A B) = {0} := by
    ext x
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, mem_finsetAddStab_iff,
      Finset.mem_singleton]
    constructor
    · intro hx
      have : x ∈ finsetAddStab (sumset A B) := hx
      rw [h_bot] at this
      exact (AddSubgroup.mem_bot (G := G)).mp this
    · rintro rfl
      simp
  have h_stab_card : (stabFinset (sumset A B)).card = 1 := by
    rw [h_stab_eq, Finset.card_singleton]
  have hA_sum : sumset A (stabFinset (sumset A B)) = A := by
    rw [h_stab_eq, sumset_zero_right]
  have hB_sum : sumset B (stabFinset (sumset A B)) = B := by
    rw [h_stab_eq, sumset_zero_right]
  rw [hA_sum, hB_sum, h_stab_card] at h_kb
  exact h_kb

lemma kneser_quotient_step {n : ℕ} (ih : ∀ m < n, kneser_bound_le m)
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hn : (sumset A B).card + A.card ≤ n)
    (hK_ne : finsetAddStab (sumset A B) ≠ ⊥) :
    (sumset A (stabFinset (sumset A B))).card + (sumset B (stabFinset (sumset A B))).card ≤
      (sumset A B).card + (stabFinset (sumset A B)).card := by
  set K := finsetAddStab (sumset A B)
  set π := QuotientAddGroup.mk' K
  set Abar := A.image π
  set Bbar := B.image π
  have hAbar_ne : Abar.Nonempty := hA.image π
  have hBbar_ne : Bbar.Nonempty := hB.image π
  have h_sumset_bar : sumset Abar Bbar = (sumset A B).image π := (image_mk_sumset K A B).symm
  have h_bot_bar : finsetAddStab (sumset Abar Bbar) = ⊥ := by
    rw [h_sumset_bar]
    exact finsetAddStab_image_mk_eq_bot (sumset A B)
  have h_card_K_ge : 2 ≤ Fintype.card K := by
    obtain ⟨x, hx, hx_ne⟩ : ∃ x ∈ K, x ≠ 0 := by
      by_contra! h_all
      apply hK_ne
      ext y
      simp only [AddSubgroup.mem_bot]
      constructor
      · intro hy
        exact h_all y hy
      · rintro rfl
        exact K.zero_mem
    have h_0_ne : (⟨0, K.zero_mem⟩ : K) ≠ ⟨x, hx⟩ := by
      intro h
      have : (0 : G) = x := congrArg Subtype.val h
      exact hx_ne this.symm
    exact Fintype.one_lt_card_iff.mpr ⟨⟨0, K.zero_mem⟩, ⟨x, hx⟩, h_0_ne⟩
  have h_sumset_card : (sumset A B).card = (sumset Abar Bbar).card * Fintype.card K := by
    rw [h_sumset_bar]
    exact card_eq_card_image_mul_subgroup_card_of_stab_le (le_refl K)
  have h_Abar_le : Abar.card ≤ A.card := Finset.card_image_le
  have h_meas_lt : (sumset Abar Bbar).card + Abar.card < (sumset A B).card + A.card := by
    have h1 : (sumset Abar Bbar).card < (sumset A B).card := by
      rw [h_sumset_card]
      have : 0 < (sumset Abar Bbar).card := by
        rcases hAbar_ne with ⟨x, hx⟩
        rcases hBbar_ne with ⟨y, hy⟩
        exact Finset.card_pos.mpr ⟨x + y, (mem_sumset_iff Abar Bbar (x + y)).mpr ⟨x, hx, y, hy, rfl⟩⟩
      nlinarith
    omega
  have h_meas_le : (sumset Abar Bbar).card + Abar.card ≤ (sumset Abar Bbar).card + Abar.card := le_rfl
  have h_ih := ih ((sumset Abar Bbar).card + Abar.card) (h_meas_lt.trans_le hn)
    (G ⧸ K) Abar Bbar hAbar_ne hBbar_ne h_meas_le
  have h_ap := aperiodic_of_kneser_bound Abar Bbar hAbar_ne hBbar_ne h_bot_bar h_ih
  have h_mul := Nat.mul_le_mul_right (Fintype.card K) h_ap
  have h_stab_card : (stabFinset (sumset A B)).card = Fintype.card K := by
    simp [stabFinset, K]
  have h_im_stab : (stabFinset (sumset A B)).image π = {0} :=
    image_mk_stabFinset K (stabFinset_nonempty (sumset A B)) rfl
  have hA_im : (sumset A (stabFinset (sumset A B))).image π = Abar := by
    rw [image_mk_sumset, h_im_stab, sumset_zero_right]
  have hA_le : (sumset A (stabFinset (sumset A B))).card ≤ Abar.card * Fintype.card K := by
    have := card_le_card_image_mul_subgroup_card K (sumset A (stabFinset (sumset A B)))
    rwa [hA_im] at this
  have hB_im : (sumset B (stabFinset (sumset A B))).image π = Bbar := by
    rw [image_mk_sumset, h_im_stab, sumset_zero_right]
  have hB_le : (sumset B (stabFinset (sumset A B))).card ≤ Bbar.card * Fintype.card K := by
    have := card_le_card_image_mul_subgroup_card K (sumset B (stabFinset (sumset A B)))
    rwa [hB_im] at this
  have h_distrib : (Abar.card + Bbar.card) * Fintype.card K =
      Abar.card * Fintype.card K + Bbar.card * Fintype.card K := add_mul Abar.card Bbar.card (Fintype.card K)
  have h_distrib_rhs : ((sumset Abar Bbar).card + 1) * Fintype.card K =
      (sumset Abar Bbar).card * Fintype.card K + Fintype.card K := by
    rw [add_mul, one_mul]
  omega

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma c1_stab_eq {A B C : Finset G} {H : AddSubgroup G} (hH : H = finsetAddStab C)
    {a b : G} {A1 B1 : Finset G}
    (hA1 : A1 ⊆ cosetFinset a H) (hB1 : B1 ⊆ cosetFinset b H)
    (hne : (sumset A1 B1).Nonempty)
    (h_sub_AB : sumset A1 B1 ⊆ sumset A B)
    (h_not : ¬ cosetFinset (a + b) H ⊆ sumset A B)
    (hC_sub : C ⊆ sumset A B) :
    finsetAddStab (C ∪ sumset A1 B1) = finsetAddStab (sumset A1 B1) := by
  apply le_antisymm
  · exact c1_stab_le hH hA1 hB1 h_sub_AB h_not hC_sub
  · intro x hx
    rw [mem_finsetAddStab_iff] at hx ⊢
    have hxH : x ∈ H := H1_le_H hA1 hB1 hne hx
    have hxC : x +ᵥ C = C := by
      rw [hH] at hxH
      exact hxH
    rw [Finset.vadd_finset_union, hxC, hx]


lemma c0_is_convergent {n : ℕ} (ih : ∀ m < n, kneser_bound_le m)
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (_hB : B.Nonempty)
    (_h_bot : finsetAddStab (sumset A B) = ⊥)
    (hn : (sumset A B).card + A.card ≤ n)
    (h_inter_ne : (A ∩ B).Nonempty)
    (h_inter_lt : (A ∩ B).card < A.card) :
    is_convergent A B (sumset (A ∩ B) (A ∪ B)) := by
  set A0 := A ∩ B
  set B0 := A ∪ B
  have hA0_ne : A0.Nonempty := h_inter_ne
  have hB0_ne : B0.Nonempty := hA.mono Finset.subset_union_left
  set C0 := sumset A0 B0
  have hC0_sub : C0 ⊆ sumset A B := sumset_inter_union_subset A B
  have hC0_card : C0.card ≤ (sumset A B).card := Finset.card_le_card hC0_sub
  have h_meas_lt : C0.card + A0.card < (sumset A B).card + A.card := by
    omega
  have h_meas_le : C0.card + A0.card ≤ C0.card + A0.card := le_rfl
  have h_ih := ih (C0.card + A0.card) (h_meas_lt.trans_le hn) G A0 B0 hA0_ne hB0_ne h_meas_le
  have hA0_sub : A0 ⊆ sumset A0 (stabFinset C0) := subset_sumset_stabFinset A0 C0
  have hA0_le : A0.card ≤ (sumset A0 (stabFinset C0)).card := Finset.card_le_card hA0_sub
  refine ⟨hC0_sub, ?_⟩
  dsimp [A0, B0, C0] at h_ih hA0_le ⊢
  omega

lemma disjoint_of_subset_coset {a b : G} {H : AddSubgroup G} (h : a - b ∉ H)
    {S T : Finset G} (hS : S ⊆ cosetFinset a H) (hT : T ⊆ cosetFinset b H) :
    Disjoint S T :=
  (cosetFinset_disjoint_of_sub_not_mem h).mono hS hT

lemma coset_subset_sumset_stab {a : G} {H : AddSubgroup G} {X : Finset G}
    (ha : a ∈ X) (hH : H ≤ finsetAddStab X) :
    cosetFinset a H ⊆ sumset X (stabFinset X) := by
  intro x hx
  rw [mem_cosetFinset_iff] at hx
  rw [mem_sumset_iff]
  refine ⟨a, ha, x - a, ?_, by abel⟩
  simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]
  exact hH hx

lemma coset_subset_sumset_stab_C {a : G} {H : AddSubgroup G} {X C : Finset G}
    (ha : a ∈ X) (hH : H = finsetAddStab C) :
    cosetFinset a H ⊆ sumset X (stabFinset C) := by
  intro x hx
  rw [mem_cosetFinset_iff] at hx
  rw [mem_sumset_iff]
  refine ⟨a, ha, x - a, ?_, by abel⟩
  simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]
  rw [← hH]
  exact hx


lemma s_t_union_card_le {a b : G} {H : AddSubgroup G} {A B C : Finset G}
    (ha : a ∈ A) (hb : b ∈ B) (hH : H = finsetAddStab C) (hab : a - b ∉ H)
    (S T : Finset G)
    (hS : S = cosetFinset a H \ (A ∪ B))
    (hT : T = cosetFinset b H \ (A ∪ B)) :
    S.card + T.card + (A ∪ B).card ≤ (sumset (A ∪ B) (stabFinset C)).card := by
  have hS_sub : S ⊆ cosetFinset a H := by rw [hS]; exact Finset.sdiff_subset
  have hT_sub : T ⊆ cosetFinset b H := by rw [hT]; exact Finset.sdiff_subset
  have hST_disj : Disjoint S T := disjoint_of_subset_coset hab hS_sub hT_sub
  have hS_disj_AB : Disjoint S (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [hS, Finset.mem_sdiff] at hx
    exact hx.2 hy
  have hT_disj_AB : Disjoint T (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [hT, Finset.mem_sdiff] at hx
    exact hx.2 hy
  have hST_union_disj : Disjoint (S ∪ T) (A ∪ B) :=
    Finset.disjoint_union_left.mpr ⟨hS_disj_AB, hT_disj_AB⟩
  have h_union_card : (S ∪ T ∪ (A ∪ B)).card = S.card + T.card + (A ∪ B).card := by
    rw [Finset.card_union_of_disjoint hST_union_disj, Finset.card_union_of_disjoint hST_disj]
  have hS_sum : S ⊆ sumset (A ∪ B) (stabFinset C) :=
    hS_sub.trans (coset_subset_sumset_stab_C (Finset.mem_union_left B ha) hH)
  have hT_sum : T ⊆ sumset (A ∪ B) (stabFinset C) :=
    hT_sub.trans (coset_subset_sumset_stab_C (Finset.mem_union_right A hb) hH)
  have hAB_sum : A ∪ B ⊆ sumset (A ∪ B) (stabFinset C) :=
    subset_sumset_stabFinset (A ∪ B) C
  have h_all_sub : S ∪ T ∪ (A ∪ B) ⊆ sumset (A ∪ B) (stabFinset C) := by
    rw [Finset.union_subset_iff, Finset.union_subset_iff]
    exact ⟨⟨hS_sum, hT_sum⟩, hAB_sum⟩
  rw [← h_union_card]
  exact Finset.card_le_card h_all_sub

lemma coset_card_le_s_a1_b2 {a : G} {H : AddSubgroup G} {A B S A1 B2 : Finset G}
    (hS : S = cosetFinset a H \ (A ∪ B))
    (hA1 : A1 = A ∩ cosetFinset a H)
    (hB2 : B2 = B ∩ cosetFinset a H) :
    (cosetFinset a H).card ≤ S.card + A1.card + B2.card := by
  have h_sub : cosetFinset a H ⊆ S ∪ A1 ∪ B2 := by
    intro x hx
    by_cases hAB : x ∈ A ∪ B
    · rcases Finset.mem_union.mp hAB with hxA | hxB
      · have : x ∈ A1 := by rw [hA1]; exact Finset.mem_inter.mpr ⟨hxA, hx⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ this)
      · have : x ∈ B2 := by rw [hB2]; exact Finset.mem_inter.mpr ⟨hxB, hx⟩
        exact Finset.mem_union_right _ this
    · have : x ∈ S := by rw [hS]; exact Finset.mem_sdiff.mpr ⟨hx, hAB⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ this)
  have h_card := Finset.card_le_card h_sub
  have h1 := Finset.card_union_le (S ∪ A1) B2
  have h2 := Finset.card_union_le S A1
  omega

lemma eq1_arith_le
    (A_inter_B A_union_B_H C H C1 H1 A_union_B_H1 A1_B1 A1 B1 : ℕ)
    (h_conv : A_inter_B + A_union_B_H ≤ C + H)
    (h_not_conv : C1 + H1 < A_inter_B + A_union_B_H1)
    (hC1 : C1 = C + A1_B1)
    (h_ih : A1 + B1 ≤ A1_B1 + H1) :
    A_union_B_H + A1 + B1 < A_union_B_H1 + H := by
  omega

lemma sumset_singleton_left (a : G) (B : Finset G) : sumset {a} B = a +ᵥ B := by
  ext x
  simp only [mem_sumset_iff, Finset.mem_singleton, Finset.mem_vadd_finset]
  constructor
  · rintro ⟨a', rfl, b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a, rfl, b, hb, rfl⟩







lemma b2_empty_subset {a : G} {H : AddSubgroup G} {A B' C : Finset G}
    (ha : a ∈ A) (hH : H = finsetAddStab C)
    {A1 : Finset G} (hA1 : A1 = A ∩ cosetFinset a H)
    (hB2 : B' ∩ cosetFinset a H = ∅)
    {H1_fin : Finset G} {H1 : AddSubgroup G} (hH1 : H1 ≤ H)
    (hH1_eq : H1_fin = (H1 : Set G).toFinset) :
    cosetFinset a H \ sumset A1 H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin := by
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  constructor
  · rw [mem_cosetFinset_iff] at hx
    rw [mem_sumset_iff]
    refine ⟨a, Finset.mem_union_left B' ha, x - a, ?_, by abel⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]
    rw [← hH]
    exact hx.1
  · intro h_in
    rw [mem_sumset_iff] at h_in
    rcases h_in with ⟨u, hu, h1, hh1, rfl⟩
    simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe] at hh1
    have hh1_H : h1 ∈ H := hH1 hh1
    have hu_coset : u ∈ cosetFinset a H := by
      rw [mem_cosetFinset_iff]
      have : u - a = (u + h1 - a) - h1 := by abel
      rw [this]
      have h_x_coset : u + h1 ∈ cosetFinset a H := hx.1
      rw [mem_cosetFinset_iff] at h_x_coset
      exact H.sub_mem h_x_coset hh1_H
    rcases Finset.mem_union.mp hu with huA | huB
    · have huA1 : u ∈ A1 := by
        rw [hA1]
        exact Finset.mem_inter.mpr ⟨huA, hu_coset⟩
      have : u + h1 ∈ sumset A1 H1_fin := by
        rw [mem_sumset_iff]
        refine ⟨u, huA1, h1, ?_, rfl⟩
        simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe, hh1]
      exact hx.2 this
    · have : u ∈ B' ∩ cosetFinset a H := Finset.mem_inter.mpr ⟨huB, hu_coset⟩
      rw [hB2] at this
      simp at this


lemma a2_empty_subset {b : G} {H : AddSubgroup G} {A B' C : Finset G}
    (hb : b ∈ B') (hH : H = finsetAddStab C)
    {B1 : Finset G} (hB1 : B1 = B' ∩ cosetFinset b H)
    (hA2 : A ∩ cosetFinset b H = ∅)
    {H1_fin : Finset G} {H1 : AddSubgroup G} (hH1 : H1 ≤ H)
    (hH1_eq : H1_fin = (H1 : Set G).toFinset) :
    cosetFinset b H \ sumset B1 H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin := by
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  constructor
  · rw [mem_cosetFinset_iff] at hx
    rw [mem_sumset_iff]
    refine ⟨b, Finset.mem_union_right A hb, x - b, ?_, by abel⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]
    rw [← hH]
    exact hx.1
  · intro h_in
    rw [mem_sumset_iff] at h_in
    rcases h_in with ⟨u, hu, h1, hh1, rfl⟩
    simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe] at hh1
    have hh1_H : h1 ∈ H := hH1 hh1
    have hu_coset : u ∈ cosetFinset b H := by
      rw [mem_cosetFinset_iff]
      have : u - b = (u + h1 - b) - h1 := by abel
      rw [this]
      have h_x_coset : u + h1 ∈ cosetFinset b H := hx.1
      rw [mem_cosetFinset_iff] at h_x_coset
      exact H.sub_mem h_x_coset hh1_H
    rcases Finset.mem_union.mp hu with huA | huB
    · have : u ∈ A ∩ cosetFinset b H := Finset.mem_inter.mpr ⟨huA, hu_coset⟩
      rw [hA2] at this
      simp at this
    · have huB1 : u ∈ B1 := by
        rw [hB1]
        exact Finset.mem_inter.mpr ⟨huB, hu_coset⟩
      have : u + h1 ∈ sumset B1 H1_fin := by
        rw [mem_sumset_iff]
        refine ⟨u, huB1, h1, ?_, rfl⟩
        simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe, hh1]
      exact hx.2 this

lemma ab_mem_H_subset {a : G} {H : AddSubgroup G} {A B' C : Finset G}
    (ha : a ∈ A) (hH : H = finsetAddStab C)
    {A1 B1 : Finset G} (hA1 : A1 = A ∩ cosetFinset a H) (hB1 : B1 = B' ∩ cosetFinset a H)
    {H1_fin : Finset G} {H1 : AddSubgroup G} (hH1 : H1 ≤ H)
    (hH1_eq : H1_fin = (H1 : Set G).toFinset) :
    cosetFinset a H \ sumset (A1 ∪ B1) H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin := by
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  constructor
  · rw [mem_cosetFinset_iff] at hx
    rw [mem_sumset_iff]
    refine ⟨a, Finset.mem_union_left B' ha, x - a, ?_, by abel⟩
    simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]
    rw [← hH]
    exact hx.1
  · intro h_in
    rw [mem_sumset_iff] at h_in
    rcases h_in with ⟨u, hu, h1, hh1, rfl⟩
    simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe] at hh1
    have hh1_H : h1 ∈ H := hH1 hh1
    have hu_coset : u ∈ cosetFinset a H := by
      rw [mem_cosetFinset_iff]
      have : u - a = (u + h1 - a) - h1 := by abel
      rw [this]
      have h_x_coset : u + h1 ∈ cosetFinset a H := hx.1
      rw [mem_cosetFinset_iff] at h_x_coset
      exact H.sub_mem h_x_coset hh1_H
    have hu_union : u ∈ A1 ∪ B1 := by
      rcases Finset.mem_union.mp hu with huA | huB
      · exact Finset.mem_union_left _ (by rw [hA1]; exact Finset.mem_inter.mpr ⟨huA, hu_coset⟩)
      · exact Finset.mem_union_right _ (by rw [hB1]; exact Finset.mem_inter.mpr ⟨huB, hu_coset⟩)
    have : u + h1 ∈ sumset (A1 ∪ B1) H1_fin := by
      rw [mem_sumset_iff]
      refine ⟨u, hu_union, h1, ?_, rfl⟩
      simp only [hH1_eq, Set.mem_toFinset, SetLike.mem_coe, hh1]
    exact hx.2 this

lemma eq1_direct_arith
    (L H A1_H1 B1_H1 : ℕ)
    (h_eq1 : L + A1_H1 + B1_H1 < H)
    (h_sub : H ≤ L + A1_H1)
    (hB1 : 1 ≤ B1_H1) :
    False := by
  omega

lemma coset_sdiff_card_eq {a : G} {H : AddSubgroup G} {X : Finset G}
    (hX : X ⊆ cosetFinset a H) :
    (cosetFinset a H \ X).card = (cosetFinset a H).card - X.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hX]



lemma b2_empty_contra {a : G} {H : AddSubgroup G} {A B' C A1 B1 H1_fin : Finset G}
    (h_sub : cosetFinset a H \ sumset A1 H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin)
    (hA1_sub : sumset A1 H1_fin ⊆ cosetFinset a H)
    (hH1_sub : sumset (A ∪ B') H1_fin ⊆ sumset (A ∪ B') (stabFinset C))
    (h_coset_card : (cosetFinset a H).card = (stabFinset C).card)
    (hB1_pos : 1 ≤ (sumset B1 H1_fin).card)
    (h_eq1 : (sumset (A ∪ B') (stabFinset C)).card + (sumset A1 H1_fin).card + (sumset B1 H1_fin).card <
      (sumset (A ∪ B') H1_fin).card + (stabFinset C).card) :
    False := by
  have h_card := Finset.card_le_card h_sub
  have h_lhs : (cosetFinset a H \ sumset A1 H1_fin).card =
      (cosetFinset a H).card - (sumset A1 H1_fin).card :=
    coset_sdiff_card_eq hA1_sub
  have h_rhs : (sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin).card =
      (sumset (A ∪ B') (stabFinset C)).card - (sumset (A ∪ B') H1_fin).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hH1_sub]
  rw [h_lhs, h_rhs, h_coset_card] at h_card
  have h1 : (sumset A1 H1_fin).card ≤ (cosetFinset a H).card := Finset.card_le_card hA1_sub
  have h2 : (sumset (A ∪ B') H1_fin).card ≤ (sumset (A ∪ B') (stabFinset C)).card := Finset.card_le_card hH1_sub
  omega

lemma a2_empty_contra {b : G} {H : AddSubgroup G} {A B' C A1 B1 H1_fin : Finset G}
    (h_sub : cosetFinset b H \ sumset B1 H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin)
    (hB1_sub : sumset B1 H1_fin ⊆ cosetFinset b H)
    (hH1_sub : sumset (A ∪ B') H1_fin ⊆ sumset (A ∪ B') (stabFinset C))
    (h_coset_card : (cosetFinset b H).card = (stabFinset C).card)
    (hA1_pos : 1 ≤ (sumset A1 H1_fin).card)
    (h_eq1 : (sumset (A ∪ B') (stabFinset C)).card + (sumset A1 H1_fin).card + (sumset B1 H1_fin).card <
      (sumset (A ∪ B') H1_fin).card + (stabFinset C).card) :
    False := by
  have h_card := Finset.card_le_card h_sub
  have h_lhs : (cosetFinset b H \ sumset B1 H1_fin).card =
      (cosetFinset b H).card - (sumset B1 H1_fin).card :=
    coset_sdiff_card_eq hB1_sub
  have h_rhs : (sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin).card =
      (sumset (A ∪ B') (stabFinset C)).card - (sumset (A ∪ B') H1_fin).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hH1_sub]
  rw [h_lhs, h_rhs, h_coset_card] at h_card
  have h1 : (sumset B1 H1_fin).card ≤ (cosetFinset b H).card := Finset.card_le_card hB1_sub
  have h2 : (sumset (A ∪ B') H1_fin).card ≤ (sumset (A ∪ B') (stabFinset C)).card := Finset.card_le_card hH1_sub
  omega

lemma ab_mem_H_contra {a : G} {H : AddSubgroup G} {A B' C A1 B1 H1_fin : Finset G}
    (h_sub : cosetFinset a H \ sumset (A1 ∪ B1) H1_fin ⊆
      sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin)
    (hAB1_sub : sumset (A1 ∪ B1) H1_fin ⊆ cosetFinset a H)
    (hH1_sub : sumset (A ∪ B') H1_fin ⊆ sumset (A ∪ B') (stabFinset C))
    (h_coset_card : (cosetFinset a H).card = (stabFinset C).card)
    (h_sum_union : (sumset (A1 ∪ B1) H1_fin).card ≤ (sumset A1 H1_fin).card + (sumset B1 H1_fin).card)
    (h_eq1 : (sumset (A ∪ B') (stabFinset C)).card + (sumset A1 H1_fin).card + (sumset B1 H1_fin).card <
      (sumset (A ∪ B') H1_fin).card + (stabFinset C).card) :
    False := by
  have h_card := Finset.card_le_card h_sub
  have h_lhs : (cosetFinset a H \ sumset (A1 ∪ B1) H1_fin).card =
      (cosetFinset a H).card - (sumset (A1 ∪ B1) H1_fin).card :=
    coset_sdiff_card_eq hAB1_sub
  have h_rhs : (sumset (A ∪ B') (stabFinset C) \ sumset (A ∪ B') H1_fin).card =
      (sumset (A ∪ B') (stabFinset C)).card - (sumset (A ∪ B') H1_fin).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hH1_sub]
  rw [h_lhs, h_rhs, h_coset_card] at h_card
  have h1 : (sumset (A1 ∪ B1) H1_fin).card ≤ (cosetFinset a H).card := Finset.card_le_card hAB1_sub
  have h2 : (sumset (A ∪ B') H1_fin).card ≤ (sumset (A ∪ B') (stabFinset C)).card := Finset.card_le_card hH1_sub
  omega

lemma a1b1_meas_lt {A B' C A1 B1 : Finset G}
    (hC_ne : C.Nonempty)
    (hC_sub : C ⊆ sumset A B')
    (hA1B1_sub : sumset A1 B1 ⊆ sumset A B')
    (h_disj : Disjoint C (sumset A1 B1))
    (hA1_sub : A1 ⊆ A) :
    (sumset A1 B1).card + A1.card < (sumset A B').card + A.card := by
  have h_union : (C ∪ sumset A1 B1).card = C.card + (sumset A1 B1).card :=
    Finset.card_union_of_disjoint h_disj
  have h_sub : C ∪ sumset A1 B1 ⊆ sumset A B' :=
    Finset.union_subset hC_sub hA1B1_sub
  have h_le : C.card + (sumset A1 B1).card ≤ (sumset A B').card := by
    rw [← h_union]
    exact Finset.card_le_card h_sub
  have hC_pos : 1 ≤ C.card := Finset.Nonempty.card_pos hC_ne
  have hA1_le : A1.card ≤ A.card := Finset.card_le_card hA1_sub
  omega

lemma c_nonempty_of_convergent {A B' C : Finset G}
    (h_inter_ne : (A ∩ B').Nonempty)
    (hC : is_convergent A B' C) :
    C.Nonempty := by
  by_contra h_empty
  have hC_empty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
  have hC_card : C.card = 0 := by rw [hC_empty, Finset.card_empty]
  have h_conv := hC.2
  rw [hC_card, zero_add] at h_conv
  have h_inter_pos : 1 ≤ (A ∩ B').card := Finset.Nonempty.card_pos h_inter_ne

  have h_stab_le : (stabFinset C).card ≤ (sumset (A ∪ B') (stabFinset C)).card := by
    rcases h_inter_ne with ⟨x, hx⟩
    have hx_union : x ∈ A ∪ B' := Finset.mem_union_left B' (Finset.mem_inter.mp hx).1
    have h_inj : Set.InjOn (fun h => x + h) (stabFinset C) := by
      intro u _ v _ heq
      exact add_left_cancel heq
    have h_im_sub : (stabFinset C).image (fun h => x + h) ⊆ sumset (A ∪ B') (stabFinset C) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨h, hh, rfl⟩
      rw [mem_sumset_iff]
      exact ⟨x, hx_union, h, hh, rfl⟩
    have h_im_card : ((stabFinset C).image (fun h => x + h)).card = (stabFinset C).card :=
      Finset.card_image_of_injOn h_inj
    rw [← h_im_card]
    exact Finset.card_le_card h_im_sub
  omega
lemma sumset_nonempty {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) : (sumset A B).Nonempty := by
  rcases hA with ⟨x, hx⟩
  rcases hB with ⟨y, hy⟩
  exact ⟨x + y, (mem_sumset_iff A B (x + y)).mpr ⟨x, hx, y, hy, rfl⟩⟩


lemma card_stabFinset_eq_card (S : Finset G) :
    (stabFinset S).card = Fintype.card (finsetAddStab S) := by
  have : stabFinset S = Finset.filter (fun h => h ∈ finsetAddStab S) Finset.univ := by
    ext x
    simp [stabFinset]
  rw [this]
  exact (Fintype.card_subtype (fun h => h ∈ finsetAddStab S)).symm

lemma stabFinset_eq_zero_of_bot (S : Finset G) (h : finsetAddStab S = ⊥) :
    stabFinset S = {0} := by
  ext y
  simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, Finset.mem_singleton]
  constructor
  · intro hy; rw [h] at hy; exact (AddSubgroup.mem_bot (G := G)).mp hy
  · rintro rfl; exact (finsetAddStab S).zero_mem

lemma stab_le_finsetAddStab_sumset_stabFinset (A S : Finset G) :
    finsetAddStab S ≤ finsetAddStab (sumset A (stabFinset S)) := by
  intro h hh
  rw [mem_finsetAddStab_iff]
  ext x
  simp only [Finset.mem_vadd_finset, mem_sumset_iff, stabFinset, Set.mem_toFinset, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, h', hh', rfl⟩, rfl⟩
    refine ⟨a, ha, h + h', (finsetAddStab S).add_mem hh hh', ?_⟩
    simp only [vadd_eq_add]
    abel
  · rintro ⟨a, ha, h', hh', rfl⟩
    refine ⟨a + (h' - h), ⟨a, ha, h' - h, (finsetAddStab S).sub_mem hh' hh, rfl⟩, ?_⟩
    simp only [vadd_eq_add]
    abel

lemma sub_le_finsetAddStab_stabFinset {H K : AddSubgroup G} (h : K ≤ H) (C : Finset G) (hH : H = finsetAddStab C) :
    K ≤ finsetAddStab (stabFinset C) := by
  intro k hk
  rw [mem_finsetAddStab_iff]
  ext x
  simp only [Finset.mem_vadd_finset, stabFinset, Set.mem_toFinset, SetLike.mem_coe, ← hH]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [vadd_eq_add]
    exact H.add_mem (h hk) hy
  · intro hx
    refine ⟨x - k, H.sub_mem hx (h hk), ?_⟩
    simp only [vadd_eq_add]
    abel

lemma eq2_arith
    (U_H U_H1 H H1 A B A_H1 B_H1 kH kA kB : ℕ)
    (h_sub : U_H1 ≤ U_H)
    (h_eq1 : U_H + A_H1 + B_H1 < U_H1 + H)
    (hH : H = kH * H1)
    (hA_H1 : A_H1 = kA * H1)
    (hB_H1 : kB * H1 = B_H1)
    (hH1 : 1 ≤ H1)
    (hA : A ≤ A_H1)
    (hB : B ≤ B_H1) :
    H1 + A + B ≤ H := by
  have h_int : (A_H1 : ℤ) + (B_H1 : ℤ) < (H : ℤ) := by omega
  have h_sum := sub_mul_ge_of_pos H A_H1 B_H1 H1 kH kA kB hH hA_H1 hB_H1 h_int hH1
  omega


lemma devos_contra {n : ℕ} (ih : ∀ m < n, kneser_bound_le m)
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B' C : Finset G) (hA : A.Nonempty) (hB' : B'.Nonempty)
    (h_inter_ne : (A ∩ B').Nonempty)
    (hn' : (sumset A B').card + A.card ≤ n)
    (h_bot : finsetAddStab (sumset A B') = ⊥)
    (hC_conv : is_convergent A B' C)
    (hC_min : ∀ D, is_convergent A B' D → (stabFinset C).card ≤ (stabFinset D).card)
    (hH_ne : finsetAddStab C ≠ ⊥) : False := by
  set H := finsetAddStab C
  have hC_ne : C.Nonempty := c_nonempty_of_convergent h_inter_ne hC_conv
  rcases exists_not_subset_coset_of_stab_eq_bot hA hB' h_bot hH_ne with ⟨a, ha, b, hb, h_not_coset⟩
  set A1 := A ∩ cosetFinset a H
  set B1 := B' ∩ cosetFinset b H
  set A2 := A ∩ cosetFinset b H
  set B2 := B' ∩ cosetFinset a H
  set S := cosetFinset a H \ (A ∪ B')
  set T := cosetFinset b H \ (A ∪ B')
  have ha_coset : a ∈ cosetFinset a H := self_mem_cosetFinset a H
  have hb_coset : b ∈ cosetFinset b H := self_mem_cosetFinset b H
  have hA1_ne : A1.Nonempty := ⟨a, Finset.mem_inter.mpr ⟨ha, ha_coset⟩⟩
  have hB1_ne : B1.Nonempty := ⟨b, Finset.mem_inter.mpr ⟨hb, hb_coset⟩⟩
  have hA1B1_ne : (sumset A1 B1).Nonempty := sumset_nonempty hA1_ne hB1_ne
  have hA1_sub_coset : A1 ⊆ cosetFinset a H := Finset.inter_subset_right
  have hB1_sub_coset : B1 ⊆ cosetFinset b H := Finset.inter_subset_right
  have hA1_sub_A : A1 ⊆ A := Finset.inter_subset_left
  have hB1_sub_B' : B1 ⊆ B' := Finset.inter_subset_left
  have hA1B1_sub_AB' : sumset A1 B1 ⊆ sumset A B' := sumset_subset_sumset hA1_sub_A hB1_sub_B'
  set H1 := finsetAddStab (sumset A1 B1)
  set H1_fin := stabFinset (sumset A1 B1)
  have hH1_le : H1 ≤ H := H1_le_H hA1_sub_coset hB1_sub_coset hA1B1_ne
  have hH1_lt : H1 < H := H1_lt_H hA1_sub_coset hB1_sub_coset hA1B1_ne hA1B1_sub_AB' h_not_coset
  have hH1_stab_eq : finsetAddStab (C ∪ sumset A1 B1) = H1 :=
    c1_stab_eq rfl hA1_sub_coset hB1_sub_coset hA1B1_ne hA1B1_sub_AB' h_not_coset hC_conv.1
  have hC1_not_conv := c1_not_convergent rfl hA1_sub_coset hB1_sub_coset hA1B1_ne hA1B1_sub_AB' h_not_coset hC_conv.1 hC_min
  have hX_coset : sumset A1 B1 ⊆ cosetFinset (a + b) H := sumset_subset_cosetFinset_add hA1_sub_coset hB1_sub_coset
  have h_not_C : ¬ cosetFinset (a + b) H ⊆ C := fun h_sub => h_not_coset (h_sub.trans hC_conv.1)
  have h_disj_coset : Disjoint (cosetFinset (a + b) H) C := disjoint_cosetFinset_of_stab (le_refl H) h_not_C
  have h_disj_C_A1B1 : Disjoint C (sumset A1 B1) := (h_disj_coset.mono_left hX_coset).symm
  have h_meas1 : (sumset A1 B1).card + A1.card < (sumset A B').card + A.card :=
    a1b1_meas_lt hC_ne hC_conv.1 hA1B1_sub_AB' h_disj_C_A1B1 hA1_sub_A
  have h_ih1 := ih ((sumset A1 B1).card + A1.card) (h_meas1.trans_le hn') G A1 B1 hA1_ne hB1_ne le_rfl
  have hA1_H1_sub : sumset A1 H1_fin ⊆ cosetFinset a H := by
    intro x hx
    rcases (mem_sumset_iff A1 H1_fin x).mp hx with ⟨u, hu, h1, hh1, rfl⟩
    have hu_coset := hA1_sub_coset hu
    rw [mem_cosetFinset_iff] at hu_coset ⊢
    simp only [H1_fin, stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hh1
    have hh1_H : h1 ∈ H := hH1_le hh1
    have : u + h1 - a = (u - a) + h1 := by abel
    rw [this]
    exact H.add_mem hu_coset hh1_H
  have hB1_H1_sub : sumset B1 H1_fin ⊆ cosetFinset b H := by
    intro x hx
    rcases (mem_sumset_iff B1 H1_fin x).mp hx with ⟨u, hu, h1, hh1, rfl⟩
    have hu_coset := hB1_sub_coset hu
    rw [mem_cosetFinset_iff] at hu_coset ⊢
    simp only [H1_fin, stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hh1
    have hh1_H : h1 ∈ H := hH1_le hh1
    have : u + h1 - b = (u - b) + h1 := by abel
    rw [this]
    exact H.add_mem hu_coset hh1_H
  have hH1_sub_H : sumset (A ∪ B') H1_fin ⊆ sumset (A ∪ B') (stabFinset C) := by
    intro x hx
    rcases (mem_sumset_iff (A ∪ B') H1_fin x).mp hx with ⟨u, hu, h1, hh1, rfl⟩
    simp only [H1_fin, stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hh1
    rw [mem_sumset_iff]
    exact ⟨u, hu, h1, by simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]; exact hH1_le hh1, rfl⟩
  have h_coset_a_card : (cosetFinset a H).card = (stabFinset C).card := by
    rw [card_cosetFinset, card_stabFinset_eq_card]
  have h_coset_b_card : (cosetFinset b H).card = (stabFinset C).card := by
    rw [card_cosetFinset, card_stabFinset_eq_card]
  have hB1_pos : 1 ≤ (sumset B1 H1_fin).card := by
    rcases hB1_ne with ⟨u, hu⟩
    exact Finset.card_pos.mpr ⟨u, subset_sumset_stabFinset B1 (sumset A1 B1) hu⟩
  have hA1_pos : 1 ≤ (sumset A1 H1_fin).card := by
    rcases hA1_ne with ⟨u, hu⟩
    exact Finset.card_pos.mpr ⟨u, subset_sumset_stabFinset A1 (sumset A1 B1) hu⟩
  have hC1_sub : C ∪ sumset A1 B1 ⊆ sumset A B' := Finset.union_subset hC_conv.1 hA1B1_sub_AB'
  have hC1_card_lt : (C ∪ sumset A1 B1).card + (stabFinset (C ∪ sumset A1 B1)).card <
      (A ∩ B').card + (sumset (A ∪ B') (stabFinset (C ∪ sumset A1 B1))).card := by
    by_contra! h_le
    exact hC1_not_conv ⟨hC1_sub, h_le⟩
  have h_C1_card : (C ∪ sumset A1 B1).card = C.card + (sumset A1 B1).card :=
    Finset.card_union_of_disjoint h_disj_C_A1B1
  have h_eq1 : (sumset (A ∪ B') (stabFinset C)).card + (sumset A1 H1_fin).card + (sumset B1 H1_fin).card <
      (sumset (A ∪ B') H1_fin).card + (stabFinset C).card := by
    have h_c_conv := hC_conv.2
    have h_stab_eq_fin : stabFinset (C ∪ sumset A1 B1) = H1_fin := by
      dsimp [stabFinset, H1_fin]
      rw [hH1_stab_eq]
    have h_ih1_le : (sumset A1 H1_fin).card + (sumset B1 H1_fin).card ≤ (sumset A1 B1).card + H1_fin.card := h_ih1
    rw [h_C1_card, h_stab_eq_fin] at hC1_card_lt
    omega
  have hB2_ne : B2.Nonempty := by
    by_contra h_empty
    have hB2_eq_empty : B' ∩ cosetFinset a H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
    have h_sub := b2_empty_subset ha rfl rfl hB2_eq_empty hH1_le rfl
    exact b2_empty_contra h_sub hA1_H1_sub hH1_sub_H h_coset_a_card hB1_pos h_eq1
  have hA2_ne : A2.Nonempty := by
    by_contra h_empty
    have hA2_eq_empty : A ∩ cosetFinset b H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
    have h_sub := a2_empty_subset hb rfl rfl hA2_eq_empty hH1_le rfl
    exact a2_empty_contra h_sub hB1_H1_sub hH1_sub_H h_coset_b_card hA1_pos h_eq1
  have hab : a - b ∉ H := by
    intro hab_in
    have h_coset_eq : cosetFinset b H = cosetFinset a H := by
      have : b ∈ cosetFinset a H := by
        rw [mem_cosetFinset_iff]
        have : b - a = -(a - b) := by abel
        rw [this]
        exact H.neg_mem hab_in
      exact cosetFinset_eq_of_mem this
    have hB1_eq : B1 = B' ∩ cosetFinset a H := by
      dsimp [B1]
      rw [h_coset_eq]
    have h_sub := ab_mem_H_subset ha rfl rfl hB1_eq hH1_le rfl
    have hAB1_sub : sumset (A1 ∪ B1) H1_fin ⊆ cosetFinset a H := by
      intro x hx
      rcases (mem_sumset_iff (A1 ∪ B1) H1_fin x).mp hx with ⟨u, hu, h1, hh1, rfl⟩
      rcases Finset.mem_union.mp hu with huA | huB
      · exact hA1_H1_sub ((mem_sumset_iff A1 H1_fin (u + h1)).mpr ⟨u, huA, h1, hh1, rfl⟩)
      · rw [hB1_eq] at huB
        have hu_coset : u - a ∈ H := by
          have := (Finset.mem_inter.mp huB).2
          rwa [mem_cosetFinset_iff] at this
        simp only [H1_fin, stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hh1
        have hh1_H : h1 ∈ H := hH1_le hh1
        rw [mem_cosetFinset_iff]
        have : u + h1 - a = (u - a) + h1 := by abel
        rw [this]
        exact H.add_mem hu_coset hh1_H
    have h_sum_union : (sumset (A1 ∪ B1) H1_fin).card ≤ (sumset A1 H1_fin).card + (sumset B1 H1_fin).card := by
      have : sumset (A1 ∪ B1) H1_fin = sumset A1 H1_fin ∪ sumset B1 H1_fin := by
        ext z
        simp only [mem_sumset_iff, Finset.mem_union]
        constructor
        · rintro ⟨u, hu, h1, hh1, rfl⟩
          rcases hu with huA | huB
          · exact Or.inl ⟨u, huA, h1, hh1, rfl⟩
          · exact Or.inr ⟨u, huB, h1, hh1, rfl⟩
        · rintro (⟨u, hu, h1, hh1, rfl⟩ | ⟨u, hu, h1, hh1, rfl⟩)
          · exact ⟨u, Or.inl hu, h1, hh1, rfl⟩
          · exact ⟨u, Or.inr hu, h1, hh1, rfl⟩
      rw [this]
      exact Finset.card_union_le _ _
    exact ab_mem_H_contra h_sub hAB1_sub hH1_sub_H h_coset_a_card h_sum_union h_eq1
  have hA2_sub_coset : A2 ⊆ cosetFinset b H := Finset.inter_subset_right
  have hB2_sub_coset : B2 ⊆ cosetFinset a H := Finset.inter_subset_right
  have hA2_sub_A : A2 ⊆ A := Finset.inter_subset_left
  have hB2_sub_B' : B2 ⊆ B' := Finset.inter_subset_left
  have hA2B2_sub_AB' : sumset A2 B2 ⊆ sumset A B' := sumset_subset_sumset hA2_sub_A hB2_sub_B'
  have hA2B2_ne : (sumset A2 B2).Nonempty := sumset_nonempty hA2_ne hB2_ne
  set H2 := finsetAddStab (sumset A2 B2)
  set H2_fin := stabFinset (sumset A2 B2)
  have hH2_le : H2 ≤ H := H1_le_H hA2_sub_coset hB2_sub_coset hA2B2_ne
  have h_meas2 : (sumset A2 B2).card + A2.card < (sumset A B').card + A.card := by
    have hX2_coset : sumset A2 B2 ⊆ cosetFinset (a + b) H := by
      intro x hx
      rcases (mem_sumset_iff A2 B2 x).mp hx with ⟨u, hu, v, hv, rfl⟩
      have hu' := hA2_sub_coset hu
      have hv' := hB2_sub_coset hv
      rw [mem_cosetFinset_iff] at hu' hv' ⊢
      have : u + v - (a + b) = (u - b) + (v - a) := by abel
      rw [this]
      exact H.add_mem hu' hv'
    have h_disj_coset2 : Disjoint (cosetFinset (a + b) H) C := h_disj_coset
    have h_disj_C_A2B2 : Disjoint C (sumset A2 B2) := (h_disj_coset2.mono_left hX2_coset).symm
    exact a1b1_meas_lt hC_ne hC_conv.1 hA2B2_sub_AB' h_disj_C_A2B2 hA2_sub_A
  have h_ih2 := ih ((sumset A2 B2).card + A2.card) (h_meas2.trans_le hn') G A2 B2 hA2_ne hB2_ne le_rfl
  have h_disj_ST := s_t_union_card_le ha hb rfl hab S T rfl rfl
  have h_not_conv_AB' : (sumset A B').card + 1 < (A ∩ B').card + (A ∪ B').card := by
    by_contra! h_le
    have h_stab_eq := stabFinset_eq_zero_of_bot (sumset A B') h_bot
    have h_kb : (sumset A (stabFinset (sumset A B'))).card + (sumset B' (stabFinset (sumset A B'))).card ≤
        (sumset A B').card + (stabFinset (sumset A B')).card := by
      rw [h_stab_eq, sumset_zero_right, sumset_zero_right, Finset.card_singleton]
      have : (A ∩ B').card + (A ∪ B').card = A.card + B'.card := by
        rw [add_comm]
        exact Finset.card_union_add_card_inter A B'
      omega
    have h_min_conv : is_convergent A B' (sumset A B') := by
      refine ⟨le_rfl, ?_⟩
      rw [h_stab_eq, sumset_zero_right, Finset.card_singleton]
      omega
    have h_min_card := hC_min (sumset A B') h_min_conv
    have h_card_bot : (stabFinset (sumset A B')).card = 1 := by
      rw [h_stab_eq, Finset.card_singleton]
    have h_H_card_ge : 2 ≤ (stabFinset C).card := by
      rw [card_stabFinset_eq_card]
      obtain ⟨x, hx, hx_ne⟩ : ∃ x ∈ H, x ≠ 0 := by
        by_contra! h_all
        apply hH_ne
        ext y
        simp only [AddSubgroup.mem_bot]
        constructor
        · intro hy; exact h_all y hy
        · rintro rfl; exact H.zero_mem
      have h_0_ne : (⟨0, H.zero_mem⟩ : H) ≠ ⟨x, hx⟩ := by
        intro h
        have : (0 : G) = x := congrArg Subtype.val h
        exact hx_ne this.symm
      exact Fintype.one_lt_card_iff.mpr ⟨⟨0, H.zero_mem⟩, ⟨x, hx⟩, h_0_ne⟩
    omega
  have h_union_eq : (A ∪ B').card + (A ∩ B').card = A.card + B'.card :=
    Finset.card_union_add_card_inter A B'
  have h_sub_AB1 : C.card + (sumset A1 B1).card ≤ (sumset A B').card := by
    have := Finset.card_le_card (Finset.union_subset hC_conv.1 hA1B1_sub_AB')
    rwa [h_C1_card] at this
  have h_sub_AB2 : C.card + (sumset A2 B2).card ≤ (sumset A B').card := by
    have h_disj2 : Disjoint C (sumset A2 B2) := by
      have hX2_coset : sumset A2 B2 ⊆ cosetFinset (a + b) H := by
        intro x hx
        rcases (mem_sumset_iff A2 B2 x).mp hx with ⟨u, hu, v, hv, rfl⟩
        have hu' := hA2_sub_coset hu
        have hv' := hB2_sub_coset hv
        rw [mem_cosetFinset_iff] at hu' hv' ⊢
        have : u + v - (a + b) = (u - b) + (v - a) := by abel
        rw [this]
        exact H.add_mem hu' hv'
      exact (h_disj_coset.mono_left hX2_coset).symm
    have := Finset.card_le_card (Finset.union_subset hC_conv.1 hA2B2_sub_AB')
    rw [Finset.card_union_of_disjoint h_disj2] at this
    exact this
  have hA1_B1_le : A1.card + B1.card ≤ (sumset A1 B1).card + H1_fin.card := by
    have hA1_le : A1.card ≤ (sumset A1 H1_fin).card := Finset.card_le_card (subset_sumset_stabFinset A1 (sumset A1 B1))
    have hB1_le : B1.card ≤ (sumset B1 H1_fin).card := Finset.card_le_card (subset_sumset_stabFinset B1 (sumset A1 B1))
    have h_ih1_le : (sumset A1 H1_fin).card + (sumset B1 H1_fin).card ≤ (sumset A1 B1).card + H1_fin.card := h_ih1
    omega
  have hA2_B2_le : A2.card + B2.card ≤ (sumset A2 B2).card + H2_fin.card := by
    have hA2_le : A2.card ≤ (sumset A2 H2_fin).card := Finset.card_le_card (subset_sumset_stabFinset A2 (sumset A2 B2))
    have hB2_le : B2.card ≤ (sumset B2 H2_fin).card := Finset.card_le_card (subset_sumset_stabFinset B2 (sumset A2 B2))
    have h_ih2_le : (sumset A2 H2_fin).card + (sumset B2 H2_fin).card ≤ (sumset A2 B2).card + H2_fin.card := h_ih2
    omega
  have h3_1 : S.card + T.card + A1.card + B1.card < (stabFinset C).card + H1_fin.card :=
    eq3_arith S.card T.card (A ∪ B').card (A ∩ B').card (sumset (A ∪ B') (stabFinset C)).card
      C.card (stabFinset C).card A.card B'.card (sumset A B').card (sumset A1 B1).card
      A1.card B1.card H1_fin.card h_disj_ST hC_conv.2 h_union_eq h_not_conv_AB' h_sub_AB1 hA1_B1_le
  have h3_2 : S.card + T.card + A2.card + B2.card < (stabFinset C).card + H2_fin.card :=
    eq3_arith S.card T.card (A ∪ B').card (A ∩ B').card (sumset (A ∪ B') (stabFinset C)).card
      C.card (stabFinset C).card A.card B'.card (sumset A B').card (sumset A2 B2).card
      A2.card B2.card H2_fin.card h_disj_ST hC_conv.2 h_union_eq h_not_conv_AB' h_sub_AB2 hA2_B2_le
  have h_coset_a := coset_card_le_s_a1_b2 (a := a) (H := H) (A := A) (B := B') (S := S) (A1 := A1) (B2 := B2) rfl rfl rfl
  have h_coset_b : (cosetFinset b H).card ≤ T.card + A2.card + B1.card :=
    coset_card_le_s_a1_b2 (a := b) (H := H) (A := A) (B := B') (S := T) (A1 := A2) (B2 := B1) rfl rfl rfl
  rw [h_coset_a_card] at h_coset_a
  rw [h_coset_b_card] at h_coset_b
  have hA1_stab : H1 ≤ finsetAddStab (sumset A1 H1_fin) := stab_le_finsetAddStab_sumset_stabFinset A1 (sumset A1 B1)
  have hB1_stab : H1 ≤ finsetAddStab (sumset B1 H1_fin) := stab_le_finsetAddStab_sumset_stabFinset B1 (sumset A1 B1)
  have hC_stab1 : H1 ≤ finsetAddStab (stabFinset C) := sub_le_finsetAddStab_stabFinset hH1_le C rfl
  have h_A1_mul := card_eq_card_image_mul_subgroup_card_of_stab_le hA1_stab
  have h_B1_mul := card_eq_card_image_mul_subgroup_card_of_stab_le hB1_stab
  have h_C_mul1 := card_eq_card_image_mul_subgroup_card_of_stab_le hC_stab1
  have h_H1_card : Fintype.card H1 = H1_fin.card := (card_stabFinset_eq_card (sumset A1 B1)).symm
  rw [h_H1_card] at h_A1_mul h_B1_mul h_C_mul1
  have h_H1_pos : 1 ≤ H1_fin.card := Finset.Nonempty.card_pos (stabFinset_nonempty (sumset A1 B1))
  have hA1_le : A1.card ≤ (sumset A1 H1_fin).card := Finset.card_le_card (subset_sumset_stabFinset A1 (sumset A1 B1))
  have hB1_le : B1.card ≤ (sumset B1 H1_fin).card := Finset.card_le_card (subset_sumset_stabFinset B1 (sumset A1 B1))
  have h_sub_U1 : (sumset (A ∪ B') H1_fin).card ≤ (sumset (A ∪ B') (stabFinset C)).card := Finset.card_le_card hH1_sub_H
  have h2_1 : H1_fin.card + A1.card + B1.card ≤ (stabFinset C).card :=
    eq2_arith (sumset (A ∪ B') (stabFinset C)).card (sumset (A ∪ B') H1_fin).card
      (stabFinset C).card H1_fin.card A1.card B1.card (sumset A1 H1_fin).card (sumset B1 H1_fin).card
      ((stabFinset C).image (QuotientAddGroup.mk' H1)).card
      ((sumset A1 H1_fin).image (QuotientAddGroup.mk' H1)).card
      ((sumset B1 H1_fin).image (QuotientAddGroup.mk' H1)).card
      h_sub_U1 h_eq1 h_C_mul1 h_A1_mul h_B1_mul.symm h_H1_pos hA1_le hB1_le

  have hH2_lt : H2 < H := by
    have h_not2 : ¬ cosetFinset (b + a) H ⊆ sumset A B' := by
      rw [add_comm b a]
      exact h_not_coset
    exact H1_lt_H hA2_sub_coset hB2_sub_coset hA2B2_ne hA2B2_sub_AB' h_not2
  have hH2_stab_eq : finsetAddStab (C ∪ sumset A2 B2) = H2 := by
    have h_not2 : ¬ cosetFinset (b + a) H ⊆ sumset A B' := by
      rw [add_comm b a]
      exact h_not_coset
    exact c1_stab_eq rfl hA2_sub_coset hB2_sub_coset hA2B2_ne hA2B2_sub_AB' h_not2 hC_conv.1
  have hC2_not_conv := by
    have h_not2 : ¬ cosetFinset (b + a) H ⊆ sumset A B' := by
      rw [add_comm b a]
      exact h_not_coset
    exact c1_not_convergent rfl hA2_sub_coset hB2_sub_coset hA2B2_ne hA2B2_sub_AB' h_not2 hC_conv.1 hC_min
  have hC2_sub : C ∪ sumset A2 B2 ⊆ sumset A B' := Finset.union_subset hC_conv.1 hA2B2_sub_AB'
  have hC2_card_lt : (C ∪ sumset A2 B2).card + (stabFinset (C ∪ sumset A2 B2)).card <
      (A ∩ B').card + (sumset (A ∪ B') (stabFinset (C ∪ sumset A2 B2))).card := by
    by_contra! h_le
    exact hC2_not_conv ⟨hC2_sub, h_le⟩
  have h_disj_C_A2B2 : Disjoint C (sumset A2 B2) := by
    have hX2_coset : sumset A2 B2 ⊆ cosetFinset (a + b) H := by
      intro x hx
      rcases (mem_sumset_iff A2 B2 x).mp hx with ⟨u, hu, v, hv, rfl⟩
      have hu' := hA2_sub_coset hu
      have hv' := hB2_sub_coset hv
      rw [mem_cosetFinset_iff] at hu' hv' ⊢
      have : u + v - (a + b) = (u - b) + (v - a) := by abel
      rw [this]
      exact H.add_mem hu' hv'
    exact (h_disj_coset.mono_left hX2_coset).symm
  have h_C2_card : (C ∪ sumset A2 B2).card = C.card + (sumset A2 B2).card :=
    Finset.card_union_of_disjoint h_disj_C_A2B2
  have h_eq1_2 : (sumset (A ∪ B') (stabFinset C)).card + (sumset A2 H2_fin).card + (sumset B2 H2_fin).card <
      (sumset (A ∪ B') H2_fin).card + (stabFinset C).card := by
    have h_c_conv := hC_conv.2
    have h_stab_eq_fin : stabFinset (C ∪ sumset A2 B2) = H2_fin := by
      dsimp [stabFinset, H2_fin]
      rw [hH2_stab_eq]
    have h_ih2_le : (sumset A2 H2_fin).card + (sumset B2 H2_fin).card ≤ (sumset A2 B2).card + H2_fin.card := h_ih2
    rw [h_C2_card, h_stab_eq_fin] at hC2_card_lt
    omega
  have hH2_sub_H : sumset (A ∪ B') H2_fin ⊆ sumset (A ∪ B') (stabFinset C) := by
    intro x hx
    rcases (mem_sumset_iff (A ∪ B') H2_fin x).mp hx with ⟨u, hu, h2, hh2, rfl⟩
    simp only [H2_fin, stabFinset, Set.mem_toFinset, SetLike.mem_coe] at hh2
    rw [mem_sumset_iff]
    exact ⟨u, hu, h2, by simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe]; exact hH2_le hh2, rfl⟩
  have hA2_stab : H2 ≤ finsetAddStab (sumset A2 H2_fin) := stab_le_finsetAddStab_sumset_stabFinset A2 (sumset A2 B2)
  have hB2_stab : H2 ≤ finsetAddStab (sumset B2 H2_fin) := stab_le_finsetAddStab_sumset_stabFinset B2 (sumset A2 B2)
  have hC_stab2 : H2 ≤ finsetAddStab (stabFinset C) := sub_le_finsetAddStab_stabFinset hH2_le C rfl
  have h_A2_mul := card_eq_card_image_mul_subgroup_card_of_stab_le hA2_stab
  have h_B2_mul := card_eq_card_image_mul_subgroup_card_of_stab_le hB2_stab
  have h_C_mul2 := card_eq_card_image_mul_subgroup_card_of_stab_le hC_stab2
  have h_H2_card : Fintype.card H2 = H2_fin.card := (card_stabFinset_eq_card (sumset A2 B2)).symm
  rw [h_H2_card] at h_A2_mul h_B2_mul h_C_mul2
  have h_H2_pos : 1 ≤ H2_fin.card := Finset.Nonempty.card_pos (stabFinset_nonempty (sumset A2 B2))
  have hA2_le : A2.card ≤ (sumset A2 H2_fin).card := Finset.card_le_card (subset_sumset_stabFinset A2 (sumset A2 B2))
  have hB2_le : B2.card ≤ (sumset B2 H2_fin).card := Finset.card_le_card (subset_sumset_stabFinset B2 (sumset A2 B2))
  have h_sub_U2 : (sumset (A ∪ B') H2_fin).card ≤ (sumset (A ∪ B') (stabFinset C)).card := Finset.card_le_card hH2_sub_H
  have h2_2 : H2_fin.card + A2.card + B2.card ≤ (stabFinset C).card :=
    eq2_arith (sumset (A ∪ B') (stabFinset C)).card (sumset (A ∪ B') H2_fin).card
      (stabFinset C).card H2_fin.card A2.card B2.card (sumset A2 H2_fin).card (sumset B2 H2_fin).card
      ((stabFinset C).image (QuotientAddGroup.mk' H2)).card
      ((sumset A2 H2_fin).image (QuotientAddGroup.mk' H2)).card
      ((sumset B2 H2_fin).image (QuotientAddGroup.mk' H2)).card
      h_sub_U2 h_eq1_2 h_C_mul2 h_A2_mul h_B2_mul.symm h_H2_pos hA2_le hB2_le

  exact devos_arith_contradiction_le (stabFinset C).card H1_fin.card H2_fin.card
    A1.card B1.card A2.card B2.card S.card T.card h2_1 h2_2 h3_1 h3_2 h_coset_a h_coset_b

lemma kneser_bound_le_step {n : ℕ} (ih : ∀ m < n, kneser_bound_le m)
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hn : (sumset A B).card + A.card ≤ n) :
    (sumset A (stabFinset (sumset A B))).card + (sumset B (stabFinset (sumset A B))).card ≤
      (sumset A B).card + (stabFinset (sumset A B)).card := by
  by_cases hK_ne : finsetAddStab (sumset A B) ≠ ⊥
  · exact kneser_quotient_step ih A B hA hB hn hK_ne
  · have hK : finsetAddStab (sumset A B) = ⊥ := not_not.mp hK_ne
    have h_stab_eq : stabFinset (sumset A B) = {0} := by
      ext x
      simp only [stabFinset, Set.mem_toFinset, SetLike.mem_coe, mem_finsetAddStab_iff,
        Finset.mem_singleton]
      constructor
      · intro hx
        have : x ∈ finsetAddStab (sumset A B) := hx
        rw [hK] at this
        exact (AddSubgroup.mem_bot (G := G)).mp this
      · rintro rfl
        simp
    rw [h_stab_eq, sumset_zero_right, sumset_zero_right, Finset.card_singleton]
    by_cases hA_card : A.card ≤ 1
    · have hA_eq_1 : A.card = 1 := by
        have : 1 ≤ A.card := Finset.Nonempty.card_pos hA
        omega
      rcases Finset.card_eq_one.mp hA_eq_1 with ⟨a, rfl⟩
      have h_sumset_eq : sumset {a} B = a +ᵥ B := sumset_singleton_left a B
      rw [h_sumset_eq, card_vadd_finset, Finset.card_singleton]
      omega
    · have hA_ge_2 : 2 ≤ A.card := by omega
      rcases exists_translate_inter_nonempty_and_psubset A B hA_ge_2 hB hK with
        ⟨x, hB'_card, hAB'_card, hAB'_bot, h_inter_ne, h_inter_lt⟩
      set B' := x +ᵥ B
      have hB'_ne : B'.Nonempty := by
        rcases hB with ⟨b, hb⟩
        exact ⟨x + b, Finset.mem_vadd_finset.mpr ⟨b, hb, rfl⟩⟩
      have hn' : (sumset A B').card + A.card ≤ n := by
        rw [hAB'_card]
        exact hn
      have hC0 := c0_is_convergent ih A B' hA hB'_ne hAB'_bot hn' h_inter_ne h_inter_lt
      rcases exists_min_convergent hC0 with ⟨C, hC_conv, hC_min⟩
      set H := finsetAddStab C
      by_cases hH : H = ⊥
      · have h_ap' := aperiodic_of_min_convergent_bot hC_conv hH
        rw [hB'_card, hAB'_card] at h_ap'
        exact h_ap'
      · exfalso
        exact devos_contra ih A B' C hA hB'_ne h_inter_ne hn' hAB'_bot hC_conv hC_min hH

theorem kneser_bound_all (n : ℕ) : kneser_bound_le n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ A B hA hB hn
    exact kneser_bound_le_step ih A B hA hB hn

theorem aperiodic_sumset_bound
    (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty)
    (h_bot : finsetAddStab (sumset A B) = ⊥) :
    A.card + B.card ≤ (sumset A B).card + 1 := by
  have h_kb := kneser_bound_all ((sumset A B).card + A.card) G A B hA hB le_rfl
  exact aperiodic_of_kneser_bound A B hA hB h_bot h_kb


end Erdos298
