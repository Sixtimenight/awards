import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs

set_option linter.unusedSectionVars false

open scoped Pointwise
open Classical

namespace Erdos298

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def sumset (A B : Finset G) : Finset G :=
  (A ×ˢ B).image (fun p => p.1 + p.2)

lemma mem_sumset_iff (A B : Finset G) (x : G) :
    x ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x := by
  simp only [sumset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨p, ⟨ha, hb⟩, rfl⟩
    exact ⟨p.1, ha, p.2, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

lemma sumset_zero_left (A : Finset G) : sumset {0} A = A := by
  ext x
  simp only [mem_sumset_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl, b, hb, rfl⟩
    rwa [zero_add]
  · intro hx
    exact ⟨0, rfl, x, hx, zero_add x⟩

lemma sumset_assoc (A B C : Finset G) :
    sumset (sumset A B) C = sumset A (sumset B C) := by
  ext x
  simp only [mem_sumset_iff]
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b + c, ⟨b, hb, c, hc, rfl⟩, (add_assoc a b c).symm⟩
  · rintro ⟨a, ha, bc, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, c, hc, add_assoc a b c⟩

lemma sumset_zero_right (A : Finset G) : sumset A {0} = A := by
  ext x
  simp only [mem_sumset_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, rfl, rfl⟩
    rwa [add_zero]
  · intro hx
    exact ⟨x, hx, 0, rfl, add_zero x⟩

lemma sumset_subset_sumset {A1 B1 A B : Finset G} (hA : A1 ⊆ A) (hB : B1 ⊆ B) : sumset A1 B1 ⊆ sumset A B := by
  intro z hz
  rcases (mem_sumset_iff A1 B1 z).mp hz with ⟨u, hu, v, hv, rfl⟩
  exact (mem_sumset_iff A B (u + v)).mpr ⟨u, hA hu, v, hB hv, rfl⟩

variable [Fintype G]

def finsetAddStab (S : Finset G) : AddSubgroup G where
  carrier := { x | x +ᵥ S = S }
  zero_mem' := by simp
  add_mem' := by
    intro a b (ha : a +ᵥ S = S) (hb : b +ᵥ S = S)
    change (a + b) +ᵥ S = S
    rw [add_vadd, hb, ha]
  neg_mem' := by
    intro a (ha : a +ᵥ S = S)
    change -a +ᵥ S = S
    have h1 : -a +ᵥ (a +ᵥ S) = -a +ᵥ S := by rw [ha]
    rw [neg_vadd_vadd] at h1
    exact h1.symm

lemma mem_finsetAddStab_iff (S : Finset G) (x : G) :
    x ∈ finsetAddStab S ↔ x +ᵥ S = S := Iff.rfl

lemma vadd_sumset_left (x : G) (A B : Finset G) :
    x +ᵥ (sumset A B) = sumset (x +ᵥ A) B := by
  ext z
  simp only [Finset.mem_vadd_finset, mem_sumset_iff]
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨x + a, ⟨a, ha, rfl⟩, b, hb, add_assoc x a b⟩
  · rintro ⟨xa, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, (add_assoc x a b).symm⟩

lemma fiber_card_le_subgroup_card (H : AddSubgroup G) (y : G ⧸ H) (T : Finset G) :
    (T.filter (fun x => QuotientAddGroup.mk' H x = y)).card ≤ Fintype.card H := by
  rcases Quotient.exists_rep y with ⟨g, rfl⟩
  set F := T.filter (fun x => QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H g)
  have h_sub : (F.image (fun x => x - g)) ⊆ (Finset.univ.filter (fun h => h ∈ H)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F] at hx ⊢
    have h_rel := QuotientAddGroup.eq.mp hx.2
    have : x - g = -(-x + g) := by abel
    rw [this]
    exact H.neg_mem h_rel
  have h_inj : Set.InjOn (fun x => x - g) (F : Set G) := by
    intro x _ z _ heq
    dsimp at heq
    exact sub_left_inj.mp heq
  have h_card_F : F.card = (F.image (fun x => x - g)).card :=
    (Finset.card_image_of_injOn h_inj).symm
  change F.card ≤ Fintype.card H
  rw [h_card_F]
  have h_le := Finset.card_le_card h_sub
  have h_H : Fintype.card H = (Finset.univ.filter (fun h => h ∈ H)).card :=
    Fintype.card_subtype (fun h => h ∈ H)
  omega

lemma card_le_card_image_mul_subgroup_card (H : AddSubgroup G) (T : Finset G) :
    T.card ≤ (T.image (QuotientAddGroup.mk' H)).card * Fintype.card H := by
  have h_sum := Finset.card_eq_sum_card_image (QuotientAddGroup.mk' H) T
  rw [h_sum]
  have h_le : ∑ y ∈ T.image (QuotientAddGroup.mk' H), (T.filter (fun x => QuotientAddGroup.mk' H x = y)).card ≤
      ∑ y ∈ T.image (QuotientAddGroup.mk' H), Fintype.card H := by
    apply Finset.sum_le_sum
    intro y hy
    exact fiber_card_le_subgroup_card H y T
  rw [Finset.sum_const, nsmul_eq_mul] at h_le
  exact h_le

lemma fiber_card_eq_subgroup_card_of_stab_le {H : AddSubgroup G} {S : Finset G}
    (hH : H ≤ finsetAddStab S) (y : G ⧸ H) (hy : y ∈ S.image (QuotientAddGroup.mk' H)) :
    (S.filter (fun x => QuotientAddGroup.mk' H x = y)).card = Fintype.card H := by
  rcases Finset.mem_image.mp hy with ⟨g, hg, rfl⟩
  set F := S.filter (fun x => QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H g)
  have h_le : F.card ≤ Fintype.card H := by
    change (S.filter (fun x => QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H g)).card ≤ Fintype.card H
    exact fiber_card_le_subgroup_card H (QuotientAddGroup.mk' H g) S
  have h_ge : Fintype.card H ≤ F.card := by
    have h_sub : (Finset.univ.filter (fun (h : G) => h ∈ H)).image (fun h => g + h) ⊆ F := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨h, hh, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
      simp only [Finset.mem_filter, F]
      constructor
      · have hh_stab : h ∈ finsetAddStab S := hH hh
        have h_eq : h +ᵥ S = S := hh_stab
        have h_in : h + g ∈ h +ᵥ S := Finset.mem_vadd_finset.mpr ⟨g, hg, rfl⟩
        rw [h_eq] at h_in
        have : g + h = h + g := add_comm g h
        rw [this]
        exact h_in
      · rw [map_add]
        have h_zero : QuotientAddGroup.mk' H h = 0 := (QuotientAddGroup.eq_zero_iff (x := h)).mpr hh
        rw [h_zero, add_zero]
    have h_inj : Set.InjOn (fun h => g + h) (Finset.univ.filter (fun (h : G) => h ∈ H) : Set G) := by
      intro h1 _ h2 _ heq
      dsimp at heq
      exact add_left_cancel heq
    have h_card_im : (Finset.univ.filter (fun (h : G) => h ∈ H)).card =
        ((Finset.univ.filter (fun (h : G) => h ∈ H)).image (fun h => g + h)).card :=
      (Finset.card_image_of_injOn h_inj).symm
    have h_H : Fintype.card H = (Finset.univ.filter (fun h => h ∈ H)).card :=
      Fintype.card_subtype (fun h => h ∈ H)
    have h_card_le := Finset.card_le_card h_sub
    omega
  change F.card = Fintype.card H
  omega

lemma card_eq_card_image_mul_subgroup_card_of_stab_le {H : AddSubgroup G} {S : Finset G}
    (hH : H ≤ finsetAddStab S) :
    S.card = (S.image (QuotientAddGroup.mk' H)).card * Fintype.card H := by
  have h_sum := Finset.card_eq_sum_card_image (QuotientAddGroup.mk' H) S
  rw [h_sum]
  have h_term : ∀ y ∈ S.image (QuotientAddGroup.mk' H),
      (S.filter (fun x => QuotientAddGroup.mk' H x = y)).card = Fintype.card H :=
    fun y hy => fiber_card_eq_subgroup_card_of_stab_le hH y hy
  rw [Finset.sum_congr rfl h_term, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma saturated_of_stab_le {H : AddSubgroup G} {S : Finset G} (hH : H ≤ finsetAddStab S)
    {x : G} (hx : QuotientAddGroup.mk' H x ∈ S.image (QuotientAddGroup.mk' H)) :
    x ∈ S := by
  rcases Finset.mem_image.mp hx with ⟨s, hs, heq⟩
  have h_diff := QuotientAddGroup.eq.mp heq
  have h_in_H : x - s ∈ H := by
    have : -s + x = x - s := by rw [add_comm, sub_eq_add_neg]
    rwa [this] at h_diff
  have h_stab : x - s ∈ finsetAddStab S := hH h_in_H
  have h_eq : (x - s) +ᵥ S = S := h_stab
  have h_mem : (x - s) + s ∈ (x - s) +ᵥ S := Finset.mem_vadd_finset.mpr ⟨s, hs, rfl⟩
  rw [h_eq] at h_mem
  have : (x - s) + s = x := sub_add_cancel x s
  rwa [this] at h_mem

lemma finsetAddStab_image_mk_eq_bot (S : Finset G) :
    finsetAddStab (S.image (QuotientAddGroup.mk' (finsetAddStab S))) = ⊥ := by
  set H := finsetAddStab S
  set Sbar := S.image (QuotientAddGroup.mk' H)
  rw [AddSubgroup.ext_iff]
  intro y
  simp only [AddSubgroup.mem_bot]
  constructor
  · intro hy
    rcases QuotientAddGroup.mk'_surjective H y with ⟨x, rfl⟩
    have hy_stab : QuotientAddGroup.mk' H x +ᵥ Sbar = Sbar := by
      exact hy
    have hx_sub : x +ᵥ S ⊆ S := by
      intro s hs
      rcases Finset.mem_vadd_finset.mp hs with ⟨s0, hs0, rfl⟩
      have h_im : QuotientAddGroup.mk' H (x + s0) ∈ Sbar := by
        rw [map_add]
        have : QuotientAddGroup.mk' H x + QuotientAddGroup.mk' H s0 ∈ QuotientAddGroup.mk' H x +ᵥ Sbar :=
          Finset.mem_vadd_finset.mpr ⟨QuotientAddGroup.mk' H s0, Finset.mem_image_of_mem _ hs0, rfl⟩
        rwa [hy_stab] at this
      exact saturated_of_stab_le (le_refl H) h_im
    have hx_card : (x +ᵥ S).card = S.card := Finset.card_vadd_finset x S
    have hx_eq : x +ᵥ S = S := Finset.eq_of_subset_of_card_le hx_sub (by rw [hx_card])
    have hx_in_H : x ∈ H := hx_eq
    exact (QuotientAddGroup.eq_zero_iff (x := x)).mpr hx_in_H
  · rintro rfl
    exact (finsetAddStab Sbar).zero_mem

lemma image_mk_sumset (H : AddSubgroup G) (A B : Finset G) :
    (sumset A B).image (QuotientAddGroup.mk' H) =
      sumset (A.image (QuotientAddGroup.mk' H)) (B.image (QuotientAddGroup.mk' H)) := by
  ext x
  simp only [mem_sumset_iff, Finset.mem_image]
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨QuotientAddGroup.mk' H a, ⟨a, ha, rfl⟩, QuotientAddGroup.mk' H b, ⟨b, hb, rfl⟩, (map_add (QuotientAddGroup.mk' H) a b).symm⟩
  · rintro ⟨a_bar, ⟨a, ha, rfl⟩, b_bar, ⟨b, hb, rfl⟩, heq⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by rw [map_add, heq]⟩

end Erdos298
