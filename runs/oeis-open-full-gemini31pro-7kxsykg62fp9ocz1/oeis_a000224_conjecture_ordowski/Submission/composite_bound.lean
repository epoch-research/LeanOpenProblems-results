import Mathlib
import Submission.Spec
open Finset

lemma composite_A000224_bound {n a b : ℕ} (hn : n = a * b) (ha : 3 ≤ a) (hb : 3 ≤ b) (h_odd : Odd n) :
  A000224 n ≤ (n - 1) / 2 := by
  have h_pos : 0 < n := by nlinarith
  haveI : NeZero n := ⟨h_pos.ne'⟩
  unfold A000224
  simp only [NeZero.ne n, ite_false, card_image_ZMod]
  let m := (n - 1) / 2
  let f : ℕ → ZMod n := fun k => (k : ZMod n) ^ 2
  have H_sub : univ.image (fun x : ZMod n => x ^ 2) ⊆ (range (m + 1)).image f := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨y, _, rfl⟩ := hx
    rw [mem_image]
    by_cases h_le : y.val ≤ m
    · refine ⟨y.val, mem_range.mpr (by omega), ?_⟩
      change ((y.val : ZMod n) ^ 2) = y ^ 2
      rw [ZMod.natCast_zmod_val]
    · refine ⟨n - y.val, mem_range.mpr (?_), ?_⟩
      · have hy : y.val < n := ZMod.val_lt y
        obtain ⟨k, hk⟩ := h_odd
        have : n = 2 * k + 1 := hk
        omega
      · change (((n - y.val : ℕ) : ZMod n) ^ 2) = y ^ 2
        have h1 : ((n - y.val : ℕ) : ZMod n) = -y := by
          rw [Nat.cast_sub (ZMod.val_lt y).le]
          have h_eq : (n : ZMod n) = 0 := ZMod.natCast_self n
          rw [h_eq, zero_sub, ZMod.natCast_zmod_val]
        rw [h1, neg_sq]
  have H_odd2 : Odd (a * b) := by rw [← hn]; exact h_odd
  have h_odd_a : Odd a := Nat.odd_mul.mp H_odd2 |>.1
  have h_odd_b : Odd b := Nat.odd_mul.mp H_odd2 |>.2
  have H_card : ((range (m + 1)).image f).card ≤ m := by
    cases le_total a b with
    | inl h_ab =>
      let x := (b - a) / 2
      let y := (b + a) / 2
      have h_x_lt_y : x < y := by omega
      have h_y_le_m : y ≤ m := by
        have H1 : 3 * b ≤ a * b := Nat.mul_le_mul_right b ha
        have H2 : b + a + 3 ≤ 3 * b := by omega
        omega
      have h_fx_eq_fy : f x = f y := by
        change ((x : ZMod n) ^ 2) = ((y : ZMod n) ^ 2)
        have h_eq : y ^ 2 = x ^ 2 + a * b := by
          have h1 : b = 2 * x + a := by
            obtain ⟨ka, hka⟩ := h_odd_a
            obtain ⟨kb, hkb⟩ := h_odd_b
            omega
          have h2 : y = x + a := by
            obtain ⟨ka, hka⟩ := h_odd_a
            obtain ⟨kb, hkb⟩ := h_odd_b
            omega
          rw [h2, h1]
          ring
        have H1 : ((y ^ 2 : ℕ) : ZMod n) = (((x ^ 2 + a * b : ℕ) : ZMod n)) := by rw [h_eq]
        rw [Nat.cast_add] at H1
        have H2 : ((a * b : ℕ) : ZMod n) = 0 := by
          rw [← hn, ZMod.natCast_self]
        rw [H2, add_zero] at H1
        have H3 : (y : ZMod n) ^ 2 = (x : ZMod n) ^ 2 := by
          push_cast at H1
          exact H1
        exact H3.symm
      have H_image_eq : ((range (m + 1)).image f) = (((range (m + 1)).erase y).image f) := by
        ext z
        simp only [mem_image, mem_erase, mem_range]
        constructor
        · rintro ⟨w, hw, rfl⟩
          by_cases hwy : w = y
          · exact ⟨x, ⟨ne_of_lt h_x_lt_y, by omega⟩, by rw [h_fx_eq_fy, hwy]⟩
          · exact ⟨w, ⟨hwy, hw⟩, rfl⟩
        · rintro ⟨w, ⟨hwy, hw⟩, rfl⟩
          exact ⟨w, hw, rfl⟩
      rw [H_image_eq]
      calc (((range (m + 1)).erase y).image f).card ≤ ((range (m + 1)).erase y).card := card_image_le
        _ = (range (m + 1)).card - 1 := by
          rw [card_erase_of_mem (mem_range.mpr (by omega))]
        _ = m := by simp
    | inr h_ba =>
      let x := (a - b) / 2
      let y := (a + b) / 2
      have h_x_lt_y : x < y := by omega
      have h_y_le_m : y ≤ m := by
        have H1 : 3 * a ≤ a * b := by
          calc 3 * a ≤ b * a := Nat.mul_le_mul_right a hb
            _ = a * b := mul_comm b a
        have H2 : a + b + 3 ≤ 3 * a := by omega
        omega
      have h_fx_eq_fy : f x = f y := by
        change ((x : ZMod n) ^ 2) = ((y : ZMod n) ^ 2)
        have h_eq : y ^ 2 = x ^ 2 + a * b := by
          have h1 : a = 2 * x + b := by
            obtain ⟨ka, hka⟩ := h_odd_a
            obtain ⟨kb, hkb⟩ := h_odd_b
            omega
          have h2 : y = x + b := by
            obtain ⟨ka, hka⟩ := h_odd_a
            obtain ⟨kb, hkb⟩ := h_odd_b
            omega
          rw [h2, h1]
          ring
        have H1 : ((y ^ 2 : ℕ) : ZMod n) = (((x ^ 2 + a * b : ℕ) : ZMod n)) := by rw [h_eq]
        rw [Nat.cast_add] at H1
        have H2 : ((a * b : ℕ) : ZMod n) = 0 := by
          rw [← hn, ZMod.natCast_self]
        rw [H2, add_zero] at H1
        have H3 : (y : ZMod n) ^ 2 = (x : ZMod n) ^ 2 := by
          push_cast at H1
          exact H1
        exact H3.symm
      have H_image_eq : ((range (m + 1)).image f) = (((range (m + 1)).erase y).image f) := by
        ext z
        simp only [mem_image, mem_erase, mem_range]
        constructor
        · rintro ⟨w, hw, rfl⟩
          by_cases hwy : w = y
          · exact ⟨x, ⟨ne_of_lt h_x_lt_y, by omega⟩, by rw [h_fx_eq_fy, hwy]⟩
          · exact ⟨w, ⟨hwy, hw⟩, rfl⟩
        · rintro ⟨w, ⟨hwy, hw⟩, rfl⟩
          exact ⟨w, hw, rfl⟩
      rw [H_image_eq]
      calc (((range (m + 1)).erase y).image f).card ≤ ((range (m + 1)).erase y).card := card_image_le
        _ = (range (m + 1)).card - 1 := by
          rw [card_erase_of_mem (mem_range.mpr (by omega))]
        _ = m := by simp
  exact (card_le_card H_sub).trans H_card
