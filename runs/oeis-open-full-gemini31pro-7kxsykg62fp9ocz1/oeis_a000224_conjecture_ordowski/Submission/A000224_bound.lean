
lemma A000224_bound {n : ℕ} (h_odd : Odd n) : A000224 n ≤ (n + 1) / 2 := by
  have h_pos : 0 < n := by
    obtain ⟨k, hk⟩ := h_odd
    omega
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
  have H_card : ((range (m + 1)).image f).card ≤ m + 1 := card_image_le.trans (by rw [card_range])
  have H_le := (card_le_card H_sub).trans H_card
  have H_eq : m + 1 = (n + 1) / 2 := by
    obtain ⟨k, hk⟩ := h_odd
    rw [hk]
    omega
  rw [H_eq] at H_le
  exact H_le
