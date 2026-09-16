import Mathlib

lemma digits_3 (B d0 d1 d2 : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h2_pos : 0 < d2) :
    Nat.digits B (d0 + B * (d1 + B * d2)) = [d0, d1, d2] := by
  have H1 : 0 < d1 + B * d2 := by positivity
  have H1' : d1 + B * d2 ≠ 0 := ne_of_gt H1
  rw [Nat.digits_add B hB d0 (d1 + B * d2) h0 (Or.inr H1')]
  have H2' : d2 ≠ 0 := ne_of_gt h2_pos
  rw [Nat.digits_add B hB d1 d2 h1 (Or.inr H2')]
  rw [Nat.digits_def' hB h2_pos]
  have : d2 / B = 0 := Nat.div_eq_of_lt h2
  rw [this, Nat.digits_zero]
  have : d2 % B = d2 := Nat.mod_eq_of_lt h2
  rw [this]

lemma card_3 (d0 d1 d2 : ℕ) (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    ([d0, d1, d2] : List ℕ).toFinset.card = 3 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rfl
    · simp [h12]
  · simp [h01, h02]

lemma distinct_digits_3 (B d0 d1 d2 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h2_pos : 0 < d2) 
    (hk : k = d0 + B * (d1 + B * d2))
    (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_3 B d0 d1 d2 hB h0 h1 h2 h2_pos]
  rw [card_3 d0 d1 d2 h01 h02 h12]
  omega

lemma digits_4 (B d0 d1 d2 d3 : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) :
    Nat.digits B (d0 + B * (d1 + B * (d2 + B * d3))) = [d0, d1, d2, d3] := by
  have H1 : 0 < d1 + B * (d2 + B * d3) := by positivity
  have H1' : d1 + B * (d2 + B * d3) ≠ 0 := Nat.ne_of_gt H1
  rw [Nat.digits_add B hB d0 (d1 + B * (d2 + B * d3)) h0 (Or.inr H1')]
  have H2 : 0 < d2 + B * d3 := by positivity
  have H2' : d2 + B * d3 ≠ 0 := Nat.ne_of_gt H2
  rw [Nat.digits_add B hB d1 (d2 + B * d3) h1 (Or.inr H2')]
  have H3' : d3 ≠ 0 := Nat.ne_of_gt h3_pos
  rw [Nat.digits_add B hB d2 d3 h2 (Or.inr H3')]
  rw [Nat.digits_def' hB h3_pos]
  have : d3 / B = 0 := Nat.div_eq_of_lt h3
  rw [this, Nat.digits_zero]
  have : d3 % B = d3 := Nat.mod_eq_of_lt h3
  rw [this]

lemma card_4 (d0 d1 d2 d3 : ℕ) (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    ([d0, d1, d2, d3] : List ℕ).toFinset.card > 2 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  have h_sub : {d0, d1, d2} ⊆ ({d0, d1, d2, d3} : Finset ℕ) := by
    intro x
    simp
    intro hx
    tauto
  have h_card : ({d0, d1, d2} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rfl
      · simp [h12]
    · simp [h01, h02]
  have h_le := Finset.card_le_card h_sub
  omega

lemma distinct_digits_4 (B d0 d1 d2 d3 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) 
    (hk : k = d0 + B * (d1 + B * (d2 + B * d3)))
    (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_4 B d0 d1 d2 d3 hB h0 h1 h2 h3 h3_pos]
  exact card_4 d0 d1 d2 d3 h01 h02 h12

lemma card_4_alt (d0 d1 d2 d3 : ℕ) (h01 : d0 ≠ d1) (h03 : d0 ≠ d3) (h13 : d1 ≠ d3) :
    ([d0, d1, d2, d3] : List ℕ).toFinset.card > 2 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  have h_sub : {d0, d1, d3} ⊆ ({d0, d1, d2, d3} : Finset ℕ) := by
    intro x
    simp
    intro hx
    tauto
  have h_card : ({d0, d1, d3} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rfl
      · simp [h13]
    · simp [h01, h03]
  have h_le := Finset.card_le_card h_sub
  omega

lemma distinct_digits_4_alt (B d0 d1 d2 d3 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) 
    (hk : k = d0 + B * (d1 + B * (d2 + B * d3)))
    (h01 : d0 ≠ d1) (h03 : d0 ≠ d3) (h13 : d1 ≠ d3) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_4 B d0 d1 d2 d3 hB h0 h1 h2 h3 h3_pos]
  exact card_4_alt d0 d1 d2 d3 h01 h03 h13

lemma region1 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 0) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 3
  have hB : b = B + 3 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 3 * B + 3^2 + x = (B + 3)^2 + x := by ring
  have H_lt : B < (B + 3)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (9) (6) (1) ((B + 3)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 3)^2 = B * B + 2 * 3 * B + 3^2 := by ring
    have h_rhs : B * ((6) + B * (1)) = (6) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region2 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 2
  have hB : b = B + 2 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 2 * B + 2^2 + x = (B + 2)^2 + x := by ring
  have H_lt : B < (B + 2)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (5) (4) (1) ((B + 2)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 2)^2 = B * B + 2 * 2 * B + 2^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region3 (b x : ℕ) (h1 : b ≥ 17) (h2 : 2 ≤ x ∧ x ≤ b - 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 0
  have hB : b = B + 0 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 0 * B + 0^2 + x = (B + 0)^2 + x := by ring
  have H_lt : B < (B + 0)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (x) (0) (1) ((B + 0)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 0)^2 = B * B + 2 * 0 * B + 0^2 := by ring
    have h_rhs : B * ((0) + B * (1)) = (0) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region4 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = b) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (2) (3) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((3) + B * (1)) = (3) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region5 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = b + 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 2
  have hB : b = B + 2 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 2 * B + 2^2 + x = (B + 2)^2 + x := by ring
  have H_lt : B < (B + 2)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (7) (5) (1) ((B + 2)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 2)^2 = B * B + 2 * 2 * B + 2^2 := by ring
    have h_rhs : B * ((5) + B * (1)) = (5) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region6a (b x : ℕ) (h1 : b ≥ 17) (h2 : b + 2 ≤ x ∧ x ≤ 2*b - 4) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (x - B + 1) (3) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((3) + B * (1)) = (3) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region6b (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 3) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (0) (4) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region7 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 2) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 3
  have hB : b = B + 3 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 3 * B + 3^2 + x = (B + 3)^2 + x := by ring
  have H_lt : B < (B + 3)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (13) (8) (1) ((B + 3)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 3)^2 = B * B + 2 * 3 * B + 3^2 := by ring
    have h_rhs : B * ((8) + B * (1)) = (8) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region8 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (2) (4) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region9 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 0
  have hB : b = B + 0 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 0 * B + 0^2 + x = (B + 0)^2 + x := by ring
  have H_lt : B < (B + 0)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (0) (2) (1) ((B + 0)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 0)^2 = B * B + 2 * 0 * B + 0^2 := by ring
    have h_rhs : B * ((2) + B * (1)) = (2) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  constructor
  · apply a306424_43
  · intros k hk
    intro h_cond
    by_cases h289 : k < 289
    · have ⟨B, hB3, hBk, h_card⟩ := bounded_cases k hk h289
      have h_card_le := h_cond B ⟨hB3, hBk⟩
      omega
    · have ⟨B, hB3, hBk, h_card⟩ := k_ge_289 k (by omega)
      have h_card_le := h_cond B ⟨hB3, hBk⟩
      omega

theorem oeis_306424_conjecture_0.disproof : ¬ (type_of% @oeis_306424_conjecture_0) := sorry
lemma k_ge_289 (k : ℕ) (hk : k ≥ 289) : ∃ B, 3 ≤ B ∧ B < k ∧ ((Nat.digits B k).toFinset.card) > 2 := by
  let b := Nat.sqrt k
  let x := k - b^2
  have h1 : b * b ≤ k := Nat.sqrt_le k
  have h2 : k < (b + 1) * (b + 1) := Nat.lt_succ_sqrt k
  have h_exp : (b + 1) * (b + 1) = b^2 + 2 * b + 1 := by ring
  have h_b : b ≥ 17 := by nlinarith
  have h_x_bound : x ≤ 2 * b := by
    have h_b2 : b * b = b^2 := by ring
    omega
  have hk_eq : k = b^2 + x := by
    have h_b2 : b * b = b^2 := by ring
    omega
  clear_value x b
  cases hk_eq
  have h_cases : x = 0 ∨ x = 1 ∨ 2 ≤ x ∧ x ≤ b - 1 ∨ x = b ∨ x = b + 1 ∨ b + 2 ≤ x ∧ x ≤ 2*b - 4 ∨ x = 2*b - 3 ∨ x = 2*b - 2 ∨ x = 2*b - 1 ∨ x = 2*b := by omega
  rcases h_cases with hc0 | hc1 | hc2 | hc3 | hc4 | hc5 | hc6 | hc7 | hc8 | hc9
  · exact region1 b x h_b hc0
  · exact region2 b x h_b hc1
  · exact region3 b x h_b hc2
  · exact region4 b x h_b hc3
  · exact region5 b x h_b hc4
  · exact region6a b x h_b hc5
  · exact region6b b x h_b hc6
  · exact region7 b x h_b hc7
  · exact region8 b x h_b hc8
  · exact region9 b x h_b hc9
