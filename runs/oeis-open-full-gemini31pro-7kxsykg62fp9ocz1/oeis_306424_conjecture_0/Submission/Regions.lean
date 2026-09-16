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

