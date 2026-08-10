import FormalConjectures.Util.ProblemImports

open List Finset Nat

set_option maxHeartbeats 0

/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition

lemma div_eq_one_of_lt_of_le {a b : ℕ} (hb : 0 < b) (h1 : b ≤ a) (h2 : a < 2 * b) : a / b = 1 := by
  have h_eq : a = (a - b) + b := by omega
  rw [h_eq]
  rw [Nat.add_div_right (a - b) hb]
  have : (a - b) < b := by omega
  rw [Nat.div_eq_of_lt this]

lemma mod_eq_sub_of_lt_of_le {a b : ℕ} (h1 : b ≤ a) (h2 : a < 2 * b) : a % b = a - b := by
  have h_eq : a = (a - b) + b := by omega
  rw [h_eq]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

lemma digits_of_lt_three_power (b k : ℕ) (hb : 2 ≤ b) (h1 : b ^ 2 ≤ k) (h2 : k < b ^ 3) :
    Nat.digits b k = [k % b, (k / b) % b, k / b ^ 2] := by
  have hb_pos : 0 < b := by omega
  have hb2_pos : 0 < b ^ 2 := by positivity
  have hk0 : 0 < k := by omega
  rw [Nat.digits_of_two_le_of_pos hb hk0]
  have h_kb : 0 < k / b := by
    rw [Nat.div_pos_iff]
    constructor
    · omega
    · have : b ≤ b ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_self b
      exact this.trans h1
  rw [Nat.digits_of_two_le_of_pos hb h_kb]
  congr 1
  have h_div_div : k / b / b = k / b ^ 2 := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  rw [h_div_div]
  have h_div_lt : k / b ^ 2 < b := by
    rw [Nat.div_lt_iff_lt_mul hb2_pos]
    have : b * b ^ 2 = b ^ 3 := by ring
    rw [this]
    exact h2
  have h_div_ne : k / b ^ 2 ≠ 0 := by
    rw [ne_eq, Nat.div_eq_zero_iff]
    push_neg
    constructor
    · omega
    · exact h1
  rw [Nat.digits_of_lt b (k / b ^ 2) h_div_ne h_div_lt]

lemma card_of_three_distinct (x y z : ℕ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ([x, y, z].toFinset.card) = 3 := by
  simp [hxy, hyz, hxz]

lemma digits_card_gt_two_of_three_power (b k : ℕ) (hb : 2 ≤ b) (h1 : b ^ 2 ≤ k) (h2 : k < b ^ 3)
    (hdy : k % b ≠ (k / b) % b) (hyz : (k / b) % b ≠ k / b ^ 2) (hdx : k % b ≠ k / b ^ 2) :
    ((Nat.digits b k).toFinset.card) > 2 := by
  rw [digits_of_lt_three_power b k hb h1 h2]
  rw [card_of_three_distinct (k % b) ((k / b) % b) (k / b ^ 2) hdy hyz hdx]
  omega

lemma case1 (b : ℕ) (hb : 14 ≤ b) :
    ∃ b' < (b + 3) ^ 2, 3 ≤ b' ∧ ((Nat.digits b' ((b + 3) ^ 2)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < (b + 3) ^ 2 := by
    have : (b + 3) ^ 2 = b ^ 2 + 6 * b + 9 := by ring
    rw [this]
    omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ (b + 3) ^ 2 := by
    have h_ring : (b + 3) ^ 2 = b ^ 2 + 6 * b + 9 := by ring
    rw [h_ring]
    omega
  have h_pow3 : (b + 3) ^ 2 < b ^ 3 := by
    have h1 : (b + 3) ^ 2 = b ^ 2 + 6 * b + 9 := by ring
    have h2 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1, h2]
    have : 6 * b + 9 < b ^ 2 * (b - 1) := by
      have hb1 : 13 ≤ b - 1 := by omega
      have hb2 : 14 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : (b + 3) ^ 2 % b = 9 := by
    have : (b + 3) ^ 2 = 9 + b * (b + 6) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : ((b + 3) ^ 2 / b) % b = 6 := by
    have : (b + 3) ^ 2 = 9 + b * (b + 6) := by ring
    rw [this]
    have h_div : (9 + b * (b + 6)) / b = 9 / b + (b + 6) := by
      rw [Nat.add_mul_div_left 9 (b + 6) hb_pos]
    rw [h_div]
    have : 9 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 6 = 6 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : (b + 3) ^ 2 / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · have : (b + 3) ^ 2 = b ^ 2 + 6 * b + 9 := by ring
      rw [this]
      have : 6 * b + 9 < b ^ 2 := by
        rw [pow_two]
        nlinarith
      omega
  have hdy : (b + 3) ^ 2 % b ≠ ((b + 3) ^ 2 / b) % b := by omega
  have hyz : ((b + 3) ^ 2 / b) % b ≠ (b + 3) ^ 2 / b ^ 2 := by omega
  have hdx : (b + 3) ^ 2 % b ≠ (b + 3) ^ 2 / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b ((b + 3) ^ 2) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case2 (b : ℕ) (hb : 6 ≤ b) :
    ∃ b' < (b + 2) ^ 2 + 1, 3 ≤ b' ∧ ((Nat.digits b' ((b + 2) ^ 2 + 1)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < (b + 2) ^ 2 + 1 := by
    have : (b + 2) ^ 2 + 1 = b ^ 2 + 4 * b + 5 := by ring
    rw [this]
    omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ (b + 2) ^ 2 + 1 := by
    have h_ring : (b + 2) ^ 2 + 1 = b ^ 2 + 4 * b + 5 := by ring
    rw [h_ring]
    omega
  have h_pow3 : (b + 2) ^ 2 + 1 < b ^ 3 := by
    have h1 : (b + 2) ^ 2 + 1 = b ^ 2 + 4 * b + 5 := by ring
    have h2 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1, h2]
    have : 4 * b + 5 < b ^ 2 * (b - 1) := by
      have hb1 : 5 ≤ b - 1 := by omega
      have hb2 : 6 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : ((b + 2) ^ 2 + 1) % b = 5 := by
    have : (b + 2) ^ 2 + 1 = 5 + b * (b + 4) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : (((b + 2) ^ 2 + 1) / b) % b = 4 := by
    have : (b + 2) ^ 2 + 1 = 5 + b * (b + 4) := by ring
    rw [this]
    have h_div : (5 + b * (b + 4)) / b = 5 / b + (b + 4) := by
      rw [Nat.add_mul_div_left 5 (b + 4) hb_pos]
    rw [h_div]
    have : 5 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 4 = 4 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : ((b + 2) ^ 2 + 1) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · have : (b + 2) ^ 2 + 1 = b ^ 2 + 4 * b + 5 := by ring
      rw [this]
      have : 4 * b + 5 < b ^ 2 := by
        rw [pow_two]
        nlinarith
      omega
  have hdy : ((b + 2) ^ 2 + 1) % b ≠ (((b + 2) ^ 2 + 1) / b) % b := by omega
  have hyz : (((b + 2) ^ 2 + 1) / b) % b ≠ ((b + 2) ^ 2 + 1) / b ^ 2 := by omega
  have hdx : ((b + 2) ^ 2 + 1) % b ≠ ((b + 2) ^ 2 + 1) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b ((b + 2) ^ 2 + 1) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case3 (b : ℕ) (hb : 8 ≤ b) :
    ∃ b' < (b + 2) ^ 2 + (b + 2) + 1, 3 ≤ b' ∧ ((Nat.digits b' ((b + 2) ^ 2 + (b + 2) + 1)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < (b + 2) ^ 2 + (b + 2) + 1 := by
    have : (b + 2) ^ 2 + (b + 2) + 1 = b ^ 2 + 5 * b + 7 := by ring
    rw [this]
    omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ (b + 2) ^ 2 + (b + 2) + 1 := by
    have h_ring : (b + 2) ^ 2 + (b + 2) + 1 = b ^ 2 + 5 * b + 7 := by ring
    rw [h_ring]
    omega
  have h_pow3 : (b + 2) ^ 2 + (b + 2) + 1 < b ^ 3 := by
    have h1 : (b + 2) ^ 2 + (b + 2) + 1 = b ^ 2 + 5 * b + 7 := by ring
    have h2 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1, h2]
    have : 5 * b + 7 < b ^ 2 * (b - 1) := by
      have hb1 : 7 ≤ b - 1 := by omega
      have hb2 : 8 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : ((b + 2) ^ 2 + (b + 2) + 1) % b = 7 := by
    have : (b + 2) ^ 2 + (b + 2) + 1 = 7 + b * (b + 5) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : (((b + 2) ^ 2 + (b + 2) + 1) / b) % b = 5 := by
    have : (b + 2) ^ 2 + (b + 2) + 1 = 7 + b * (b + 5) := by ring
    rw [this]
    have h_div : (7 + b * (b + 5)) / b = 7 / b + (b + 5) := by
      rw [Nat.add_mul_div_left 7 (b + 5) hb_pos]
    rw [h_div]
    have : 7 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 5 = 5 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : ((b + 2) ^ 2 + (b + 2) + 1) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · have : (b + 2) ^ 2 + (b + 2) + 1 = b ^ 2 + 5 * b + 7 := by ring
      rw [this]
      have : 5 * b + 7 < b ^ 2 := by
        rw [pow_two]
        nlinarith
      omega
  have hdy : ((b + 2) ^ 2 + (b + 2) + 1) % b ≠ (((b + 2) ^ 2 + (b + 2) + 1) / b) % b := by omega
  have hyz : (((b + 2) ^ 2 + (b + 2) + 1) / b) % b ≠ ((b + 2) ^ 2 + (b + 2) + 1) / b ^ 2 := by omega
  have hdx : ((b + 2) ^ 2 + (b + 2) + 1) % b ≠ ((b + 2) ^ 2 + (b + 2) + 1) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b ((b + 2) ^ 2 + (b + 2) + 1) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case4 (b : ℕ) (hb : 14 ≤ b) :
    ∃ b' < (b + 3) ^ 2 + 2 * (b + 3) - 2, 3 ≤ b' ∧ ((Nat.digits b' ((b + 3) ^ 2 + 2 * (b + 3) - 2)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_eq : (b + 3) ^ 2 + 2 * (b + 3) - 2 = b ^ 2 + 8 * b + 13 := by
    have h1 : (b + 3) ^ 2 = b ^ 2 + 6 * b + 9 := by ring
    have h2 : 2 * (b + 3) = 2 * b + 6 := by ring
    rw [h1, h2]
    omega
  have h_lt : b < (b + 3) ^ 2 + 2 * (b + 3) - 2 := by
    rw [h_eq]
    omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ (b + 3) ^ 2 + 2 * (b + 3) - 2 := by
    rw [h_eq]
    omega
  have h_pow3 : (b + 3) ^ 2 + 2 * (b + 3) - 2 < b ^ 3 := by
    have h2 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h_eq, h2]
    have : 8 * b + 13 < b ^ 2 * (b - 1) := by
      have hb1 : 13 ≤ b - 1 := by omega
      have hb2 : 14 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : ((b + 3) ^ 2 + 2 * (b + 3) - 2) % b = 13 := by
    rw [h_eq]
    have : b ^ 2 + 8 * b + 13 = 13 + b * (b + 8) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : (((b + 3) ^ 2 + 2 * (b + 3) - 2) / b) % b = 8 := by
    rw [h_eq]
    have : b ^ 2 + 8 * b + 13 = 13 + b * (b + 8) := by ring
    rw [this]
    have h_div : (13 + b * (b + 8)) / b = 13 / b + (b + 8) := by
      rw [Nat.add_mul_div_left 13 (b + 8) hb_pos]
    rw [h_div]
    have : 13 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 8 = 8 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : ((b + 3) ^ 2 + 2 * (b + 3) - 2) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · rw [h_eq]
      have : 8 * b + 13 < b ^ 2 := by
        rw [pow_two]
        nlinarith
      omega
  have hdy : ((b + 3) ^ 2 + 2 * (b + 3) - 2) % b ≠ (((b + 3) ^ 2 + 2 * (b + 3) - 2) / b) % b := by omega
  have hyz : (((b + 3) ^ 2 + 2 * (b + 3) - 2) / b) % b ≠ ((b + 3) ^ 2 + 2 * (b + 3) - 2) / b ^ 2 := by omega
  have hdx : ((b + 3) ^ 2 + 2 * (b + 3) - 2) % b ≠ ((b + 3) ^ 2 + 2 * (b + 3) - 2) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b ((b + 3) ^ 2 + 2 * (b + 3) - 2) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case3_prime (b d : ℕ) (hb : 17 ≤ b) (hd1 : 2 ≤ d) (hd2 : d < b) :
    ∃ b' < b ^ 2 + d, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + d)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + d := by
    rw [pow_two]
    nlinarith
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + d := by omega
  have h_pow3 : b ^ 2 + d < b ^ 3 := by
    have h1 : b ^ 3 = b * b ^ 2 := by ring
    rw [h1]
    nlinarith
  have hd0 : (b ^ 2 + d) % b = d := by
    have : b ^ 2 + d = d + b * b := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt hd2]
  have hd1 : ((b ^ 2 + d) / b) % b = 0 := by
    have : b ^ 2 + d = d + b * b := by ring
    rw [this]
    have h_div : (d + b * b) / b = d / b + b := by
      rw [Nat.add_mul_div_left d b hb_pos]
    rw [h_div]
    have : d / b = 0 := by
      rw [Nat.div_eq_of_lt hd2]
    rw [this, zero_add]
    rw [Nat.mod_self]
  have hd2 : (b ^ 2 + d) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · nlinarith
  have hdy : (b ^ 2 + d) % b ≠ ((b ^ 2 + d) / b) % b := by omega
  have hyz : ((b ^ 2 + d) / b) % b ≠ (b ^ 2 + d) / b ^ 2 := by omega
  have hdx : (b ^ 2 + d) % b ≠ (b ^ 2 + d) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + d) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case4_prime (b : ℕ) (hb : 16 ≤ b) :
    ∃ b' < b ^ 2 + 3 * b + 2, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + 3 * b + 2)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + 3 * b + 2 := by omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + 3 * b + 2 := by omega
  have h_pow3 : b ^ 2 + 3 * b + 2 < b ^ 3 := by
    have h1 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1]
    have : 3 * b + 2 < b ^ 2 * (b - 1) := by
      have hb1 : 15 ≤ b - 1 := by omega
      have hb2 : 16 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : (b ^ 2 + 3 * b + 2) % b = 2 := by
    have : b ^ 2 + 3 * b + 2 = 2 + b * (b + 3) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : ((b ^ 2 + 3 * b + 2) / b) % b = 3 := by
    have : b ^ 2 + 3 * b + 2 = 2 + b * (b + 3) := by ring
    rw [this]
    have h_div : (2 + b * (b + 3)) / b = 2 / b + (b + 3) := by
      rw [Nat.add_mul_div_left 2 (b + 3) hb_pos]
    rw [h_div]
    have : 2 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 3 = 3 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : (b ^ 2 + 3 * b + 2) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · nlinarith
  have hdy : (b ^ 2 + 3 * b + 2) % b ≠ ((b ^ 2 + 3 * b + 2) / b) % b := by omega
  have hyz : ((b ^ 2 + 3 * b + 2) / b) % b ≠ (b ^ 2 + 3 * b + 2) / b ^ 2 := by omega
  have hdx : (b ^ 2 + 3 * b + 2) % b ≠ (b ^ 2 + 3 * b + 2) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + 3 * b + 2) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case6_prime (b d : ℕ) (hb : 16 ≤ b) (hd1 : 2 ≤ d) (hd2 : d < b - 2) :
    ∃ b' < b ^ 2 + 3 * b + 2 + d, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + 3 * b + 2 + d)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + 3 * b + 2 + d := by omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + 3 * b + 2 + d := by omega
  have h_pow3 : b ^ 2 + 3 * b + 2 + d < b ^ 3 := by
    have h1 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1]
    have : 3 * b + 2 + d < b ^ 2 * (b - 1) := by
      have h_b1 : 15 ≤ b - 1 := by omega
      have h_d : d < b := by omega
      have h_b2 : b * 16 ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      generalize hX : b - 1 = X
      generalize hY : b ^ 2 = Y
      have : 3 * b + 2 + d < 16 * b * 15 := by omega
      have : 16 * b * 15 ≤ Y * X := by
        nlinarith
      omega
    omega
  have hd0 : (b ^ 2 + 3 * b + 2 + d) % b = 2 + d := by
    have : b ^ 2 + 3 * b + 2 + d = (2 + d) + b * (b + 3) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hd1 : ((b ^ 2 + 3 * b + 2 + d) / b) % b = 3 := by
    have : b ^ 2 + 3 * b + 2 + d = (2 + d) + b * (b + 3) := by ring
    rw [this]
    have h_div : ((2 + d) + b * (b + 3)) / b = (2 + d) / b + (b + 3) := by
      rw [Nat.add_mul_div_left (2 + d) (b + 3) hb_pos]
    rw [h_div]
    have : (2 + d) / b = 0 := by
      rw [Nat.div_eq_of_lt (by omega)]
    rw [this, zero_add]
    have : b + 3 = 3 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hd2 : (b ^ 2 + 3 * b + 2 + d) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · have : 3 * b + 2 + d < b ^ 2 := by
        have : d < b := by omega
        have : 3 * b + 2 + d ≤ 4 * b := by omega
        have : 4 * b < b ^ 2 := by
          rw [pow_two]
          nlinarith
        omega
      omega
  have hdy : (b ^ 2 + 3 * b + 2 + d) % b ≠ ((b ^ 2 + 3 * b + 2 + d) / b) % b := by omega
  have hyz : ((b ^ 2 + 3 * b + 2 + d) / b) % b ≠ (b ^ 2 + 3 * b + 2 + d) / b ^ 2 := by omega
  have hdx : (b ^ 2 + 3 * b + 2 + d) % b ≠ (b ^ 2 + 3 * b + 2 + d) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + 3 * b + 2 + d) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case6_prime_boundary (b : ℕ) (hb : 16 ≤ b) :
    ∃ b' < b ^ 2 + 4 * b, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + 4 * b)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + 4 * b := by omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + 4 * b := by omega
  have h_pow3 : b ^ 2 + 4 * b < b ^ 3 := by
    have h1 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1]
    have : 4 * b < b ^ 2 * (b - 1) := by
      have hb1 : 15 ≤ b - 1 := by omega
      have hb2 : 16 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : (b ^ 2 + 4 * b) % b = 0 := by
    have : b ^ 2 + 4 * b = b * (b + 4) := by ring
    rw [this]
    rw [Nat.mul_mod_right]
  have hd1 : ((b ^ 2 + 4 * b) / b) % b = 4 := by
    have : b ^ 2 + 4 * b = b * (b + 4) := by ring
    rw [this]
    rw [Nat.mul_div_cancel_left _ hb_pos]
    have : b + 4 = 4 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : (b ^ 2 + 4 * b) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · nlinarith
  have hdy : (b ^ 2 + 4 * b) % b ≠ ((b ^ 2 + 4 * b) / b) % b := by omega
  have hyz : ((b ^ 2 + 4 * b) / b) % b ≠ (b ^ 2 + 4 * b) / b ^ 2 := by omega
  have hdx : (b ^ 2 + 4 * b) % b ≠ (b ^ 2 + 4 * b) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + 4 * b) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case8_prime (b : ℕ) (hb : 16 ≤ b) :
    ∃ b' < b ^ 2 + 4 * b + 2, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + 4 * b + 2)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + 4 * b + 2 := by omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + 4 * b + 2 := by omega
  have h_pow3 : b ^ 2 + 4 * b + 2 < b ^ 3 := by
    have h1 : b ^ 3 = b ^ 2 + b ^ 2 * (b - 1) := by
      rw [Nat.mul_sub_left_distrib]
      rw [mul_one]
      have : b ^ 2 * b = b ^ 3 := by ring
      rw [this]
      rw [Nat.add_sub_cancel']
      have : b ^ 2 ≤ b ^ 3 := by
        have : b ^ 3 = b * b ^ 2 := by ring
        rw [this]
        nlinarith
      exact this
    rw [h1]
    have : 4 * b + 2 < b ^ 2 * (b - 1) := by
      have hb1 : 15 ≤ b - 1 := by omega
      have hb2 : 16 * b ≤ b ^ 2 := by
        rw [pow_two]
        nlinarith
      nlinarith
    omega
  have hd0 : (b ^ 2 + 4 * b + 2) % b = 2 := by
    have : b ^ 2 + 4 * b + 2 = 2 + b * (b + 4) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd1 : ((b ^ 2 + 4 * b + 2) / b) % b = 4 := by
    have : b ^ 2 + 4 * b + 2 = 2 + b * (b + 4) := by ring
    rw [this]
    have h_div : (2 + b * (b + 4)) / b = 2 / b + (b + 4) := by
      rw [Nat.add_mul_div_left 2 (b + 4) hb_pos]
    rw [h_div]
    have : 2 / b = 0 := by
      rw [Nat.div_eq_of_lt]
      omega
    rw [this, zero_add]
    have : b + 4 = 4 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : (b ^ 2 + 4 * b + 2) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · nlinarith
  have hdy : (b ^ 2 + 4 * b + 2) % b ≠ ((b ^ 2 + 4 * b + 2) / b) % b := by omega
  have hyz : ((b ^ 2 + 4 * b + 2) / b) % b ≠ (b ^ 2 + 4 * b + 2) / b ^ 2 := by omega
  have hdx : (b ^ 2 + 4 * b + 2) % b ≠ (b ^ 2 + 4 * b + 2) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + 4 * b + 2) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma case9_prime (b : ℕ) (hb : 17 ≤ b) :
    ∃ b' < b ^ 2 + 2 * b, 3 ≤ b' ∧ ((Nat.digits b' (b ^ 2 + 2 * b)).toFinset.card) > 2 := by
  use b
  have hb2 : 2 ≤ b := by omega
  have hb_pos : 0 < b := by omega
  have h_lt : b < b ^ 2 + 2 * b := by omega
  have h3 : 3 ≤ b := by omega
  refine ⟨h_lt, h3, ?_⟩
  have h_pow2 : b ^ 2 ≤ b ^ 2 + 2 * b := by omega
  have h_pow3 : b ^ 2 + 2 * b < b ^ 3 := by
    have h1 : b ^ 3 = b * b ^ 2 := by ring
    rw [h1]
    nlinarith
  have hd0 : (b ^ 2 + 2 * b) % b = 0 := by
    have : b ^ 2 + 2 * b = b * (b + 2) := by ring
    rw [this]
    rw [Nat.mul_mod_right]
  have hd1 : ((b ^ 2 + 2 * b) / b) % b = 2 := by
    have : b ^ 2 + 2 * b = b * (b + 2) := by ring
    rw [this]
    rw [Nat.mul_div_cancel_left _ hb_pos]
    have : b + 2 = 2 + b * 1 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have hd2 : (b ^ 2 + 2 * b) / b ^ 2 = 1 := by
    apply div_eq_one_of_lt_of_le
    · positivity
    · exact h_pow2
    · nlinarith
  have hdy : (b ^ 2 + 2 * b) % b ≠ ((b ^ 2 + 2 * b) / b) % b := by omega
  have hyz : ((b ^ 2 + 2 * b) / b) % b ≠ (b ^ 2 + 2 * b) / b ^ 2 := by omega
  have hdx : (b ^ 2 + 2 * b) % b ≠ (b ^ 2 + 2 * b) / b ^ 2 := by omega
  exact digits_card_gt_two_of_three_power b (b ^ 2 + 2 * b) hb2 h_pow2 h_pow3 hdy hyz hdx

lemma condition_43 : A306424_condition 43 := by
  intro b ⟨hb1, hb2⟩
  interval_cases b <;> simp

theorem main_conjecture_part_2 (k : ℕ) (hk : 43 < k) : ¬ A306424_condition k := by
  by_cases h_lt : k < 289
  · interval_cases k
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 7 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 9 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 8 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 6 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 7 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 5 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 4 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp
    · intro h; have h1 := h 3 (by decide); revert h1; simp

  · have hk289 : 289 ≤ k := by omega
    have h_b_ge : 17 ≤ Nat.sqrt k := Nat.le_sqrt.mpr (by omega)
    let b := Nat.sqrt k
    have h_sqrt_le_pow : b ^ 2 ≤ k := by
      rw [pow_two]
      exact Nat.sqrt_le k
    have h_lt_succ : k < (b + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.lt_succ_sqrt k
    generalize hd : k - b ^ 2 = d
    have hd_le : d ≤ 2 * b := by
      have h_lt' : k < (b + 1) ^ 2 := h_lt_succ
      have : (b + 1) ^ 2 = b ^ 2 + 2 * b + 1 := by ring
      rw [this] at h_lt'
      omega
    have h_k_eq : k = b ^ 2 + d := by omega
    intro h_cond
    rcases eq_or_ne d 0 with rfl | hd0
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 3 + 3) ^ 2 := by
          have h_b : b = b - 3 + 3 := by omega
          rw [h_b] at h_k_eq
          rw [h_k_eq]
          ring
        rw [h_k_eq2]
        exact case1 (b - 3) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases eq_or_ne d 1 with rfl | hd1
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 2 + 2) ^ 2 + 1 := by
          have h_b : b = b - 2 + 2 := by omega
          rw [h_b] at h_k_eq
          rw [h_k_eq]
        rw [h_k_eq2]
        exact case2 (b - 2) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases lt_or_ge d b with hd_lt_b | hd_ge_b
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        rw [h_k_eq]
        have hd_ge_2 : 2 ≤ d := by omega
        exact case3_prime b d h_b_ge hd_ge_2 hd_lt_b
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases eq_or_ne d b with rfl | hdb
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 1) ^ 2 + 3 * (b - 1) + 2 := by
          have h_b : b = (b - 1) + 1 := by omega
          rw [h_b] at h_k_eq
          rw [h_k_eq]
          generalize (b - 1) = X
          ring
        rw [h_k_eq2]
        exact case4_prime (b - 1) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases eq_or_ne d (b + 1) with rfl | hdb1
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 2 + 2) ^ 2 + (b - 2 + 2) + 1 := by
          have h_b : b = b - 2 + 2 := by omega
          rw [h_b] at h_k_eq
          rw [h_k_eq]
          ring
        rw [h_k_eq2]
        exact case3 (b - 2) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases lt_or_ge d (2 * b - 2) with hd_lt_2b2 | hd_ge_2b2
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        let d' := d - b
        have hd'1 : 2 ≤ d' := by omega
        rcases lt_or_ge d' (b - 3) with hd'2_lt | hd'2_ge
        · have hd'2 : d' < (b - 1) - 2 := by omega
          have h_eq' : k = (b - 1) ^ 2 + 3 * (b - 1) + 2 + d' := by
            have h_b : b = (b - 1) + 1 := by omega
            have h_d : d = d' + (b - 1) + 1 := by omega
            rw [h_b] at h_k_eq
            rw [h_d] at h_k_eq
            rw [h_k_eq]
            generalize (b - 1) = X
            ring
          rw [h_eq']
          exact case6_prime (b-1) d' (by omega) hd'1 hd'2
        · have hd'_eq : d' = b - 3 := by omega
          have h_eq' : k = (b - 1) ^ 2 + 4 * (b - 1) := by
            have h_b : b = (b - 3) + 3 := by omega
            rw [h_b] at h_k_eq
            have h_d : d = (b - 3) + ((b - 3) + 3) := by omega
            rw [h_d] at h_k_eq
            rw [h_k_eq]
            have h_b1 : b - 1 = (b - 3) + 2 := by omega
            rw [h_b1]
            generalize (b - 3) = Y
            ring
          rw [h_eq']
          exact case6_prime_boundary (b-1) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases eq_or_ne d (2 * b - 2) with rfl | hdb2
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 3 + 3) ^ 2 + 2 * (b - 3 + 3) - 2 := by
          have h_b : b = (b - 3) + 3 := by omega
          rw [h_b] at h_k_eq
          rw [h_k_eq]
          omega
        rw [h_k_eq2]
        exact case4 (b - 3) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    rcases eq_or_ne d (2 * b - 1) with rfl | hdb1'
    · have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        have h_k_eq2 : k = (b - 1) ^ 2 + 4 * (b - 1) + 2 := by
          have h_b : b = (b - 1) + 1 := by omega
          rw [h_b] at h_k_eq
          have h_sub : 2 * ((b - 1) + 1) - 1 = 2 * (b - 1) + 1 := by omega
          rw [h_sub] at h_k_eq
          rw [h_k_eq]
          generalize (b - 1) = X
          ring
        rw [h_k_eq2]
        exact case8_prime (b - 1) (by omega)
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega
    · have hd_eq_2b : d = 2 * b := by omega
      have : ∃ b' < k, 3 ≤ b' ∧ ((Nat.digits b' k).toFinset.card) > 2 := by
        rw [h_k_eq, hd_eq_2b]
        exact case9_prime b h_b_ge
      rcases this with ⟨b', hb'_lt, hb'_ge, hb'_card⟩
      have : ((Nat.digits b' k).toFinset.card) ≤ 2 := h_cond b' ⟨hb'_ge, hb'_lt⟩
      omega

theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  constructor
  · exact condition_43
  · exact main_conjecture_part_2
