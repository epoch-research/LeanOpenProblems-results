import FormalConjectures.Util.ProblemImports

open Nat

lemma div2_lt_self_of_pos {n : ℕ} (h : 0 < n) : div2 n < n := by
  have h1 := bodd_add_div2 n
  have hb : n.bodd.toNat ≤ 1 := by
    cases n.bodd <;> decide
  omega

lemma choose_mod_two_eq (n k : ℕ) : (n.choose k : ZMod 2) = (n % 2).choose (k % 2) * (n / 2).choose (k / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_rhs : ((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ZMod 2) = (((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ℕ) : ZMod 2) := by push_cast; rfl
  rw [h_rhs]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma and_eq_self_of_choose_mod_two_eq_one (n k : ℕ) (h : (n.choose k : ZMod 2) = 1) : k &&& n = k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn] at h
      have hk : k = 0 := by
        by_contra hk_ne
        have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk_ne)
        rw [this] at h
        exact zero_ne_one h
      rw [hk]
      change bitwise and 0 n = 0
      rw [bitwise_zero_left]
      rfl
    · rw [choose_mod_two_eq] at h
      have h_mul : ∀ (x y : ZMod 2), x * y = 1 → x = 1 ∧ y = 1 := by
        decide
      rcases h_mul _ _ h with ⟨h1, h2⟩
      have h_div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have h_div2 : div2 n = n / 2 := div2_val n
      have h_k_div2 : div2 k = k / 2 := div2_val k
      have h2_eq : ((n / 2).choose (k / 2) : ZMod 2) = 1 := h2
      have ih_res := ih (n / 2) h_div_lt (k / 2) h2_eq
      have h_bodd : (bodd k = false) ∨ (bodd k = true ∧ bodd n = true) := by
        cases hk : bodd k <;> cases hn2 : bodd n
        · left; rfl
        · left; rfl
        · have h_n_mod_eq : n % 2 = n.bodd.toNat := by
            have := bodd_add_div2 n
            omega
          have h_k_mod_eq : k % 2 = k.bodd.toNat := by
            have := bodd_add_div2 k
            omega
          rw [h_n_mod_eq, hn2, h_k_mod_eq, hk] at h1
          simp at h1
        · right; exact ⟨rfl, rfl⟩
      have h_k_eq : k = bit (bodd k) (div2 k) := (bit_bodd_div2 k).symm
      have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
      rw [h_k_eq, h_n_eq]
      rw [land_bit]
      rw [h_div2, h_k_div2]
      rw [ih_res]
      rcases h_bodd with hk_false | ⟨hk_true, hn_true⟩
      · rw [hk_false]
        simp
      · rw [hk_true, hn_true]
        simp

lemma le_of_and_eq_self (a b : ℕ) (h : b &&& a = b) : b ≤ a := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha] at h
      have hb : b = 0 := by
        rw [← h]
        change bitwise and b 0 = 0
        rw [bitwise_zero_right]
        rfl
      rw [hb, ha]
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and : bit (bodd b) (div2 b) &&& bit (bodd a) (div2 a) = bit (bodd b) (div2 b) := by
        rw [← h_b_eq, ← h_a_eq]
        exact h
      rw [land_bit] at h_and
      have h_div : div2 b &&& div2 a = div2 b := by
        have h_d := congr_arg div2 h_and
        rw [div2_bit, div2_bit] at h_d
        exact h_d
      have h_bodd : (bodd b && bodd a) = bodd b := by
        have h_b := congr_arg bodd h_and
        rw [bodd_bit, bodd_bit] at h_b
        exact h_b
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div
      rw [h_a_eq, h_b_eq]
      rw [bit_val, bit_val]
      cases h1 : bodd a <;> cases h2 : bodd b
      · simp; omega
      · rw [h1, h2] at h_bodd
        simp at h_bodd
      · simp; omega
      · simp; omega

lemma sub_eq_ldiff_of_and_eq_self (a b : ℕ) (h : b &&& a = b) : a - b = ldiff a b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha]
      rw [ha] at h
      have hb : b = 0 := by
        rw [← h]
        change bitwise and b 0 = 0
        rw [bitwise_zero_right]
        rfl
      rw [hb]
      change 0 - 0 = Nat.bitwise (fun a b => a && !b) 0 0
      rw [Nat.bitwise_zero_left]
      rfl
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and : bit (bodd b) (div2 b) &&& bit (bodd a) (div2 a) = bit (bodd b) (div2 b) := by
        rw [← h_b_eq, ← h_a_eq]
        exact h
      rw [land_bit] at h_and
      have h_bodd : (bodd b && bodd a) = bodd b := by
        have h_b := congr_arg bodd h_and
        rw [bodd_bit, bodd_bit] at h_b
        exact h_b
      have h_div : div2 b &&& div2 a = div2 b := by
        have h_d := congr_arg div2 h_and
        rw [div2_bit, div2_bit] at h_d
        exact h_d
      have h_le := le_of_and_eq_self (div2 a) (div2 b) h_div
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div
      rw [h_a_eq, h_b_eq]
      rw [ldiff_bit]
      rw [← h_ih]
      rw [bit_val, bit_val, bit_val]
      cases h1 : bodd a <;> cases h2 : bodd b
      · simp; omega
      · rw [h1, h2] at h_bodd
        simp at h_bodd
      · simp; omega
      · simp; omega



lemma add_eq_lor_of_and_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · rw [ha, zero_add]
      have h_lor : 0 ||| b = b := by
        change bitwise or 0 b = b
        rw [bitwise_zero_left]
        rfl
      rw [h_lor]
    · have h_div2_lt : div2 a < a := div2_lt_self_of_pos (Nat.pos_of_ne_zero ha)
      have h_a_eq : a = bit (bodd a) (div2 a) := (bit_bodd_div2 a).symm
      have h_b_eq : b = bit (bodd b) (div2 b) := (bit_bodd_div2 b).symm
      have h_and_zero : bit (bodd a) (div2 a) &&& bit (bodd b) (div2 b) = 0 := by
        rw [← h_a_eq, ← h_b_eq]
        exact h
      rw [land_bit] at h_and_zero
      rw [Nat.bit_eq_zero_iff] at h_and_zero
      rcases h_and_zero with ⟨h_div_zero, h_bodd_zero⟩
      have h_ih := ih (div2 a) h_div2_lt (div2 b) h_div_zero
      rw [h_a_eq, h_b_eq]
      rw [lor_bit]
      rw [bit_val, bit_val, bit_val]
      rw [← h_ih]
      have h_bodd : (bodd a || bodd b).toNat = (bodd a).toNat + (bodd b).toNat := by
        cases h1 : bodd a <;> cases h2 : bodd b <;> (try rfl)
        · rw [h1, h2] at h_bodd_zero
          simp at h_bodd_zero
      rw [h_bodd]
      omega
