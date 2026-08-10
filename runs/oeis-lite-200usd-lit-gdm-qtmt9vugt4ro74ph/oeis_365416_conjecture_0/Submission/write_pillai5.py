with open("/workspace/leanproject/Submission/Pillai53.lean", "w") as f:
    f.write("""import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
open Nat

lemma pow_five_zmod_nine (e : ℕ) : (5 : ZMod 9) ^ e = 7 ↔ e % 6 = 2 := by
  have h_eq : e = 6 * (e / 6) + e % 6 := (Nat.div_add_mod e 6).symm
  have h_pow : (5 : ZMod 9) ^ e = (5 : ZMod 9) ^ (e % 6) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (5 : ZMod 9) ^ 6 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 6 <;> decide

lemma pow_three_zmod_125 (f : ℕ) : (3 : ZMod 125) ^ f = 2 ↔ f % 100 = 43 := by
  have h_eq : f = 100 * (f / 100) + f % 100 := (Nat.div_add_mod f 100).symm
  have h_pow : (3 : ZMod 125) ^ f = (3 : ZMod 125) ^ (f % 100) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 125) ^ 100 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : f % 100 < 100 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : f % 100 <;> decide

lemma f_mod_250_of_f_mod_100 (f : ℕ) (h : f % 100 = 43) :
    f % 250 = 43 ∨ f % 250 = 93 ∨ f % 250 = 143 ∨ f % 250 = 193 ∨ f % 250 = 243 := by
  have h_eq : f = 100 * (f / 100) + 43 := by
    have := Nat.div_add_mod f 100
    rw [h] at this
    exact this.symm
  set k := f / 100
  have hk_mod : k % 5 < 5 := Nat.mod_lt _ (by decide)
  have h_eq2 : k = 5 * (k / 5) + k % 5 := (Nat.div_add_mod k 5).symm
  interval_cases hk : k % 5
  · have : k = 5 * (k / 5) := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 43 := by omega
    rw [this]
    left
    omega
  · have : k = 5 * (k / 5) + 1 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 143 := by omega
    rw [this]
    right; right; left
    omega
  · have : k = 5 * (k / 5) + 2 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 243 := by omega
    rw [this]
    right; right; right; right
    omega
  · have : k = 5 * (k / 5) + 3 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 343 := by omega
    rw [this]
    have : 250 * (2 * (k / 5)) + 343 = 250 * (2 * (k / 5) + 1) + 93 := by omega
    rw [this]
    right; left
    omega
  · have : k = 5 * (k / 5) + 4 := by omega
    rw [this] at h_eq
    have : f = 250 * (2 * (k / 5)) + 443 := by omega
    rw [this]
    have : 250 * (2 * (k / 5)) + 443 = 250 * (2 * (k / 5) + 1) + 193 := by omega
    rw [this]
    right; right; right; left
    omega

lemma check_mod_251 (f r : ℕ)
    (h_f : f % 250 = 43 ∨ f % 250 = 93 ∨ f % 250 = 143 ∨ f % 250 = 193 ∨ f % 250 = 243) :
    (3 : ZMod 251) ^ f - 2 ≠ (25 : ZMod 251) ^ r := by
  have h_eq_f : f = 250 * (f / 250) + f % 250 := (Nat.div_add_mod f 250).symm
  have h_pow_f : (3 : ZMod 251) ^ f = (3 : ZMod 251) ^ (f % 250) := by
    conv_lhs => rw [h_eq_f]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 251) ^ 250 = 1 := by decide
    rw [this, one_pow, one_mul]
  have h_eq_r : r = 125 * (r / 125) + r % 125 := (Nat.div_add_mod r 125).symm
  have h_pow_r : (25 : ZMod 251) ^ r = (25 : ZMod 251) ^ (r % 125) := by
    conv_lhs => rw [h_eq_r]
    rw [pow_add, pow_mul]
    have : (25 : ZMod 251) ^ 125 = 1 := by decide
    rw [this, one_pow, one_mul]
  intro h
  rw [h_pow_f, h_pow_r] at h
  have h_mod_r : r % 125 < 125 := Nat.mod_lt _ (by decide)
  rcases h_f with h1 | h2 | h3 | h4 | h5
  · rw [h1] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h2] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h3] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h4] at h
    interval_cases hr : r % 125 <;> revert h <;> decide
  · rw [h5] at h
    interval_cases hr : r % 125 <;> revert h <;> decide

lemma pow_three_eq_27 (f : ℕ) (h : 3 ^ f = 27) : f = 3 := by
  have h_lt : f < 4 := by
    by_contra hc
    have h_ge4 : f ≥ 4 := by omega
    have : 3 ^ f ≥ 81 := by
      calc 3 ^ f ≥ 3 ^ 4 := Nat.pow_le_pow_right (by decide) h_ge4
      _ = 81 := by decide
    omega
  interval_cases f
  · contradiction
  · contradiction
  · contradiction
  · rfl

lemma pow_five_ne_seven (e : ℕ) : 5 ^ e ≠ 7 := by
  intro h
  have h_lt : e < 2 := by
    by_contra hc
    have h_ge2 : e ≥ 2 := by omega
    have : 5 ^ e ≥ 25 := by
      calc 5 ^ e ≥ 5 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge2
      _ = 25 := by decide
    omega
  interval_cases e
  · contradiction
  · contradiction

lemma pillai_diff_two_5_3 (e f : ℕ) (he : 1 < e) (hf : 1 < f) (h : 3 ^ f - 5 ^ e = 2) : e = 2 ∧ f = 3 := by
  have h_cases : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
  rcases h_cases with he_even | he_odd
  · -- e is even
    have he_eq : e = 2 * (e / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he_even)).symm
    set r := e / 2
    have hr : r ≥ 1 := by omega
    by_cases hr1 : r = 1
    · -- r = 1 => e = 2
      have h_e2 : e = 2 := by omega
      rw [h_e2]
      have h3 : 3 ^ f = 27 := by
        have h52 : 5 ^ e = 25 := by
          rw [h_e2]
          rfl
        omega
      have hf3 := pow_three_eq_27 f h3
      exact ⟨rfl, hf3⟩
    · -- r >= 2
      have hr_ge2 : r ≥ 2 := by omega
      have h5 : 5 ^ e = 5 ^ (2 * r) := by rw [he_eq]
      have h125 : 125 ∣ 5 ^ e := by
        rw [h5]
        have : 2 * r = (2 * r - 3) + 3 := by omega
        rw [this, pow_add]
        -- 5^3 = 125
        use 5 ^ (2 * r - 3)
        ring
      have h3_eq : 3 ^ f = 5 ^ e + 2 := by omega
      have h_zmod_125 : (3 : ZMod 125) ^ f = 2 := by
        have h_cast : ((3 ^ f : ℕ) : ZMod 125) = ((5 ^ e + 2 : ℕ) : ZMod 125) := by rw [h3_eq]
        push_cast at h_cast
        have h_div : (5 ^ e : ZMod 125) = 0 := by
          rcases h125 with ⟨c, hc⟩
          have hc_cast : ((5 ^ e : ℕ) : ZMod 125) = ((125 * c : ℕ) : ZMod 125) := congrArg Nat.cast hc
          have h_goal : (5 ^ e : ZMod 125) = ((5 ^ e : ℕ) : ZMod 125) := by push_cast; rfl
          rw [h_goal, hc_cast]
          push_cast
          have h125_zero : (125 : ZMod 125) = 0 := rfl
          rw [h125_zero, zero_mul]
        rw [h_div, zero_add] at h_cast
        exact h_cast
      have h_f_mod := (pow_three_zmod_125 f).mp h_zmod_125
      have h_f_mod_250 := f_mod_250_of_f_mod_100 f h_f_mod
      have h_zmod_251 : (3 : ZMod 251) ^ f - 2 = (25 : ZMod 251) ^ r := by
        have h_cast : ((3 ^ f - 2 : ℕ) : ZMod 251) = ((5 ^ e : ℕ) : ZMod 251) := by
          rw [h3_eq, Nat.add_sub_cancel]
        push_cast at h_cast
        rw [h5] at h_cast
        have h25 : 5 ^ (2 * r) = (25 : ℕ) ^ r := by
          rw [pow_mul]
          rfl
        rw [h25] at h_cast
        push_cast at h_cast
        exact h_cast
      have h_contra := check_mod_251 f r h_f_mod_250
      contradiction
  · -- e is odd
    by_cases hf3 : f ≥ 3
    · have h9 : 9 ∣ 3 ^ f := by
        have : f = (f - 2) + 2 := by omega
        rw [this, pow_add]
        use 3 ^ (f - 2)
        ring
      have h_zmod : (5 : ZMod 9) ^ e = 7 := by
        have : 3 ^ f = 5 ^ e + 2 := by omega
        have h_cast : ((3 ^ f : ℕ) : ZMod 9) = ((5 ^ e + 2 : ℕ) : ZMod 9) := by rw [this]
        push_cast at h_cast
        have h_div : (3 ^ f : ZMod 9) = 0 := by
          rcases h9 with ⟨c, hc⟩
          have hc_cast : ((3 ^ f : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
          have h_goal : (3 ^ f : ZMod 9) = ((3 ^ f : ℕ) : ZMod 9) := by push_cast; rfl
          rw [h_goal, hc_cast]
          push_cast
          have h9_zero : (9 : ZMod 9) = 0 := rfl
          rw [h9_zero, zero_mul]
        rw [h_div] at h_cast
        have : (0 : ZMod 9) = (5 ^ e : ZMod 9) + 2 := h_cast
        have : (5 : ZMod 9) ^ e = -2 := by omega
        have : (-2 : ZMod 9) = 7 := by decide
        omega
      have h_mod := (pow_five_zmod_nine e).mp h_zmod
      have : e % 2 = 0 := by
        have h_div_mod : e = 6 * (e / 6) + e % 6 := (Nat.div_add_mod e 6).symm
        rw [h_mod] at h_div_mod
        rw [h_div_mod]
        clear h hp hq he hf hf3 h9 h_zmod h_mod
        omega
      omega
    · clear h_cases he_even he_odd
      have h_lt3 : f < 3 := by omega
      have h_f2 : f = 2 := by omega
      have h_ne : 5 ^ e = 7 := by
        have h_sub : 3 ^ f - 5 ^ e = 2 := h
        rw [h_f2] at h_sub
        omega
      exact False.elim (pow_five_ne_seven e h_ne)
""")
