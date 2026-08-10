import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
open Nat

lemma p_ne_three (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) : (p : ZMod 3) = 1 ∨ (p : ZMod 3) = 2 := by
  have h_ne : p % 3 ≠ 0 := by
    intro hc
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hc
    rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
    · contradiction
    · exact hp3 h2.symm
  have h_mod : p % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hp_mod : p % 3
  · contradiction
  · left
    have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hp_mod]
    rfl
  · right
    have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hp_mod]
    rfl

lemma e_odd_of_ne_three (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    e % 2 = 1 := by
  by_contra hc
  have he_even : e % 2 = 0 := by omega
  have he_eq : e = 2 * (e / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he_even)).symm
  have h_zmod : (q : ZMod 3) ^ f = 0 := by
    have h_eq : q ^ f = p ^ e + 2 := by omega
    have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
    push_cast at h_cast
    rw [he_eq] at h_cast
    have hp_pow : (p : ZMod 3) ^ (2 * (e / 2)) = ((p : ZMod 3) ^ 2) ^ (e / 2) := by rw [pow_mul]
    rw [hp_pow] at h_cast
    rcases p_ne_three p hp hp3 with hp1 | hp2
    · rw [hp1] at h_cast
      simp only [one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
    · rw [hp2] at h_cast
      have : (2 : ZMod 3) ^ 2 = 1 := rfl
      rw [this, one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
  rcases p_ne_three q hq hq3 with hq1 | hq2
  · rw [hq1] at h_zmod
    simp only [one_pow, one_ne_zero] at h_zmod
  · rw [hq2] at h_zmod
    have h_pow_ne_zero : (2 : ZMod 3) ^ f ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one f with hf_even | hf_odd
      · have hf_eq : f = 2 * (f / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hf_even)).symm
        rw [hf_eq]
        have : (2 : ZMod 3) ^ (2 * (f / 2)) = ((2 : ZMod 3) ^ 2) ^ (f / 2) := by rw [pow_mul]
        rw [this]
        have : (2 : ZMod 3) ^ 2 = 1 := rfl
        rw [this, one_pow]
        decide
      · have hf_eq : f = 2 * (f / 2) + 1 := by omega
        rw [hf_eq]
        have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
        rw [this]
        have : (2 : ZMod 3) ^ 2 = 1 := rfl
        rw [this, one_pow, one_mul]
        decide
    exact h_pow_ne_zero h_zmod

lemma p_mod_three_eq_two_of_ne_three (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    p % 3 = 2 := by
  have he_odd := e_odd_of_ne_three p q e f hp hq he hf h hp3 hq3
  rcases p_ne_three p hp hp3 with hp1 | hp2
  · exfalso
    have h_zmod : (q : ZMod 3) ^ f = 0 := by
      have h_eq : q ^ f = p ^ e + 2 := by omega
      have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
      push_cast at h_cast
      rw [hp1] at h_cast
      simp only [one_pow] at h_cast
      have : (1 : ZMod 3) + 2 = 0 := rfl
      rw [this] at h_cast
      exact h_cast
    rcases p_ne_three q hq hq3 with hq1 | hq2
    · rw [hq1] at h_zmod
      simp only [one_pow, one_ne_zero] at h_zmod
    · rw [hq2] at h_zmod
      have h_pow_ne_zero : (2 : ZMod 3) ^ f ≠ 0 := by
        rcases Nat.mod_two_eq_zero_or_one f with hf_even | hf_odd
        · have hf_eq : f = 2 * (f / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hf_even)).symm
          rw [hf_eq]
          have : (2 : ZMod 3) ^ (2 * (f / 2)) = ((2 : ZMod 3) ^ 2) ^ (f / 2) := by rw [pow_mul]
          rw [this]
          have : (2 : ZMod 3) ^ 2 = 1 := rfl
          rw [this, one_pow]
          decide
        · have hf_eq : f = 2 * (f / 2) + 1 := by omega
          rw [hf_eq]
          have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
          rw [this]
          have : (2 : ZMod 3) ^ 2 = 1 := rfl
          rw [this, one_pow, one_mul]
          decide
      exact h_pow_ne_zero h_zmod
  · have h_mod : p % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hp_mod : p % 3
    · have : ((p : ℕ) : ZMod 3) = 0 := by
        have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hp_mod]
        rfl
      rw [this] at hp2
      contradiction
    · have : ((p : ℕ) : ZMod 3) = 1 := by
        have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hp_mod]
        rfl
      rw [this] at hp2
      contradiction
    · rfl

lemma q_mod_three_eq_one_of_f_odd (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) (hf_odd : f % 2 = 1) :
    q % 3 = 1 := by
  have hp_mod := p_mod_three_eq_two_of_ne_three p q e f hp hq he hf h hp3 hq3
  have he_odd := e_odd_of_ne_three p q e f hp hq he hf h hp3 hq3
  have h_zmod : (q : ZMod 3) ^ f = 1 := by
    have h_eq : q ^ f = p ^ e + 2 := by omega
    have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((p ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h_eq
    push_cast at h_cast
    have hp_pow : (p : ZMod 3) ^ e = (p : ZMod 3) ^ (2 * (e / 2) + 1) := congrArg (fun x => (p : ZMod 3) ^ x) (by omega)
    rw [hp_pow] at h_cast
    have hp_pow2 : (p : ZMod 3) ^ (2 * (e / 2) + 1) = ((p : ZMod 3) ^ 2) ^ (e / 2) * p := by rw [pow_succ, pow_mul]
    rw [hp_pow2] at h_cast
    have hp_cast : (p : ZMod 3) = 2 := by
      have : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
      rw [this, hp_mod]
      rfl
    rw [hp_cast] at h_cast
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul] at h_cast
    have : (2 : ZMod 3) + 2 = 1 := rfl
    rw [this] at h_cast
    exact h_cast
  rcases p_ne_three q hq hq3 with hq1 | hq2
  · have h_mod : q % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hq_mod : q % 3
    · have : ((q : ℕ) : ZMod 3) = 0 := by
        have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hq_mod]
        rfl
      rw [this] at hq1
      contradiction
    · rfl
    · have : ((q : ℕ) : ZMod 3) = 2 := by
        have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
        rw [this, hq_mod]
        rfl
      rw [this] at hq1
      contradiction
  · exfalso
    rw [hq2] at h_zmod
    have hf_eq : f = 2 * (f / 2) + 1 := by omega
    rw [hf_eq] at h_zmod
    have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by rw [pow_succ, pow_mul]
    rw [this] at h_zmod
    have : (2 : ZMod 3) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul] at h_zmod
    have : (2 : ZMod 3) = 1 := h_zmod
    contradiction

lemma f_even_of_q_mod_three_eq_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hp3 : p ≠ 3) (hq3 : q ≠ 3) (hq_mod : q % 3 = 2) :
    f % 2 = 0 := by
  by_contra hc
  have hf_odd : f % 2 = 1 := by omega
  have hq_mod_eq_one := q_mod_three_eq_one_of_f_odd p q e f hp hq he hf h hp3 hq3 hf_odd
  omega

lemma not_dvd_three_f_of_q3 (p e f : ℕ) (hp : Nat.Prime p) (he : 1 < e) (h : 3 ^ f - p ^ e = 2) : ¬ 3 ∣ e := by
  rintro ⟨s, rfl⟩
  have h9 : 9 ∣ 3 ^ f := by
    have hp2 : p ≥ 2 := hp.two_le
    have : p ^ (3 * s) ≥ 8 := by
      have h3s : 3 * s ≥ 3 := by omega
      calc p ^ (3 * s) ≥ p ^ 3 := Nat.pow_le_pow_right (by omega) h3s
      _ ≥ 2 ^ 3 := Nat.pow_le_pow_left hp2 3
      _ = 8 := by decide
    have : 3 ^ f ≥ 10 := by omega
    have h_f_ge3 : f ≥ 3 := by
      by_contra hc
      have : f < 3 := by omega
      interval_cases f <;> omega
    have : f = (f - 2) + 2 := by omega
    rw [this, pow_add]
    use 3 ^ (f - 2)
    ring
  rcases h9 with ⟨c, hc⟩
  have h_eq : 3 ^ f = p ^ (3 * s) + 2 := by omega
  have h_cast : ((3 ^ f : ℕ) : ZMod 9) = ((p ^ (3 * s) + 2 : ℕ) : ZMod 9) := congrArg Nat.cast h_eq
  push_cast at h_cast
  have h_div : (3 ^ f : ZMod 9) = 0 := by
    have hc_cast : ((3 ^ f : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
    have h_goal : (3 ^ f : ZMod 9) = ((3 ^ f : ℕ) : ZMod 9) := by push_cast; rfl
    rw [h_goal, hc_cast]
    push_cast
    have : (9 : ZMod 9) = 0 := rfl
    rw [this, zero_mul]
  rw [h_div] at h_cast
  have h_cast2 : (p : ZMod 9) ^ (3 * s) = -2 := by
    calc (p : ZMod 9) ^ (3 * s) = ((p : ZMod 9) ^ (3 * s) + 2) - 2 := by ring
    _ = 0 - 2 := by rw [← h_cast]
    _ = -2 := by ring
  have h_cube : ((p : ZMod 9) ^ s) ^ 3 = 7 := by
    calc ((p : ZMod 9) ^ s) ^ 3 = (p : ZMod 9) ^ (3 * s) := by ring
    _ = -2 := h_cast2
    _ = 7 := rfl
  set y := (p : ZMod 9) ^ s
  have h_val : y.val < 9 := y.val_lt
  have h_eq_y : y = (y.val : ZMod 9) := (ZMod.natCast_zmod_val y).symm
  rw [h_eq_y] at h_cube
  interval_cases h_y : y.val <;> revert h_cube <;> decide

lemma not_dvd_three_e_of_p3 (q e f : ℕ) (hq : Nat.Prime q) (hf : 1 < f) (h : q ^ f - 3 ^ e = 2) : ¬ 3 ∣ f := by
  rintro ⟨s, rfl⟩
  have h9 : 9 ∣ 3 ^ e := by
    have : e ≥ 2 := by
      have hq2 : q ≥ 2 := hq.two_le
      have : q ^ (3 * s) ≥ 8 := by
        have : 3 * s ≥ 3 := by omega
        calc q ^ (3 * s) ≥ q ^ 3 := Nat.pow_le_pow_right (by omega) this
        _ ≥ 2 ^ 3 := Nat.pow_le_pow_left hq2 3
        _ = 8 := by decide
      have : 3 ^ e ≥ 6 := by omega
      have : e ≥ 2 := by
        by_contra hc
        have : e < 2 := by omega
        interval_cases e <;> omega
      omega
    have : e = (e - 2) + 2 := by omega
    rw [this, pow_add]
    use 3 ^ (e - 2)
    ring
  rcases h9 with ⟨c, hc⟩
  have h_eq : q ^ (3 * s) = 3 ^ e + 2 := by omega
  have h_cast : ((q ^ (3 * s) : ℕ) : ZMod 9) = ((3 ^ e + 2 : ℕ) : ZMod 9) := congrArg Nat.cast h_eq
  push_cast at h_cast
  have h_div : (3 ^ e : ZMod 9) = 0 := by
    have hc_cast : ((3 ^ e : ℕ) : ZMod 9) = ((9 * c : ℕ) : ZMod 9) := congrArg Nat.cast hc
    have h_goal : (3 ^ e : ZMod 9) = ((3 ^ e : ℕ) : ZMod 9) := by push_cast; rfl
    rw [h_goal, hc_cast]
    push_cast
    have : (9 : ZMod 9) = 0 := rfl
    rw [this, zero_mul]
  rw [h_div, zero_add] at h_cast
  have h_cube : ((q : ZMod 9) ^ s) ^ 3 = 2 := by
    calc ((q : ZMod 9) ^ s) ^ 3 = (q : ZMod 9) ^ (3 * s) := by ring
    _ = 2 := h_cast
  set y := (q : ZMod 9) ^ s
  have h_val : y.val < 9 := y.val_lt
  have h_eq_y : y = (y.val : ZMod 9) := (ZMod.natCast_zmod_val y).symm
  rw [h_eq_y] at h_cube
  interval_cases h_y : y.val <;> revert h_cube <;> decide

