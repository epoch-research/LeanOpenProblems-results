import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Choose.Lucas

open Nat

lemma choose_lucas_step (j : ℕ) (hj : j ≥ 1) :
  choose (4 * j - 1) (2 * j) ≡ choose (2 * j - 1) j [MOD 2] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_lucas : choose (4 * j - 1) (2 * j) ≡ choose ((4 * j - 1) % 2) ((2 * j) % 2) * choose ((4 * j - 1) / 2) ((2 * j) / 2) [MOD 2] := Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h_num_mod : (4 * j - 1) % 2 = 1 := by omega
  have h_num_div : (4 * j - 1) / 2 = 2 * j - 1 := by omega
  have h_den_mod : (2 * j) % 2 = 0 := by omega
  have h_den_div : (2 * j) / 2 = j := by omega
  rw [h_num_mod, h_num_div, h_den_mod, h_den_div] at h_lucas
  have h_choose_1_0 : choose 1 0 = 1 := rfl
  rw [h_choose_1_0, one_mul] at h_lucas
  exact h_lucas

lemma odd_mul_odd_iff (a b : ℕ) : Odd (a * b) ↔ Odd a ∧ Odd b := Nat.odd_mul

lemma my_odd_two_mul_add_one (k : ℕ) : Odd (2 * k + 1) := by
  use k

lemma modEq_two_iff_odd_iff (a b : ℕ) (h : a ≡ b [MOD 2]) : Odd a ↔ Odd b := by
  rw [Nat.odd_iff, Nat.odd_iff]
  exact Iff.intro (fun ha => by rw [← h, ha]) (fun hb => by rw [h, hb])

lemma choose_two_mul (m : ℕ) (hm : m ≥ 1) : choose (2 * m) m = 2 * choose (2 * m - 1) (m - 1) := by
  have h_eq : ((2 * m - 1) + 1) * choose (2 * m - 1) (m - 1) = choose ((2 * m - 1) + 1) ((m - 1) + 1) * ((m - 1) + 1) := by
    exact add_one_mul_choose_eq (2 * m - 1) (m - 1)
  have h_succ1 : (2 * m - 1) + 1 = 2 * m := by omega
  have h_succ2 : (m - 1) + 1 = m := by omega
  rw [h_succ1, h_succ2] at h_eq
  have h_eq2 : choose (2 * m) m * m = (2 * choose (2 * m - 1) (m - 1)) * m := by linarith
  have h_m_pos : m > 0 := by omega
  exact Nat.eq_of_mul_eq_mul_right h_m_pos h_eq2

lemma odd_j_choose_even (j : ℕ) (hj : j ≥ 3) (hodd : Odd j) : ¬ Odd (choose (2 * j - 1) j) := by
  rcases hodd with ⟨m, rfl⟩
  have hm : m ≥ 1 := by omega
  have h_eq : 2 * (2 * m + 1) - 1 = 4 * m + 1 := by omega
  rw [h_eq]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_lucas : choose (4 * m + 1) (2 * m + 1) ≡ choose ((4 * m + 1) % 2) ((2 * m + 1) % 2) * choose ((4 * m + 1) / 2) ((2 * m + 1) / 2) [MOD 2] := Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h_num_mod : (4 * m + 1) % 2 = 1 := by omega
  have h_num_div : (4 * m + 1) / 2 = 2 * m := by omega
  have h_den_mod : (2 * m + 1) % 2 = 1 := by omega
  have h_den_div : (2 * m + 1) / 2 = m := by omega
  rw [h_num_mod, h_num_div, h_den_mod, h_den_div] at h_lucas
  have h_choose_1_1 : choose 1 1 = 1 := rfl
  rw [h_choose_1_1, one_mul] at h_lucas
  have h_parity : Odd (choose (4 * m + 1) (2 * m + 1)) ↔ Odd (choose (2 * m) m) := by
    exact modEq_two_iff_odd_iff (choose (4 * m + 1) (2 * m + 1)) (choose (2 * m) m) h_lucas
  rw [h_parity]
  have h_two_mul := choose_two_mul m hm
  rw [h_two_mul]
  intro ho
  rcases ho with ⟨x, hx⟩
  omega

lemma K_even_j_parity (j : ℕ) (hj : j ≥ 1) (heven : Even j) :
  Odd ((2 * j + 1) * choose (4 * j - 1) (2 * j)) ↔ Odd ((j + 1) * choose (2 * j - 1) j) := by
  rw [odd_mul_odd_iff, odd_mul_odd_iff]
  have h_odd_1 : Odd (2 * j + 1) := my_odd_two_mul_add_one j
  have h_odd_2 : Odd (j + 1) := by
    rcases heven with ⟨k, rfl⟩
    use k
    ring
  simp [h_odd_1, h_odd_2]
  have h_step := choose_lucas_step j hj
  exact modEq_two_iff_odd_iff (choose (4 * j - 1) (2 * j)) (choose (2 * j - 1) j) h_step

def CongruentMod2 (q1 q2 : ℚ) : Prop :=
  ∃ (z d : ℤ), Odd d ∧ q1 - q2 = (2 * z : ℚ) / (d : ℚ)

lemma congruent_mod2_int_parity (a b : ℤ) (h : CongruentMod2 (a : ℚ) (b : ℚ)) : (Odd a ↔ Odd b) := by
  rcases h with ⟨z, d, hd_odd, hdiff⟩
  have hd_ne : (d : ℚ) ≠ 0 := by
    intro hd_eq_zero
    have : d = 0 := by exact_mod_cast hd_eq_zero
    subst this
    have : ¬ Odd (0 : ℤ) := by decide
    contradiction
  have h_mul := by
    have hdiff_mul : (a - b : ℚ) * d = (2 * z / d) * d := by rw [hdiff]
    rw [div_mul_cancel₀ _ hd_ne] at hdiff_mul
    exact hdiff_mul
  have h_eq : (a - b) * d = 2 * z := by
    exact_mod_cast h_mul
  constructor
  · intro ha
    rcases ha with ⟨x, hx⟩
    rcases hd_odd with ⟨y, hy⟩
    use x - z + y * (2 * x + 1 - b)
    have h_subst : 2 * z = (2 * x + 1 - b) * (2 * y + 1) := by
      rw [← h_eq, hx, hy]
    have h_val : 2 * (x - z + y * (2 * x + 1 - b)) + 1 = 2 * x + 1 + 2 * y * (2 * x + 1 - b) - 2 * z := by ring
    rw [h_val, h_subst]
    ring
  · intro hb
    rcases hb with ⟨x, hx⟩
    rcases hd_odd with ⟨y, hy⟩
    use x + z - y * (a - (2 * x + 1))
    have h_subst : 2 * z = (a - (2 * x + 1)) * (2 * y + 1) := by
      rw [← h_eq, hx, hy]
    have h_val : 2 * (x + z - y * (a - (2 * x + 1))) + 1 = 2 * x + 1 - 2 * y * (a - (2 * x + 1)) + 2 * z := by ring
    rw [h_val, h_subst]
    ring


theorem K_parity (n : ℕ) (hn : n ≥ 2) :
  Odd ((n + 1) * choose (2 * n - 1) n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m := by
  induction' n using Nat.strong_induction_on with n ih
  have h_mod2 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases h_mod2 with h_even | h_odd
  · obtain ⟨j, hj⟩ : 2 ∣ n := Nat.dvd_of_mod_eq_zero h_even
    have h_j_ge1 : j ≥ 1 := by omega
    have h_n_eq : n = 2 * j := hj
    have h_j_cases : j = 1 ∨ j ≥ 2 := by omega
    rcases h_j_cases with rfl | hj_ge2
    · -- case j = 1 (n = 2)
      constructor
      · intro _
        use 1
        refine ⟨by omega, by omega⟩
      · intro _
        have h_choose : choose 3 2 = 3 := rfl
        rw [h_n_eq, h_choose]
        decide
    · -- case j >= 2 (n = 2 * j)
      have h_j_lt : j < n := by omega
      have ih_j := ih j h_j_lt hj_ge2
      rw [h_n_eq]
      have h_j_mod2 : j % 2 = 0 ∨ j % 2 = 1 := Nat.mod_two_eq_zero_or_one _
      rcases h_j_mod2 with h_j_even | h_j_odd
      · have h_j_even_prop : Even j := Nat.even_iff.mpr h_j_even
        have h_rw_goal : 2 * (2 * j) - 1 = 4 * j - 1 := by omega
        rw [h_rw_goal]
        rw [K_even_j_parity j h_j_ge1 h_j_even_prop, ih_j]
        constructor
        · rintro ⟨m, hm, rfl⟩
          use m + 1
          refine ⟨by omega, ?_⟩
          rw [pow_succ, mul_comm]
        · rintro ⟨m, hm, h_pow⟩
          have hm2 : m ≥ 2 := by
            by_contra!
            (interval_cases m; omega)
          use m - 1
          constructor
          · omega
          · have h_rw_m : m = (m - 1) + 1 := by omega
            rw [h_rw_m, pow_succ, mul_comm] at h_pow
            omega
      · -- j is odd and >= 2, so j >= 3
        have h_j_odd_prop : Odd j := Nat.odd_iff.mpr h_j_odd
        have h_j_ge3 : j ≥ 3 := by omega
        constructor
        · intro h_lhs
          have h_rw_goal : 2 * (2 * j) - 1 = 4 * j - 1 := by omega
          rw [h_rw_goal, odd_mul_odd_iff] at h_lhs
          have h_choose_parity : Odd (choose (4 * j - 1) (2 * j)) ↔ Odd (choose (2 * j - 1) j) := by
            exact modEq_two_iff_odd_iff (choose (4 * j - 1) (2 * j)) (choose (2 * j - 1) j) (choose_lucas_step j h_j_ge1)
          rw [h_choose_parity] at h_lhs
          have h_even_choose := odd_j_choose_even j h_j_ge3 h_j_odd_prop
          exact False.elim (h_even_choose h_lhs.2)
        · rintro ⟨m, hm, h_pow⟩
          have hm2 : m ≥ 2 := by
            by_contra!
            (interval_cases m; omega)
          have h_rw_m : m = (m - 1) + 1 := by omega
          rw [h_rw_m, pow_succ, mul_comm] at h_pow
          have h_j_eq : j = 2^(m - 1) := by omega
          have h_j_mod2_contra : j % 2 = 0 := by
            have h_m_sub : m - 1 = (m - 2) + 1 := by omega
            rw [h_j_eq, h_m_sub, pow_succ]
            generalize 2^(m - 2) = X
            omega
          have h_j_mod : j % 2 = 1 := h_j_odd
          omega
  · -- Odd case: n is odd and >= 2, so n is odd and >= 3
    have h_odd_prop : Odd n := Nat.odd_iff.mpr h_odd
    have h_ge3 : n ≥ 3 := by omega
    constructor
    · intro h_lhs
      rw [odd_mul_odd_iff] at h_lhs
      have h_n_plus_one_even : Even (n + 1) := by
        rcases h_odd_prop with ⟨k, rfl⟩
        use k + 1
        ring
      rcases h_n_plus_one_even with ⟨k, hk⟩
      have h_n_plus_one_mod2 : (n + 1) % 2 = 0 := by
        rw [hk]
        ring_nf
        omega
      have h_lhs_odd_mod : (n + 1) % 2 = 1 := Nat.odd_iff.mp h_lhs.1
      omega
    · rintro ⟨m, hm, rfl⟩
      have h_even_pow : 2^m % 2 = 0 := by
        have h_m_eq : m = (m - 1) + 1 := by omega
        rw [h_m_eq, pow_succ]
        generalize 2^(m - 1) = X
        omega
      have h_odd_pow : 2^m % 2 = 1 := Nat.odd_iff.mp h_odd_prop
      omega
