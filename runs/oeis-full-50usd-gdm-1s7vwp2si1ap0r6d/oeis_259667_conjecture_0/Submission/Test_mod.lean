import FormalConjectures.Util.ProblemImports

open Nat

lemma pow_three_gt_self (x : ℕ) : 3^x > x := by
  induction x with
  | zero => omega
  | succ x ih =>
    have : 3^(x+1) = 3^x * 3 := by ring
    omega

lemma exists_m (j : ℕ) (hj : j ≥ 3) : ∃ m, 3^m < 2^(j+1) ∧ 2^(j+1) ≤ 3^(m+1) := by
  let P := fun x => 3^x < 2^(j+1)
  let n := 2^(j+1)
  let m := Nat.findGreatest P n
  use m
  have h_eq_iff : Nat.findGreatest P n = m ↔ m ≤ n ∧ (m ≠ 0 → P m) ∧ ∀ ⦃x⦄, m < x → x ≤ n → ¬P x := Nat.findGreatest_eq_iff
  have h_m_eq : Nat.findGreatest P n = m := rfl
  rw [h_m_eq] at h_eq_iff
  have h_spec := h_eq_iff.mp rfl
  rcases h_spec with ⟨hm_le, hm_prop, h_greatest⟩
  have h_P0 : P 0 := by
    dsimp [P]
    have h_pow : 2^(j+1) ≥ 2^4 := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    have : 2^4 = 16 := by rfl
    omega
  have h_Pm : P m := by
    by_cases h : m = 0
    · rw [h]
      exact h_P0
    · exact hm_prop h
  refine ⟨h_Pm, ?_⟩
  have h_m_lt_n : m < n := by
    by_contra h_ge
    have h_eq : m = n := by omega
    have h_Pn : P n := by
      rw [← h_eq]
      exact h_Pm
    change 3^n < n at h_Pn
    have h_gt := pow_three_gt_self n
    omega
  have h_not_P : ¬ P (m + 1) := by
    apply h_greatest (by omega) (by omega)
  change ¬ (3^(m+1) < 2^(j+1)) at h_not_P
  omega

lemma div_from_equation (u m : ℕ) (h_eq : 2 * (u % 3^m) = 3^m - 1) : 3^m ∣ 2 * u + 1 := by
  have h_div_add : u = 3^m * (u / 3^m) + u % 3^m := (Nat.div_add_mod u (3^m)).symm
  have h_mul : 2 * u + 1 = 2 * (3^m * (u / 3^m) + u % 3^m) + 1 := by
    nth_rewrite 1 [h_div_add]
    rfl
  have h_ring : 2 * (3^m * (u / 3^m) + u % 3^m) + 1 = 3^m * (2 * (u / 3^m)) + (2 * (u % 3^m) + 1) := by ring
  rw [h_ring] at h_mul
  rw [h_eq] at h_mul
  have h_sub : 3^m - 1 + 1 = 3^m := by
    have : 3^m ≥ 1 := Nat.one_le_pow m 3 (by omega)
    omega
  rw [h_sub] at h_mul
  have h_ring2 : 3^m * (2 * (u / 3^m)) + 3^m = 3^m * (2 * (u / 3^m) + 1) := by ring
  rw [h_ring2] at h_mul
  rw [h_mul]
  exact Nat.dvd_mul_right (3^m) (2 * (u / 3^m) + 1)

lemma three_pow_mod_eight (m : ℕ) : 3^m % 8 = 1 ∨ 3^m % 8 = 3 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
    rcases ih with h1 | h3
    · right
      have : 3^(m+1) = 3^m * 3 := by ring
      rw [this, Nat.mul_mod, h1]
    · left
      have : 3^(m+1) = 3^m * 3 := by ring
      rw [this, Nat.mul_mod, h3]

lemma two_pow_mod_eight (n : ℕ) (hn : n ≥ 3) : 2^n % 8 = 0 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have : 2^(n+1) = 2^n * 2 := by ring
    rw [this, Nat.mul_mod, ih]

lemma power_equation_impossible (j m : ℕ) (hj : j ≥ 3) (heq : 2^(j+1) - 3^m = 1) : False := by
  have h_two_pow : 2^(j+1) % 8 = 0 := by
    apply two_pow_mod_eight (j+1)
    omega
  have h_three_pow := three_pow_mod_eight m
  have h_eq_add : 2^(j+1) = 3^m + 1 := by omega
  have h_mod : 2^(j+1) % 8 = (3^m + 1) % 8 := by rw [h_eq_add]
  rw [h_two_pow] at h_mod
  rcases h_three_pow with h1 | h3
  · have h_mod_add : (3^m + 1) % 8 = (3^m % 8 + 1) % 8 := Nat.add_mod (3^m) 1 8
    rw [h_mod_add, h1] at h_mod
    contradiction
  · have h_mod_add : (3^m + 1) % 8 = (3^m % 8 + 1) % 8 := Nat.add_mod (3^m) 1 8
    rw [h_mod_add, h3] at h_mod
    contradiction

axiom cantor_two_mul_add_one (u : ℕ) (hc1 : ∀ m, u / 3^m % 3 < 2) (hc2 : ∀ m, (2 * u + 1) / 3^m % 3 < 2) :
    ∀ j, 2 * u < 3^j - 1 ∨ 2 * (u % 3^j) = 3^j - 1

lemma case_two_contradiction (j : ℕ) (hj : j ≥ 3) (hc1 : ∀ m, (2^j - 1) / 3^m % 3 < 2) (hc2 : ∀ m, (2^(j+1) - 1) / 3^m % 3 < 2) : False := by
  let u := 2^j - 1
  have h_u : 2^(j+1) - 1 = 2 * u + 1 := by
    have : 2^(j+1) = 2^j * 2 := by ring
    have : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
    omega
  have hc2' : ∀ m, (2 * u + 1) / 3^m % 3 < 2 := by
    rw [← h_u]
    exact hc2
  obtain ⟨m, h_lt, h_ge⟩ := exists_m j hj
  have h_or := cantor_two_mul_add_one u hc1 hc2' m
  rcases h_or with h_or_lt | h_or_eq
  · have : 3^m - 1 ≤ 2 * u := by
      have : 2 * u = 2^(j+1) - 2 := by
        have : 2^(j+1) = 2^j * 2 := by ring
        have : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
        omega
      omega
    omega
  · have h_dvd := div_from_equation u m h_or_eq
    rw [← h_u] at h_dvd
    rcases h_dvd with ⟨q, hq⟩
    have h_q_lt : q < 3 := by
      have h_pow : 3^(m+1) = 3 * 3^m := by ring
      rw [h_pow] at h_ge
      have h_mul_lt : 3^m * q < 3^m * 3 := by omega
      by_contra h_ge3
      push_neg at h_ge3
      have h_mono : 3^m * q ≥ 3^m * 3 := Nat.mul_le_mul_left (3^m) h_ge3
      omega
    have h_q_gt : q > 0 := by
      by_contra h_zero
      push_neg at h_zero
      have : q = 0 := by omega
      rw [this] at hq
      omega
    have h_q_cases : q = 1 ∨ q = 2 := by omega
    rcases h_q_cases with rfl | rfl
    · have : 2^(j+1) - 3^m = 1 := by omega
      exact power_equation_impossible j m hj this
    · have h_odd : (2^(j+1) - 1) % 2 = 1 := by
        have h_pow : 2^(j+1) = 2^j * 2 := by ring
        have h_ge : 2^j ≥ 1 := Nat.one_le_pow j 2 (by omega)
        have h_eq : 2^(j+1) - 1 = 2 * (2^j - 1) + 1 := by omega
        rw [h_eq]
        omega
      have h_even : (3^m * 2) % 2 = 0 := by
        rw [mul_comm]
        omega
      have h_mod_eq : (2^(j+1) - 1) % 2 = (3^m * 2) % 2 := by rw [hq]
      rw [h_odd, h_even] at h_mod_eq
      contradiction

lemma test_mod_mod (x : ℕ) : (x % 6) % 2 = x % 2 := by
  have : 2 ∣ 6 := by decide
  exact Nat.mod_mod_of_dvd x this
