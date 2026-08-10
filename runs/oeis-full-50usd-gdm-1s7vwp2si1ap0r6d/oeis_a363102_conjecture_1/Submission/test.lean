import FormalConjectures.Util.ProblemImports

open Nat Finset

theorem gcd_dvd_mul_gcd (N D p : ℕ) : Nat.gcd N (p * D) ∣ p * Nat.gcd N D := by
  have h1 : Nat.gcd N (p * D) ∣ p * N := dvd_mul_of_dvd_right (Nat.gcd_dvd_left N (p * D)) p
  have h2 : Nat.gcd N (p * D) ∣ p * D := Nat.gcd_dvd_right N (p * D)
  have h3 : Nat.gcd N (p * D) ∣ Nat.gcd (p * N) (p * D) := Nat.dvd_gcd h1 h2
  rw [Nat.gcd_mul_left] at h3
  exact h3

def a_simp (m : ℕ) : ℕ :=
  ((m + 7)^2 - 2) / Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial)

theorem a_simp_dvd_N (m : ℕ) : a_simp m ∣ (m + 7)^2 - 2 :=
  ⟨Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial), by
    dsimp [a_simp]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩

theorem prime_not_m_plus_5 (m p : ℕ) (hp : Nat.Prime p) (hp5 : p = m + 5) : ¬ (p ∣ a_simp m) := by
  intro hdvd
  have h_dvd_N : p ∣ (m + 7)^2 - 2 := dvd_trans hdvd (a_simp_dvd_N m)
  have h_eq : m + 7 = p + 2 := by omega
  rw [h_eq] at h_dvd_N
  have h_alg : (p + 2)^2 - 2 = p * (p + 4) + 2 := by
    have h_sq : (p + 2)^2 = p^2 + 4 * p + 4 := by ring
    have h_ring : p * (p + 4) + 2 = p^2 + 4 * p + 2 := by ring
    rw [h_sq, h_ring]
    omega
  rw [h_alg] at h_dvd_N
  have h_dvd2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_right p (p + 4))).mp h_dvd_N
  have hp2 : p = 2 := by
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd2
    have h_ge : p ≥ 2 := hp.two_le
    omega
  omega

theorem p_dvd_D (m p : ℕ) (hp : Nat.Prime p) (h_le : p ≤ m + 6) (hne5 : p ≠ m + 5) :
  p ∣ 2 * (m + 6) * (m + 4).factorial := by
  have h_cases : p ≤ m + 4 ∨ p = m + 6 := by omega
  rcases h_cases with h_le4 | h_eq6
  · have h_fact : p ∣ (m + 4).factorial := Nat.dvd_factorial hp.pos h_le4
    exact dvd_mul_of_dvd_right h_fact _
  · rw [h_eq6]
    use 2 * (m + 4).factorial
    ring

theorem prime_not_m_plus_6 (m p : ℕ) (hp : Nat.Prime p) (hp6 : p = m + 6) : ¬ (p ∣ a_simp m) := by
  intro hdvd
  have h_dvd_N : p ∣ (m + 7)^2 - 2 := dvd_trans hdvd (a_simp_dvd_N m)
  have h_eq : m + 7 = p + 1 := by omega
  rw [h_eq] at h_dvd_N
  have h_alg : (p + 1)^2 - 2 + 1 = p * (p + 2) := by
    have h_sq : (p + 1)^2 = p^2 + 2 * p + 1 := by ring
    have h_ring : p * (p + 2) = p^2 + 2 * p := by ring
    rw [h_sq, h_ring]
    omega
  have h_dvd_add : p ∣ (p + 1)^2 - 2 + 1 := by
    rw [h_alg]
    exact dvd_mul_right p (p + 2)
  have h_dvd_one : p ∣ 1 := (Nat.dvd_add_right h_dvd_N).mp h_dvd_add
  have hp1 : p = 1 := Nat.eq_one_of_dvd_one h_dvd_one
  have hp_prime : p ≠ 1 := hp.ne_one
  contradiction


theorem odd_of_mul_odd {A B : ℕ} (h : A * B % 2 = 1) : A % 2 = 1 := by
  have h_cases : A % 2 = 0 ∨ A % 2 = 1 := by omega
  rcases h_cases with h0 | h1
  · rcases (Nat.dvd_of_mod_eq_zero h0) with ⟨k, hk⟩
    rw [hk] at h
    have : (2 * k) * B % 2 = 0 := by
      rw [mul_assoc]
      exact Nat.mul_mod_right 2 (k * B)
    omega
  · exact h1

theorem p_pow_step (N D p G : ℕ) (hG : G = Nat.gcd N D) (hdvd : p ∣ N / G) (j : ℕ)
  (hD : p^j ∣ D) (hN : p^j ∣ N) : p^(j+1) ∣ N := by
  have h_gcd : p^j ∣ G := hG ▸ Nat.dvd_gcd hN hD
  rcases h_gcd with ⟨g', hg'⟩
  have h_div : p ∣ N / G := hdvd
  rcases h_div with ⟨q', hq'⟩
  have h_eq : N = G * (N / G) := (Nat.mul_div_cancel' (hG ▸ Nat.gcd_dvd_left N D)).symm
  rw [h_eq, hq', hg']
  use g' * q'
  ring

theorem p_pow_div_induction (m p : ℕ) (_hp : Nat.Prime p) (hdvd : p ∣ a_simp m) (j : ℕ) :
  p^j ∣ 2 * (m + 6) * (m + 4).factorial → p^(j+1) ∣ (m + 7)^2 - 2 := by
  induction j with
  | zero =>
    intro _
    have h_dvdN := a_simp_dvd_N m
    rw [pow_one]
    exact dvd_trans hdvd h_dvdN
  | succ j ih =>
    intro h_D
    have h_D_j : p^j ∣ 2 * (m + 6) * (m + 4).factorial := by
      have h_pow : p^j ∣ p^(j+1) := by
        use p
        ring
      exact dvd_trans h_pow h_D
    have h_N_j1 : p^(j+1) ∣ (m + 7)^2 - 2 := ih h_D_j
    exact p_pow_step ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial) p (Nat.gcd ((m + 7)^2 - 2) (2 * (m + 6) * (m + 4).factorial)) rfl hdvd (j+1) h_D h_N_j1


theorem prime_factor_cases (m : ℕ) (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ a_simp m) : p ≥ m + 7 ∨ a_simp m = p := by
  have h_dec : Decidable (p ≥ m + 7 ∨ a_simp m = p) := Classical.dec _
  cases h_dec with
  | isTrue h => exact h
  | isFalse h =>
    exfalso
    have h_lt : p < m + 7 := by omega
    have h_ne : a_simp m ≠ p := by omega
    have h_le : p ≤ m + 6 := by omega
    have h_ne5 : p ≠ m + 5 := by
      intro h_eq
      exact prime_not_m_plus_5 m p hp h_eq hdvd
    have h_ne6 : p ≠ m + 6 := by
      intro h_eq
      exact prime_not_m_plus_6 m p hp h_eq hdvd
    have h_le4 : p ≤ m + 4 := by omega
    have h_dvdD : p ∣ 2 * (m + 6) * (m + 4).factorial := p_dvd_D m p hp h_le h_ne5
    have h_pow1 : p^1 ∣ 2 * (m + 6) * (m + 4).factorial := by
      rw [pow_one]
      exact h_dvdD
    have h_pow2 : p^2 ∣ (m + 7)^2 - 2 := p_pow_div_induction m p hp hdvd 1 h_pow1
    sorry

theorem a_simp_pos (m : ℕ) : 0 < a_simp m := by
  dsimp [a_simp]
  apply Nat.div_pos
  · have h : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
    have h1 : 0 < (m + 7)^2 - 2 := by rw [h]; omega
    exact Nat.gcd_le_left _ h1
  · have h : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
    have h1 : 0 < (m + 7)^2 - 2 := by rw [h]; omega
    exact Nat.gcd_pos_of_pos_left _ h1

theorem exists_two_prime_factors_of_not_prime_or_one {q : ℕ} (hq1 : q ≠ 1) (hq2 : ¬ Nat.Prime q) :
  ∃ p1 p2, Nat.Prime p1 ∧ Nat.Prime p2 ∧ p1 * p2 ∣ q := by
  by_cases hq0 : q = 0
  · use 2, 2
    refine ⟨Nat.prime_two, Nat.prime_two, ?_⟩
    rw [hq0]
    exact dvd_zero _
  · have hq_gt_one : 1 < q := by omega
    have h_not_irr : ¬ Irreducible q := hq2
    have h_unit (x : ℕ) : IsUnit x ↔ x = 1 := isUnit_iff_dvd_one.trans Nat.dvd_one
    have h_comp : ∃ a b, q = a * b ∧ a ≠ 1 ∧ b ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply h_not_irr
      have h_not_unit : ¬ IsUnit q := by
        rw [h_unit]
        exact hq1
      refine ⟨h_not_unit, ?_⟩
      intro a b hab
      have h_or := hc a b hab
      rw [h_unit, h_unit]
      by_cases ha1 : a = 1
      · left; exact ha1
      · right; exact h_or ha1
    rcases h_comp with ⟨a, b, hab, ha, hb⟩
    have ⟨p1, hp1_prime, hp1_dvd⟩ := Nat.exists_prime_and_dvd ha
    have ⟨p2, hp2_prime, hp2_dvd⟩ := Nat.exists_prime_and_dvd hb
    use p1, p2
    refine ⟨hp1_prime, hp2_prime, ?_⟩
    rw [hab]
    exact mul_dvd_mul hp1_dvd hp2_dvd

theorem oeis_a363102_conjecture_1_test (m : ℕ) : a_simp m = 1 ∨ Nat.Prime (a_simp m) := by
  have h_dec : Decidable (a_simp m = 1 ∨ Nat.Prime (a_simp m)) := Classical.dec _
  cases h_dec with
  | isTrue h => exact h
  | isFalse h =>
    exfalso
    have ha1 : a_simp m ≠ 1 := by
      intro h1
      apply h
      left; exact h1
    have ha2 : ¬ Nat.Prime (a_simp m) := by
      intro h2
      apply h
      right; exact h2
    rcases (exists_two_prime_factors_of_not_prime_or_one ha1 ha2) with ⟨p1, p2, hp1, hp2, hdvd⟩
    have hdvd1 : p1 ∣ a_simp m := by
      rcases hdvd with ⟨k, hk⟩
      rw [hk]
      use p2 * k
      ring
    have hdvd2 : p2 ∣ a_simp m := by
      rcases hdvd with ⟨k, hk⟩
      rw [hk]
      use p1 * k
      ring
    have h_cases1 := prime_factor_cases m p1 hp1 hdvd1
    have h_cases2 := prime_factor_cases m p2 hp2 hdvd2
    have hp1_ge : p1 ≥ m + 7 := by
      rcases h_cases1 with h_ge | h_eq
      · exact h_ge
      · exfalso
        rw [h_eq] at ha2
        exact ha2 hp1
    have hp2_ge : p2 ≥ m + 7 := by
      rcases h_cases2 with h_ge | h_eq
      · exact h_ge
      · exfalso
        rw [h_eq] at ha2
        exact ha2 hp2
    have h_prod : p1 * p2 ≥ (m + 7)^2 := by
      nlinarith
    have h_a_le : a_simp m ≤ (m + 7)^2 - 2 := by
      have h_dvdN := a_simp_dvd_N m
      have hN_pos : 0 < (m + 7)^2 - 2 := by
        have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
        omega
      exact Nat.le_of_dvd hN_pos h_dvdN
    have h_prod_le : p1 * p2 ≤ a_simp m := by
      have h_pos : 0 < a_simp m := a_simp_pos m
      exact Nat.le_of_dvd h_pos hdvd
    have h_contra : (m + 7)^2 ≤ (m + 7)^2 - 2 :=
      le_trans h_prod (le_trans h_prod_le h_a_le)
    have h_false : (m + 7)^2 > (m + 7)^2 - 2 := by
      have : (m + 7)^2 = m^2 + 14 * m + 49 := by ring
      omega
    omega