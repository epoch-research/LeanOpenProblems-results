import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_next
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


theorem cast_mod_10_to_5 (p : ℕ) : (p : ZMod 5) = ((p % 10 : ℕ) : ZMod 5) := by
  have h : p = 5 * (2 * (p / 10)) + p % 10 := by omega
  nth_rw 1 [h]
  push_cast
  have h5 : (5 : ZMod 5) = 0 := rfl
  rw [h5]
  ring

theorem isSquare_p_zmod_5 (p : ℕ) (hp_mod : p % 10 = 1 ∨ p % 10 = 9) : IsSquare (p : ZMod 5) := by
  rw [cast_mod_10_to_5 p]
  rcases hp_mod with hp_mod1 | hp_mod9
  · rw [hp_mod1]
    use 1
    rfl
  · rw [hp_mod9]
    use 2
    rfl

theorem exists_sq_eq_five_zmod (p : ℕ) (hp_prime : p.Prime) (hp_mod : p % 10 = 1 ∨ p % 10 = 9) :
    ∃ x : ZMod p, x^2 = 5 := by
  have h_fact_p : Fact p.Prime := ⟨hp_prime⟩
  have h_fact_five : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    revert hp_mod
    decide
  have h_sq_five : IsSquare (p : ZMod 5) := isSquare_p_zmod_5 p hp_mod
  have h_eq : IsSquare (p : ZMod 5) ↔ IsSquare (5 : ZMod p) :=
    ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) rfl hp_ne_two
  have h_sq : IsSquare (5 : ZMod p) := h_eq.mp h_sq_five
  rcases h_sq with ⟨x, hx⟩
  use x
  rw [pow_two]
  exact hx.symm

theorem exists_n_mod_p (p : ℕ) (hp_prime : p.Prime) (hp_mod : p % 10 = 1 ∨ p % 10 = 9) :
    ∃ n : ℕ, n < p ∧ n ≥ 3 ∧ ((n : ℤ)^2 + 2 * (n : ℤ) - 4) % (p : ℤ) = 0 := by
  obtain ⟨x, hx⟩ := exists_sq_eq_five_zmod p hp_prime hp_mod
  have hp_ge_11 : p ≥ 11 := by
    by_contra! h
    interval_cases p
    · exact Nat.not_prime_zero hp_prime
    · exact Nat.not_prime_one hp_prime
    · revert hp_mod; decide
    · revert hp_mod; decide
    · revert hp_prime; decide
    · revert hp_mod; decide
    · revert hp_prime; decide
    · revert hp_mod; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
    · revert hp_prime; decide
  have h_nz_p : NeZero p := ⟨by omega⟩
  have hdvd : (p : ℤ) ∣ (x.val : ℤ)^2 - 5 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have h_coe : (x.val : ZMod p) = x := by
      rw [ZMod.natCast_val x, ZMod.cast_id]
    rw [h_coe]
    rw [hx]
    ring
  -- Now we show x.val ≥ 4
  have hx_val_ge_4 : x.val ≥ 4 := by
    by_contra! h
    have h_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by omega
    rcases h_val with h0 | h1 | h2 | h3
    · rw [h0] at hdvd
      have : ((0 : ℕ) : ℤ)^2 - 5 = -5 := rfl
      rw [this] at hdvd
      have hdvd' : p ∣ 5 := by exact_mod_cast dvd_neg.mp hdvd
      have hle : p ≤ 5 := Nat.le_of_dvd (by decide) hdvd'
      omega
    · rw [h1] at hdvd
      have : ((1 : ℕ) : ℤ)^2 - 5 = -4 := rfl
      rw [this] at hdvd
      have hdvd' : p ∣ 4 := by exact_mod_cast dvd_neg.mp hdvd
      have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hdvd'
      omega
    · rw [h2] at hdvd
      have : ((2 : ℕ) : ℤ)^2 - 5 = -1 := rfl
      rw [this] at hdvd
      have hdvd' : p ∣ 1 := by exact_mod_cast dvd_neg.mp hdvd
      have hle : p ≤ 1 := Nat.le_of_dvd (by decide) hdvd'
      omega
    · rw [h3] at hdvd
      have : ((3 : ℕ) : ℤ)^2 - 5 = 4 := rfl
      rw [this] at hdvd
      have hdvd' : p ∣ 4 := by exact_mod_cast hdvd
      have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hdvd'
      omega
  -- Since x.val ≥ 4, let n = x.val - 1
  -- We have n ≥ 3 and n < p - 1 < p
  have h_x_val_lt_p : x.val < p := ZMod.val_lt x
  let n := x.val - 1
  use n
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · -- we want to show ((n : ℤ)^2 + 2 * (n : ℤ) - 4) % (p : ℤ) = 0
    have hn_eq : (n : ℤ) + 1 = x.val := by
      omega
    have h_poly : (n : ℤ)^2 + 2 * (n : ℤ) - 4 = (x.val : ℤ)^2 - 5 := by
      rw [← hn_eq]
      ring
    rw [h_poly]
    exact Int.emod_eq_zero_of_dvd hdvd

def N_rec (n : ℕ) (k : ℕ) : ℤ :=
  if n ≤ k then 4
  else if k = n - 1 then 5 * (n : ℤ) - 4
  else (k : ℤ) * N_rec n (k + 1) - ((k : ℤ) + 1) * N_rec n (k + 2)
termination_by n - k

lemma continued_fraction_denominator_ge_sub_two (n k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 1) :
  continued_fraction_denominator n k ≥ (k : ℚ) - 2 := by
  rw [continued_fraction_denominator]
  have hn2 : ¬ (n ≤ 2) := by omega
  have hk_range : 2 ≤ k ∧ k ≤ n - 1 := by omega
  split_ifs
  · -- k = n - 1
    have hn_ge : (n : ℚ) ≥ 4 := by
      have : n ≥ 4 := by omega
      exact_mod_cast this
    linarith
  · -- k < n - 1
    have hk1 : 3 ≤ k + 1 ∧ k + 1 ≤ n - 1 := by omega
    have ih := continued_fraction_denominator_ge_sub_two n (k + 1) hk1
    set R_next := continued_fraction_denominator n (k + 1)
    push_cast at ih
    push_cast
    have hk_q : (k : ℚ) ≥ 3 := by
      have : 3 ≤ k := hk.1
      exact_mod_cast this
    have hR_pos : R_next > 0 := by linarith
    have h_div : ((k : ℚ) + 1) / R_next ≤ 2 := by
      rw [div_le_iff₀ hR_pos]
      linarith
    linarith
termination_by n - k

lemma continued_fraction_denominator_three_pos (n : ℕ) (hn : n ≥ 4) :
  continued_fraction_denominator n 3 > 0 := by
  have h_ge := continued_fraction_denominator_ge_sub_two n 3 ⟨by decide, by omega⟩
  norm_num at h_ge
  linarith

lemma continued_fraction_denominator_eq_N_rec (n k : ℕ) (hk : 2 ≤ k ∧ k ≤ n - 1) :
  continued_fraction_denominator n k = (N_rec n k : ℚ) / (N_rec n (k+1) : ℚ) := by
  rw [continued_fraction_denominator]
  have hn2 : ¬ (n ≤ 2) := by omega
  split_ifs with h_eq
  · -- k = n - 1
    have h_eq_n : k + 1 = n := by omega
    have h_N_rec_k : N_rec n k = 5 * (n : ℤ) - 4 := by
      rw [N_rec]
      have h_not_le : ¬ (n ≤ k) := by omega
      rw [if_neg h_not_le, if_pos (by omega)]
    have h_N_rec_kp1 : N_rec n (k + 1) = 4 := by
      rw [h_eq_n, N_rec]
      rw [if_pos (by omega)]
    rw [h_N_rec_k, h_N_rec_kp1]
    push_cast
    have hk_eq : (k : ℚ) = (n : ℚ) - 1 := by
      have h1 : (k : ℤ) = (n : ℤ) - 1 := by omega
      exact_mod_cast h1
    rw [hk_eq]
    ring
  · -- k < n - 1
    have hk1 : 2 ≤ k + 1 ∧ k + 1 ≤ n - 1 := by omega
    have ih := continued_fraction_denominator_eq_N_rec n (k + 1) hk1
    set R_next := continued_fraction_denominator n (k + 1)
    have h_ge_3 : 3 ≤ k + 1 ∧ k + 1 ≤ n - 1 := by omega
    have h_ge := continued_fraction_denominator_ge_sub_two n (k + 1) h_ge_3
    have hk_q : (k : ℚ) ≥ 2 := by
      have : 2 ≤ k := hk.1
      exact_mod_cast this
    have h_R_next_pos : R_next > 0 := by
      push_cast at h_ge
      linarith
    have hB_ne : (N_rec n (k+2) : ℚ) ≠ 0 := by
      intro hB
      rw [hB, div_zero] at ih
      rw [ih] at h_R_next_pos
      linarith
    have h_R_next_ne : R_next ≠ 0 := by linarith
    have h_eq_mul : R_next * (N_rec n (k + 2) : ℚ) = (N_rec n (k + 1) : ℚ) := by
      rw [ih]
      exact div_mul_cancel₀ _ hB_ne
    have h_div_cancel : (N_rec n (k + 1) : ℚ) / R_next = (N_rec n (k + 2) : ℚ) := by
      rw [← h_eq_mul]
      rw [mul_comm]
      exact mul_div_cancel_right₀ _ h_R_next_ne
    have h_N_rec_k : N_rec n k = (k : ℤ) * N_rec n (k+1) - ((k : ℤ) + 1) * N_rec n (k+2) := by
      rw [N_rec]
      have h_not_le : ¬ (n ≤ k) := by omega
      have h_not_eq : ¬ (k = n - 1) := by omega
      rw [if_neg h_not_le, if_neg h_not_eq]
    have h_mul_eq : ((k : ℚ) - (k + 1 : ℚ) / R_next) * (N_rec n (k+1) : ℚ) = (N_rec n k : ℚ) := by
      calc ((k : ℚ) - (k + 1 : ℚ) / R_next) * (N_rec n (k+1) : ℚ)
        _ = (k : ℚ) * (N_rec n (k+1) : ℚ) - ((k + 1 : ℚ) / R_next) * (N_rec n (k+1) : ℚ) := by ring
        _ = (k : ℚ) * (N_rec n (k+1) : ℚ) - (k + 1 : ℚ) * ((N_rec n (k+1) : ℚ) / R_next) := by ring
        _ = (k : ℚ) * (N_rec n (k+1) : ℚ) - (k + 1 : ℚ) * (N_rec n (k+2) : ℚ) := by rw [h_div_cancel]
        _ = (N_rec n k : ℚ) := by
          rw [h_N_rec_k]
          push_cast
          ring
    have h_A_ne : (N_rec n (k+1) : ℚ) ≠ 0 := by
      intro hA
      rw [ih, hA, zero_div] at h_R_next_pos
      linarith
    rw [← h_mul_eq]
    rw [mul_div_cancel_right₀ _ h_A_ne]
termination_by n - k

lemma N_rec_two_eq_m_aux (n : ℕ) (d : ℕ) :
  ∀ m : ℕ, 2 ≤ m → m ≤ n - 1 → m - 2 = d →
  N_rec n 2 = (m - 1 : ℤ) * N_rec n m - ((m : ℤ)^2 - 2 * (m : ℤ)) * N_rec n (m + 1) := by
  induction d with
  | zero =>
    intro m hm2 hmn hd
    have hm : m = 2 := by omega
    subst hm
    ring
  | succ d ih =>
    intro m hm2 hmn hd
    let m' := m - 1
    have hm'_eq : m = m' + 1 := by omega
    have hm2' : 2 ≤ m' := by omega
    have hmn' : m' ≤ n - 1 := by omega
    have h_m'_d : m' - 2 = d := by omega
    have ih' := ih m' hm2' hmn' h_m'_d
    have h_N_rec_m' : N_rec n m' = (m' : ℤ) * N_rec n (m' + 1) - ((m' : ℤ) + 1) * N_rec n (m' + 2) := by
      rw [N_rec]
      have h_not_le : ¬ (n ≤ m') := by omega
      have h_not_eq : ¬ (m' = n - 1) := by omega
      rw [if_neg h_not_le, if_neg h_not_eq]
    rw [h_N_rec_m'] at ih'
    rw [ih']
    rw [hm'_eq]
    push_cast
    ring

lemma N_rec_two_eq_m (n : ℕ) (m : ℕ) (hm : 2 ≤ m ∧ m ≤ n - 1) :
  N_rec n 2 = (m - 1 : ℤ) * N_rec n m - ((m : ℤ)^2 - 2 * (m : ℤ)) * N_rec n (m + 1) := by
  exact N_rec_two_eq_m_aux n (m - 2) m hm.1 hm.2 rfl

theorem N_rec_two_eq_poly (n : ℕ) (hn : n ≥ 3) :
  N_rec n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have hm : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := by omega
  have h_eq := N_rec_two_eq_m n (n - 1) hm
  have h_nat : n - 1 + 1 = n := by omega
  have h_rec_n : N_rec n n = 4 := by
    rw [N_rec]
    rw [if_pos (by omega)]
  have h_rec_nm1 : N_rec n (n - 1) = 5 * (n : ℤ) - 4 := by
    rw [N_rec]
    have h_not_le : ¬ (n ≤ n - 1) := by omega
    rw [if_neg h_not_le, if_pos (by omega)]
  rw [h_nat, h_rec_nm1, h_rec_n] at h_eq
  have hn_cast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hn_cast] at h_eq
  rw [h_eq]
  ring

lemma not_dvd_N_rec_step (n : ℕ) (hn : n ≥ 3) (p : ℕ) (hp : p.Prime) (hp11 : p ≥ 11) (h_n_lt : n < p) (k : ℕ) (hk : 2 ≤ k ∧ k < n)
  (hdvd1 : (p : ℤ) ∣ N_rec n k) (hdvd2 : (p : ℤ) ∣ N_rec n (k+1)) : False := by
  by_cases h_eq : k = n - 1
  · have h_eq_n : k + 1 = n := by omega
    have h_rec_n : N_rec n (k + 1) = 4 := by
      rw [h_eq_n, N_rec]
      rw [if_pos (by omega)]
    rw [h_rec_n] at hdvd2
    have hp_dvd_4 : p ∣ 4 := by
      exact_mod_cast hdvd2
    have hp_le_4 : p ≤ 4 := Nat.le_of_dvd (by decide) hp_dvd_4
    omega
  · have h_not_le : ¬ (n ≤ k) := by omega
    have h_not_eq : ¬ (k = n - 1) := by omega
    have h_rec : N_rec n k = (k : ℤ) * N_rec n (k+1) - ((k : ℤ) + 1) * N_rec n (k+2) := by
      rw [N_rec]
      rw [if_neg h_not_le, if_neg h_not_eq]
    have hdvd3_mul : (p : ℤ) ∣ ((k : ℤ) + 1) * N_rec n (k+2) := by
      have h_eq_diff : ((k : ℤ) + 1) * N_rec n (k+2) = (k : ℤ) * N_rec n (k+1) - N_rec n k := by linarith
      rw [h_eq_diff]
      exact dvd_sub (dvd_mul_of_dvd_right hdvd2 _) hdvd1
    have h_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hdvd_or := (h_prime.dvd_mul).mp hdvd3_mul
    rcases hdvd_or with hdvd_k1 | hdvd_kp2
    · have hk1_pos : (k : ℤ) + 1 > 0 := by omega
      have hk1_lt : (k : ℤ) + 1 < (p : ℤ) := by omega
      have h_not_dvd : ¬ ((p : ℤ) ∣ (k : ℤ) + 1) := by
        intro h_dvd
        have h_le : (p : ℤ) ≤ (k : ℤ) + 1 := Int.le_of_dvd hk1_pos h_dvd
        omega
      exact h_not_dvd hdvd_k1
    · have hk2 : 2 ≤ k + 1 ∧ k + 1 < n := by omega
      exact not_dvd_N_rec_step n hn p hp hp11 h_n_lt (k+1) hk2 hdvd2 hdvd_kp2
termination_by n - k

lemma not_dvd_N_rec_three (n : ℕ) (hn : n ≥ 3) (p : ℕ) (hp : p.Prime) (hp11 : p ≥ 11) (h_n_lt : n < p)
  (hdvd1 : (p : ℤ) ∣ N_rec n 2) (hdvd2 : (p : ℤ) ∣ N_rec n 3) : False := by
  exact not_dvd_N_rec_step n hn p hp hp11 h_n_lt 2 ⟨by decide, by omega⟩ hdvd1 hdvd2

lemma m_dvd_N_rec_of_m_dvd_N_rec_two_aux (n : ℕ) (hn : n ≥ 3) (m : ℤ) (hm : 2 ≤ m ∧ m ≤ (n : ℤ) - 1) (h_dvd : m ∣ N_rec n 2) (d : ℕ) :
  ∀ k : ℕ, m.natAbs - k = d → 2 ≤ k → k ≤ m.natAbs → m ∣ N_rec n k := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk_eq hk2 hkm
    let m_nat := m.natAbs
    by_cases hk_m : k = m_nat
    · subst hk_m
      have hm_nat_le : m_nat ≤ n - 1 := by omega
      have h_eq := N_rec_two_eq_m n m_nat ⟨by omega, hm_nat_le⟩
      have h_m_cast : (m_nat : ℤ) = m := by omega
      rw [h_m_cast] at h_eq
      have hdvd_term : m ∣ (m^2 - 2 * m) * N_rec n (m_nat + 1) := by
        have h_eq_prod : m^2 - 2 * m = m * (m - 2) := by ring
        rw [h_eq_prod]
        exact dvd_mul_of_dvd_left (dvd_mul_right m (m - 2)) _
      have hdvd_mul : m ∣ (m - 1 : ℤ) * N_rec n m_nat := by
        have h_eq_sum : (m - 1 : ℤ) * N_rec n m_nat = N_rec n 2 + (m^2 - 2 * m) * N_rec n (m_nat + 1) := by linarith
        rw [h_eq_sum]
        exact dvd_add h_dvd hdvd_term
      have h_coprime : IsCoprime m (m - 1) := by
        use 1, -1
        ring
      have hdvd_mul' : m ∣ N_rec n m_nat * (m - 1) := by
        rw [mul_comm]
        exact hdvd_mul
      exact IsCoprime.dvd_of_dvd_mul_right h_coprime hdvd_mul'
    · by_cases hk_m1 : k = m_nat - 1
      · subst hk_m1
        have hdvd_N_rec_m : m ∣ N_rec n m_nat := by
          have h_eq_zero : m_nat - m_nat = 0 := by omega
          exact ih 0 (by omega) m_nat h_eq_zero (by omega) (by omega)
        have h_rec_nm1 : N_rec n (m_nat - 1) = (m_nat - 1 : ℤ) * N_rec n m_nat - m * N_rec n (m_nat + 1) := by
          rw [N_rec]
          have h_not_le : ¬ (n ≤ m_nat - 1) := by omega
          have h_not_eq : ¬ (m_nat - 1 = n - 1) := by omega
          rw [if_neg h_not_le, if_neg h_not_eq]
          have h_k1 : (m_nat - 1 : ℕ) + 1 = m_nat := by omega
          have h_k2 : (m_nat - 1 : ℕ) + 2 = m_nat + 1 := by omega
          rw [h_k1, h_k2]
          have h_coeff : (((m_nat - 1 : ℕ) : ℤ) + 1) = m := by omega
          rw [h_coeff]
          have h_sub : ((m_nat - 1 : ℕ) : ℤ) = (m_nat : ℤ) - 1 := by omega
          rw [h_sub]
        have hdvd_term1 : m ∣ (m_nat - 1 : ℤ) * N_rec n m_nat :=
          dvd_mul_of_dvd_right hdvd_N_rec_m _
        have hdvd_term2 : m ∣ m * N_rec n (m_nat + 1) :=
          dvd_mul_right m _
        rw [h_rec_nm1]
        exact dvd_sub hdvd_term1 hdvd_term2
      · have hdvd_kp1 : m ∣ N_rec n (k + 1) := by
          have h_lt : m_nat - (k + 1) < d := by omega
          exact ih (m_nat - (k + 1)) h_lt (k + 1) rfl (by omega) (by omega)
        have hdvd_kp2 : m ∣ N_rec n (k + 2) := by
          have h_lt : m_nat - (k + 2) < d := by omega
          exact ih (m_nat - (k + 2)) h_lt (k + 2) rfl (by omega) (by omega)
        have h_not_le : ¬ (n ≤ k) := by omega
        have h_not_eq : ¬ (k = n - 1) := by omega
        have h_rec : N_rec n k = (k : ℤ) * N_rec n (k+1) - ((k : ℤ) + 1) * N_rec n (k+2) := by
          rw [N_rec]
          rw [if_neg h_not_le, if_neg h_not_eq]
        rw [h_rec]
        exact dvd_sub (dvd_mul_of_dvd_right hdvd_kp1 _) (dvd_mul_of_dvd_right hdvd_kp2 _)

lemma m_dvd_N_rec_of_m_dvd_N_rec_two (n : ℕ) (hn : n ≥ 3) (m : ℤ) (hm : 2 ≤ m ∧ m ≤ (n : ℤ) - 1) (h_dvd : m ∣ N_rec n 2) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ m.natAbs) :
  m ∣ N_rec n k := by
  exact m_dvd_N_rec_of_m_dvd_N_rec_two_aux n hn m hm h_dvd (m.natAbs - k) k rfl hk.1 hk.2

lemma A363347_eq_p (n : ℕ) (hn : n ≥ 3) (p : ℕ) (hp : p.Prime) (hp11 : p ≥ 11) (h_n_lt : n < p)
  (hdvd : (p : ℤ) ∣ N_rec n 2) : A363347 n = p := by
  have h_cf : continued_fraction_denominator n 2 = (N_rec n 2 : ℚ) / (N_rec n 3 : ℚ) :=
    continued_fraction_denominator_eq_N_rec n 2 ⟨by decide, by omega⟩
  have h_A : A363347 n = (continued_fraction_denominator n 2).num.natAbs := by
    rw [A363347]
    rw [if_neg (by omega)]
  have h_div_eq : (N_rec n 2 : ℚ) / (N_rec n 3 : ℚ) = (N_rec n 2) /. (N_rec n 3) := by
    rw [Rat.divInt_eq_div]
  have h_A_num : (continued_fraction_denominator n 2).num = ((N_rec n 2) /. (N_rec n 3)).num := by
    rw [h_cf, h_div_eq]
  let q := N_rec n 2 / (p : ℤ)
  have h_N2_eq : N_rec n 2 = q * (p : ℤ) := by
    rw [Int.ediv_mul_cancel hdvd]
  have h_N2_pos : N_rec n 2 > 0 := by
    rw [N_rec_two_eq_poly n hn]
    have hn_z : (n : ℤ) ≥ 3 := by omega
    nlinarith
  have h_q_pos : q > 0 := by
    have hp_pos : (p : ℤ) > 0 := by omega
    nlinarith
  have h_q_ne_2 : q ≠ 2 := by
    intro hq2
    have h_N2_eq_2p : N_rec n 2 = 2 * (p : ℤ) := by rw [h_N2_eq, hq2]
    rw [N_rec_two_eq_poly n hn] at h_N2_eq_2p
    have h_even_sq : ((n : ℤ)^2) % 2 = 0 := by
      have : (n : ℤ)^2 = 2 * (p : ℤ) - 2 * (n : ℤ) + 4 := by omega
      rw [this]
      omega
    have h_even_n : (n : ℤ) % 2 = 0 := by
      have h_not : (n : ℤ) % 2 ≠ 1 := by
        intro h_odd
        have h_odd_sq : ((n : ℤ)^2) % 2 = 1 := by
          have h_sq_eq : (n : ℤ)^2 = (n : ℤ) * (n : ℤ) := by ring
          rw [h_sq_eq, Int.mul_emod, h_odd]
          rfl
        omega
      omega
    let k := (n : ℤ) / 2
    have hn_eq_2k : (n : ℤ) = 2 * k := by omega
    have hp_even : (p : ℤ) % 2 = 0 := by
      have h_eq_p : (p : ℤ) = 2 * (k^2 + k - 1) := by
        have h_double : 2 * (p : ℤ) = 2 * (2 * k^2 + 2 * k - 2) := by
          calc 2 * (p : ℤ)
            _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := h_N2_eq_2p.symm
            _ = (2 * k)^2 + 2 * (2 * k) - 4 := by rw [hn_eq_2k]
            _ = 2 * (2 * k^2 + 2 * k - 2) := by ring
        linarith
      rw [h_eq_p]
      omega
    have hp_even_nat : p % 2 = 0 := by
      exact_mod_cast hp_even
    have hp_odd_nat : p % 2 = 1 := by
      have hp_ne_2 : p ≠ 2 := by omega
      exact (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp_ne_2
    omega
  have h_q_cases : q = 1 ∨ q ≥ 3 := by omega
  have h_q_dvd_3 : q ∣ N_rec n 3 := by
    rcases h_q_cases with hq1 | hq3
    · rw [hq1]; exact one_dvd _
    · have hqm_le : q ≤ (n : ℤ) - 1 := by
        by_contra! hg
        have h_q_ge_n : q ≥ (n : ℤ) := by omega
        by_cases hn4 : n ≥ 4
        · have hn_z : (n : ℤ) ≥ 4 := by omega
          have h_pn1 : (p : ℤ) ≥ (n : ℤ) + 1 := by omega
          have h_poly_val : N_rec n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := N_rec_two_eq_poly n hn
          have h_qp_eq : q * (p : ℤ) = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
            rw [← h_N2_eq, h_poly_val]
          have h_np_le_qp : (n : ℤ) * (p : ℤ) ≤ q * (p : ℤ) := by
            nlinarith [h_q_ge_n, h_pn1]
          have h_np_lt : (n : ℤ) * (p : ℤ) < (n : ℤ) * ((n : ℤ) + 2) := by
            linarith [h_qp_eq, h_np_le_qp]
          have hp_lt_n2 : (p : ℤ) < (n : ℤ) + 2 := by
            have : (n : ℤ) * (p : ℤ) < (n : ℤ) * ((n : ℤ) + 2) := h_np_lt
            nlinarith [hn_z]
          have hp_eq_n1 : (p : ℤ) = (n : ℤ) + 1 := by omega
          have h_qp_eq' : q * ((n : ℤ) + 1) = ((n : ℤ) + 1)^2 - 5 := by
            calc q * ((n : ℤ) + 1)
              _ = q * (p : ℤ) := by rw [hp_eq_n1]
              _ = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := h_qp_eq
              _ = ((n : ℤ) + 1)^2 - 5 := by ring
          have h_div_five : ((n : ℤ) + 1) ∣ 5 := by
            have : q * ((n : ℤ) + 1) - ((n : ℤ) + 1)^2 = -5 := by linarith [h_qp_eq']
            have h_dvd_neg_five : ((n : ℤ) + 1) ∣ -5 := by
              rw [← this]
              exact dvd_sub (dvd_mul_left _ _) (dvd_pow_self _ (by decide))
            exact dvd_neg.mp h_dvd_neg_five
          have h_div_five_nat : (n + 1) ∣ 5 := by
            exact_mod_cast h_div_five
          have h_le_five : n + 1 ≤ 5 := Nat.le_of_dvd (by decide) h_div_five_nat
          omega
        · have hn3_eq : n = 3 := by omega
          have h_poly_val : N_rec n 2 = 11 := by
            rw [N_rec_two_eq_poly n hn, hn3_eq]
            rfl
          have h_qp_11 : q * (p : ℤ) = 11 := by
            rw [← h_N2_eq, h_poly_val]
          have hp11' : (p : ℤ) = 11 := by
            have : p ∣ 11 := by
              have hdvd' : (p : ℤ) ∣ 11 := by
                rw [← h_poly_val]
                exact hdvd
              exact_mod_cast hdvd'
            have : p = 11 := Nat.Prime.eq_one_or_self_of_dvd (by decide) p this |>.resolve_left (by omega)
            exact_mod_cast this
          rw [hp11'] at h_qp_11
          have hq1 : q = 1 := by linarith
          omega
      have hq_nat : q.natAbs = q := by omega
      have hq_nat_range : 2 ≤ q.natAbs ∧ q.natAbs ≤ n - 1 := by omega
      have h_dvd_q : q ∣ N_rec n 2 := by
        rw [h_N2_eq]
        exact dvd_mul_right q (p : ℤ)
      have h_dvd_3 := m_dvd_N_rec_of_m_dvd_N_rec_two n hn q ⟨by omega, by omega⟩ h_dvd_q 3 ⟨by decide, by omega⟩
      exact h_dvd_3
  have h3_ne_zero : N_rec n 3 ≠ 0 := by
    by_cases hn4 : n ≥ 4
    · intro h3
      have h_cf3 : continued_fraction_denominator n 3 = (N_rec n 3 : ℚ) / (N_rec n 4 : ℚ) :=
        continued_fraction_denominator_eq_N_rec n 3 ⟨by decide, by omega⟩
      rw [h3] at h_cf3
      push_cast at h_cf3
      rw [zero_div] at h_cf3
      have h_pos := continued_fraction_denominator_three_pos n hn4
      rw [h_cf3] at h_pos
      linarith
    · have hn3_eq : n = 3 := by omega
      rw [hn3_eq, N_rec]
      rw [if_pos (by omega)]
      decide
  have h_gcd_eq : (N_rec n 3).gcd (N_rec n 2) = q.natAbs := by
    let g := (N_rec n 3).gcd (N_rec n 2)
    have hq3_nat : q.natAbs ∣ (N_rec n 3).natAbs := Int.natAbs_dvd_natAbs.mpr h_q_dvd_3
    have h_dvd_q : q ∣ N_rec n 2 := by
      rw [h_N2_eq]
      exact dvd_mul_right q (p : ℤ)
    have hq2_nat : q.natAbs ∣ (N_rec n 2).natAbs := Int.natAbs_dvd_natAbs.mpr h_dvd_q
    have hq_dvd_g : q.natAbs ∣ g := Nat.dvd_gcd hq3_nat hq2_nat
    let g' := g / q.natAbs
    have h_g_eq : g = q.natAbs * g' := (Nat.mul_div_cancel' hq_dvd_g).symm
    have h_g'_dvd_p : g' ∣ p := by
      have h_g_dvd : g ∣ (N_rec n 2).natAbs := Int.gcd_dvd_natAbs_right (N_rec n 3) (N_rec n 2)
      rw [h_g_eq, h_N2_eq, Int.natAbs_mul] at h_g_dvd
      have hp_natCast : (p : ℤ).natAbs = p := by omega
      rw [hp_natCast] at h_g_dvd
      have h_q_pos_nat : q.natAbs > 0 := by omega
      exact (Nat.mul_dvd_mul_iff_left h_q_pos_nat).mp h_g_dvd
    have h_g'_cases : g' = 1 ∨ g' = p := Nat.Prime.eq_one_or_self_of_dvd hp g' h_g'_dvd_p
    rcases h_g'_cases with hg1 | hgp
    · rw [hg1, mul_one] at h_g_eq
      exact h_g_eq
    · have h_g_dvd_3 : g ∣ (N_rec n 3).natAbs := Int.gcd_dvd_natAbs_left (N_rec n 3) (N_rec n 2)
      have hp_dvd_3 : p ∣ (N_rec n 3).natAbs := by
        rw [h_g_eq, hgp] at h_g_dvd_3
        exact dvd_of_mul_left_dvd h_g_dvd_3
      have hp_dvd_3_int : (p : ℤ) ∣ N_rec n 3 := by
        have h_dvd_abs : (p : ℤ).natAbs ∣ (N_rec n 3).natAbs := by
          have hp_natCast : (p : ℤ).natAbs = p := by omega
          rw [hp_natCast]
          exact hp_dvd_3
        exact Int.natAbs_dvd_natAbs.mp h_dvd_abs
      exfalso
      exact not_dvd_N_rec_three n hn p hp hp11 h_n_lt hdvd hp_dvd_3_int
  rw [h_A, h_A_num, Rat.num_divInt]
  rw [h_gcd_eq]
  have h_q_cast : (q.natAbs : ℤ) = q := by omega
  rw [h_q_cast]
  have h_sign_abs : (N_rec n 3).sign.natAbs = 1 := by
    exact Int.natAbs_sign_of_ne_zero h3_ne_zero
  rw [h_N2_eq]
  have h_div_q : (N_rec n 3).sign * (q * (p : ℤ)) / q = (N_rec n 3).sign * (p : ℤ) := by
    have : (N_rec n 3).sign * (q * (p : ℤ)) = q * ((N_rec n 3).sign * (p : ℤ)) := by ring
    rw [this]
    exact Int.mul_ediv_cancel_left _ (by omega)
  rw [h_div_q]
  rw [Int.natAbs_mul]
  rw [h_sign_abs, one_mul]
  rfl

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p hp_cond
  have hp : p.Prime := hp_cond.1
  have hp_mod : p % 10 = 1 ∨ p % 10 = 9 := hp_cond.2
  have h_exists := exists_n_mod_p p hp hp_mod
  rcases h_exists with ⟨n, hn_lt, hn3, h_poly⟩
  use n
  have hp11 : p ≥ 11 := by
    by_contra! h_lt
    interval_cases p
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp
    · revert hp_mod; decide
    · revert hp_mod; decide
    · revert hp; decide
    · revert hp_mod; decide
    · revert hp; decide
    · revert hp_mod; decide
    · revert hp; decide
    · revert hp; decide
    · revert hp; decide
  have h_rec_poly : N_rec n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := N_rec_two_eq_poly n hn3
  have hdvd : (p : ℤ) ∣ N_rec n 2 := by
    rw [h_rec_poly]
    exact Int.dvd_of_emod_eq_zero h_poly
  exact A363347_eq_p n hn3 p hp hp11 hn_lt hdvd
