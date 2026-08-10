import FormalConjectures.Util.ProblemImports

open Rat Nat

lemma p_ne_two (p : ℕ) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : p ≠ 2 := by
  intro h
  simp [Nat.ModEq] at hp10
  subst h
  omega

lemma two_ne_zero_mod_five : (2 : ZMod 5) ≠ 0 := by decide

lemma legendreSym_five (p : ℕ) [hp : Fact p.Prime] (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  legendreSym p 5 = 1 := by
  haveI : Fact (5 : ℕ).Prime := ⟨Nat.prime_five⟩
  have h_rec := legendreSym.quadratic_reciprocity_one_mod_four (by decide : (5 : ℕ) % 4 = 1) (by exact_mod_cast p_ne_two p hp10)
  change legendreSym p ↑(5 : ℕ) = 1
  rw [h_rec]
  rw [legendreSym.mod 5 (p : ℤ)]
  simp [Nat.ModEq] at hp10
  have h_p5 : p % 5 = 1 ∨ p % 5 = 4 := by
    rcases hp10 with h1 | h2
    · left
      have : p = (p / 10) * 10 + p % 10 := by omega
      rw [h1] at this
      have : p = (p / 10) * 10 + 1 := this
      omega
    · right
      have : p = (p / 10) * 10 + p % 10 := by omega
      rw [h2] at this
      have : p = (p / 10) * 10 + 9 := this
      omega
  change legendreSym 5 (↑p % 5) = 1
  rcases h_p5 with h1 | h2
  · -- p % 5 = 1
    have h_p_cast : (p : ℤ) % 5 = 1 := by
      have : (p : ℤ) = ((p : ℤ) / 5) * 5 + (p % 5 : ℕ) := by omega
      rw [h1] at this
      omega
    rw [h_p_cast]
    exact legendreSym.at_one 5
  · -- p % 5 = 4
    have h_p_cast : (p : ℤ) % 5 = 4 := by
      have : (p : ℤ) = ((p : ℤ) / 5) * 5 + (p % 5 : ℕ) := by omega
      rw [h2] at this
      omega
    rw [h_p_cast]
    have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact legendreSym.sq_one' 5 (by exact_mod_cast two_ne_zero_mod_five)

lemma p_ge_eleven (p : ℕ) (hp : p.Prime) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : p ≥ 11 := by
  simp [Nat.ModEq] at hp10
  have h2 : p ≠ 2 := by intro h; subst h; omega
  have h3 : p ≠ 3 := by intro h; subst h; omega
  have h5 : p ≠ 5 := by intro h; subst h; omega
  have h7 : p ≠ 7 := by intro h; subst h; omega
  by_contra h_lt
  have : p < 11 := by omega
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hp (by decide)
  · exact h5 rfl
  · exact absurd hp (by decide)
  · exact h7 rfl
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

lemma five_ne_zero_mod_p (p : ℕ) (hp : p.Prime) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  (5 : ZMod p) ≠ 0 := by
  have hp11 := p_ge_eleven p hp hp10
  change ((5 : ℕ) : ZMod p) ≠ 0
  intro h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
  have h_le := Nat.le_of_dvd (by decide : 5 > 0) h
  omega

lemma exists_sq_eq_five (p : ℕ) (hp : p.Prime) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  ∃ r : ℕ, r ^ 2 ≡ 5 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_leg := legendreSym_five p hp10
  have h_ne : ((5 : ℤ) : ZMod p) ≠ 0 := by
    exact_mod_cast five_ne_zero_mod_p p hp hp10
  have h_sq : IsSquare (5 : ZMod p) := by
    have h_eq := legendreSym.eq_one_iff p h_ne
    have h_cast : (5 : ZMod p) = ((5 : ℤ) : ZMod p) := by push_cast; rfl
    rw [h_cast]
    rw [← h_eq]
    exact h_leg
  rcases h_sq with ⟨y, hy⟩
  use y.val
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  rw [sq]
  exact hy.symm



def P (k n : ℕ) : ℚ :=
  if h : k ≥ n then 4
  else if k = n - 1 then (5 * n - 4 : ℚ)
  else
    (k : ℚ) * P (k + 1) n - (k + 1 : ℚ) * P (k + 2) n
termination_by n - k
decreasing_by
  · simp_all; omega
  · simp_all; omega

def T : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | k + 4 => (k + 2 : ℤ) * (T (k + 3) - T (k + 2))

lemma T_identity_induction (d : ℕ) :
  ((d : ℤ) + 1) * T (d + 4) - ((d : ℤ) + 2) * T (d + 3) = - (factorial (d + 2) : ℤ) := by
  induction d with
  | zero =>
    rfl
  | succ d ih =>
    have h_T5 : T (d + 5) = (d + 3 : ℤ) * (T (d + 4) - T (d + 3)) := rfl
    rw [h_T5]
    have h_sub_d1 : d + 1 + 3 = d + 4 := by omega
    have h_sub_d2 : d + 1 + 2 = d + 3 := by omega
    rw [h_sub_d1, h_sub_d2]
    push_cast
    have h_fac_succ : (factorial (d + 3) : ℤ) = ((d : ℤ) + 3) * (factorial (d + 2) : ℤ) := by
      have : d + 3 = (d + 2) + 1 := by omega
      rw [this, factorial_succ]
      push_cast
      ring
    rw [h_fac_succ]
    linear_combination ((d : ℤ) + 3) * ih


lemma P_eq_formula (n : ℕ) (hn : n ≥ 3) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k ≤ n) :
  P k n = (2 * P 3 n * (k - 2 : ℚ) + P 2 n * (T k : ℚ)) / (factorial (k - 1) : ℚ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk_lt4 : k < 4
    · interval_cases k
      · have h_T2 : T 2 = 1 := rfl
        have h_fac1 : factorial 1 = 1 := rfl
        rw [h_T2, h_fac1]
        push_cast
        ring
      · have h_T3 : T 3 = 0 := rfl
        have h_fac2 : factorial 2 = 2 := rfl
        rw [h_T3, h_fac2]
        push_cast
        ring
    · have hk_ge4 : k ≥ 4 := by omega
      let j := k - 2
      have hj_eq : k = j + 2 := by omega
      have hj_ge2 : 2 ≤ j := by omega
      have hj_lt : j < k := by omega
      have hj1_lt : j + 1 < k := by omega
      have hj_le_n2 : j ≤ n - 2 := by omega
      have hj_le_n : j ≤ n := by omega
      have hj1_le_n : j + 1 ≤ n := by omega
      have ih_j := ih j hj_lt hj_ge2 hj_le_n
      have ih_j1 := ih (j + 1) hj1_lt (by omega) hj1_le_n
      have h_P_rec : P j n = (j : ℚ) * P (j + 1) n - (j + 1 : ℚ) * P (j + 2) n := by
        have hj_lt_n1 : j < n - 1 := by omega
        rw [P.eq_def j n]
        split_ifs <;> try omega
        rfl
      have h_P_j2 : P (j + 2) n = ((j : ℚ) * P (j + 1) n - P j n) / (j + 1 : ℚ) := by
        have hj1_pos : (j : ℚ) + 1 ≠ 0 := by linarith
        field_simp
        linarith
      rw [hj_eq, h_P_j2, ih_j, ih_j1]
      have h_fac_j : (factorial j : ℚ) = (j : ℚ) * (factorial (j - 1) : ℚ) := by
        have : j = (j - 1) + 1 := by omega
        rw [this]
        rw [factorial_succ]
        push_cast
        rfl
      have h_fac_j1 : (factorial (j + 1) : ℚ) = ((j : ℚ) + 1) * (factorial j : ℚ) := by
        rw [factorial_succ]
        push_cast
        rfl
      have h_T_rec : (T (j + 2) : ℚ) = (j : ℚ) * ((T (j + 1) : ℚ) - (T j : ℚ)) := by
        let d := j - 2
        have hjd : j = d + 2 := by omega
        rw [hjd]
        have h_sub_d1 : d + 2 + 2 = d + 4 := by omega
        have h_sub_d2 : d + 2 + 1 = d + 3 := by omega
        rw [h_sub_d1, h_sub_d2]
        have hT4 : T (d + 4) = (d + 2 : ℤ) * (T (d + 3) - T (d + 2)) := rfl
        rw [hT4]
        push_cast
        rfl
      have h_fac_j1_ne : (factorial (j + 1) : ℚ) ≠ 0 := by
        exact_mod_cast (factorial_ne_zero (j + 1))
      have h_fac_j_ne : (factorial j : ℚ) ≠ 0 := by
        exact_mod_cast (factorial_ne_zero j)
      have h_fac_jm1_ne : (factorial (j - 1) : ℚ) ≠ 0 := by
        exact_mod_cast (factorial_ne_zero (j - 1))
      have hj1_ne : (j : ℚ) + 1 ≠ 0 := by
        have : j + 1 > 0 := by omega
        exact_mod_cast (_root_.ne_of_gt this)
      have hj_ne : (j : ℚ) ≠ 0 := by
        have : j > 0 := by omega
        exact_mod_cast (_root_.ne_of_gt this)
      have h_sub_j1 : j + 2 - 1 = j + 1 := by omega
      have h_sub_j2 : j + 1 - 1 = j := by omega
      rw [h_sub_j1, h_sub_j2]
      rw [h_fac_j1, h_fac_j, h_T_rec]
      field_simp
      push_cast
      ring


lemma T_identity (n : ℕ) (hn : n ≥ 4) :
  ((n : ℤ) - 3) * T n - ((n : ℤ) - 2) * T (n - 1) = - (factorial (n - 2) : ℤ) := by
  let d := n - 4
  have hn_eq : n = d + 4 := by omega
  rw [hn_eq]
  have h_sub1 : d + 4 - 1 = d + 3 := by omega
  have h_sub2 : d + 4 - 2 = d + 2 := by omega
  rw [h_sub1, h_sub2]
  push_cast
  have h1 : (d : ℤ) + 4 - 3 = d + 1 := by ring
  have h2 : (d : ℤ) + 4 - 2 = d + 2 := by ring
  rw [h1, h2]
  exact T_identity_induction d

lemma T_identity_rat (n : ℕ) (hn : n ≥ 4) :
  ((n : ℚ) - 3) * (T n : ℚ) - ((n : ℚ) - 2) * (T (n - 1) : ℚ) = - (factorial (n - 2) : ℚ) := by
  have h := T_identity n hn
  have h_cast : (((((n : ℤ) - 3) * T n - ((n : ℤ) - 2) * T (n - 1)) : ℤ) : ℚ) = (((- (factorial (n - 2) : ℤ)) : ℤ) : ℚ) := by rw [h]
  push_cast at h_cast
  exact h_cast

lemma P_n_n (n : ℕ) : P n n = 4 := by
  rw [P.eq_def]
  split_ifs <;> try omega
  rfl

lemma P_n_sub_1_n (n : ℕ) (hn : n ≥ 3) : P (n - 1) n = 5 * n - 4 := by
  rw [P.eq_def]
  split_ifs <;> try omega
  push_cast
  rfl

lemma P2_eq_formula (n : ℕ) (hn : n ≥ 3) :
  P 2 n = (n : ℚ) ^ 2 + 2 * (n : ℚ) - 4 := by
  by_cases hn4 : n ≥ 4
  · have h_fac_n2_ne : (factorial (n - 2) : ℚ) ≠ 0 := by
      exact_mod_cast (factorial_ne_zero (n - 2))
    have h_fac_n1 : (factorial (n - 1) : ℚ) = ((n : ℚ) - 1) * (factorial (n - 2) : ℚ) := by
      have h_sub : n - 1 = (n - 2) + 1 := by omega
      nth_rw 1 [h_sub]
      rw [factorial_succ]
      push_cast
      have h_sub_cast : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := Nat.cast_sub (by omega)
      rw [h_sub_cast]
      ring
    have h1 := P_eq_formula n hn n (by omega) (by omega)
    have h2 := P_eq_formula n hn (n - 1) (by omega) (by omega)
    rw [P_n_n n] at h1
    rw [P_n_sub_1_n n hn] at h2
    have h_sub1 : n - 1 - 1 = n - 2 := by omega
    rw [h_sub1] at h2
    have h_sub_n3 : ((n - 1 : ℕ) : ℚ) - 2 = (n : ℚ) - 3 := by
      have : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := Nat.cast_sub (by omega)
      rw [this]
      ring
    rw [h_sub_n3] at h2
    push_cast at h2
    have h1_clear : 4 * (factorial (n - 1) : ℚ) = 2 * P 3 n * ((n : ℚ) - 2) + P 2 n * (T n : ℚ) := by
      have : (factorial (n - 1) : ℚ) ≠ 0 := by
        exact_mod_cast (factorial_ne_zero (n - 1))
      field_simp [this] at h1
      linarith
    have h2_clear : (5 * (n : ℚ) - 4) * (factorial (n - 2) : ℚ) = 2 * P 3 n * ((n : ℚ) - 3) + P 2 n * (T (n - 1) : ℚ) := by
      field_simp [h_fac_n2_ne] at h2
      linarith
    have h_elim : ((n : ℚ) - 3) * (4 * (factorial (n - 1) : ℚ)) - ((n : ℚ) - 2) * ((5 * (n : ℚ) - 4) * (factorial (n - 2) : ℚ)) =
      P 2 n * (((n : ℚ) - 3) * (T n : ℚ) - ((n : ℚ) - 2) * (T (n - 1) : ℚ)) := by
      linear_combination ((n : ℚ) - 3) * h1_clear - ((n : ℚ) - 2) * h2_clear
    rw [T_identity_rat n hn4] at h_elim
    rw [h_fac_n1] at h_elim
    have h_ring : ((n : ℚ) - 3) * (4 * (((n : ℚ) - 1) * (factorial (n - 2) : ℚ))) - ((n : ℚ) - 2) * ((5 * (n : ℚ) - 4) * (factorial (n - 2) : ℚ)) =
      - (factorial (n - 2) : ℚ) * ((n : ℚ) ^ 2 + 2 * (n : ℚ) - 4) := by ring
    rw [h_ring] at h_elim
    have h_neg_fac_ne : - (factorial (n - 2) : ℚ) ≠ 0 := by
      intro h
      have h_zero : (factorial (n - 2) : ℚ) = 0 := by linarith
      exact h_fac_n2_ne h_zero
    have h_elim2 : - (factorial (n - 2) : ℚ) * ((n : ℚ) ^ 2 + 2 * (n : ℚ) - 4) = - (factorial (n - 2) : ℚ) * P 2 n := by
      calc
        - (factorial (n - 2) : ℚ) * ((n : ℚ) ^ 2 + 2 * (n : ℚ) - 4) = P 2 n * - (factorial (n - 2) : ℚ) := h_elim
        _ = - (factorial (n - 2) : ℚ) * P 2 n := mul_comm _ _
    exact (mul_left_cancel₀ h_neg_fac_ne h_elim2).symm
  · have : n = 3 := by omega
    subst this
    rw [P.eq_def 2 3]
    split_ifs <;> try omega
    norm_num
