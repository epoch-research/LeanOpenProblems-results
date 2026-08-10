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
        -- R_k = k - (k+1) / R_{k+1}
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

-- Helper lemmas from Scratch.lean and temp_check.lean

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
def P_int (k n : ℕ) : ℤ :=
  if h : k ≥ n then 4
  else if k = n - 1 then (5 * (n : ℤ) - 4)
  else
    (k : ℤ) * P_int (k + 1) n - (k + 1 : ℤ) * P_int (k + 2) n
termination_by n - k
decreasing_by
  · simp_all; omega
  · simp_all; omega

lemma P_eq_P_int (k n : ℕ) : P k n = (P_int k n : ℚ) := by
  induction k using P.induct n with
  | case1 x h =>
    rw [P.eq_def, P_int.eq_def]
    split_ifs <;> rfl
  | case2 h =>
    rw [P.eq_def, P_int.eq_def]
    split_ifs <;> try omega
    push_cast
    rfl
  | case3 x h1 h2 ih1 ih2 =>
    rw [P.eq_def, P_int.eq_def]
    split_ifs <;> try omega
    push_cast
    rw [ih1, ih2]

lemma continued_fraction_denominator_ge_f (n k : ℕ) (hn : n > 2) (hk1 : 2 ≤ k) (hk2 : k ≤ n - 1) :
  continued_fraction_denominator n k ≥ ((k : ℚ)^2 - 2 * (k : ℚ)) / ((k : ℚ) - 1) := by
  induction k using continued_fraction_denominator.induct n with
  | case1 x h =>
    omega
  | case2 h1 h2 =>
    have h_cf : continued_fraction_denominator n (n - 1) = (n - 1 : ℚ) + (n : ℚ) / 4 := by
      rw [continued_fraction_denominator.eq_def]
      split_ifs <;> try omega
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    rw [h_cf]
    rw [Nat.cast_sub (by omega)]
    push_cast
    have h_sub : (n : ℚ) - 1 - 1 = n - 2 := by ring
    rw [h_sub]
    have h_pos : (n : ℚ) - 2 > 0 := by
      have : (n : ℚ) > 2 := by exact_mod_cast hn
      linarith
    have h_ne : (n : ℚ) - 2 ≠ 0 := by linarith
    field_simp [h_ne]
    nlinarith
  | case3 x h1 h2 h3 ih =>
    have h_x1 : 2 ≤ x + 1 := by omega
    have h_x2 : x + 1 ≤ n - 1 := by omega
    have ih_eval := ih h_x1 h_x2
    have h_cf : continued_fraction_denominator n x = (x : ℚ) - (x + 1 : ℚ) / continued_fraction_denominator n (x + 1) := by
      rw [continued_fraction_denominator.eq_def n x]
      split_ifs <;> try omega
      rfl
    rw [h_cf]
    push_cast at ih_eval
    have h_alg : (((x : ℚ) + 1) ^ 2 - 2 * ((x : ℚ) + 1)) / ((x : ℚ) + 1 - 1) = ((x : ℚ)^2 - 1) / (x : ℚ) := by
      have h_sub_alg : (x : ℚ) + 1 - 1 = x := by ring
      rw [h_sub_alg]
      congr 1
      ring
    rw [h_alg] at ih_eval
    have h_pos_alg : ((x : ℚ)^2 - 1) / (x : ℚ) > 0 := by
      have hx : (x : ℚ) ≥ 2 := by exact_mod_cast h2.1
      have h_num : (x : ℚ)^2 - 1 > 0 := by nlinarith
      have h_den : (x : ℚ) > 0 := by linarith
      exact _root_.div_pos h_num h_den
    have h_pos_R : continued_fraction_denominator n (x + 1) > 0 := by
      linarith
    have hx_sub_pos : (x : ℚ) - 1 > 0 := by
      have hx : (x : ℚ) ≥ 2 := by exact_mod_cast h2.1
      linarith
    have h_ne1 : continued_fraction_denominator n (x + 1) ≠ 0 := by linarith
    have h_ne2 : (x : ℚ) - 1 ≠ 0 := by linarith
    have h_ne3 : (x : ℚ) ≠ 0 := by linarith
    push_cast
    field_simp [h_ne1, h_ne2, h_ne3] at ih_eval ⊢
    have hx : (x : ℚ) ≥ 2 := by exact_mod_cast h2.1
    nlinarith
  | case4 x h1 h2 =>
    omega

lemma continued_fraction_denominator_eq_P (n k : ℕ) (hn : n > 2) (hk1 : 2 ≤ k) (hk2 : k ≤ n - 1) :
  continued_fraction_denominator n k = P k n / P (k + 1) n := by
  induction k using continued_fraction_denominator.induct n with
  | case1 x h =>
    omega
  | case2 h1 h2 =>
    have h_cf : continued_fraction_denominator n (n - 1) = (n - 1 : ℚ) + (n : ℚ) / 4 := by
      rw [continued_fraction_denominator.eq_def]
      split_ifs <;> try omega
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    rw [h_cf]
    have h_p1 : P (n - 1) n = (5 * (n : ℚ) - 4 : ℚ) := by
      rw [P.eq_def]
      split_ifs <;> try omega
      push_cast
      rfl
    have h_p2 : P n n = 4 := by
      rw [P.eq_def]
      split_ifs <;> try omega
      rfl
    rw [h_p1]
    have h_add : n - 1 + 1 = n := by omega
    rw [h_add, h_p2]
    push_cast
    ring
  | case3 x h1 h2 h3 ih =>
    have h_x1 : 2 ≤ x + 1 := by omega
    have h_x2 : x + 1 ≤ n - 1 := by omega
    have ih_eval := ih h_x1 h_x2
    have h_cf : continued_fraction_denominator n x = (x : ℚ) - (x + 1 : ℚ) / continued_fraction_denominator n (x + 1) := by
      rw [continued_fraction_denominator.eq_def n x]
      split_ifs <;> try omega
      rfl
    rw [h_cf, ih_eval]
    have h_p : P x n = (x : ℚ) * P (x + 1) n - (x + 1 : ℚ) * P (x + 2) n := by
      rw [P.eq_def x n]
      split_ifs <;> try omega
      rfl
    rw [h_p]
    have h_pos_R1 : continued_fraction_denominator n (x + 1) > 0 := by
      have hx1 := continued_fraction_denominator_ge_f n (x + 1) hn (by omega) (by omega)
      push_cast at hx1
      have h_pos_alg : (((x : ℚ) + 1)^2 - 2 * ((x : ℚ) + 1)) / ((x : ℚ) + 1 - 1) > 0 := by
        have h_sub_alg : (x : ℚ) + 1 - 1 = x := by ring
        have h_num_alg : ((x : ℚ) + 1)^2 - 2 * ((x : ℚ) + 1) = (x : ℚ)^2 - 1 := by ring
        rw [h_sub_alg, h_num_alg]
        have hx : (x : ℚ) ≥ 2 := by exact_mod_cast h2.1
        have h_num : (x : ℚ)^2 - 1 > 0 := by nlinarith
        have h_den : (x : ℚ) > 0 := by linarith
        exact _root_.div_pos h_num h_den
      linarith
    have h_ne1 : P (x + 1) n ≠ 0 := by
      intro h
      have h_div : P (x + 1) n / P (x + 2) n = 0 := by rw [h, zero_div]
      rw [← ih_eval] at h_div
      linarith [h_pos_R1]
    have h_ne2 : P (x + 2) n ≠ 0 := by
      intro h
      have h_div : P (x + 1) n / P (x + 2) n = 0 := by rw [h, div_zero]
      rw [← ih_eval] at h_div
      linarith [h_pos_R1]
    field_simp
  | case4 x h1 h2 =>
    omega


lemma p_dvd_P_int (p : ℕ) (hp_prime : p.Prime) (n : ℕ) (hn_lt_p : n < p) (k : ℕ) (hk1 : 2 ≤ k) (hk2 : k ≤ n)
  (h2 : (p : ℤ) ∣ P_int 2 n) (h3 : (p : ℤ) ∣ P_int 3 n) : (p : ℤ) ∣ P_int k n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk_lt4 : k < 4
    · interval_cases k
      · exact h2
      · exact h3
    · have hk_ge4 : k ≥ 4 := by omega
      let j := k - 2
      have hj_eq : k = j + 2 := by omega
      have hj_ge2 : 2 ≤ j := by omega
      have hj_lt : j < k := by omega
      have hj1_lt : j + 1 < k := by omega
      have hj_le_n : j ≤ n := by omega
      have hj1_le_n : j + 1 ≤ n := by omega
      have ih_j := ih j hj_lt hj_ge2 hj_le_n
      have ih_j1 := ih (j + 1) hj1_lt (by omega) hj1_le_n
      have h_rec : P_int j n = (j : ℤ) * P_int (j + 1) n - (j + 1 : ℤ) * P_int (j + 2) n := by
        rw [P_int]
        split_ifs <;> try omega
      have h_div : (p : ℤ) ∣ (j + 1 : ℤ) * P_int (j + 2) n := by
        have : (j + 1 : ℤ) * P_int (j + 2) n = (j : ℤ) * P_int (j + 1) n - P_int j n := by linarith
        rw [this]
        exact dvd_sub (dvd_mul_of_dvd_right ih_j1 _) ih_j
      haveI : Fact p.Prime := ⟨hp_prime⟩
      have h_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
      rcases h_prime_int.dvd_mul.mp h_div with hj1 | hj2
      · have hj1_pos : (j : ℤ) + 1 > 0 := by omega
        have hj1_le : (p : ℤ) ≤ (j : ℤ) + 1 := Int.le_of_dvd hj1_pos hj1
        omega
      · rw [hj_eq]
        exact hj2

lemma p_odd_helper (p : ℕ) (hp10 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : p % 2 = 1 := by
  rcases hp10 with h1 | h2
  · have : p % 10 = 1 := h1
    omega
  · have : p % 10 = 9 := h2
    omega

lemma mul_four_mod_two (Y : ℕ) : (4 * Y) % 2 = 0 := by
  omega

lemma pc_odd_helper (A B : ℕ) (h_eq : A + 5 = B) (h_even : B % 2 = 0) : A % 2 = 1 := by
  omega

lemma gcd_helper (c G : ℕ) (h_div : G ∣ c) (h_div8 : G ∣ 8) (hc_odd : c % 2 = 1) : G = 1 := by
  have hG_pos : G > 0 := Nat.pos_of_dvd_of_pos h_div8 (by decide)
  have hG_le : G ≤ 8 := Nat.le_of_dvd (by decide) h_div8
  interval_cases G
  · rfl
  · have : 2 ∣ c := h_div
    have : c % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega
  · have h_not : ¬ 3 ∣ 8 := by decide
    exact absurd h_div8 h_not
  · have : 4 ∣ c := h_div
    have h24 : 2 ∣ 4 := by decide
    have : 2 ∣ c := dvd_trans h24 h_div
    have : c % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega
  · have h_not : ¬ 5 ∣ 8 := by decide
    exact absurd h_div8 h_not
  · have h_not : ¬ 6 ∣ 8 := by decide
    exact absurd h_div8 h_not
  · have h_not : ¬ 7 ∣ 8 := by decide
    exact absurd h_div8 h_not
  · have : 8 ∣ c := h_div
    have h28 : 2 ∣ 8 := by decide
    have : 2 ∣ c := dvd_trans h28 h_div
    have : c % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp this
    omega

/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p :=
  by
    intro p hp
    rcases hp with ⟨hp_prime, hp10⟩
    have hp11 := p_ge_eleven p hp_prime hp10
    haveI : Fact p.Prime := ⟨hp_prime⟩
    rcases exists_sq_eq_five p hp_prime hp10 with ⟨r, hr⟩
    let x1 := r % p
    have h_x1_lt : x1 < p := Nat.mod_lt r (by omega)
    have h1_ne : (x1 : ZMod p) ≠ 0 := by
      intro h_zero
      have h_r_mod : (r : ZMod p) ^ 2 = (5 : ZMod p) := by
        rw [← ZMod.natCast_eq_natCast_iff] at hr
        push_cast at hr
        exact hr
      have h_sq : (x1 : ZMod p) ^ 2 = 5 := by
        have : (x1 : ZMod p) = (r : ZMod p) := ZMod.natCast_mod r p
        rw [this, h_r_mod]
      rw [h_zero, zero_pow (by decide)] at h_sq
      have : (5 : ZMod p) ≠ 0 := five_ne_zero_mod_p p hp_prime hp10
      exact this h_sq.symm
    have h1_val_pos : x1 > 0 := by
      have : x1 ≠ 0 := by
        intro h
        have : (x1 : ZMod p) = 0 := by rw [h, Nat.cast_zero]
        exact h1_ne this
      omega
    let x := if x1 % 2 = 0 then x1 else p - x1
    have hx_lt : x < p := by
      unfold x
      split_ifs with h_even
      · exact h_x1_lt
      · omega
    have h_p_pos : p > 0 := by omega
    have h_r_mod : (r : ZMod p) ^ 2 = (5 : ZMod p) := by
      rw [← ZMod.natCast_eq_natCast_iff] at hr
      push_cast at hr
      exact hr
    have h_x_sq_zmod : (x : ZMod p) ^ 2 = (5 : ZMod p) := by
      unfold x
      split_ifs with h_even
      · have : (x1 : ZMod p) = (r : ZMod p) := ZMod.natCast_mod r p
        rw [this, h_r_mod]
      · have h_eq : ((p - x1 : ℕ) : ZMod p) = - (r : ZMod p) := by
          have h_le : x1 ≤ p := by omega
          rw [Nat.cast_sub h_le]
          have : (x1 : ZMod p) = (r : ZMod p) := ZMod.natCast_mod r p
          rw [this, ZMod.natCast_self p]
          ring
        rw [h_eq]
        ring_nf
        exact h_r_mod
    have h_x_sq : x ^ 2 ≡ 5 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact h_x_sq_zmod
    -- Now we want to prove that x ≥ 4.
    -- If x ≤ 3, then x^2 ≤ 9. But x^2 % p = 5 % p = 5 (since p ≥ 11).
    -- So x^2 % p = 5. Since x^2 ≤ 9 and p ≥ 11, we must have x^2 = 5, which is impossible.
    have hx_ge_4 : x ≥ 4 := by
      by_contra h_lt
      have hx_le_3 : x ≤ 3 := by omega
      have hx_sq_le_9 : x ^ 2 ≤ 9 := by nlinarith
      have h_mod : x ^ 2 % p = 5 % p := h_x_sq
      have h_mod_5 : x ^ 2 % p = 5 := by
        rw [h_mod]
        exact Nat.mod_eq_of_lt (by omega)
      have h_eq_5 : x ^ 2 = 5 := by
        have : x ^ 2 < p := by linarith
        rw [← h_mod_5]
        exact (Nat.mod_eq_of_lt this).symm
      interval_cases x <;> omega
    let n := x - 1
    use n
    have hn_ge_3 : n ≥ 3 := by omega
    have hn_le2_f : ¬(n ≤ 2) := by omega
    unfold A363347
    split_ifs <;> try omega
    change (continued_fraction_denominator n 2).num.natAbs = p
    have h_eq_P := continued_fraction_denominator_eq_P n 2 (by omega) (by omega) (by omega)

    have h_n_eq : (n : ℚ) = (x : ℚ) - 1 := by
      have : n = x - 1 := rfl
      rw [this]
      have : 1 ≤ x := by omega
      exact Nat.cast_sub this
    have h_P2_x : P 2 n = (x : ℚ) ^ 2 - 5 := by
      rw [P2_eq_formula n hn_ge_3]
      rw [h_n_eq]
      ring
    have h_div_mod : x ^ 2 = p * (x ^ 2 / p) + x ^ 2 % p := (Nat.div_add_mod (x ^ 2) p).symm
    have h_mod : x ^ 2 % p = 5 := by
      have h1 : x ^ 2 % p = 5 % p := h_x_sq
      have h2 : 5 % p = 5 := Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]
    have h_c_eq : x ^ 2 = p * (x ^ 2 / p) + 5 := by
      nth_rw 1 [h_div_mod]
      rw [h_mod]
    let c := x ^ 2 / p
    have hc_pos : c > 0 := by
      have hc_ne_zero : c ≠ 0 := by
        intro hc_zero
        have h_x2 : x ^ 2 = 5 := by
          calc
            x ^ 2 = p * c + 5 := h_c_eq
            _ = p * 0 + 5 := by rw [hc_zero]
            _ = 5 := by ring
        have h_ge : x ^ 2 ≥ 16 := by nlinarith
        rw [h_x2] at h_ge
        revert h_ge
        decide
      exact Nat.pos_of_ne_zero hc_ne_zero
    have h_cast_c : (x : ℚ) ^ 2 = (c : ℚ) * (p : ℚ) + 5 := by
      have : ((x ^ 2 : ℕ) : ℚ) = (((p * c + 5 : ℕ) : ℚ)) := by rw [h_c_eq]
      push_cast at this
      rw [this]
      ring
    have h_P2_cp : P 2 n = (c : ℚ) * (p : ℚ) := by
      rw [h_P2_x]
      rw [h_cast_c]
      ring
    have hc_lt_n : c < n := by
      have h_P2_eq : (c : ℚ) * (p : ℚ) = (x : ℚ) ^ 2 - 5 := by
        rw [← h_P2_cp]
        rw [h_P2_x]
      have h_c_p : (c : ℚ) < (n : ℚ) := by
        have h_cp_eq : (c : ℚ) * (p : ℚ) = (x : ℚ) ^ 2 - 5 := h_P2_eq
        have h_np_gt : (x : ℚ) ^ 2 - 5 < (n : ℚ) * (p : ℚ) := by
          rw [h_n_eq]
          have hp_ge : (p : ℚ) ≥ (x : ℚ) + 1 := by exact_mod_cast (by omega)
          have h_x_ge : (x : ℚ) ≥ 4 := by exact_mod_cast hx_ge_4
          nlinarith
        have hp_pos : (p : ℚ) > 0 := by exact_mod_cast h_p_pos
        nlinarith
      exact_mod_cast h_c_p


    have hc_le_n1 : c ≤ n - 1 := by omega
    have h_fac_dvd : (c : ℤ) ∣ (factorial (n - 1) : ℤ) := by
      have hd : c ∣ factorial (n - 1) := Nat.dvd_factorial hc_pos hc_le_n1
      exact_mod_cast hd
    rcases h_fac_dvd with ⟨k_fac, hk_fac⟩
    have hx_even : x % 2 = 0 := by
      unfold x
      split_ifs with h_even
      · exact h_even
      · have hp_odd : p % 2 = 1 := p_odd_helper p hp10
        have hx1_odd : x1 % 2 = 1 := by omega
        omega
    have h_x_sq_even : x ^ 2 % 2 = 0 := by
      have : ∃ k, x = 2 * k := by
        use x / 2
        have h_div := Nat.div_add_mod x 2
        rw [hx_even] at h_div
        exact h_div.symm
      rcases this with ⟨k, hk⟩
      rw [hk]
      have h_eq2 : (2 * k) ^ 2 = 4 * (k ^ 2) := by ring
      rw [h_eq2]
      exact mul_four_mod_two (k ^ 2)
    have h_pc_odd : (p * c) % 2 = 1 := pc_odd_helper (p * c) (x ^ 2) h_c_eq.symm h_x_sq_even
    have hc_odd : c % 2 = 1 := by
      have hp_odd : p % 2 = 1 := p_odd_helper p hp10
      have h_mod_mul : (p * c) % 2 = (p % 2 * (c % 2)) % 2 := Nat.mul_mod p c 2
      rw [h_pc_odd, hp_odd] at h_mod_mul
      have h_one_mul : 1 * (c % 2) = c % 2 := by ring
      rw [h_one_mul] at h_mod_mul
      have h_mod_mod : (c % 2) % 2 = c % 2 := Nat.mod_mod c 2
      rw [h_mod_mod] at h_mod_mul
      exact h_mod_mul.symm
    have h_P2_eq_P_int : P 2 n = (P_int 2 n : ℚ) := P_eq_P_int 2 n
    have h_P2_val : (P_int 2 n : ℚ) = ((c * p : ℤ) : ℚ) := by
      rw [← h_P2_eq_P_int]
      rw [h_P2_cp]
      push_cast
      rfl
    have h_P2_int : P_int 2 n = (c : ℤ) * (p : ℤ) := by
      exact_mod_cast h_P2_val
    have h_P_int_rel_cast : ( (2 * P_int 3 n * ((n : ℤ) - 2) : ℤ) : ℚ ) = ( (4 * (factorial (n - 1) : ℤ) - P_int 2 n * T n : ℤ) : ℚ ) := by
      push_cast
      rw [← P_eq_P_int 3 n, ← P_eq_P_int 2 n]
      have h_eq_formula := P_eq_formula n hn_ge_3 n (by omega) (by omega)
      rw [P_n_n n] at h_eq_formula
      have h_fac_ne : (factorial (n - 1) : ℚ) ≠ 0 := by
        exact_mod_cast (factorial_ne_zero (n - 1))
      field_simp [h_fac_ne] at h_eq_formula
      linarith
    have h_P_int_rel : 2 * P_int 3 n * ((n : ℤ) - 2) = 4 * (factorial (n - 1) : ℤ) - P_int 2 n * T n := by
      exact_mod_cast h_P_int_rel_cast
    have h_dvd_2_P3_n2 : (c : ℤ) ∣ 2 * P_int 3 n * ((n : ℤ) - 2) := by
      rw [h_P_int_rel, hk_fac, h_P2_int]
      use 4 * k_fac - (p : ℤ) * T n
      ring
    have h_c_dvd_8P3 : (c : ℤ) ∣ 8 * P_int 3 n := by
      have h_div : (c : ℤ) ∣ 2 * P_int 3 n * ((n : ℤ) - 2) * ((n : ℤ) + 4) := dvd_mul_of_dvd_left h_dvd_2_P3_n2 _
      have h_eq : (c : ℤ) * (2 * P_int 3 n * (p : ℤ)) - 8 * P_int 3 n = 2 * P_int 3 n * ((n : ℤ) - 2) * ((n : ℤ) + 4) := by
        have h_cp_eq : (c : ℤ) * (p : ℤ) = ((n : ℤ) - 2) * ((n : ℤ) + 4) + 4 := by
          have h_cp_val : ((c : ℤ) * (p : ℤ) : ℚ) = (((n : ℤ) - 2) * ((n : ℤ) + 4) + 4 : ℚ) := by
            push_cast
            rw [← h_P2_cp]
            rw [P2_eq_formula n hn_ge_3]
            ring
          exact_mod_cast h_cp_val
        linear_combination (2 * P_int 3 n) * h_cp_eq
      rw [← h_eq] at h_div
      have h_div_c : (c : ℤ) ∣ (c : ℤ) * (2 * P_int 3 n * (p : ℤ)) := dvd_mul_right _ _
      have h_div_8P3 : (c : ℤ) ∣ - (8 * P_int 3 n) := by
        exact (dvd_add_right h_div_c).mp h_div
      exact Int.dvd_neg.mp h_div_8P3


    have h_gcd_c_8 : Int.gcd (c : ℤ) 8 = 1 := by
      have h_gcd_eq : Int.gcd (c : ℤ) 8 = Nat.gcd c 8 := by
        have h1 : (c : ℤ).natAbs = c := rfl
        have h2 : (8 : ℤ).natAbs = 8 := rfl
        change Nat.gcd (c : ℤ).natAbs (8 : ℤ).natAbs = Nat.gcd c 8
        rw [h1, h2]
      rw [h_gcd_eq]
      exact gcd_helper c (Nat.gcd c 8) (Nat.gcd_dvd_left c 8) (Nat.gcd_dvd_right c 8) hc_odd
    have h_c_dvd_P3 : (c : ℤ) ∣ P_int 3 n := by
      exact Int.dvd_of_dvd_mul_right_of_gcd_one h_c_dvd_8P3 h_gcd_c_8
    rcases h_c_dvd_P3 with ⟨d_int, hd_int⟩
    have h_P3_ne : (P_int 3 n : ℚ) ≠ 0 := by
      have h_P3_eq : (P_int 3 n : ℚ) = P 3 n := (P_eq_P_int 3 n).symm
      rw [h_P3_eq]
      by_cases hn3 : n = 3
      · rw [hn3]
        rw [P.eq_def 3 3]
        have : 3 ≥ 3 := by decide
        rw [dif_pos this]
        decide
      · have hn4 : n ≥ 4 := by omega
        have h_cf3 := continued_fraction_denominator_ge_f n 3 (by omega) (by omega) (by omega)
        have h_cf3_pos : continued_fraction_denominator n 3 > 0 := by
          push_cast at h_cf3
          linarith
        have h_cf3_eq := continued_fraction_denominator_eq_P n 3 (by omega) (by omega) (by omega)
        rw [h_cf3_eq] at h_cf3_pos
        intro h_zero
        rw [h_zero, zero_div] at h_cf3_pos
        linarith
    have h_P3_val : (P_int 3 n : ℚ) = (c : ℚ) * (d_int : ℚ) := by
      push_cast
      rw [hd_int]
      push_cast
      rfl
    have h_R2_red : P 2 n / P 3 n = ( (p : ℤ) : ℚ ) / (d_int : ℚ) := by
      rw [P_eq_P_int 2 n, P_eq_P_int 3 n, h_P2_int]
      rw [h_P3_val]
      push_cast
      have h_c_ne_rat : (c : ℚ) ≠ 0 := by exact_mod_cast (_root_.ne_of_gt hc_pos)
      have h_d_ne_rat : (d_int : ℚ) ≠ 0 := by
        intro h_zero
        have h_zero_int : d_int = 0 := by exact_mod_cast h_zero
        rw [h_zero_int] at hd_int
        rw [mul_zero] at hd_int
        have : (P_int 3 n : ℚ) = 0 := by exact_mod_cast hd_int
        exact h_P3_ne this
      field_simp
    have hd_int_pos : d_int > 0 := by
      by_contra hd_le
      have hd_le : d_int ≤ 0 := by omega
      have h_R2_pos : continued_fraction_denominator n 2 > 0 := by
        by_cases hn3 : n = 3
        · rw [hn3]
          rw [continued_fraction_denominator.eq_def 3 2]
          norm_num
        · have hn4 : n ≥ 4 := by omega
          have h_cf2 := continued_fraction_denominator_ge_f n 2 (by omega) (by omega) (by omega)
          push_cast at h_cf2
          norm_num at h_cf2
          have h_P2_ne : P 2 n ≠ 0 := by
            rw [h_P2_cp]
            have hc_ne : (c : ℚ) ≠ 0 := by exact_mod_cast (_root_.ne_of_gt hc_pos)
            have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast (_root_.ne_of_gt h_p_pos)
            exact mul_ne_zero hc_ne hp_ne
          have h_cf_eq_R2 : continued_fraction_denominator n 2 = P 2 n / P 3 n := h_eq_P
          have h_cf_ne : continued_fraction_denominator n 2 ≠ 0 := by
            rw [h_cf_eq_R2]
            have h_P3_ne_rat : P 3 n ≠ 0 := by
              rw [P_eq_P_int 3 n]
              exact h_P3_ne
            exact div_ne_zero h_P2_ne h_P3_ne_rat
          rcases lt_or_eq_of_le h_cf2 with h_lt | h_eq
          · exact h_lt
          · exact absurd h_eq.symm h_cf_ne
      rw [h_eq_P] at h_R2_pos
      rw [h_R2_red] at h_R2_pos
      push_cast at h_R2_pos
      have hp_pos_rat : (p : ℚ) > 0 := by exact_mod_cast h_p_pos
      have hd_le_rat : (d_int : ℚ) ≤ 0 := by exact_mod_cast hd_le
      have : (p : ℚ) / (d_int : ℚ) ≤ 0 := by
        exact div_nonpos_of_nonneg_of_nonpos (by linarith) hd_le_rat
      linarith
    have h_p_not_dvd_d : ¬ ((p : ℤ) ∣ d_int) := by
      intro h_dvd
      have h_dvd_P3 : (p : ℤ) ∣ P_int 3 n := by
        rw [hd_int]
        exact dvd_mul_of_dvd_right h_dvd _
      have h_dvd_P2 : (p : ℤ) ∣ P_int 2 n := by
        rw [h_P2_int]
        exact dvd_mul_of_dvd_right (dvd_rfl) _
      have hp_dvd_Pn : (p : ℤ) ∣ P_int n n := by
        have hn_lt_p : n < p := by
          have : n = x - 1 := rfl
          omega
        exact p_dvd_P_int p hp_prime n hn_lt_p n (by omega) (by omega) h_dvd_P2 h_dvd_P3
      have h_Pn_val : P_int n n = 4 := by
        rw [P_int]
        split_ifs <;> try omega
      rw [h_Pn_val] at hp_dvd_Pn
      have hp_le_4 : p ≤ 4 := by
        have h_pos : (4 : ℤ) > 0 := by decide
        have hp_le_4_int := Int.le_of_dvd h_pos hp_dvd_Pn
        exact_mod_cast hp_le_4_int
      omega
    have h_coprime : Nat.Coprime p d_int.natAbs := by
      rw [Nat.Prime.coprime_iff_not_dvd hp_prime]
      intro h_dvd_nat
      have h_dvd : (p : ℤ) ∣ d_int := by
        have h_abs : (d_int.natAbs : ℤ) = d_int := Int.natAbs_of_nonneg (by linarith)
        rw [← h_abs]
        exact Int.natCast_dvd_natCast.mpr h_dvd_nat
      exact h_p_not_dvd_d h_dvd
    have h_R2_num : (continued_fraction_denominator n 2).num = p := by
      rw [h_eq_P]
      rw [h_R2_red]
      have hb0 : 0 < (d_int : ℤ) := by exact_mod_cast hd_int_pos
      have h_cop : Nat.Coprime (p : ℤ).natAbs (d_int : ℤ).natAbs := by
        have hp_abs : (p : ℤ).natAbs = p := by rfl
        have hd_abs : (d_int : ℤ).natAbs = d_int.natAbs := by rfl
        rw [hp_abs, hd_abs]
        exact h_coprime
      have h_eq_num := num_div_eq_of_coprime hb0 h_cop
      exact_mod_cast h_eq_num
    rw [h_R2_num]
    rfl


