import FormalConjectures.Util.ProblemImports

open Rat Nat

def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) + (n : ℚ) / 4
      else
        let R_next := continued_fraction_denominator n (k + 1)
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

lemma p_ne_2_and_5 (p : ℕ) (hp : p.Prime) (h : p % 10 = 1 ∨ p % 10 = 9) : p ≠ 2 ∧ p ≠ 5 := by
  have : p ≥ 2 := hp.two_le
  rcases h with h1 | h2
  · omega
  · omega

lemma test_legendre (p : ℕ) [hp : Fact p.Prime] (h1 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : IsSquare (5 : ZMod p) := by
  have hp_prime : p.Prime := hp.out
  have h_ne : p ≠ 2 ∧ p ≠ 5 := p_ne_2_and_5 p hp_prime h1
  have hp_ne_2 : p ≠ 2 := h_ne.1
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h_qr : legendreSym p 5 = legendreSym 5 p := by
    exact @legendreSym.quadratic_reciprocity_one_mod_four 5 p _ _ (by decide) hp_ne_2
  have h_mod10 : p % 10 = 1 ∨ p % 10 = 9 := by
    rcases h1 with h_eq1 | h_eq9
    · left; exact h_eq1
    · right; exact h_eq9
  have h_mod5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
  have h_val : legendreSym 5 p = 1 := by
    rw [legendreSym.mod 5 p]
    rcases h_mod5 with h5_1 | h5_4
    · have : (p : ℤ) % ((5 : ℕ) : ℤ) = 1 := by omega
      rw [this]
      rfl
    · have : (p : ℤ) % ((5 : ℕ) : ℤ) = 4 := by omega
      rw [this]
      rfl
  have h_ne5 : (5 : ZMod p) ≠ 0 := by
    intro h0
    have hp_dvd_5 : p ∣ 5 := (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h0
    have hp_eq_5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp_prime (by decide)).mp hp_dvd_5
    exact h_ne.2 hp_eq_5
  have h_ne5_int : ((5 : ℤ) : ZMod p) ≠ 0 := by
    exact_mod_cast h_ne5
  have h_leg_eq_one : legendreSym p 5 = 1 := by
    rw [h_qr, h_val]
  have h_is_sq : IsSquare ((5 : ℤ) : ZMod p) := by
    exact (legendreSym.eq_one_iff p h_ne5_int).mp h_leg_eq_one
  exact_mod_cast h_is_sq

lemma exists_n_dvd (p : ℕ) [hp : Fact p.Prime] (h1 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : ∃ n : ℕ, p ∣ (n + 1) ^ 2 - 5 := by
  have hp_prime : p.Prime := hp.out
  have hp_ge_11 : p ≥ 11 := by
    have h_ne : p ≠ 2 ∧ p ≠ 5 := p_ne_2_and_5 p hp_prime h1
    have : p ≥ 2 := hp_prime.two_le
    rcases h1 with h_mod1 | h_mod9
    · have : p % 10 = 1 := h_mod1
      omega
    · have : p % 10 = 9 := h_mod9
      have : p ≠ 9 := by
        intro hp9
        subst hp9
        have : ¬ Nat.Prime 9 := by decide
        contradiction
      omega
  rcases (test_legendre p h1) with ⟨x, hx⟩
  have h_val_ge_3 : x.val ≥ 3 := by
    by_contra h_lt
    have h_cases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases h_cases with h0 | h1_eq | h2
    · have hx0 : x = 0 := (ZMod.val_eq_zero x).mp h0
      have : (5 : ZMod p) = 0 := by
        calc (5 : ZMod p) = x * x := hx
        _ = 0 * 0 := by rw [hx0]
        _ = 0 := by ring
      have h_dvd : p ∣ 5 := (CharP.cast_eq_zero_iff (ZMod p) p 5).mp this
      have : p ≤ 5 := Nat.le_of_dvd (by decide) h_dvd
      omega
    · have h_1_lt : 1 < p := by omega
      have hx1 : x = 1 := (ZMod.val_eq_one h_1_lt x).mp h1_eq
      have : (5 : ZMod p) = 1 := by
        calc (5 : ZMod p) = x * x := hx
        _ = 1 * 1 := by rw [hx1]
        _ = 1 := by ring
      have : ((4 : ℕ) : ZMod p) = 0 := by
        calc ((4 : ℕ) : ZMod p) = (5 : ZMod p) - 1 := by ring
        _ = 1 - 1 := by rw [this]
        _ = 0 := by ring
      have h_dvd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp this
      have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
      omega
    · have h_2_lt : 2 < p := by omega
      have hx2 : x = 2 := by
        apply ZMod.val_injective p
        rw [ZMod.val_two_eq_two_mod]
        rw [Nat.mod_eq_of_lt h_2_lt]
        exact h2
      have : (5 : ZMod p) = 4 := by
        calc (5 : ZMod p) = x * x := hx
        _ = 2 * 2 := by rw [hx2]
        _ = 4 := by ring
      have : ((1 : ℕ) : ZMod p) = 0 := by
        calc ((1 : ℕ) : ZMod p) = (5 : ZMod p) - 4 := by ring
        _ = 4 - 4 := by rw [this]
        _ = 0 := by ring
      have h_dvd : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp this
      have : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd
      omega
  use x.val - 1
  have h_sub : (x.val - 1) + 1 = x.val := by omega
  rw [h_sub]
  have h_val_sq : x.val ^ 2 ≥ 5 := by
    nlinarith
  have h_zmod_eq : (((x.val ^ 2 - 5 : ℕ) : ZMod p) = 0) := by
    rw [Nat.cast_sub h_val_sq]
    push_cast
    have : (x.val : ZMod p) = x := ZMod.natCast_zmod_val x
    rw [this]
    rw [pow_two]
    rw [← hx]
    ring
  exact (CharP.cast_eq_zero_iff (ZMod p) p (x.val ^ 2 - 5)).mp h_zmod_eq







def S (n k : ℕ) : ℚ :=
  if h1 : k > n then 0
  else if h2 : k = n then 4
  else if h3 : k = n - 1 then 5 * (n : ℚ) - 4
  else
    have : k < n - 1 := by omega
    have : n - (k + 1) < n - k := by omega
    have : n - (k + 2) < n - k := by omega
    (k : ℚ) * S n (k + 1) - (k + 1 : ℚ) * S n (k + 2)
termination_by n - k

lemma S_step (n k : ℕ) (hk2 : k < n - 1) :
  S n k = (k : ℚ) * S n (k + 1) - (k + 1 : ℚ) * S n (k + 2) := by
  rw [S]
  have h1 : ¬ k > n := by omega
  have h2 : ¬ k = n := by omega
  have h3 : ¬ k = n - 1 := by omega
  simp [h1, h2, h3]


lemma S_self (n : ℕ) : S n n = 4 := by
  rw [S]
  have h1 : ¬ n > n := by omega
  have h2 : n = n := rfl
  simp [h1, h2]

lemma S_sub_one (n : ℕ) (hn : 1 ≤ n) : S n (n - 1) = 5 * (n : ℚ) - 4 := by
  rw [S]
  have h1 : ¬ n - 1 > n := by omega
  have h2 : ¬ n - 1 = n := by omega
  have h3 : n - 1 = n - 1 := rfl
  simp [h1, h2, h3]


lemma S_eval_helper (n d : ℕ) (hn : 3 ≤ n) (hd : d ≤ n - 3) :
  let k := n - 1 - d
  (((k - 1 : ℕ) : ℚ)) * S n k - (k : ℚ) * (((k - 2 : ℕ) : ℚ)) * S n (k + 1) = (n^2 + 2 * n - 4 : ℚ) := by
  induction d with
  | zero =>
    intro k
    dsimp [k]
    have h_sub_1 : ((n - 1 : ℕ) : ℚ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h_sub_2 : ((n - 2 : ℕ) : ℚ) = n - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h_sub_3 : ((n - 3 : ℕ) : ℚ) = n - 3 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h_rew_n1 : n - 1 - 1 = n - 2 := by omega
    have h_rew_n2 : n - 1 - 2 = n - 3 := by omega
    rw [h_rew_n1, h_rew_n2]
    have h_sub2 : n - 1 + 1 = n := by omega
    rw [h_sub2]
    rw [S_self n]
    rw [S_sub_one n (by omega)]
    rw [h_sub_1, h_sub_2, h_sub_3]
    push_cast
    ring
  | succ d ih =>
    intro k
    -- Since succ d <= n - 3, we have d <= n - 3.
    have hd_le : d ≤ n - 3 := by omega
    -- Let us specialize the IH
    have h_ih := ih hd_le
    dsimp [k]
    let j := n - 1 - (d + 1)
    have hj_lt : j < n - 1 := by omega
    have h_step := S_step n j hj_lt
    have h_sub_j1 : ((j - 1 : ℕ) : ℚ) = j - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h_sub_j2 : ((j - 2 : ℕ) : ℚ) = j - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have h_eq : ((((j - 1 : ℕ) : ℚ)) * S n j - (j : ℚ) * (((j - 2 : ℕ) : ℚ)) * S n (j + 1)) =
                ((j : ℚ) * S n (j + 1) - (j + 1 : ℚ) * (((j - 1 : ℕ) : ℚ)) * S n (j + 2)) := by
      rw [h_step]
      rw [h_sub_j1, h_sub_j2]
      push_cast
      ring
    have h_LHS_next : ((j : ℚ) * S n (j + 1) - (j + 1 : ℚ) * (((j - 1 : ℕ) : ℚ)) * S n (j + 2)) = (n^2 + 2 * n - 4 : ℚ) := by


def S_int (n k : ℕ) : ℤ :=
  if h1 : k > n then 0
  else if h2 : k = n then 4
  else if h3 : k = n - 1 then 5 * (n : ℤ) - 4
  else
    have : k < n - 1 := by omega
    have : n - (k + 1) < n - k := by omega
    have : n - (k + 2) < n - k := by omega
    (k : ℤ) * S_int n (k + 1) - (k + 1 : ℤ) * S_int n (k + 2)
termination_by n - k

lemma S_eq_S_int (n k : ℕ) : S n k = (S_int n k : ℚ) := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rw [S, S_int]
    by_cases h1 : k > n
    · simp [h1]
    · simp [h1]
      by_cases h2 : k = n
      · simp [h2]
      · simp [h2]
        by_cases h3 : k = n - 1
        · simp [h3]
          push_cast
          rfl
        · simp [h3]
          -- Now we use IH for k + 1 and k + 2
          have hk1 : n - (k + 1) < n - k := by omega
          have hk2 : n - (k + 2) < n - k := by omega
          have h_ih1 := ih (k + 1) (by omega) n
          have h_ih2 := ih (k + 2) (by omega) n
          rw [h_ih1, h_ih2]
          push_cast
          rfl
termination_by n - k

      have h_rew_nat : n - 1 - d - 1 = j := by omega
      have h_rew2_nat : n - 1 - d = j + 1 := by omega
      have h_rew3_nat : n - 1 - d - 2 = j - 1 := by omega
      have h_rew4_nat : n - 1 - d + 1 = j + 2 := by omega
      have h_ih_simp : ((n - 1 - d - 1 : ℕ) : ℚ) * S n (n - 1 - d) - (((n - 1 - d : ℕ) : ℚ)) * (((n - 1 - d - 2 : ℕ) : ℚ)) * S n (n - 1 - d + 1) = (n^2 + 2 * n - 4 : ℚ) := h_ih
      rw [h_rew3_nat, h_rew_nat, h_rew4_nat, h_rew2_nat] at h_ih_simp
      push_cast at h_ih_simp
      exact h_ih_simp
    rw [h_eq, h_LHS_next]



lemma S_two_eq (n : ℕ) (hn : 3 ≤ n) : S n 2 = (n^2 + 2 * n - 4 : ℚ) := by
  have h_helper := S_eval_helper n (n - 3) hn (by omega)
  dsimp only at h_helper
  have h_k_eq : n - 1 - (n - 3) = 2 := by omega
  have h_k_sub1 : n - 1 - (n - 3) - 1 = 1 := by omega
  have h_k_sub2 : n - 1 - (n - 3) - 2 = 0 := by omega
  have h_k_add1 : n - 1 - (n - 3) + 1 = 3 := by omega
  rw [h_k_sub1, h_k_sub2, h_k_add1, h_k_eq] at h_helper
  push_cast at h_helper
  linarith


lemma S_two_eq_kp (n p k : ℕ) (hn : 3 ≤ n) (hkp : n^2 + 2 * n - 4 = k * p) :
  S n 2 = (k : ℚ) * (p : ℚ) := by
  have h := S_two_eq n hn
  rw [h]
  have h_eq : ((n^2 + 2 * n - 4 : ℕ) : ℚ) = ((k * p : ℕ) : ℚ) := by
    exact congrArg Nat.cast hkp
  rw [Nat.cast_sub (by omega)] at h_eq
  push_cast at h_eq
  exact h_eq



lemma S_two_pos (n : ℕ) (hn : 3 ≤ n) : S n 2 > 0 := by
  rw [S_two_eq n hn]
  have hn_q : (n : ℚ) ≥ 3 := by exact_mod_cast hn
  have : (n^2 + 2 * n - 4 : ℚ) ≥ 11 := by
    push_cast
    nlinarith
  linarith

lemma S_pos_helper (n d : ℕ) (hn : 3 ≤ n) (hd : d ≤ n - 2) :
  let k := n - d
  S n k > 0 := by
  induction d with
  | zero =>
    intro k
    dsimp [k]
    rw [S_self n]
    linarith
  | succ d ih =>
    intro k
    dsimp [k]
    by_cases hd0 : d = 0
    · subst hd0
      rw [S_sub_one n (by omega)]
      have hn_q : (n : ℚ) ≥ 3 := by exact_mod_cast hn
      have : (5 * (n : ℚ) - 4) ≥ 11 := by
        linarith
      linarith
    · have hk_ge : 2 ≤ n - (d + 1) := by omega
      let j := n - d
      have hj_le : d ≤ n - 2 := by omega
      have h_ih_j := ih hj_le
      -- h_ih_j is S n (n - d) > 0, which is S n j > 0.
      have hd_le : d ≤ n - 3 := by omega
      have h_eval := S_eval_helper n d hn hd_le
      dsimp only at h_eval
      -- Now h_eval is: ↑(n - 1 - d - 1) * S n (n - 1 - d) - ↑(n - 1 - d) * ↑(n - 1 - d - 2) * S n (n - 1 - d + 1) = ↑n ^ 2 + 2 * ↑n - 4
      -- We want to prove S n (n - (d + 1)) > 0
      rw [← S_two_eq n hn] at h_eval
      have h_rew1 : n - 1 - d = n - (d + 1) := by omega
      have h_rew2 : n - 1 - d - 1 = n - (d + 1) - 1 := by omega
      have h_rew3 : n - 1 - d - 2 = n - (d + 1) - 2 := by omega
      have h_rew4 : n - 1 - d + 1 = n - d := by omega
      rw [h_rew2, h_rew3, h_rew4, h_rew1] at h_eval
      -- Now h_eval is: ↑(n - (d + 1) - 1) * S n (n - (d + 1)) - ↑(n - (d + 1)) * ↑(n - (d + 1) - 2) * S n (n - d) = S n 2
      have h_s2_pos := S_two_pos n hn
      have h_c1 : ((n - (d + 1) - 1 : ℕ) : ℚ) ≥ 1 := by
        have : n - (d + 1) - 1 ≥ 1 := by omega
        exact_mod_cast this
      have h_c2 : ((n - (d + 1) : ℕ) : ℚ) ≥ 2 := by
        have : 2 ≤ n - (d + 1) := hk_ge
        exact_mod_cast this
      have h_c3 : ((n - (d + 1) - 2 : ℕ) : ℚ) ≥ 0 := by
        exact_mod_cast (by omega : n - (d + 1) - 2 ≥ 0)
      have h_term_nonneg : ((n - (d + 1) : ℕ) : ℚ) * (((n - (d + 1) - 2 : ℕ) : ℚ)) * S n (n - d) ≥ 0 := by
        have h_c2_nonneg : ((n - (d + 1) : ℕ) : ℚ) ≥ 0 := by linarith
        have h_ih_nonneg : S n (n - d) ≥ 0 := by linarith
        positivity
      have h_prod : (((n - (d + 1) - 1 : ℕ) : ℚ)) * S n (n - (d + 1)) > 0 := by
        linarith
      have : S n (n - (d + 1)) > 0 := by
        nlinarith
      exact this


lemma continued_fraction_denominator_eq_S_helper (n d : ℕ) (hn : 3 ≤ n) (hd : d ≤ n - 3) :
  let k := n - 1 - d
  continued_fraction_denominator n k = S n k / S n (k + 1) := by
  induction d with
  | zero =>
    intro k
    dsimp [k]
    have h_sub1 : n - 1 + 1 = n := by omega
    -- Let us unfold continued_fraction_denominator
    rw [continued_fraction_denominator]
    have h_n2 : ¬ n ≤ 2 := by omega
    have h_cond : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := by omega
    have h_eq_case : n - 1 = n - 1 := rfl
    simp [h_n2, h_cond, h_eq_case]
    -- Now goal is: ↑(n - 1) + ↑n / 4 = S n (n - 1) / S n (n - 1 + 1)
    rw [h_sub1]
    rw [S_self n]
    rw [S_sub_one n (by omega)]
    have : 1 ≤ n := by omega
    rw [Nat.cast_sub this]
    push_cast
    ring
  | succ d ih =>
    intro k
    have hd_le : d ≤ n - 3 := by omega
    have h_ih := ih hd_le
    dsimp [k]
    let j := n - 1 - (d + 1)
    have h_j : n - 1 - (d + 1) = j := rfl
    rw [h_j]
    -- Unfold continued_fraction_denominator
    rw [continued_fraction_denominator]
    have h_n2 : ¬ n ≤ 2 := by omega
    have hj_cond : 2 ≤ j ∧ j ≤ n - 1 := by omega
    have hj_ne : ¬ j = n - 1 := by omega
    simp [h_n2, hj_cond, hj_ne]
    -- Now goal is: ↑j - ↑(j + 1) / continued_fraction_denominator n (j + 1) = S n j / S n (j + 1)
    -- We know j + 1 = n - 1 - d
    have h_j_add : j + 1 = n - 1 - d := by omega
    rw [← h_j_add] at h_ih
    rw [h_ih]
    -- Now we want to show: ↑j - ↑(j + 1) / (S n (j + 1) / S n (j + 2)) = S n j / S n (j + 1)
    have hj_lt : j < n - 1 := by omega
    have hj_le2 : d + 1 ≤ n - 2 := by omega
    have h_sj1_pos : S n (j + 1) > 0 := by
      have : S n (n - (d + 1)) > 0 := S_pos_helper n (d + 1) hn hj_le2
      have h_nat_eq : j + 1 = n - (d + 1) := by omega
      rw [← h_nat_eq] at this
      exact this
    have h_sj1_ne : S n (j + 1) ≠ 0 := by linarith
    rw [div_div_eq_mul_div]
    rw [S_step n j hj_lt]
    rw [sub_div]
    rw [mul_div_cancel_right₀ (↑j) h_sj1_ne]



lemma continued_fraction_denominator_two_eq (n : ℕ) (hn : 3 ≤ n) :
  continued_fraction_denominator n 2 = S n 2 / S n 3 := by
  have := continued_fraction_denominator_eq_S_helper n (n - 3) hn (by omega)
  dsimp only at this
  have h_rew : n - 1 - (n - 3) = 2 := by omega
  rw [h_rew] at this
  exact this



