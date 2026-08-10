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

lemma exists_n_dvd (p : ℕ) [hp : Fact p.Prime] (h1 : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : ∃ n : ℕ, 3 ≤ n ∧ n < p ∧ p ∣ (n + 1) ^ 2 - 5 := by
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
  have h_ne_3 : x.val ≠ 3 := by
    intro h3
    have h_zmod_3 : x = 3 := by
      rw [← ZMod.natCast_zmod_val x, h3]
      rfl
    have h_5_eq_9 : (5 : ZMod p) = 9 := by
      calc (5 : ZMod p) = x * x := hx
      _ = (3 : ZMod p) * 3 := by rw [h_zmod_3]
      _ = 9 := by ring
    have : (4 : ZMod p) = 0 := by
      calc (4 : ZMod p) = (9 : ZMod p) - 5 := by ring
      _ = 5 - 5 := by rw [← h_5_eq_9]
      _ = 0 := by ring
    have h_dvd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp this
    have : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd
    omega
  have h_val_ge_4 : x.val ≥ 4 := by omega
  have hn_ge_3 : x.val - 1 ≥ 3 := by omega
  use x.val - 1
  have h_lt_p : x.val - 1 < p := by
    have : x.val < p := x.val_lt
    omega
  refine ⟨hn_ge_3, h_lt_p, ?_⟩
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



def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


lemma A363347_eq_of_S (n : ℕ) (hn : 3 ≤ n) : A363347 n = (S n 2 / S n 3).num.natAbs := by
  have this : ¬ n ≤ 2 := by omega
  unfold A363347
  rw [if_neg this]
  rw [continued_fraction_denominator_two_eq n hn]


lemma S_is_int_helper (n d : ℕ) : ∀ k, n - k = d → ∃ z : ℤ, S n k = (z : ℚ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk_eq
    rw [S]
    split_ifs with h1 h2 h3
    · use 0; rfl
    · use 4; rfl
    · use 5 * (n : ℤ) - 4; push_cast; rfl
    · have hd1 : n - (k + 1) < d := by omega
      have hd2 : n - (k + 2) < d := by omega
      rcases ih (n - (k + 1)) hd1 (k + 1) (by omega) with ⟨z1, hz1⟩
      rcases ih (n - (k + 2)) hd2 (k + 2) (by omega) with ⟨z2, hz2⟩
      rw [hz1, hz2]
      use (k : ℤ) * z1 - (k + 1 : ℤ) * z2
      push_cast
      rfl

lemma S_is_int (n k : ℕ) : ∃ z : ℤ, S n k = (z : ℚ) := by
  exact S_is_int_helper n (n - k) k rfl


def M_val : ℕ → ℤ
  | 0 => 1
  | d + 1 => M_val d + (d + 1).factorial

lemma M_val_even (d : ℕ) (hd : d ≥ 1) : Even (M_val d) := by
  induction d with
  | zero => contradiction
  | succ d ih =>
    by_cases hd0 : d = 0
    · subst hd0
      exact ⟨1, rfl⟩
    · have : d ≥ 1 := by omega
      have h_even : Even (M_val d) := ih this
      have h_fac_even : Even ((d + 1).factorial : ℤ) := by
        have h_ge : d + 1 ≥ 2 := by omega
        have h_dvd : 2 ∣ (d + 1).factorial := Nat.dvd_factorial (by decide) h_ge
        have h_dvd_z : (2 : ℤ) ∣ ((d + 1).factorial : ℤ) := by exact_mod_cast h_dvd
        exact even_iff_two_dvd.mpr h_dvd_z
      exact Even.add h_even h_fac_even

lemma S_congruence_helper_d (n : ℕ) (hn : 3 ≤ n) (d : ℕ) (hd : d + 3 < n) :
  2 * S n 3 - ((d + 3 : ℕ) : ℚ) * (((d + 1).factorial : ℕ) : ℚ) * S n (d + 4) = ((M_val d : ℤ) : ℚ) * S n 2 := by
  induction d generalizing n with
  | zero =>
    -- d = 0, k = 3. S_eval_helper for d_eval = n - 4.
    -- Since d + 3 < n, 3 < n, so n - 4 is valid.
    have hd_eval : n - 4 ≤ n - 3 := by omega
    have h_eval := S_eval_helper n (n - 4) hn hd_eval
    dsimp only at h_eval
    have h_k_eq : n - 1 - (n - 4) = 3 := by omega
    rw [h_k_eq] at h_eval
    have h_rew2 : 3 - 1 = 2 := by decide
    have h_rew3 : 3 - 2 = 1 := by decide
    have h_rew4 : 3 + 1 = 4 := by decide
    rw [h_rew2, h_rew3, h_rew4] at h_eval
    push_cast at h_eval
    rw [← S_two_eq n hn] at h_eval
    have h_goal : 2 * S n 3 - ((0 + 3 : ℕ) : ℚ) * (((0 + 1).factorial : ℕ) : ℚ) * S n (0 + 4) = 2 * S n 3 - 3 * 1 * S n 4 := by
      norm_num
    rw [h_goal]
    push_cast
    unfold M_val
    push_cast
    linarith
  | succ d ih =>
    -- We have IH for d. Since (d + 1) + 3 < n, d + 3 < n.
    have hd_lt : d + 3 < n := by omega
    have h_ih := ih n hn hd_lt
    -- Now we want S_eval_helper for k = d + 4, which is d_eval = n - 1 - (d + 4) = n - d - 5
    have hd_eval : n - d - 5 ≤ n - 3 := by omega
    have h_eval := S_eval_helper n (n - d - 5) hn hd_eval
    dsimp only at h_eval
    have h_k_eq : n - 1 - (n - d - 5) = d + 4 := by omega
    rw [h_k_eq] at h_eval
    have h_rew2 : d + 4 - 1 = d + 3 := by omega
    have h_rew3 : d + 4 - 2 = d + 2 := by omega
    have h_rew4 : d + 4 + 1 = d + 5 := by omega
    rw [h_rew2, h_rew3, h_rew4] at h_eval
    rw [← S_two_eq n hn] at h_eval
    -- h_eval is: (d + 3) * S n (d + 4) - (d + 4) * (d + 2) * S n (d + 5) = S n 2
    -- Let us multiply h_eval by (d + 1)!
    have h_mult : ((d + 3 : ℕ) : ℚ) * (((d + 1).factorial : ℕ) : ℚ) * S n (d + 4) -
                  ((d + 4 : ℕ) : ℚ) * (((d + 2).factorial : ℕ) : ℚ) * S n (d + 5) =
                  (((d + 1).factorial : ℕ) : ℚ) * S n 2 := by
      -- we can use Nat.factorial_succ to rewrite (d + 2) * (d + 1)! to (d + 2)!
      have h_fac : ((d + 2 : ℕ) : ℚ) * (((d + 1).factorial : ℕ) : ℚ) = (((d + 2).factorial : ℕ) : ℚ) := by
        push_cast
        rw [Nat.factorial_succ (d + 1)]
        push_cast
        ring
      rw [← h_fac]
      calc ((d + 3 : ℕ) : ℚ) * (((d + 1).factorial : ℕ) : ℚ) * S n (d + 4) - ((d + 4 : ℕ) : ℚ) * (((d + 2 : ℕ) : ℚ) * (((d + 1).factorial : ℕ) : ℚ)) * S n (d + 5)
        _ = (((d + 1).factorial : ℕ) : ℚ) * (((d + 3 : ℕ) : ℚ) * S n (d + 4) - ((d + 4 : ℕ) : ℚ) * ((d + 2 : ℕ) : ℚ) * S n (d + 5)) := by ring
        _ = (((d + 1).factorial : ℕ) : ℚ) * S n 2 := by rw [h_eval]
    -- Now we combine h_ih and h_mult
    push_cast at h_ih
    push_cast at h_mult
    have h1 : d + 1 + 3 = d + 4 := by omega
    have h2 : d + 1 + 1 = d + 2 := by omega
    have h3 : d + 1 + 4 = d + 5 := by omega
    rw [h1, h2, h3]
    unfold M_val
    push_cast
    linarith


lemma k_le_n_sub_3_or_dvd_4 (n p k : ℕ) (hn : 3 ≤ n) (hkp : n^2 + 2 * n - 4 = k * p) (hn_lt_p : n < p) :
  k ≤ n - 3 ∨ k ∣ 4 := by
  rw [pow_two] at hkp
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  by_cases h : k ≤ n - 3
  · left; exact h
  · right
    have hp_ge : p ≥ n + 1 := by omega
    have h_kp : k * p = n * n + 2 * n - 4 := hkp.symm
    -- We show k < n + 1
    have h_lt : k < n + 1 := by
      by_contra h_ge
      have h_ge_le : n + 1 ≤ k := by omega
      have h1 : k * p ≥ (n + 1) * (n + 1) := Nat.mul_le_mul h_ge_le hp_ge
      have h_expand : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
      have h2 : n * n + 2 * n - 4 < (n + 1) * (n + 1) := by
        omega
      omega
    -- So k can be n - 2, n - 1, or n
    have h_cases : k = n - 2 ∨ k = n - 1 ∨ k = n := by omega
    rcases h_cases with hk_n2 | hk_n1 | hk_n
    · -- k = n - 2
      have h_dvd : (n - 2) ∣ (n * n + 2 * n - 4) := by
        rw [← hk_n2, ← h_kp]
        exact dvd_mul_right k p
      have h_sub1_exact : 4 ≤ n * n + 2 * n := by omega
      have h_alg : n * n + 2 * n - 4 = (n - 2) * (n + 4) + 4 := by
        zify [hn2, h_sub1_exact]
        ring
      rw [h_alg] at h_dvd
      have h_dvd_4 : (n - 2) ∣ 4 := (Nat.dvd_add_right (dvd_mul_right (n - 2) (n + 4))).mp h_dvd
      rw [hk_n2]
      exact h_dvd_4
    · -- k = n - 1
      by_cases hp_ge2 : p ≥ n + 3
      · have : k * p ≥ (n - 1) * (n + 3) := by
          rw [hk_n1]
          exact Nat.mul_le_mul_left (n - 1) hp_ge2
        have h_sub3_exact : 3 ≤ n * n + 2 * n := by nlinarith
        have h_expand : (n - 1) * (n + 3) = n * n + 2 * n - 3 := by
          zify [hn1, h_sub3_exact]
          ring
        have : n * n + 2 * n - 4 < (n - 1) * (n + 3) := by
          rw [h_expand]
          omega
        omega
      · have : p = n + 1 ∨ p = n + 2 := by omega
        rcases this with hp1 | hp2
        · -- p = n + 1
          have h_eq : (n - 1) * (n + 1) = n * n + 2 * n - 4 := by
            rw [hk_n1, hp1] at h_kp
            exact h_kp
          have h_sub4_exact : 1 ≤ n * n := by nlinarith
          have h_expand : (n - 1) * (n + 1) = n * n - 1 := by
            zify [hn1, h_sub4_exact]
            ring
          rw [h_expand] at h_eq
          have h_eq_z : (n * n : ℤ) - 1 = (n * n : ℤ) + 2 * (n : ℤ) - 4 := by
            have h_le1 : 1 ≤ n * n := by nlinarith
            have h_le2 : 4 ≤ n * n + 2 * n := by nlinarith
            have h_cast1 : ((n * n - 1 : ℕ) : ℤ) = (n * n : ℤ) - 1 := Nat.cast_sub h_le1
            have h_cast2 : ((n * n + 2 * n - 4 : ℕ) : ℤ) = (n * n + 2 * n : ℤ) - 4 := Nat.cast_sub h_le2
            rw [← h_cast1, ← h_cast2]
            rw [h_eq]
          linarith
        · -- p = n + 2
          have h_eq : (n - 1) * (n + 2) = n * n + 2 * n - 4 := by
            rw [hk_n1, hp2] at h_kp
            exact h_kp
          have h_sub5_exact : 2 ≤ n * n + n := by nlinarith
          have h_expand : (n - 1) * (n + 2) = n * n + n - 2 := by
            zify [hn1, h_sub5_exact]
            ring
          rw [h_expand] at h_eq
          have h_eq_z : (n * n : ℤ) + (n : ℤ) - 2 = (n * n : ℤ) + 2 * (n : ℤ) - 4 := by
            have h_le1 : 2 ≤ n * n + n := by nlinarith
            have h_le2 : 4 ≤ n * n + 2 * n := by nlinarith
            have h_cast1 : ((n * n + n - 2 : ℕ) : ℤ) = (n * n + n : ℤ) - 2 := Nat.cast_sub h_le1
            have h_cast2 : ((n * n + 2 * n - 4 : ℕ) : ℤ) = (n * n + 2 * n : ℤ) - 4 := Nat.cast_sub h_le2
            rw [← h_cast1, ← h_cast2]
            rw [h_eq]
          linarith
    · -- k = n
      by_cases hp_ge2 : p ≥ n + 2
      · have h_ge : k * p ≥ n * (n + 2) := by
          rw [hk_n]
          exact Nat.mul_le_mul_left n hp_ge2
        have h_expand : n * (n + 2) = n * n + 2 * n := by
          ring
        have h_ge_rew : n * n + 2 * n - 4 ≥ n * n + 2 * n := by
          rw [← h_kp]
          rw [h_expand] at h_ge
          exact h_ge
        have h_eq_z : (n * n + 2 * n : ℤ) - 4 ≥ (n * n + 2 * n : ℤ) := by
          have h_le1 : 4 ≤ n * n + 2 * n := by nlinarith
          have h_cast1 : ((n * n + 2 * n - 4 : ℕ) : ℤ) = (n * n + 2 * n : ℤ) - 4 := Nat.cast_sub h_le1
          rw [← h_cast1]
          exact_mod_cast h_ge_rew
        linarith
      · have : p = n + 1 := by omega
        have h_eq : n * (n + 1) = n * n + 2 * n - 4 := by
          rw [hk_n, this] at h_kp
          exact h_kp
        have h_expand : n * (n + 1) = n * n + n := by
          ring
        rw [h_expand] at h_eq
        have : n = 4 := by omega
        subst this
        have : k = 4 := by omega
        subst this
        decide


noncomputable def S_int (n k : ℕ) : ℤ := (S_is_int n k).choose

lemma S_int_spec (n k : ℕ) : S n k = (S_int n k : ℚ) := (S_is_int n k).choose_spec

lemma S_int_self (n : ℕ) : S_int n n = 4 := by
  have h : (S_int n n : ℚ) = 4 := by
    rw [← S_int_spec, S_self]
  exact_mod_cast h

lemma S_int_sub_one (n : ℕ) (hn : 1 ≤ n) : S_int n (n - 1) = 5 * (n : ℤ) - 4 := by
  have h : (S_int n (n - 1) : ℚ) = 5 * (n : ℚ) - 4 := by
    rw [← S_int_spec, S_sub_one n hn]
  exact_mod_cast h

lemma S_int_step (n k : ℕ) (hk : k < n - 1) :
  S_int n k = (k : ℤ) * S_int n (k + 1) - (k + 1 : ℤ) * S_int n (k + 2) := by
  have h : (S_int n k : ℚ) = (k : ℚ) * S n (k + 1) - (k + 1 : ℚ) * S n (k + 2) := by
    rw [← S_int_spec, S_step n k hk]
  rw [S_int_spec n (k + 1), S_int_spec n (k + 2)] at h
  exact_mod_cast h

lemma S_int_even_helper (n d : ℕ) (hn : Even n) : ∀ k, n - k = d → 2 ∣ S_int n k := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk_eq
    by_cases hk_gt : k > n
    · have : S_int n k = 0 := by
        have : (S_int n k : ℚ) = 0 := by
          rw [← S_int_spec, S]
          simp [hk_gt]
        exact_mod_cast this
      rw [this]
      exact dvd_zero 2
    · by_cases hk_eq_n : k = n
      · subst hk_eq_n
        rw [S_int_self]
        decide
      · by_cases hk_eq_n1 : k = n - 1
        · subst hk_eq_n1
          have hn_ge : n ≥ 1 := by omega
          rw [S_int_sub_one n hn_ge]
          rcases hn with ⟨m, rfl⟩
          use 5 * (m : ℤ) - 2
          push_cast
          ring
        · have hk_lt : k < n - 1 := by omega
          rw [S_int_step n k hk_lt]
          have hd1 : n - (k + 1) < d := by omega
          have hd2 : n - (k + 2) < d := by omega
          have h1 := ih (n - (k + 1)) hd1 (k + 1) (by omega)
          have h2 := ih (n - (k + 2)) hd2 (k + 2) (by omega)
          exact dvd_sub (dvd_mul_of_dvd_right h1 k) (dvd_mul_of_dvd_right h2 (k + 1))

lemma S_int_even (n k : ℕ) (hn : Even n) : 2 ∣ S_int n k := by
  exact S_int_even_helper n (n - k) hn k rfl

noncomputable def T_int (n k : ℕ) : ℤ := S_int n k / 2

lemma S_int_eq_two_mul_T (n k : ℕ) (hn : Even n) : S_int n k = 2 * T_int n k := by
  unfold T_int
  have h_dvd := S_int_even n k hn
  exact (Int.mul_ediv_cancel' h_dvd).symm

lemma T_int_self (n : ℕ) (hn : Even n) : T_int n n = 2 := by
  unfold T_int
  rw [S_int_self n]
  rfl

lemma T_int_sub_one (n : ℕ) (hn : Even n) (hn1 : 1 ≤ n) : T_int n (n - 1) = 5 * (n / 2 : ℤ) - 2 := by
  unfold T_int
  rw [S_int_sub_one n hn1]
  rcases hn with ⟨m, rfl⟩
  push_cast
  omega

lemma T_int_step (n k : ℕ) (hn : Even n) (hk : k < n - 1) :
  T_int n k = (k : ℤ) * T_int n (k + 1) - (k + 1 : ℤ) * T_int n (k + 2) := by
  have h_step : 2 * T_int n k = 2 * ((k : ℤ) * T_int n (k + 1) - (k + 1 : ℤ) * T_int n (k + 2)) := by
    calc 2 * T_int n k = S_int n k := by rw [S_int_eq_two_mul_T n k hn]
    _ = (k : ℤ) * S_int n (k + 1) - (k + 1 : ℤ) * S_int n (k + 2) := S_int_step n k hk
    _ = (k : ℤ) * (2 * T_int n (k + 1)) - (k + 1 : ℤ) * (2 * T_int n (k + 2)) := by
          rw [S_int_eq_two_mul_T n (k + 1) hn, S_int_eq_two_mul_T n (k + 2) hn]
    _ = 2 * ((k : ℤ) * T_int n (k + 1) - (k + 1 : ℤ) * T_int n (k + 2)) := by ring
  linarith

lemma T_int_even_helper (n d : ℕ) (hn : Even n) (hn6 : 6 ≤ n) : ∀ k, n - k = d → d ≥ 2 → 2 ∣ T_int n k := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk_eq hd_ge
    have hn_ge1 : 1 ≤ n := by omega
    by_cases hd_eq2 : d = 2
    · subst hd_eq2
      have hk_eq_n2 : k = n - 2 := by omega
      subst hk_eq_n2
      rw [T_int_step n (n - 2) hn (by omega)]
      have h1 : T_int n (n - 2 + 2) = T_int n n := by
        have : n - 2 + 2 = n := by omega
        rw [this]
      have h2 : T_int n (n - 2 + 1) = T_int n (n - 1) := by
        have : n - 2 + 1 = n - 1 := by omega
        rw [this]
      rw [h1, h2]
      rw [T_int_self n hn]
      have : ((n - 2 : ℕ) : ℤ) = 2 * (((n / 2 : ℕ) : ℤ) - 1) := by
        rcases hn with ⟨m, rfl⟩
        omega
      rw [this]
      use (((n / 2 : ℕ) : ℤ) - 1) * T_int n (n - 1) - (2 * (((n / 2 : ℕ) : ℤ) - 1) + 1)
      ring
    · have hd_gt : d > 2 := by omega
      by_cases hd_eq3 : d = 3
      · subst hd_eq3
        have hk_eq_n3 : k = n - 3 := by omega
        subst hk_eq_n3
        rw [T_int_step n (n - 3) hn (by omega)]
        have h1 : T_int n (n - 3 + 1) = T_int n (n - 2) := by
          have : n - 3 + 1 = n - 2 := by omega
          rw [this]
        have h2 : T_int n (n - 3 + 2) = T_int n (n - 1) := by
          have : n - 3 + 2 = n - 1 := by omega
          rw [this]
        rw [h1, h2]
        have hd2 : n - (n - 2) < 3 := by omega
        have h_t2 : 2 ∣ T_int n (n - 2) := by
          apply ih (n - (n - 2)) (by omega) (n - 2) (by omega) (by omega)
        rcases h_t2 with ⟨z, hz⟩
        rw [hz]
        have h_rew_n3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
        rw [h_rew_n3]
        have h_rew_n3_1 : (n : ℤ) - 3 + 1 = 2 * (((n / 2 : ℕ) : ℤ) - 1) := by
          rcases hn with ⟨m, rfl⟩
          omega
        rw [h_rew_n3_1]
        use (n - 3 : ℤ) * z - (((n / 2 : ℕ) : ℤ) - 1) * T_int n (n - 1)
        ring
      · have hk_lt : k < n - 3 := by omega
        rw [T_int_step n k hn (by omega)]
        have hd1 : n - (k + 1) < d := by omega
        have hd2 : n - (k + 2) < d := by omega
        have h1 := ih (n - (k + 1)) hd1 (k + 1) (by omega) (by omega)
        have h2 := ih (n - (k + 2)) hd2 (k + 2) (by omega) (by omega)
        exact dvd_sub (dvd_mul_of_dvd_right h1 k) (dvd_mul_of_dvd_right h2 (k + 1))

lemma T_int_even (n k : ℕ) (hn : Even n) (hn6 : 6 ≤ n) (hk : k ≤ n - 2) : 2 ∣ T_int n k := by
  have : n - k ≥ 2 := by omega
  exact T_int_even_helper n (n - k) hn hn6 k rfl this

lemma S_int_congruence (n : ℕ) (hn : 3 ≤ n) (d : ℕ) (hd : d + 3 < n) :
  2 * S_int n 3 - (d + 3 : ℤ) * ((d + 1).factorial : ℤ) * S_int n (d + 4) = (M_val d : ℤ) * S_int n 2 := by
  have hM := S_congruence_helper_d n hn d hd
  have h_eq : ((2 * S_int n 3 - (d + 3 : ℤ) * ((d + 1).factorial : ℤ) * S_int n (d + 4) : ℤ) : ℚ) = (((M_val d * S_int n 2 : ℤ) : ℚ)) := by
    push_cast
    rw [← S_int_spec, ← S_int_spec, ← S_int_spec]
    push_cast at hM
    exact hM
  exact_mod_cast h_eq

lemma even_n_of_even_kp (n k p : ℕ) (hn : 3 ≤ n) (hkp : n^2 + 2 * n - 4 = k * p) (hk : Even k) : Even n := by
  have hk_z : Even (k : ℤ) := by exact_mod_cast hk
  have hkp_z : (n : ℤ)^2 + 2 * (n : ℤ) - 4 = (k : ℤ) * (p : ℤ) := by
    have : n^2 + 2 * n ≥ 4 := by omega
    exact_mod_cast hkp
  have h_even : Even ((n : ℤ)^2 + 2 * (n : ℤ) - 4) := by
    rw [hkp_z]
    rcases hk_z with ⟨r, hr⟩
    rw [hr]
    use r * (p : ℤ)
    ring
  have h_n_z : Even (n : ℤ) := by
    by_contra hn_odd
    have hn_odd_z : ∃ q : ℤ, (n : ℤ) = 2 * q + 1 := by
      exact Int.not_even_iff_odd.mp hn_odd
    rcases hn_odd_z with ⟨q, hq⟩
    rcases h_even with ⟨s, hs⟩
    have : (n : ℤ)^2 + 2 * (n : ℤ) - 4 = 2 * (2 * q^2 + 4 * q - 1) + 1 := by
      rw [hq]
      ring
    rw [this] at hs
    have h_mod : (2 * (2 * q^2 + 4 * q - 1) + 1) % 2 = (2 * s) % 2 := by
      rw [hs]
      omega
    omega
  exact_mod_cast h_n_z

lemma p_dvd_S_all_helper (n : ℕ) (hn : 3 ≤ n) (hp_prime : p.Prime) (hn_lt_p : n < p) (hp : (p : ℤ) ∣ S_int n 2) (hp3 : (p : ℤ) ∣ S_int n 3) :
  ∀ k, k ≤ n → k ≥ 2 → (p : ℤ) ∣ S_int n k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk_le hk_ge
    by_cases hk2 : k = 2
    · subst hk2; exact hp
    · by_cases hk3 : k = 3
      · subst hk3; exact hp3
      · have hk_gt : k ≥ 4 := by omega
        have h_step := S_int_step n (k - 2) (by omega)
        have h_ind1 : k - 2 + 1 = k - 1 := by omega
        have h_ind2 : k - 2 + 2 = k := by omega
        have h_coeff1 : ((k - 2 : ℕ) : ℤ) + 1 = (k - 1 : ℤ) := by omega
        rw [h_ind1, h_ind2, h_coeff1] at h_step
        have h_dvd1 := ih (k - 2) (by omega) (by omega) (by omega)
        have h_dvd2 := ih (k - 1) (by omega) (by omega) (by omega)
        have h_dvd_prod : (p : ℤ) ∣ (k - 1 : ℤ) * S_int n k := by
          have : (k - 1 : ℤ) * S_int n k = ((k - 2 : ℕ) : ℤ) * S_int n (k - 1) - S_int n (k - 2) := by linarith [h_step]
          rw [this]
          exact dvd_sub (dvd_mul_of_dvd_right h_dvd2 ((k - 2 : ℕ) : ℤ)) h_dvd1
        have hp_prime_z : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
        have h_not_dvd_k1 : ¬ (p : ℤ) ∣ (k - 1 : ℤ) := by
          intro h_dvd
          have h_pos : 0 < (k - 1 : ℤ) := by omega
          have : (p : ℤ) ≤ (k - 1 : ℤ) := Int.le_of_dvd h_pos h_dvd
          omega
        exact (Prime.dvd_mul hp_prime_z).mp h_dvd_prod |>.resolve_left h_not_dvd_k1

lemma p_ge_11_of_mod10 (p : ℕ) (hp_prime : p.Prime) (h_mod : p % 10 = 1 ∨ p % 10 = 9) : p ≥ 11 := by
  have h_ne : p ≠ 2 ∧ p ≠ 5 := p_ne_2_and_5 p hp_prime h_mod
  have hp_ge_2 : p ≥ 2 := hp_prime.two_le
  rcases h_mod with h_mod1 | h_mod9
  · clear hp_prime
    omega
  · have : p ≠ 9 := by
      intro hp9
      subst hp9
      have : ¬ Nat.Prime 9 := by decide
      contradiction
    clear hp_prime
    omega

lemma p_not_dvd_S3 (n p : ℕ) (hn : 3 ≤ n) (hp_prime : p.Prime) (h_mod : p % 10 = 1 ∨ p % 10 = 9) (hn_lt_p : n < p) (hp : (p : ℤ) ∣ S_int n 2) :
  ¬ (p : ℤ) ∣ S_int n 3 := by
  intro hp3
  have hn_le : n ≤ n := by omega
  have hn_ge2 : n ≥ 2 := by omega
  have h_dvd_n := p_dvd_S_all_helper n hn hp_prime hn_lt_p hp hp3 n hn_le hn_ge2
  rw [S_int_self n] at h_dvd_n
  have hp_ge_11 : p ≥ 11 := p_ge_11_of_mod10 p hp_prime h_mod
  have : p ∣ 4 := by exact_mod_cast h_dvd_n
  have : p ≤ 4 := Nat.le_of_dvd (by decide) this
  linarith

lemma k_dvd_S3 (n p k : ℕ) (hn : 3 ≤ n) (hkp : n^2 + 2 * n - 4 = k * p) (hp_prime : p.Prime) (h_mod : p % 10 = 1 ∨ p % 10 = 9) (hn_lt_p : n < p) :
  (k : ℤ) ∣ S_int n 3 := by
  by_cases hk_case : k ≤ n - 3 ∧ k ≥ 3
  · have hk_le := hk_case.1
    have hk_ge := hk_case.2
    have hd_eq : (k - 3) + 3 < n := by omega
    have hM := S_int_congruence n hn (k - 3) hd_eq
    have hk_sub3 : ((k - 3 : ℕ) : ℤ) + 3 = (k : ℤ) := by omega
    rw [hk_sub3] at hM
    have h_s2_eq : S_int n 2 = k * p := by
      have : (S_int n 2 : ℚ) = (k * p : ℚ) := by
        rw [← S_int_spec, S_two_eq_kp n p k hn hkp]
      exact_mod_cast this
    rw [h_s2_eq] at hM
    have h_dvd_2 : (k : ℤ) ∣ 2 * S_int n 3 := by
      use (k - 3 + 1).factorial * S_int n (k - 3 + 4) + M_val (k - 3) * p
      linarith
    by_cases hk_even : Even k
    · have hn_even : Even n := even_n_of_even_kp n k p hn hkp hk_even
      have hn6 : 6 ≤ n := by
        have hk_ne_2 : k ≠ 2 := by
          intro hk2
          subst hk2
          rcases hk_even with ⟨m, hm⟩
          have hn_eq_2m : n = 2 * m := by omega
          subst hn_eq_2m
          have h_kp_even : 4 * m * m + 4 * m - 4 = 2 * p := by
            have : (2 * m)^2 = 4 * m * m := by ring
            omega
          have h_p_even : p = 2 * (m * m + m - 1) := by
            generalize m * m = mm at h_kp_even ⊢
            omega
          have : p = 2 := by
            have hp_dvd_2 : 2 ∣ p := ⟨m * m + m - 1, h_p_even⟩
            rcases hp_prime.eq_one_or_self_of_dvd 2 hp_dvd_2 with h21 | h2p
            · contradiction
            · exact h2p.symm
          rcases h_mod with h_mod1 | h_mod9
          · omega
          · omega
        omega
      have h_s3_eq : S_int n 3 = 2 * T_int n 3 := S_int_eq_two_mul_T n 3 hn_even
      have h_sk_eq : S_int n (k + 1) = 2 * T_int n (k + 1) := S_int_eq_two_mul_T n (k + 1) hn_even
      rcases hk_even with ⟨r, rfl⟩
      have hk_sub3_ge1 : 2 * r - 3 ≥ 1 := by omega
      have h_M_even : Even (M_val (2 * r - 3)) := M_val_even (2 * r - 3) hk_sub3_ge1
      rcases h_M_even with ⟨M', hM'⟩
      have h_div : T_int n 3 = (r : ℤ) * (((2 * r - 2).factorial : ℤ) * T_int n (2 * r + 1) + M' * p) := by
        have h_eq : 2 * (2 * T_int n 3) - (2 * r : ℤ) * ((2 * r - 2).factorial : ℤ) * (2 * T_int n (2 * r + 1)) = (2 * M' : ℤ) * (2 * r * p) := by
          have h_k_eq : r + r = 2 * r := by omega
          rw [h_k_eq] at hM
          have h_rew : 2 * r - 3 + 4 = 2 * r + 1 := by omega
          rw [h_rew] at hM
          rw [S_int_eq_two_mul_T n 3 hn_even, S_int_eq_two_mul_T n (2 * r + 1) hn_even, hM'] at hM
          have h_fac_rew : (2 * r - 3 + 1).factorial = (2 * r - 2).factorial := by congr 1; omega
          have hM'_rew : M' + M' = 2 * M' := by ring
          have h_r_rew : ((2 * r : ℕ) : ℤ) = 2 * (r : ℤ) := by omega
          rw [h_fac_rew, hM'_rew, h_r_rew] at hM
          exact hM
        have h_calc : 4 * T_int n 3 = 4 * ((r : ℤ) * (((2 * r - 2).factorial : ℤ) * T_int n (2 * r + 1) + M' * p)) := by
          calc 4 * T_int n 3 = 2 * (2 * T_int n 3) := by ring
          _ = (2 * r : ℤ) * ((2 * r - 2).factorial : ℤ) * (2 * T_int n (2 * r + 1)) + (2 * M' : ℤ) * (2 * r * p) := by linarith [h_eq]
          _ = 4 * ((r : ℤ) * (((2 * r - 2).factorial : ℤ) * T_int n (2 * r + 1) + M' * p)) := by ring
        linarith
      use (((2 * r - 2).factorial : ℤ) * T_int n (2 * r + 1) + M' * p)
      rw [h_s3_eq, h_div]
      push_cast
      ring
    · have h_gcd : Nat.Coprime k 2 := by
        have : Odd k := Nat.not_even_iff_odd.mp hk_even
        exact Nat.Coprime.symm (Nat.coprime_two_left.mpr this)
      have h_gcd_z : IsCoprime (k : ℤ) 2 := by
        exact_mod_cast h_gcd
      exact IsCoprime.dvd_of_dvd_mul_left h_gcd_z h_dvd_2
  · have hk_dvd : k ∣ 4 := by
      rcases k_le_n_sub_3_or_dvd_4 n p k hn hkp hn_lt_p with h1 | h2
      · have : k < 3 := by omega
        have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases this with rfl | rfl | rfl
        · omega
        · decide
        · decide
      · exact h2
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 := by
      have hk_le4 : k ≤ 4 := Nat.le_of_dvd (by decide) hk_dvd
      have hk_ne_zero : k ≠ 0 := by
        intro hk0
        subst hk0
        omega
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · exfalso
        have : ¬ 3 ∣ 4 := by decide
        exact this hk_dvd
      · right; right; rfl
    rcases hk_cases with hk1 | hk2 | hk4
    · subst hk1
      exact one_dvd (S_int n 3)
    · subst hk2
      have hn_even : Even n := even_n_of_even_kp n 2 p hn hkp (by use 1)
      rcases hn_even with ⟨m, hm⟩
      have hn_eq_2m : n = 2 * m := by omega
      subst hn_eq_2m
      have hm_ge_2 : m ≥ 2 := by omega
      have h_sq : (2 * m)^2 = 4 * m * m := by ring
      rw [h_sq] at hkp
      have h_kp_even : 4 * (m * m + m) = 2 * p + 4 := by
        calc 4 * (m * m + m) = 4 * m * m + 4 * m := by ring
        _ = 2 * p + 4 := by omega
      have h_X_ge : m * m + m ≥ 1 := by omega
      have h_p_even : p = 2 * (m * m + m - 1) := by
        generalize m * m + m = X at h_kp_even h_X_ge ⊢
        clear h_mod hp_prime hn_lt_p hm_ge_2
        omega
      have : p = 2 := by
        have hp_dvd_2 : 2 ∣ p := ⟨m * m + m - 1, h_p_even⟩
        rcases hp_prime.eq_one_or_self_of_dvd 2 hp_dvd_2 with h21 | h2p
        · contradiction
        · exact h2p.symm
      rcases h_mod with h_mod1 | h_mod9
      · omega
      · omega
    · subst hk4
      have hn_even : Even n := even_n_of_even_kp n 4 p hn hkp (by use 2)
      have hn6 : 6 ≤ n := by
        have hp_ge_11 := p_ge_11_of_mod10 p hp_prime h_mod
        have h_kp_ge : 4 * p ≥ 44 := by omega
        have : n * n + 2 * n ≥ 48 := by
          have h_eq : n * n + 2 * n = 4 * p + 4 := by
            have hkp_rew : n * n + 2 * n - 4 = 4 * p := by
              rw [← pow_two]
              exact hkp
            generalize n * n = nn at hkp_rew ⊢
            clear h_mod hp_prime hn_lt_p
            omega
          generalize n * n = nn at h_eq ⊢
          clear h_mod hp_prime hn_lt_p
          omega
        by_contra h_lt
        have : n ≤ 5 := by omega
        nlinarith
      have h_s3_eq : S_int n 3 = 2 * T_int n 3 := S_int_eq_two_mul_T n 3 hn_even
      have h_t3_even : 2 ∣ T_int n 3 := T_int_even n 3 hn_even hn6 (by omega)
      rcases h_t3_even with ⟨z, hz⟩
      rw [h_s3_eq, hz]
      use z
      ring

lemma rat_div_helper (k p : ℕ) (s3 : ℚ) (hs3 : s3 ≠ 0) (hk : (k : ℚ) ≠ 0) :
  ((k * p : ℚ) / s3) = (p : ℚ) / (s3 / (k : ℚ)) := by
  field_simp

theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p hp_cond
  have hp : Fact p.Prime := ⟨hp_cond.1⟩
  rcases exists_n_dvd p hp_cond.2 with ⟨n, hn_ge3, hn_lt_p, hn_dvd⟩
  use n
  rw [A363347_eq_of_S n hn_ge3]
  have h_eq_s2 : (n + 1)^2 - 5 = n^2 + 2 * n - 4 := by
    have h_expand : (n + 1)^2 = n * n + 2 * n + 1 := by ring
    rw [h_expand, pow_two]
    omega
  have h_dvd : p ∣ n^2 + 2 * n - 4 := by
    rw [← h_eq_s2]
    exact hn_dvd
  rcases h_dvd with ⟨k, hk_eq⟩
  have hk_eq' : n^2 + 2 * n - 4 = k * p := by
    rw [hk_eq]
    ring
  have h_s2_kp : S n 2 = (k : ℚ) * (p : ℚ) := S_two_eq_kp n p k hn_ge3 hk_eq'
  have hk_gt : k > 0 := by
    have h_s2_pos : n^2 + 2 * n - 4 > 0 := by omega
    have h_kp_pos : k * p > 0 := by
      rw [← hk_eq']
      exact h_s2_pos
    -- Since p is positive (it is prime), k must be positive
    have : p > 0 := hp_cond.1.pos
    exact Nat.pos_of_mul_pos_right h_kp_pos
  have hk_nz : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hs3_pos : S n 3 > 0 := by
    have h_helper := S_pos_helper n (n - 3) hn_ge3 (by omega)
    dsimp only at h_helper
    have h_rew : n - (n - 3) = 3 := by omega
    rw [h_rew] at h_helper
    exact h_helper
  have hs3_nz : S n 3 ≠ 0 := hs3_pos.ne'
  have h_rat_eq : S n 2 / S n 3 = (p : ℚ) / (S n 3 / (k : ℚ)) := by
    rw [h_s2_kp]
    have h_comm : (k : ℚ) * (p : ℚ) = (k * p : ℚ) := by push_cast; rfl
    rw [h_comm]
    exact rat_div_helper k p (S n 3) hs3_nz hk_nz
  have h_dvd_S3 : (k : ℤ) ∣ S_int n 3 := k_dvd_S3 n p k hn_ge3 hk_eq' hp_cond.1 hp_cond.2 hn_lt_p
  rcases h_dvd_S3 with ⟨Q_int, hQ⟩
  have hQ_rat : S n 3 / (k : ℚ) = (Q_int : ℚ) := by
    rw [S_int_spec n 3]
    rw [hQ]
    push_cast
    field_simp
  have h_frac : S n 2 / S n 3 = ((p : ℤ) : ℚ) / ((Q_int : ℤ) : ℚ) := by
    rw [h_rat_eq]
    rw [hQ_rat]
    push_cast
    rfl
  have hQ_pos : Q_int > 0 := by
    have h_pos : (S_int n 3 : ℚ) > 0 := by
      rw [← S_int_spec]
      exact hs3_pos
    have : (S_int n 3 : ℤ) > 0 := by exact_mod_cast h_pos
    have : (k : ℤ) * Q_int > 0 := by
      rw [← hQ]
      exact this
    have hk_z_pos : (k : ℤ) > 0 := by exact_mod_cast hk_gt
    exact pos_of_mul_pos_right this (by omega)
  have h_p_dvd_s2 : (p : ℤ) ∣ S_int n 2 := by
    have : S_int n 2 = p * k := by
      have : (S_int n 2 : ℚ) = (p * k : ℚ) := by
        rw [← S_int_spec, S_two_eq_kp n p k hn_ge3 hk_eq']
        ring
      exact_mod_cast this
    rw [this]
    exact dvd_mul_right (p : ℤ) (k : ℤ)
  have h_not_dvd : ¬ (p : ℤ) ∣ Q_int := by
    intro h_dvd
    have h_dvd_s3 : (p : ℤ) ∣ S_int n 3 := by
      rw [hQ]
      exact dvd_mul_of_dvd_right h_dvd k
    exact p_not_dvd_S3 n p hn_ge3 hp_cond.1 hp_cond.2 hn_lt_p h_p_dvd_s2 h_dvd_s3
  have h_coprime : Nat.Coprime p Q_int.natAbs := by
    have h_prime_z : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_cond.1
    have h_coprime_z : IsCoprime (p : ℤ) Q_int := by
      rwa [Irreducible.coprime_iff_not_dvd h_prime_z.irreducible]
    rw [Int.isCoprime_iff_nat_coprime] at h_coprime_z
    exact h_coprime_z
  have h_num : (S n 2 / S n 3).num = p := by
    rw [h_frac]
    have h_gcd : (p : ℤ).natAbs.Coprime Q_int.natAbs := by
      have : (p : ℤ).natAbs = p := rfl
      rw [this]
      exact h_coprime
    have h_rat := Rat.num_div_eq_of_coprime (by omega) h_gcd
    exact_mod_cast h_rat
  rw [h_num]
  rfl

