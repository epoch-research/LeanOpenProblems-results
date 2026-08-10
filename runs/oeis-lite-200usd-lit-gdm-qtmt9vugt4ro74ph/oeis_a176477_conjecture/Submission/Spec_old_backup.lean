/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1)\binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

theorem a_Q_ge_two (n : ℕ) (hn : n ≥ 1) : a_Q n ≥ 2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · omega
  · rfl
  · unfold a_Q
    dsimp only
    have h_lt : k + 1 < k + 2 := by omega
    have h_ge1 : k + 1 ≥ 1 := by omega
    have h_prev := ih (k + 1) h_lt h_ge1
    have h_den_pos : 0 < (2 * (↑(k + 2) : ℚ) + 1) ^ 3 := by positivity
    rw [ge_iff_le]
    rw [le_div_iff₀ h_den_pos]
    have h_prev' : a_Q (k + 2 - 1) ≥ 2 := h_prev
    have h_term2_pos : (21 * (↑(k + 2) : ℚ) ^ 3 + 22 * (↑(k + 2) : ℚ) ^ 2 + 8 * (↑(k + 2) : ℚ) + 1) * (↑((2 * (k + 2) - 1).choose (k + 2)) : ℚ) ^ 4 ≥ 0 := by positivity
    have h_x_nat : k + 2 ≥ 2 := by omega
    have h_x : (↑(k + 2) : ℚ) ≥ 2 := by exact_mod_cast h_x_nat
    have h_pow2 : (↑(k + 2) : ℚ) ^ 2 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) := by ring
    have h_pow3 : (↑(k + 2) : ℚ) ^ 3 = (↑(k + 2) : ℚ) * (↑(k + 2) : ℚ) ^ 2 := by ring
    have h_x_pow2 : (↑(k + 2) : ℚ) ^ 2 ≥ 0 := by positivity
    have h1 : 24 * (↑(k + 2) : ℚ) ^ 2 ≤ 12 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2_a : 12 * (↑(k + 2) : ℚ) ≤ 6 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h2_b : 6 * (↑(k + 2) : ℚ) ^ 2 ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h2 : 12 * (↑(k + 2) : ℚ) ≤ 3 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h3_a : (2 : ℚ) ≤ 4 * (↑(k + 2) : ℚ) := by linarith
    have h3_b : 4 * (↑(k + 2) : ℚ) ≤ 2 * (↑(k + 2) : ℚ) ^ 2 := by nlinarith
    have h3_c : 2 * (↑(k + 2) : ℚ) ^ 2 ≤ (↑(k + 2) : ℚ) ^ 3 := by nlinarith
    have h3 : (2 : ℚ) ≤ (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_expand : 2 * (2 * (↑(k + 2) : ℚ) + 1) ^ 3 = 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 := by ring
    have h_sum : 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 16 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_sum2 : 16 * (↑(k + 2) : ℚ) ^ 3 + 24 * (↑(k + 2) : ℚ) ^ 2 + 12 * (↑(k + 2) : ℚ) + 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 := by linarith
    have h_cube_pos : 32 * (↑(k + 2) : ℚ) ^ 3 ≥ 0 := by positivity
    have h_mult : 32 * (↑(k + 2) : ℚ) ^ 3 * 2 ≤ 32 * (↑(k + 2) : ℚ) ^ 3 * a_Q (k + 2 - 1) := by nlinarith
    linarith

theorem a_pos (n : ℕ) (hn : n ≥ 1) : a n > 0 := by
  have h1 := a_Q_ge_two n hn
  unfold a
  have h2 : (2 : ℤ) ≤ (a_Q n).floor := Int.le_floor.mpr h1
  generalize h_x : (a_Q n).floor = x
  rw [h_x] at h2
  omega

private lemma no_pow2_3 (m : ℕ) (h : 3 = 2^m) : False := by
  rcases m with _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 3) = 2^m_prime * 8 := by ring
    omega

private lemma no_pow2_5 (m : ℕ) (h : 5 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_6 (m : ℕ) (h : 6 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma no_pow2_7 (m : ℕ) (h : 7 = 2^m) : False := by
  rcases m with _ | _ | _ | _ | m_prime
  · omega
  · omega
  · omega
  · omega
  · have : 2^(m_prime + 4) = 2^m_prime * 16 := by ring
    omega

private lemma a2_val : a 2 = 181 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  rw [h_choose2]
  norm_num
  rfl

private lemma a3_val : a 3 = 23488 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  rw [h_choose2, h_choose3]
  norm_num
  rfl

private lemma a4_val : a 4 = 3625081 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  have h_choose4 : choose 7 4 = 35 := rfl
  rw [h_choose2, h_choose3, h_choose4]
  norm_num
  rfl

private lemma a5_val : a 5 = 619898336 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  have h_choose4 : choose 7 4 = 35 := rfl
  have h_choose5 : choose 9 5 = 126 := rfl
  rw [h_choose2, h_choose3, h_choose4, h_choose5]
  norm_num
  rfl

private lemma a6_val : a 6 = 113451041232 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  have h_choose4 : choose 7 4 = 35 := rfl
  have h_choose5 : choose 9 5 = 126 := rfl
  have h_choose6 : choose 11 6 = 462 := rfl
  rw [h_choose2, h_choose3, h_choose4, h_choose5, h_choose6]
  norm_num
  rfl

private lemma a7_val : a 7 = 21790823094272 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  have h_choose4 : choose 7 4 = 35 := rfl
  have h_choose5 : choose 9 5 = 126 := rfl
  have h_choose6 : choose 11 6 = 462 := rfl
  have h_choose7 : choose 13 7 = 1716 := rfl
  rw [h_choose2, h_choose3, h_choose4, h_choose5, h_choose6, h_choose7]
  norm_num
  rfl

private lemma a8_val : a 8 = 4339409873332321 := by
  unfold a
  dsimp only [a_Q]
  have h_choose2 : choose 3 2 = 3 := rfl
  have h_choose3 : choose 5 3 = 10 := rfl
  have h_choose4 : choose 7 4 = 35 := rfl
  have h_choose5 : choose 9 5 = 126 := rfl
  have h_choose6 : choose 11 6 = 462 := rfl
  have h_choose7 : choose 13 7 = 1716 := rfl
  have h_choose8 : choose 15 8 = 6435 := rfl
  rw [h_choose2, h_choose3, h_choose4, h_choose5, h_choose6, h_choose7, h_choose8]
  norm_num
  rfl

def CongruentMod2 (q1 q2 : ℚ) : Prop :=
  ∃ (z d : ℤ), Odd d ∧ q1 - q2 = (2 * z : ℚ) / (d : ℚ)

lemma P_M_pow4_sub_D_K_even (k : ℤ) (M : ℤ) :
  ∃ z : ℤ, (21 * (k+2)^3 + 22 * (k+2)^2 + 8 * (k+2) + 1) * M^4 - (2 * k + 5)^3 * (k + 3) * M = 2 * z := by
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  have hM : M = 2 * (M / 2) + M % 2 := by omega
  have hk_mod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hM_mod : M % 2 = 0 ∨ M % 2 = 1 := by omega
  generalize hk_div : k / 2 = k_div
  generalize hM_div : M / 2 = M_div
  rcases hk_mod with hk0 | hk1
  · rcases hM_mod with hM0 | hM1
    · use 1344*M_div^4*k_div^3+4736*M_div^4*k_div^2+5568*M_div^4*k_div+2184*M_div^4-128*M_div*k_div^4-672*M_div*k_div^3-1320*M_div*k_div^2-1150*M_div*k_div-375*M_div
      rw [hk, hM, hk0, hM0, hk_div, hM_div]
      ring
    · use 1344*M_div^4*k_div^3+4736*M_div^4*k_div^2+5568*M_div^4*k_div+2184*M_div^4+2688*M_div^3*k_div^3+9472*M_div^3*k_div^2+11136*M_div^3*k_div+4368*M_div^3+2016*M_div^2*k_div^3+7104*M_div^2*k_div^2+8352*M_div^2*k_div+3276*M_div^2-128*M_div*k_div^4+1048*M_div*k_div^2+1634*M_div*k_div+717*M_div-64*k_div^4-252*k_div^3-364*k_div^2-227*k_div-51
      rw [hk, hM, hk0, hM1, hk_div, hM_div]
      ring
  · rcases hM_mod with hM0 | hM1
    · use 1344*M_div^4*k_div^3+6752*M_div^4*k_div^2+11312*M_div^4*k_div+6320*M_div^4-128*M_div*k_div^4-928*M_div*k_div^3-2520*M_div*k_div^2-3038*M_div*k_div-1372*M_div
      rw [hk, hM, hk1, hM0, hk_div, hM_div]
      ring
    · use 1344*M_div^4*k_div^3+6752*M_div^4*k_div^2+11312*M_div^4*k_div+6320*M_div^4+2688*M_div^3*k_div^3+13504*M_div^3*k_div^2+22624*M_div^3*k_div+12640*M_div^3+2016*M_div^2*k_div^3+10128*M_div^2*k_div^2+16968*M_div^2*k_div+9480*M_div^2-128*M_div*k_div^4-256*M_div*k_div^3+856*M_div*k_div^2+2618*M_div*k_div+1788*M_div-64*k_div^4-380*k_div^3-838*k_div^2-812*k_div-291
      rw [hk, hM, hk1, hM1, hk_div, hM_div]
      ring

lemma a_Q_recurrence_lemma (k : ℕ) :
  a_Q (k + 2) * (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 = 32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) + (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4 := by
  have h_sub : k + 2 - 1 = k + 1 := by omega
  generalize h_prev : a_Q (k + 1) = prev
  unfold a_Q
  dsimp only
  rw [h_sub, h_prev]
  have h_den_ne : (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 ≠ 0 := by
    have : (2 * ((k + 2 : ℕ) : ℚ) + 1) > 0 := by positivity
    positivity
  rw [div_mul_cancel₀ _ h_den_ne]

lemma a_Q_congruent_mod2 (n : ℕ) (hn : n ≥ 1) :
  CongruentMod2 (a_Q n) (((n + 1 : ℕ) : ℚ) * (choose (2 * n - 1) n : ℚ)) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · omega
  · -- Case n = 1: a_Q 1 = 2, target is (1+1)*choose 1 1 = 2
    use 0, 1
    refine ⟨by decide, ?_⟩
    have : a_Q 1 = 2 := rfl
    rw [this]
    norm_num
  · -- Case n = k + 2
    have hk1 : k + 1 ≥ 1 := by omega
    have h_lt : k + 1 < k + 2 := by omega
    have ih_k1 := ih (k + 1) h_lt hk1
    rcases ih_k1 with ⟨z, d, hd_odd, hdiff⟩
    have h_den_odd : Odd ((2 * (k : ℤ) + 5) ^ 3) := by
      use 4 * k^3 + 30 * k^2 + 75 * k + 62
      ring
    have hd_prod : Odd (((2 * (k : ℤ) + 5) ^ 3) * d) := Odd.mul h_den_odd hd_odd
    have h_rec := a_Q_recurrence_lemma k
    have h_even := P_M_pow4_sub_D_K_even (k : ℤ) (choose (2 * k + 3) (k + 2) : ℤ)
    rcases h_even with ⟨z_even, hz_even⟩
    use 32 * (k + 2 : ℤ) ^ 3 * z + d * (16 * (k + 2 : ℤ) ^ 3 * (k + 2 : ℤ) * (choose (2 * k + 1) (k + 1) : ℤ) + z_even), ((2 * (k : ℤ) + 5) ^ 3) * d
    refine ⟨hd_prod, ?_⟩
    have h_B_eq : a_Q (k + 1) = ↑(k + 2) * ↑(choose (2 * k + 1) (k + 1)) + 2 * (z : ℚ) / (d : ℚ) := by
      have h_choose_sub3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      have hdiff' := hdiff
      rw [h_choose_sub3] at hdiff'
      linarith
    have hd_ne : (d : ℚ) ≠ 0 := by
      intro hc
      have : d = 0 := by exact_mod_cast hc
      subst this
      have : ¬ Odd (0 : ℤ) := by decide
      contradiction
    have h_D_ne : (2 * (k : ℚ) + 5) ^ 3 ≠ 0 := by positivity
    have h_choose_sub : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
    have h_rec_div : a_Q (k + 2) = (32 * ((k + 2 : ℕ) : ℚ) ^ 3 * a_Q (k + 1) + (21 * ((k + 2 : ℕ) : ℚ) ^ 3 + 22 * ((k + 2 : ℕ) : ℚ) ^ 2 + 8 * ((k + 2 : ℕ) : ℚ) + 1) * (Nat.choose (2 * (k + 2) - 1) (k + 2) : ℚ) ^ 4) / (2 * ((k + 2 : ℕ) : ℚ) + 1) ^ 3 := by
      rw [← h_rec]
      rw [mul_div_cancel_right₀ _ (by positivity)]
    rw [h_rec_div, h_B_eq]
    push_cast
    rw [h_choose_sub]
    have h_P_eq : ((k + 2 : ℚ) * ((k + 2 : ℚ) * ((k + 2 : ℚ) * 21 + 22) + 8) + 1) = 21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1 := by ring
    have h_simp3 : (k : ℚ) + 1 + 1 + 1 = k + 3 := by ring
    have h_simp4 : (k : ℚ) * 2 + 5 = 2 * k + 5 := by ring
    have h_den_rw : 2 * ((k : ℚ) + 2) + 1 = 2 * k + 5 := by ring
    rw [h_den_rw]
    field_simp [hd_ne, h_D_ne]
    generalize h_c1 : (choose (2 * k + 1) (k + 1) : ℚ) = C1
    generalize h_c2 : (choose (2 * k + 3) (k + 2) : ℚ) = C2
    rw [h_P_eq, h_simp3, h_simp4]
    have hz_even_q : (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * C2 ^ 4 - (2 * k + 5) ^ 3 * (k + 3 : ℚ) * C2 = 2 * (z_even : ℚ) := by
      have : (( (21 * (k + 2 : ℤ) ^ 3 + 22 * (k + 2 : ℤ) ^ 2 + 8 * (k + 2 : ℤ) + 1) * (choose (2 * k + 3) (k + 2) : ℤ) ^ 4 - (2 * k + 5) ^ 3 * (k + 3 : ℤ) * (choose (2 * k + 3) (k + 2) : ℤ) : ℤ) : ℚ) = (((2 * z_even : ℤ) : ℤ) : ℚ) := by
        rw [hz_even]
      push_cast at this
      rw [h_c2] at this
      exact this
    have h_subst : (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * C2 ^ 4 = 2 * (z_even : ℚ) + (2 * k + 5) ^ 3 * (k + 3 : ℚ) * C2 := by linarith [hz_even_q]
    have h_assoc : (d : ℚ) * (21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * C2 ^ 4 = (d : ℚ) * ((21 * (k + 2 : ℚ) ^ 3 + 22 * (k + 2 : ℚ) ^ 2 + 8 * (k + 2 : ℚ) + 1) * C2 ^ 4) := by ring
    rw [h_assoc, h_subst]
    ring



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

lemma a_Q_int (n : ℕ) (hn : n ≥ 1) : ∃ (z : ℤ), a_Q n = (z : ℚ) := by
  sorry

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · exact a_pos n hn
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · omega
    · -- n = 1
      constructor
      · intro h
        have : ¬ Odd 2 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        rcases m with _ | m_prime
        · omega
        · have : 2^m_prime ≥ 1 := Nat.one_le_pow m_prime 2 (by omega)
          omega
    · -- n = 2
      constructor
      · intro _
        use 1
        refine ⟨by omega, rfl⟩
      · intro _
        rw [a2_val]
        have : Odd 181 := by decide
        exact this
    · -- n = 3
      constructor
      · intro h
        rw [a3_val] at h
        have : ¬ Odd 23488 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_3 m h_pow)
    · -- n = 4
      constructor
      · intro _
        use 2
        refine ⟨by omega, rfl⟩
      · intro _
        rw [a4_val]
        have : Odd 3625081 := by decide
        exact this
    · -- n = 5
      constructor
      · intro h
        rw [a5_val] at h
        have : ¬ Odd 619898336 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_5 m h_pow)
    · -- n = 6
      constructor
      · intro h
        rw [a6_val] at h
        have : ¬ Odd 113451041232 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_6 m h_pow)
    · -- n = 7
      constructor
      · intro h
        rw [a7_val] at h
        have : ¬ Odd 21790823094272 := by decide
        contradiction
      · rintro ⟨m, hm, h_pow⟩
        exact False.elim (no_pow2_7 m h_pow)
    · -- n = 8
      constructor
      · intro _
        use 3
        refine ⟨by omega, rfl⟩
      · intro _
        rw [a8_val]
        have : Odd 4339409873332321 := by decide
        exact this
    · -- n >= 9
      have hn_ge2 : k + 9 ≥ 2 := by omega
      have hn_ge1 : k + 9 ≥ 1 := by omega
      have h_int := a_Q_int (k + 9) hn_ge1
      rcases h_int with ⟨z, hz⟩
      have h_a_eq : a (k + 9) = z.toNat := by
        unfold a
        have h_floor : (a_Q (k + 9)).floor = z := by
          rw [hz]
          norm_cast
        rw [h_floor]
      have hz_ge2 : z ≥ 2 := by
        have h_ge := a_Q_ge_two (k + 9) hn_ge1
        rw [hz] at h_ge
        exact_mod_cast h_ge
      have hz_coe : a_Q (k + 9) = (((a (k + 9) : ℤ) : ℚ)) := by
        rw [h_a_eq, Int.toNat_of_nonneg (by omega)]
        exact hz
      have h_cong := a_Q_congruent_mod2 (k + 9) hn_ge1
      rw [hz_coe] at h_cong
      have h_rw_idx : k + 9 + 1 = k + 10 := by omega
      rw [h_rw_idx] at h_cong
      generalize h_B : (k + 10) * choose (2 * (k + 9) - 1) (k + 9) = B_val
      have h_cast : (((k + 10 : ℕ) : ℚ) * (choose (2 * (k + 9) - 1) (k + 9) : ℚ)) = (((B_val : ℕ) : ℚ)) := by
        rw [← h_B]
        push_cast
        rfl
      rw [h_cast] at h_cong
      have h_parity := congruent_mod2_int_parity (a (k + 9) : ℤ) (B_val : ℤ) h_cong
      rw [Int.odd_coe_nat, Int.odd_coe_nat] at h_parity
      have h_idx_eq : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 9 := by omega
      rw [h_idx_eq]
      rw [h_parity]
      have h_B_eq : ((k + 9 + 1) * choose (2 * (k + 9) - 1) (k + 9)) = B_val := by
        have : k + 9 + 1 = k + 10 := by omega
        rw [this, h_B]
      have h_k_parity := K_parity (k + 9) hn_ge2
      rw [h_B_eq] at h_k_parity
      exact h_k_parity

