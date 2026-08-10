import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat

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

lemma a_Q_recurrence (k : ℕ) :
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
    -- Let B = a_Q (k+1), K_prev = (k+2) * choose (2k+1) (k+1)
    -- ih_k1 : CongruentMod2 B K_prev
    rcases ih_k1 with ⟨z, d, hd_odd, hdiff⟩
    -- We want to prove CongruentMod2 (a_Q (k+2)) ( (k+3) * choose (2k+3) (k+2) )
    -- Let D = (2k+5)^3
    have h_den_odd : Odd ((2 * (k : ℤ) + 5) ^ 3) := by
      use 4 * k^3 + 30 * k^2 + 75 * k + 62
      ring
    have hd_prod : Odd (((2 * (k : ℤ) + 5) ^ 3) * d) := Odd.mul h_den_odd hd_odd
    -- From a_Q_recurrence:
    have h_rec := a_Q_recurrence k
    -- We want to show (a_Q (k+2)) - (k+3) * choose (2k+3) (k+2) = 2 * z' / (D * d)
    -- Let's extract z_even from P_M_pow4_sub_D_K_even
    have h_even := P_M_pow4_sub_D_K_even (k : ℤ) (choose (2 * k + 3) (k + 2) : ℤ)
    rcases h_even with ⟨z_even, hz_even⟩
    -- Now we just do algebra to prove the difference is of the required form
    use 32 * (k + 2 : ℤ) ^ 3 * z + d * (16 * (k + 2 : ℤ) ^ 3 * (k + 2 : ℤ) * (choose (2 * k + 1) (k + 1) : ℤ) + z_even), ((2 * (k : ℤ) + 5) ^ 3) * d
    refine ⟨hd_prod, ?_⟩
    -- We have hdiff : a_Q (k + 1) - ↑(k + 2) * ↑((2 * (k + 1) - 1).choose (k + 1)) = 2 * ↑z / ↑d
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
    -- Note: 2 * (k + 2) - 1 = 2 * k + 3
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
