import decimal
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 300

limit = 60

pi_lb = Decimal('3.141592653589793238462643383279502884197169399375105820974944592307816406286208')
pi_ub = Decimal('3.141592653589793238462643383279502884197169399375105820974944592307816406286210')

def format_decimal(d):
    s = "{:f}".format(d)
    if '.' in s:
        s = s.rstrip('0').rstrip('.')
    return s

pi_lb_val_scaled = int(pi_lb * 10**limit)

# Read the header from Spec.lean up to line 230
header_lines = []
with open("/workspace/leanproject/Submission/Spec.lean.bak", "r") as f:
    for i in range(230):
        line = f.readline()
        if not line:
            break
        header_lines.append(line)
header = "".join(header_lines)

out = [header]

# Generate subgoal cases for N in 1..60
for N in range(1, limit + 1):
    ten_to_N = 10**N
    one_div_ten_to_N = f"1 / {ten_to_N}"
    
    L_int = int(pi_lb * ten_to_N)
    U_int = L_int + 1
    
    pi_ub_scaled = format_decimal(pi_ub * ten_to_N)
    pi_lb_scaled = format_decimal(pi_lb * ten_to_N)
    
    lemma = f"""
lemma subgoal_case_{N} : ¬ ∃ (k : ℤ),
    (Real.pi * (10 : ℝ) ^ ({N} : ℕ).cast < k.cast) ∧
    (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ ({N} : ℕ).cast)) := by
  intro ⟨k, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_ub := upper_bound_interval_tight {N} (by norm_num)
  have h_ten : (10 : ℝ) ^ (-({N} : ℕ).cast : ℤ) = {one_div_ten_to_N} := by norm_num
  have h_lt : (k : ℝ) < Real.pi * {ten_to_N} + 2 * ({one_div_ten_to_N}) := by
    have h_ub_simp := h_ub
    simp only [h_ten] at h_ub_simp
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rw [h_pow_cast_real] at h2
    linarith [h2, h_ub_simp]
  have h_gt : Real.pi * {ten_to_N} < (k : ℝ) := by
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rwa [h_pow_cast_real] at h1
  have h_k_lt : (k : ℝ) < {pi_ub_scaled} + 2 * ({one_div_ten_to_N}) := by
    linarith [h_pi_lt, h_lt]
  have h_k_gt : {pi_lb_scaled} < (k : ℝ) := by linarith [h_pi_gt, h_gt]
  have hk_gt : {L_int} < k := by
    exact_mod_cast (by linarith : ({L_int} : ℝ) < (k : ℝ))
  have hk_lt : k < {U_int} := by
    exact_mod_cast (by linarith : (k : ℝ) < ({U_int} : ℝ))
  omega
"""
    out.append(lemma)

main_theorem = f"""
theorem oeis_a011545_conjecture_0 (n : ℕ) :
    ¬ ∃ (k : ℤ),
      (Real.pi * (10 : ℝ) ^ n.cast < k.cast) ∧
      (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast)) := by
  rcases n with _ | n
  · intro ⟨k, h1, h2⟩
    have h_pi_gt : 3 < Real.pi := Real.pi_gt_three
    have h_pi_lt : Real.pi < 4 := Real.pi_lt_four
    simp only [Nat.cast_zero, pow_zero, div_one] at h1 h2
    have h_art : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
    rw [h_art] at h2
    have h_div : Real.pi / (Real.pi / 4) = 4 := by
      have : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    rw [h_div] at h2
    have hk_gt : 3 < k := by
      exact_mod_cast (by linarith : 3 < (k : ℝ))
    have hk_lt : k < 4 := by
      exact_mod_cast (by linarith : (k : ℝ) < 4)
    omega
  · have h_or : n < {limit} ∨ {limit} ≤ n := by omega
    rcases h_or with hn_lt | hn_ge
    · interval_cases n
"""

for N in range(1, limit + 1):
    main_theorem += f"      · exact subgoal_case_{N}\n"

main_theorem += f"""    · intro ⟨k, h1, h2⟩
      have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
      have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
      have h_ub := upper_bound_interval_tight (n + 1) (by omega)
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := by simp
        rw [h_pow_cast_real] at h2
        have h_ub' := h_ub
        push_cast at h_ub'
        linarith [h2, h_ub']
      have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := by simp
        rwa [h_pow_cast_real] at h1
      have hn_ge_limit : {limit} ≤ n := hn_ge
      have hn_ge_limit1 : {limit + 1} ≤ n + 1 := by omega
      have h_ten_neg : 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) ≤ 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) := by
        have h_neg_le : -((n + 1) : ℤ) ≤ -{limit + 1} := by omega
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact zpow_le_zpow_right₀ (by norm_num) h_neg_le
      have h_ten_neg_le : 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) < 1 := by
        have : (10 : ℝ) ^ (-{limit + 1} : ℤ) = 1 / {10**(limit + 1)} := by norm_num
        rw [this]
        norm_num
      have h_lt' : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 1 := by
        calc (k : ℝ)
          _ < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := h_lt
          _ ≤ Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) := by linarith
          _ < Real.pi * (10 : ℝ) ^ (n + 1) + 1 := by linarith
          
      have h_mod : k % 10 = 0 ∨ k % 10 = 1 ∨ k % 10 = 2 ∨ k % 10 = 3 ∨ k % 10 = 4 ∨ k % 10 = 5 ∨ k % 10 = 6 ∨ k % 10 = 7 ∨ k % 10 = 8 ∨ k % 10 = 9 := by omega
      rcases h_mod with hk0 | hk1 | hk2 | hk3 | hk4 | hk5 | hk6 | hk7 | hk8 | hk9
      · -- Case k % 10 = 0.
        have h_div_10 : ∃ q, k = 10 * q := by
          use k / 10
          omega
        rcases h_div_10 with ⟨q, hq⟩
        have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast hq
          have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) := by rwa [this] at h_gt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := by
            rw [pow_succ]
            ring
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
          
        have h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast hq
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := by
            rw [pow_succ]
            ring
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
            have : -((n + 1) : ℤ) = -n - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
          have h_arctan_lower := pi_div_arctan_gt n (by omega)
          have h_pow_neg_eq : (10 : ℝ) ^ (-(n + 2 : ℤ)) = 0.01 * (10 : ℝ) ^ (-n : ℤ) := by
            have : (-(n + 2 : ℤ)) = (-n : ℤ) + (-2 : ℤ) := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_neg_eq] at h_arctan_lower
          linarith
          
        have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n.cast < k'.cast ∧ k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n.cast) := by
          use q
          have h_cast_n : (n : ℝ) = n.cast := by rfl
          rw [h_cast_n]
          exact ⟨h_q_gt, h_q_lt⟩
        exact oeis_a011545_conjecture_0 n h_contra
"""

for d in range(1, 10):
    main_theorem += f"""      · -- Case k % 10 = {d}.
        have h_div_10 : ∃ q, k = 10 * q + {d} := by
          use k / 10
          omega
        rcases h_div_10 with ⟨q, hq⟩
        have h_pow_eq_10 : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ {limit + 1} * (10 : ℝ) ^ (n - {limit}) := by
          have : n + 1 = {limit + 1} + (n - {limit}) := by omega
          rw [this, pow_add]
        have hn_ge_limit_use : {limit} ≤ n := hn_ge
        have h_ten_neg_limit : 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) ≤ 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) := by
          have h_neg_le : -((n + 1) : ℤ) ≤ -{limit + 1} := by omega
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact zpow_le_zpow_right₀ (by norm_num) h_neg_le
        have h_ten_neg_limit_le : 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) < 1 / 10^{limit} := by
          have : (10 : ℝ) ^ (-{limit + 1} : ℤ) = 1 / 10^{limit + 1} := by norm_num
          rw [this]
          norm_num
        have h_lt_limit : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 1 / 10^{limit} := by
          calc (k : ℝ)
            _ < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := h_lt
            _ ≤ Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-{limit + 1} : ℤ) := by linarith
            _ < Real.pi * (10 : ℝ) ^ (n + 1) + 1 / 10^{limit} := by linarith
            
        have h_pi_limit_gt : {int(pi_lb * 10**(limit))} / 10^{limit} < Real.pi := by linarith [h_pi_gt]
        have h_pi_limit_lt : Real.pi < {int(pi_ub * 10**(limit))} / 10^{limit} := by linarith [h_pi_lt]
        
        have h_gt_mul : ({int(pi_lb * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
          calc ({int(pi_lb * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1)
            _ < Real.pi * (10 : ℝ) ^ (n + 1) := by
              apply mul_lt_mul_of_pos_right h_pi_limit_gt (by positivity)
            _ < (k : ℝ) := h_gt
            
        have h_lt_mul : (k : ℝ) < ({int(pi_ub * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1) := by
          calc (k : ℝ)
            _ < Real.pi * (10 : ℝ) ^ (n + 1) + 1 / 10^{limit} := h_lt_limit
            _ < ({int(pi_ub * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1) := by
              have h_diff_pos : 0 < ({int(pi_ub * 10**(limit))} / 10^{limit} - Real.pi) * (10 : ℝ) ^ (n + 1) - 1 / 10^{limit} := by
                have h_pi_diff : 1 / (10 : ℝ)^({limit + 3}) ≤ {int(pi_ub * 10**(limit))} / 10^{limit} - Real.pi := by linarith [h_pi_lt]
                have hn_ge_limit_plus : {limit + 3} ≤ n + 1 := by omega
                have h_ten_n_ge_plus : (10 : ℝ) ^ {limit + 3} ≤ (10 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hn_ge_limit_plus
                have h_factor : 1 / 10^{limit} < (1 / (10 : ℝ)^{limit + 3}) * (10 : ℝ)^{limit + 3} := by
                  calc 1 / 10^{limit}
                    _ < 1000 / 10^{limit} := by norm_num
                    _ = (1 / (10 : ℝ)^{limit + 3}) * (10 : ℝ)^{limit + 3} := by ring
                have h_mul : (1 / (10 : ℝ)^{limit + 3}) * (10 : ℝ)^{limit + 3} ≤ ({int(pi_ub * 10**(limit))} / 10^{limit} - Real.pi) * (10 : ℝ) ^ (n + 1) := by
                  apply mul_le_mul_of_nonneg h_pi_diff h_ten_n_ge_plus (by positivity) (by positivity)
                linarith
              linarith
              
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ {limit} * (10 : ℝ) ^ (n + 1 - {limit}) := by
          have : n + 1 = {limit} + (n + 1 - {limit}) := by omega
          rw [this, pow_add]
          
        have h_gt_mul_simp : (({int(pi_lb * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}) < (k : ℝ) := by
          have h_calc : ({int(pi_lb * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1) = (({int(pi_lb * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}) := by
            rw [h_pow_eq]
            have : (10 : ℝ) ^ {limit} ≠ 0 := by positivity
            field_simp
            ring
          rwa [h_calc] at h_gt_mul
          
        have h_lt_mul_simp : (k : ℝ) < (({int(pi_ub * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}) := by
          have h_calc : ({int(pi_ub * 10**(limit))} / 10^{limit}) * (10 : ℝ) ^ (n + 1) = (({int(pi_ub * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}) := by
            rw [h_pow_eq]
            have : (10 : ℝ) ^ {limit} ≠ 0 := by positivity
            field_simp
            ring
          rwa [h_calc] at h_lt_mul
          
        have hk_gt' : {int(pi_lb * 10**(limit))} * 10 ^ (n + 1 - {limit}) < k := by
          exact_mod_cast (by linarith : (({int(pi_lb * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}) < (k : ℝ))
          
        have hk_lt' : k < {int(pi_ub * 10**(limit))} * 10 ^ (n + 1 - {limit}) := by
          exact_mod_cast (by linarith : (k : ℝ) < (({int(pi_ub * 10**(limit))} : ℤ) : ℝ) * (10 : ℝ) ^ (n + 1 - {limit}))
          
        have h_M_or : n + 1 - {limit} = 1 ∨ n + 1 - {limit} = 2 ∨ n + 1 - {limit} = 3 ∨ n + 1 - {limit} = 4 ∨ 5 ≤ n + 1 - {limit} := by omega
        rcases h_M_or with hM1 | hM2 | hM3 | hM4 | hM5
        · have : k = 10 * q + {d} := hq
          have h_gt_val : {int(pi_lb * 10**(limit))} * 10 ^ (1 : ℕ) < k := by rwa [hM1] at hk_gt'
          have h_lt_val : k < {int(pi_ub * 10**(limit))} * 10 ^ (1 : ℕ) := by rwa [hM1] at hk_lt'
          omega
        · have : k = 10 * q + {d} := hq
          have h_gt_val : {int(pi_lb * 10**(limit))} * 10 ^ (2 : ℕ) < k := by rwa [hM2] at hk_gt'
          have h_lt_val : k < {int(pi_ub * 10**(limit))} * 10 ^ (2 : ℕ) := by rwa [hM2] at hk_lt'
          omega
        · have : k = 10 * q + {d} := hq
          have h_gt_val : {int(pi_lb * 10**(limit))} * 10 ^ (3 : ℕ) < k := by rwa [hM3] at hk_gt'
          have h_lt_val : k < {int(pi_ub * 10**(limit))} * 10 ^ (3 : ℕ) := by rwa [hM3] at hk_lt'
          omega
        · have : k = 10 * q + {d} := hq
          have h_gt_val : {int(pi_lb * 10**(limit))} * 10 ^ (4 : ℕ) < k := by rwa [hM4] at hk_gt'
          have h_lt_val : k < {int(pi_ub * 10**(limit))} * 10 ^ (4 : ℕ) := by rwa [hM4] at hk_lt'
          omega
        · have h_pow_M : (10 : ℤ) ^ (n + 1 - {limit}) = (10 : ℤ) ^ (n + 1 - {limit} - 1) * 10 := by
            have : n + 1 - {limit} = (n + 1 - {limit} - 1) + 1 := by omega
            rw [this, pow_add]
            ring
          have hk_gt_M : {int(pi_lb * 10**(limit))} * 10 * (10 : ℤ) ^ (n + 1 - {limit} - 1) < k := by
            have h_rw := hk_gt'
            rw [h_pow_M] at h_rw
            linarith
          have hk_lt_M : k < {int(pi_ub * 10**(limit))} * 10 * (10 : ℤ) ^ (n + 1 - {limit} - 1) := by
            have h_rw := hk_lt'
            rw [h_pow_M] at h_rw
            linarith
          have h_Y_eq : ∃ Y, (10 : ℤ) ^ (n + 1 - {limit} - 1) = (10 : ℤ) ^ 4 * Y := by
            use (10 : ℤ) ^ (n + 1 - {limit} - 5)
            have : n + 1 - {limit} - 1 = 4 + (n + 1 - {limit} - 5) := by omega
            rw [this, pow_add]
          rcases h_Y_eq with ⟨Y, hY_val⟩
          have h_Y_pos : 1 ≤ Y := by
            have : 0 ≤ n + 1 - {limit} - 5 := by omega
            apply one_le_pow_of_one_le (by norm_num) this
          have : k = 10 * q + {d} := hq
          have h_gt_final : {int(pi_lb * 10**(limit) * 100000)} * Y < 10 * q + {d} := by
            have h_rw := hk_gt_M
            rw [hY_val] at h_rw
            have : {int(pi_lb * 10**(limit))} * 10 * (10 : ℤ) ^ 4 = {int(pi_lb * 10**(limit) * 100000)} := by norm_num
            linarith
          have h_lt_final : 10 * q + {d} < {int(pi_ub * 10**(limit) * 100000)} * Y := by
            have h_rw := hk_lt_M
            rw [hY_val] at h_rw
            have : {int(pi_ub * 10**(limit))} * 10 * (10 : ℤ) ^ 4 = {int(pi_ub * 10**(limit) * 100000)} := by norm_num
            linarith
          omega
"""

main_theorem += """
#print axioms oeis_a011545_conjecture_0
"""

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("".join(out))
    f.write(main_theorem)

print("generate_final_v16.py successfully wrote Submission/Spec.lean")
