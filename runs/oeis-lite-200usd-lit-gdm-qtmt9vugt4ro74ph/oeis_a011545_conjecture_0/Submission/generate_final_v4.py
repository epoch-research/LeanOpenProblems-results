import decimal
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 100

n = 50
k = 25

u = [Fraction(0)]
u_str = []
for i in range(1, n + 1):
    v = (Decimal(2) + Decimal(u[-1].numerator) / Decimal(u[-1].denominator)).sqrt()
    target = Decimal(2) - v
    den = 10**(int(i * 0.6) + k)
    num = int(target * den)
    u.append(2 - Fraction(num, den))
    u_str.append(f"2-{num}/{den}")
    
l = [Fraction(0)]
l_str = []
for i in range(1, n + 1):
    v = (Decimal(2) + Decimal(l[-1].numerator) / Decimal(l[-1].denominator)).sqrt()
    target = Decimal(2) - v
    den = 10**(int(i * 0.6) + k)
    num = int(target * den) + 1
    l.append(2 - Fraction(num, den))
    l_str.append(f"2-{num}/{den}")

header = f"""import FormalConjectures.Util.ProblemImports

open Real Int

theorem pi_gt_50 : 3.141592653589793238462638 < Real.pi := by
  pi_lower_bound [
    {", ".join(u_str)}
  ]

theorem pi_lt_50 : Real.pi < 3.141592653589793238462651 := by
  pi_upper_bound [
    {", ".join(l_str)}
  ]

theorem hasDerivAt_g (x : ℝ) :
    HasDerivAt (fun x => arctan x - x + x ^ 3 / 3) (x ^ 4 / (1 + x ^ 2)) x := by
  have h1 : HasDerivAt arctan (1 / (1 + x ^ 2)) x := hasDerivAt_arctan x
  have h2 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
  have h3 : HasDerivAt (fun x => x ^ 3 / 3) (x ^ 2) x := by
    have : HasDerivAt (fun x => x ^ 3) (3 * x ^ 2) x := hasDerivAt_pow 3 x
    have h_div := HasDerivAt.div_const this (3 : ℝ)
    have : (3 * x ^ 2) / 3 = x ^ 2 := by ring
    rwa [this] at h_div
  have h12 := HasDerivAt.sub h1 h2
  have h123 := HasDerivAt.add h12 h3
  have h_eq : (1 / (1 + x ^ 2) - 1) + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by
    have h_denom : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rwa [h_eq] at h123

lemma arctan_gt_sub_cube (x : ℝ) (hx : 0 < x) : x - x ^ 3 / 3 < arctan x := by
  have h_mono : StrictMonoOn (fun x => arctan x - x + x ^ 3 / 3) (Set.Ici 0) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    · apply Continuous.continuousOn
      continuity
    · intro y _
      exact (hasDerivAt_g y).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy_pos : 0 < y := hy
      have hy4_pos : 0 < y ^ 4 := by positivity
      have hdenom : 0 < 1 + y ^ 2 := by positivity
      exact div_pos hy4_pos hdenom
  have h_g0 : (fun x => arctan x - x + x ^ 3 / 3) 0 = 0 := by
    simp
  have h_gx_gt := h_mono (Set.self_mem_Ici) (le_of_lt hx) hx
  rw [h_g0] at h_gx_gt
  linarith

lemma upper_bound_interval_tight (n : ℕ) (hn : 1 ≤ n) :
    Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) < Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := by
  let x := 1 / (10 : ℝ) ^ n
  have h_pow_pos : (0 : ℝ) < (10 : ℝ) ^ n := by positivity
  have hx_pos : 0 < x := by positivity
  have hx_le : x ≤ 0.1 := by
    have : (10 : ℝ) ^ (1 : ℕ) ≤ (10 : ℝ) ^ n := by
      apply pow_le_pow_right₀ (by norm_num) hn
    norm_num at this
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h_at := arctan_gt_sub_cube x hx_pos
  have h_sub_pos : 0 < x - x ^ 3 / 3 := by
    have : x ^ 2 / 3 < 1 := by
      have : x ^ 2 ≤ 0.01 := by nlinarith [hx_le, hx_pos]
      linarith
    have : x * (1 - x ^ 2 / 3) = x - x ^ 3 / 3 := by ring
    rw [← this]
    apply mul_pos hx_pos
    linarith
  have h_pi_div : Real.pi / Real.arctan x < Real.pi / (x - x ^ 3 / 3) := by
    apply div_lt_div_of_pos_left Real.pi_pos h_sub_pos h_at
  have h_le : Real.pi / (x - x ^ 3 / 3) ≤ Real.pi / x + 2 * x := by
    rw [div_le_iff₀ h_sub_pos]
    have : (Real.pi / x + 2 * x) * (x - x ^ 3 / 3) = Real.pi - Real.pi * x ^ 2 / 3 + 2 * x ^ 2 - 2 * x ^ 4 / 3 := by
      have : Real.pi / x * x = Real.pi := div_mul_cancel₀ Real.pi (ne_of_gt hx_pos)
      calc (Real.pi / x + 2 * x) * (x - x ^ 3 / 3)
        _ = (Real.pi / x) * (x - x ^ 3 / 3) + 2 * x * (x - x ^ 3 / 3) := by ring
        _ = (Real.pi / x) * x - (Real.pi / x) * (x ^ 3 / 3) + (2 * x ^ 2 - 2 * x ^ 4 / 3) := by ring
        _ = Real.pi - (Real.pi / x) * (x ^ 3 / 3) + (2 * x ^ 2 - 2 * x ^ 4 / 3) := by rw [this]
        _ = Real.pi - Real.pi * x ^ 2 / 3 + 2 * x ^ 2 - 2 * x ^ 4 / 3 := by
          have : (Real.pi / x) * (x ^ 3 / 3) = Real.pi * x ^ 2 / 3 := by
            have : x ≠ 0 := ne_of_gt hx_pos
            field_simp
          rw [this]
          ring
    rw [this]
    have h_pi_lt : Real.pi < 4 := Real.pi_lt_four
    have : Real.pi / 3 + 2 * x ^ 2 / 3 ≤ 2 := by
      have h1 : Real.pi / 3 < 4 / 3 := div_lt_div_of_pos_right h_pi_lt (by norm_num)
      have h2 : 2 * x ^ 2 / 3 ≤ 2 * 0.01 / 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [hx_le, hx_pos]
      linarith
    have : Real.pi * x ^ 2 / 3 + 2 * x ^ 4 / 3 ≤ 2 * x ^ 2 := by
      have h_le : x ^ 2 * (Real.pi / 3 + 2 * x ^ 2 / 3) ≤ x ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have h_expand : x ^ 2 * (Real.pi / 3 + 2 * x ^ 2 / 3) = Real.pi * x ^ 2 / 3 + 2 * x ^ 4 / 3 := by ring
      rw [h_expand] at h_le
      linarith
    have h_diff : 0 ≤ 2 * x ^ 2 - (Real.pi * x ^ 2 / 3 + 2 * x ^ 4 / 3) := by linarith
    linarith
  have h_eq : Real.pi / x + 2 * x = Real.pi * (10 : ℝ) ^ n + 2 * (10 : ℝ) ^ (-n : ℤ) := by
    have h_x_eq : x = (10 : ℝ) ^ (-n : ℤ) := by
      dsimp [x]
      rw [zpow_neg, zpow_natCast]
      ring
    rw [h_x_eq]
    have : Real.pi / (10 : ℝ) ^ (-n : ℤ) = Real.pi * (10 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast]
      have : (10 : ℝ) ^ n ≠ 0 := by positivity
      field_simp
    rw [this]
  linarith
"""

out = [header]

pi_lb = Decimal('3.141592653589793238462638')
pi_ub = Decimal('3.141592653589793238462651')

for N in range(1, 22):
    ten_to_N = 10**N
    one_div_ten_to_N = f"1 / {ten_to_N}"
    
    # Floor value of 10^N * pi_lb
    L = int(pi_lb * ten_to_N)
    U = L + 1
    
    gt_val_scaled = f"{L}"
    lt_val_scaled = f"{L}"
    
    lemma = f"""
lemma subgoal_case_{N} : ¬ ∃ (k : ℤ),
    (Real.pi * (10 : ℝ) ^ ({N} : ℕ).cast < k.cast) ∧
    (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ ({N} : ℕ).cast)) := by
  intro ⟨k, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462638 < Real.pi := pi_gt_50
  have h_pi_lt : Real.pi < 3.141592653589793238462651 := pi_lt_50
  have h_ub := upper_bound_interval_tight {N} (by norm_num)
  have h_lt : (k : ℝ) < Real.pi * {ten_to_N} + 2 * ({one_div_ten_to_N}) := by
    have h_ub_simp := h_ub
    have h_pow1 : (10 : ℝ) ^ {N} = {ten_to_N} := by norm_num
    have h_pow2 : (10 : ℝ) ^ (-({N} : ℕ).cast : ℤ) = {one_div_ten_to_N} := by norm_num
    rw [h_pow1, h_pow2] at h_ub_simp
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rw [h_pow_cast_real] at h2
    linarith [h2, h_ub_simp]
  have h_gt : Real.pi * {ten_to_N} < (k : ℝ) := by
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rwa [h_pow_cast_real] at h1
  have h_k_lt : (k : ℝ) < {lt_val_scaled} + 2 * ({one_div_ten_to_N}) := by
    linarith [h_pi_lt, h_lt]
  have h_k_gt : {gt_val_scaled} < (k : ℝ) := by linarith [h_pi_gt, h_gt]
  have hk_gt : {L} < k := by
    exact_mod_cast (by linarith : {L} < (k : ℝ))
  have hk_lt : k < {U} := by
    exact_mod_cast (by linarith : (k : ℝ) < {U})
  omega
"""
    out.append(lemma)

main_theorem = """
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
  · have h_or : n < 21 ∨ 21 ≤ n := by omega
    rcases h_or with hn_lt | hn_ge
    · interval_cases n
"""

for N in range(1, 22):
    main_theorem += f"      · exact subgoal_case_{N}\n"

main_theorem += """    · intro ⟨k, h1, h2⟩
      have h_pi_gt : 3.141592653589793238462638 < Real.pi := pi_gt_50
      have h_pi_lt : Real.pi < 3.141592653589793238462651 := pi_lt_50
      have h_ub := upper_bound_interval_tight (n + 1) (by omega)
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := by rfl
        rw [h_pow_cast_real] at h2
        have h_ub' := h_ub
        push_cast at h_ub'
        linarith [h2, h_ub']
      have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := by rfl
        rwa [h_pow_cast_real] at h1
      have hn_ge_21 : 21 ≤ n + 1 := by omega
      have h_ten_neg : 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) ≤ 2 * (10 : ℝ) ^ (-21 : ℤ) := by
        have h_neg_le : -((n + 1) : ℤ) ≤ -21 := by omega
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact zpow_le_zpow_right₀ (by norm_num) h_neg_le
      have h_ten_neg_le : 2 * (10 : ℝ) ^ (-21 : ℤ) < 1 := by
        have : (10 : ℝ) ^ (-21 : ℤ) = 1 / 1000000000000000000000 := by norm_num
        rw [this]
        norm_num
      have h_lt' : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 1 := by
        calc (k : ℝ)
          _ < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := h_lt
          _ ≤ Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-21 : ℤ) := by linarith
          _ < Real.pi * (10 : ℝ) ^ (n + 1) + 1 := by linarith
          
      have h_pi_21_gt : 3141592653589793238462 / 10^21 < Real.pi := by linarith [h_pi_gt]
      have h_pi_21_lt : Real.pi < 3141592653589793238463 / 10^21 := by linarith [h_pi_lt]
      
      have h_gt_mul : (3141592653589793238462 / 10^21) * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
        calc (3141592653589793238462 / 10^21) * (10 : ℝ) ^ (n + 1)
          _ < Real.pi * (10 : ℝ) ^ (n + 1) := by
            apply mul_lt_mul_of_pos_right h_pi_21_gt (by positivity)
          _ < (k : ℝ) := h_gt
          
      have h_lt_mul : (k : ℝ) < (3141592653589793238463 / 10^21) * (10 : ℝ) ^ (n + 1) := by
        calc (k : ℝ)
          _ < Real.pi * (10 : ℝ) ^ (n + 1) + 1 := h_lt'
          _ < (3141592653589793238463 / 10^21) * (10 : ℝ) ^ (n + 1) := by
            have h_diff_pos : 0 < (3141592653589793238463 / 10^21 - Real.pi) * (10 : ℝ) ^ (n + 1) - 1 := by
              have h_pi_diff : 349 / 10^24 ≤ 3141592653589793238463 / 10^21 - Real.pi := by linarith [h_pi_lt]
              have hn_ge_22 : 22 ≤ n + 1 := by omega
              have h_ten_n_ge_22 : (10 : ℝ) ^ 22 ≤ (10 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) hn_ge_22
              have h_factor : 349 / 100 ≤ (349 / (10 : ℝ)^24) * (10 : ℝ)^22 := by
                calc 349 / 100
                  _ = (349 / (10 : ℝ)^24) * (10 : ℝ)^22 := by ring
                  _ ≤ (349 / (10 : ℝ)^24) * (10 : ℝ)^(n+1) := mul_le_mul_of_nonneg_left h_ten_n_ge_22 (by positivity)
              have h_mul : (349 / (10 : ℝ)^24) * (10 : ℝ)^(n+1) ≤ (3141592653589793238463 / 10^21 - Real.pi) * (10 : ℝ) ^ (n + 1) := by
                apply mul_le_mul_of_nonneg_right h_pi_diff (by positivity)
              linarith
            linarith
            
      have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ 21 * (10 : ℝ) ^ (n - 20) := by
        have : n + 1 = 21 + (n - 20) := by omega
        rw [this, pow_add]
        
      have h_gt_mul_simp : ((3141592653589793238462 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20) < (k : ℝ) := by
        have h_calc : (3141592653589793238462 / 10^21) * (10 : ℝ) ^ (n + 1) = ((3141592653589793238462 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20) := by
          rw [h_pow_eq]
          have : (10 : ℝ) ^ 21 ≠ 0 := by positivity
          field_simp
          ring
        rwa [h_calc] at h_gt_mul
        
      have h_lt_mul_simp : (k : ℝ) < ((3141592653589793238463 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20) := by
        have h_calc : (3141592653589793238463 / 10^21) * (10 : ℝ) ^ (n + 1) = ((3141592653589793238463 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20) := by
          rw [h_pow_eq]
          have : (10 : ℝ) ^ 21 ≠ 0 := by positivity
          field_simp
          ring
        rwa [h_calc] at h_lt_mul
        
      have hk_gt : 3141592653589793238462 * 10 ^ (n - 20) < k := by
        exact_mod_cast (by linarith : ((3141592653589793238462 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20) < (k : ℝ))
        
      have hk_lt : k < 3141592653589793238463 * 10 ^ (n - 20) := by
        exact_mod_cast (by linarith : (k : ℝ) < ((3141592653589793238463 : ℤ) : ℝ) * (10 : ℝ) ^ (n - 20))
        
      -- To show a contradiction here, we notice that:
      -- k must be a multiple of 10^(n-20).
      -- Let's prove that k is a multiple of 10^(n-20).
      -- Let X = 10^(n-20). Since 21 <= n, so n-20 >= 1.
      -- So we can write k as X * q + d where 0 <= d < X.
      -- If we show d = 0:
      -- Then k = X * q, so A * X < X * q < (A + 1) * X, so A < q < A + 1, which has no integer solution.
      -- To prove d = 0, we can use the fact that k is extremely close to Real.pi * 10^(n+1).
      -- Wait, can we do this using a simpler induction on n?
      -- Actually, we can prove the theorem for n >= 21 by showing that:
      -- If there is a counterexample k for n+1, then there is a counterexample q for n.
      -- Let's define this step relation!
      -- If there is a counterexample for n+1, we have:
      -- Real.pi * 10^(n+1) < k < Real.pi * 10^(n+1) + 2 * 10^(-(n+1)) (since 2 * 10^(-(n+1)) < 1 for n >= 21).
      -- This implies k is a multiple of 10!
      -- Why? Because:
      -- If k is not a multiple of 10, then k = 10 * q + d with 1 <= d <= 9.
      -- This implies Real.pi * 10^n < q + d/10 < Real.pi * 10^n + 2 * 10^(-(n+2)).
      -- Subtracting Real.pi * 10^n:
      -- 0 < q + d/10 - Real.pi * 10^n < 2 * 10^(-(n+2)).
      -- Since n >= 21:
      -- 10^n * Real.pi is extremely close to the decimal q + d/10.
      -- But we know that 10^n * Real.pi cannot be close to any non-integer decimal of length 1!
      -- Specifically, 10^n * Real.pi is never close to q + d/10 with d != 0.
      -- In Lean, we can prove this for all n >= 21 using the fact that 10^21 * Real.pi is not close to any such rational.
      -- Specifically, we can write:
      -- 10^n * Real.pi = 10^(n-21) * (10^21 * Real.pi).
      -- Since 10^21 * Real.pi is in (A + 0.63, A + 0.66):
      -- q + d/10 is in (10^(n-21) * (A + 0.63), 10^(n-21) * (A + 0.66) + 2 * 10^(-23 - (n-21))).
      -- This is a contradiction because the digits of pi starting from position 22 do not match the required run of 9s or 0s!
      -- Let's formalize this contradiction.
      -- Wait, actually, can we prove that k must be a multiple of 10^(n-20)?
      -- Yes! Let's write the proof of `10 ∣ k` directly!
      -- Let k_mod = k % 10.
      -- We show k_mod = 0.
      have h_mod : k % 10 = 0 ∨ k % 10 = 1 ∨ k % 10 = 2 ∨ k % 10 = 3 ∨ k % 10 = 4 ∨ k % 10 = 5 ∨ k % 10 = 6 ∨ k % 10 = 7 ∨ k % 10 = 8 ∨ k % 10 = 9 := by omega
      rcases h_mod with hk0 | hk1 | hk2 | hk3 | hk4 | hk5 | hk6 | hk7 | hk8 | hk9
      · -- Case k % 10 = 0. This means 10 ∣ k!
        have h_div_10 : ∃ q, k = 10 * q := by
          use k / 10
          omega
        rcases h_div_10 with ⟨q, hq⟩
        -- We will prove that q is a counterexample for n, which is a contradiction!
        -- Actually, we can show that:
        -- Real.pi * 10^n < q
        have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by
            exact_mod_cast hq
          have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) := by rwa [← this] at h_gt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := by
            have : n + 1 = n + 1 := by rfl
            rw [pow_succ]
            ring
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
          
        -- And q < Real.pi / arctan (1 / 10^n)
        have h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          -- we know: q < Real.pi * 10^n + 0.2 * 10^(-n)
          have : (k : ℝ) = 10 * (q : ℝ) := by
            exact_mod_cast hq
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [← this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := by
            rw [pow_succ]
            ring
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
            have : -((n + 1) : ℤ) = -n - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
          -- But we also know: Real.pi * 10^n + 0.2 * 10^(-n) < Real.pi / arctan (1 / 10^n)
          -- Actually, we can show that:
          -- 0.2 * 10^(-n) <= 2 * 10^(-(n+1)), wait, no.
          -- Since n >= 21:
          -- Real.pi / Real.arctan (1 / 10^n) > Real.pi * 10^n + 0.2 * 10^(-n)
          -- Let's prove this!
          have h_arctan_lt : Real.arctan (1 / (10 : ℝ) ^ n) < 1 / (10 : ℝ) ^ n := by
            apply arctan_lt_id
            positivity
          have h_arctan_pos : 0 < Real.arctan (1 / (10 : ℝ) ^ n) := by
            apply arctan_pos
            positivity
          have h_div_gt : Real.pi / (1 / (10 : ℝ) ^ n) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
            apply div_lt_div_of_pos_left Real.pi_pos h_arctan_pos h_arctan_lt
          have h_div_simp : Real.pi / (1 / (10 : ℝ) ^ n) = Real.pi * (10 : ℝ) ^ n := by
            have : (10 : ℝ) ^ n ≠ 0 := by positivity
            field_simp
            ring
          rw [h_div_simp] at h_div_gt
          -- Since q < Real.pi * 10^n + 0.2 * 10^(-n) is not enough because we only know Real.pi * 10^n < Real.pi / arctan
          -- Wait!
          -- Why don't we do this:
          -- If 10 ∣ k, then q is a counterexample for n.
          -- But wait! By induction, we can show that for any n, there is no counterexample!
          -- Actually, if we just prove this for n+1, we can prove the theorem by induction!
          -- Let's write the complete proof of step!
          sorry
      · -- Case k % 10 = 1. This means k = 10 * q + 1
        sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
"""

out.append(main_theorem)

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("".join(out))
print("Spec.lean successfully generated!")
