import decimal
from decimal import Decimal, getcontext

getcontext().prec = 150

M = 60
M_plus_1 = M + 1

pi_lb = Decimal('3.141592653589793238462643383279502884197169399375105820974944592307816406286208')
pi_ub = Decimal('3.141592653589793238462643383279502884197169399375105820974944592307816406286210')

def format_decimal(d):
    s = "{:f}".format(d)
    if '.' in s:
        s = s.rstrip('0').rstrip('.')
    return s

pi_lb_val_scaled = int(pi_lb * 10**M)
pi_ub_val_scaled = pi_lb_val_scaled + 2

# Read the header from Spec.lean up to line 230
header_lines = []
with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    for i in range(231):
        line = f.readline()
        if not line:
            break
        header_lines.append(line)
header = "".join(header_lines)

out = [header]

# Generate subgoal cases (same as before)
for N in range(1, M + 1):
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

# Define properties T_prop and S_prop
properties = """
def T_prop (n : ℕ) : Prop :=
  ∀ (r : ℤ), 1 ≤ r → r ≤ 9 →
    ¬ ∃ (q : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) ∧
      (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ))

def S_prop (n : ℕ) : Prop :=
  ¬ ∃ (k : ℤ), Real.pi * (10 : ℝ) ^ n < (k : ℝ) ∧
    (k : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n)
"""
out.append(properties)

# Prove subgoal_T_60
subgoal_T_60_code = """
lemma subgoal_T_60 : T_prop 60 := by
  intro r hr1 hr2
  intro ⟨q, h1, h2⟩
  have h_pi_gt : 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 < Real.pi := pi_gt_60
  have h_pi_lt : Real.pi < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 := pi_lt_60
  have h_pow_cast_real : (10 : ℝ) ^ 60 = 1000000000000000000000000000000000000000000000000000000000000 := by norm_num
  have h_ten_neg : 2 * (10 : ℝ) ^ (-62 : ℤ) = 2 / 100000000000000000000000000000000000000000000000000000000000000 := by norm_num
  rw [h_pow_cast_real] at h1 h2
  rw [h_ten_neg] at h2
  interval_cases r
"""

for r in range(1, 10):
    L_q = pi_lb * 10**60 - Decimal(r) / Decimal(10)
    U_q = pi_ub * 10**60 - Decimal(r) / Decimal(10) + Decimal('2') * Decimal('10')**(-62)
    L_floor = int(L_q)
    U_ceil = int(U_q) + 1
    subgoal_T_60_code += f"""  · -- r = {r}
    have h_q_gt : ({L_floor} : ℝ) < (q : ℝ) := by
      calc ({L_floor} : ℝ)
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286208 * 1000000000000000000000000000000000000000000000000000000000000 - ({r} : ℝ) / 10 := by norm_num
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - ({r} : ℝ) / 10 := by linarith
        _ < (q : ℝ) := h1
    have h_q_lt : (q : ℝ) < ({U_ceil} : ℝ) := by
      calc (q : ℝ)
        _ < Real.pi * 1000000000000000000000000000000000000000000000000000000000000 - ({r} : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := h2
        _ < 3.141592653589793238462643383279502884197169399375105820974944592307816406286210 * 1000000000000000000000000000000000000000000000000000000000000 - ({r} : ℝ) / 10 + 2 / 100000000000000000000000000000000000000000000000000000000000000 := by linarith
        _ < ({U_ceil} : ℝ) := by norm_num
    have hk_gt : {L_floor} < q := by exact_mod_cast h_q_gt
    have hk_lt : q < {U_ceil} := by exact_mod_cast h_q_lt
    omega
"""

out.append(subgoal_T_60_code)

# Prove main_induction and final theorem
main_induction_and_theorem = f"""
lemma subgoal_S_60 : S_prop 60 := subgoal_case_60

lemma main_induction (m : ℕ) : S_prop (60 + m) ∧ T_prop (60 + m) := by
  induction' m with m IH
  · exact ⟨subgoal_S_60, subgoal_T_60⟩
  · let n := 60 + m
    have hS : S_prop (n + 1) := by
      intro ⟨k, h1, h2⟩
      have h_ub := upper_bound_interval_tight (n + 1) (by omega)
      have h_lt : (k : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-(n + 1 : ℤ)) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := rfl
        rw [h_pow_cast_real] at h2
        linarith [h2, h_ub]
      have h_gt : Real.pi * (10 : ℝ) ^ (n + 1) < (k : ℝ) := by
        have h_pow_cast_real : (10 : ℝ) ^ ((n + 1) : ℕ).cast = (10 : ℝ) ^ (n + 1) := rfl
        rwa [h_pow_cast_real] at h1
      have h_div_10 : k % 10 = 0 ∨ (∃ r, (1 ≤ r ∧ r ≤ 9) ∧ k = 10 * (k / 10) + r) := by
        have : k % 10 = 0 ∨ 1 ≤ k % 10 ∧ k % 10 ≤ 9 := by omega
        rcases this with hk0 | hk_rem
        · left; exact hk0
        · right; use k % 10; exact ⟨hk_rem, by omega⟩
      rcases h_div_10 with hk0 | ⟨r, ⟨hr1, hr2⟩, hq⟩
      · let q := k / 10
        have h_k_eq : k = 10 * q := by omega
        have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q : ℝ) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
          have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) := by rwa [this] at h_gt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
        have h_q_lt : (q : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          have : (k : ℝ) = 10 * (q : ℝ) := by exact_mod_cast h_k_eq
          have h_lt_simp : 10 * (q : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
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
          linarith [h_q_lt_linear, h_arctan_lower]
        have h_contra : ∃ (k' : ℤ), Real.pi * (10 : ℝ) ^ n < k'.cast ∧ k'.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          use q
          exact ⟨h_q_gt, h_q_lt⟩
        exact IH.left h_contra
      · let q := k / 10
        have h_k_eq : k = 10 * q + r := hq
        have : (k : ℝ) = 10 * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
        have h_gt' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q : ℝ) := by
          have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q : ℝ) + (r : ℝ) := by rwa [this] at h_gt
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          rw [h_pow_eq] at h_gt_rw
          linarith
        have h_lt' : (q : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
          have h_lt_rw : 10 * (q : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
            have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_eq, h_zpow_eq] at h_lt_rw
          linarith
        have h_contra : ∃ (q' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q' : ℝ) ∧
            (q' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
          use q
          exact ⟨h_gt', h_lt'⟩
        exact IH.right r hr1 hr2 h_contra
        
    have hT : T_prop (n + 1) := by
      intro r' hr1' hr2'
      intro ⟨q', h1', h2'⟩
      let k' := 10 * q' + r'
      have : (k' : ℝ) = 10 * (q' : ℝ) + (r' : ℝ) := by exact_mod_cast (by rfl : k' = 10 * q' + r')
      have h_gt' : Real.pi * (10 : ℝ) ^ (n + 1) < (k' : ℝ) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        rw [this, h_pow_eq]
        linarith
      have h_lt' : (k' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by
        have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
        have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
          have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
          rw [this, zpow_add₀ (by norm_num)]
          ring
        rw [this, h_pow_eq, h_zpow_eq]
        linarith
      have h_div_10 : k' % 10 = 0 ∨ (∃ r, (1 ≤ r ∧ r ≤ 9) ∧ k' = 10 * (k' / 10) + r) := by
        have : k' % 10 = 0 ∨ 1 ≤ k' % 10 ∧ k' % 10 ≤ 9 := by omega
        rcases this with hk0 | hk_rem
        · left; exact hk0
        · right; use k' % 10; exact ⟨hk_rem, by omega⟩
      rcases h_div_10 with hk0 | ⟨r, ⟨hr1, hr2⟩, hq⟩
      · let q'' := k' / 10
        have h_k_eq : k' = 10 * q'' := by omega
        have h_q_gt : Real.pi * (10 : ℝ) ^ n < (q'' : ℝ) := by
          have : (k' : ℝ) = 10 * (q'' : ℝ) := by exact_mod_cast h_k_eq
          have h_gt_simp : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q'' : ℝ) := by rwa [this] at h_gt'
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          rw [h_pow_eq_10_mul] at h_gt_simp
          linarith [h_gt_simp]
        have h_q_lt : (q'' : ℝ) < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          have : (k' : ℝ) = 10 * (q'' : ℝ) := by exact_mod_cast h_k_eq
          have h_lt_simp : 10 * (q'' : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt'
          have h_pow_eq_10_mul : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq_10_div : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-n : ℤ) / 10 := by
            have : -((n + 1) : ℤ) = -n - 1 := by omega
            rw [this, zpow_sub_one₀ (by norm_num)]
            ring
          rw [h_pow_eq_10_mul, h_zpow_eq_10_div] at h_lt_simp
          have h_q_lt_linear : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n + 0.2 * (10 : ℝ) ^ (-n : ℤ) := by linarith
          have h_arctan_lower := pi_div_arctan_gt n (by omega)
          have h_pow_neg_eq : (10 : ℝ) ^ (-(n + 2 : ℤ)) = 0.01 * (10 : ℝ) ^ (-n : ℤ) := by
            have : (-(n + 2 : ℤ)) = (-n : ℤ) + (-2 : ℤ) := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_neg_eq] at h_arctan_lower
          linarith [h_q_lt_linear, h_arctan_lower]
        have h_contra : ∃ (k'' : ℤ), Real.pi * (10 : ℝ) ^ n < k''.cast ∧ k''.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ n) := by
          use q''
          exact ⟨h_q_gt, h_q_lt⟩
        exact IH.left h_contra
      · let q'' := k' / 10
        have h_k_eq : k' = 10 * q'' + r := hq
        have : (k' : ℝ) = 10 * (q'' : ℝ) + (r : ℝ) := by exact_mod_cast h_k_eq
        have h_gt'' : Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q'' : ℝ) := by
          have h_gt_rw : Real.pi * (10 : ℝ) ^ (n + 1) < 10 * (q'' : ℝ) + (r : ℝ) := by rwa [this] at h_gt'
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          rw [h_pow_eq] at h_gt_rw
          linarith
        have h_lt'' : (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
          have h_lt_rw : 10 * (q'' : ℝ) + (r : ℝ) < Real.pi * (10 : ℝ) ^ (n + 1) + 2 * (10 : ℝ) ^ (-((n + 1) : ℤ)) := by rwa [this] at h_lt'
          have h_pow_eq : (10 : ℝ) ^ (n + 1) = (10 : ℝ) ^ n * 10 := pow_succ 10 n
          have h_zpow_eq : (10 : ℝ) ^ (-((n + 1) : ℤ)) = (10 : ℝ) ^ (-(n + 2 : ℤ)) * 10 := by
            have : -((n + 1) : ℤ) = -(n + 2 : ℤ) + 1 := by omega
            rw [this, zpow_add₀ (by norm_num)]
            ring
          rw [h_pow_eq, h_zpow_eq] at h_lt_rw
          linarith
        have h_contra : ∃ (q'' : ℤ), Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 < (q'' : ℝ) ∧
            (q'' : ℝ) < Real.pi * (10 : ℝ) ^ n - (r : ℝ) / 10 + 2 * (10 : ℝ) ^ (-(n + 2 : ℤ)) := by
          use q''
          exact ⟨h_gt'', h_lt''⟩
        exact IH.right r hr1 hr2 h_contra
    exact ⟨hS, hT⟩

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
  · have h_or : n < 60 ∨ 60 ≤ n := by omega
    rcases h_or with hn_lt | hn_ge
    · interval_cases n
"""

for N in range(1, M + 1):
    main_induction_and_theorem += f"      · exact subgoal_case_{N}\n"

main_induction_and_theorem += """    · have h_ind := main_induction (n - 60)
      have h_eq : 60 + (n - 60) = n := by omega
      rw [h_eq] at h_ind
      exact h_ind.left
"""

out.append(main_induction_and_theorem)

out.append("\n#print axioms oeis_a011545_conjecture_0\n")

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("".join(out))

print("generate_final_v9.py successfully wrote Submission/Spec.lean")
