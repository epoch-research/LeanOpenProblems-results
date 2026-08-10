import decimal
from decimal import Decimal, getcontext

getcontext().prec = 100

pi_lb = Decimal('3.14159265358979323846')
pi_ub = Decimal('3.14159265358979323846983')

# We want to generate Spec.lean
header = """import FormalConjectures.Util.ProblemImports

open Real Int

theorem pi_lt_34 : Real.pi < 3.14159265358979323846983 := by
  -- bound[31415926535897932384699*^-22, Iters -> 34, Rounding -> .5, Precision -> 46]
  pi_upper_bound [
    215157040700/152139002499, 936715022285/506946517009, 1760670193473/897581880893,
    2-6049918861/628200981455, 2-8543385003/3546315642356, 2-2687504973/4461606579043,
    2-1443277808/9583752057175, 2-546886849/14525765179168, 2-650597193/69121426717657,
    2-199969519/84981432264454, 2-226282901/384655467333100, 2-60729699/412934601558121,
    2-25101251/682708800188252, 2-7156464/778571703825145, 2-7524725/3274543383827551,
    2-4663362/8117442793616861, 2-1913009/13319781840326041, 2-115805/3225279830894912,
    2-708749/78957345705688293, 2-131255/58489233342660393, 2-101921/181670219085488669,
    2-44784/319302953916238627, 2-82141/2342610212364552264, 2-4609/525783249231842696,
    2-4567/2083967975041722089, 2-2273/4148770928197796067, 2-563/4110440884426500846,
    2-784/22895812812720260289, 2-1717/200571992854289218531, 2-368/171952226838388893139,
    2-149/278487845640434185590, 2-207/1547570041545500037992, 2-20/598094702046570062987,
    2-7/837332582865198088180]

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

noncomputable def a (n : ℕ) : ℕ :=
  (floor (Real.pi * (10 : ℝ) ^ n.cast)).toNat
"""

out = [header]

# Generate each of the 21 cases as separate lemmas
for N in range(1, 22):
    ten_to_N = 10**N
    one_div_ten_to_N = f"1 / {ten_to_N}"
    
    low = pi_lb * ten_to_N
    high = pi_ub * ten_to_N + 2 * Decimal(10)**(-N)
    L_int = int(low)
    U_int = int(high) + 1
    
    lemma = f"""
lemma subgoal_case_{N} : ¬ ∃ (k : ℤ),
    (Real.pi * (10 : ℝ) ^ ({N} : ℕ).cast < k.cast) ∧
    (k.cast < Real.pi / Real.arctan (1 / (10 : ℝ) ^ ({N} : ℕ).cast)) := by
  intro ⟨k, h1, h2⟩
  have h_pi_gt : 3.14159265358979323846 < Real.pi := Real.pi_gt_d20
  have h_pi_lt : Real.pi < 3.14159265358979323846983 := pi_lt_34
  have h_ub := upper_bound_interval_tight {N} (by norm_num)
  have h_ten : (10 : ℝ) ^ (-{N} : ℤ) = {one_div_ten_to_N} := by norm_num
  have h_lt : (k : ℝ) < Real.pi * {ten_to_N} + 2 * ({one_div_ten_to_N}) := by
    have h_ub_simp := h_ub
    simp only [Nat.cast_ofNat] at h_ub_simp
    rw [h_ten] at h_ub_simp
    have h_pow_cast_nat : (10 : ℝ) ^ {N} = {ten_to_N} := by norm_num
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rw [h_pow_cast_real] at h2
    rw [h_pow_cast_nat] at h_ub_simp
    linarith [h2, h_ub_simp]
  have h_gt : Real.pi * {ten_to_N} < (k : ℝ) := by
    have h_pow_cast_real : (10 : ℝ) ^ ({N} : ℕ).cast = {ten_to_N} := by norm_num
    rwa [h_pow_cast_real] at h1
  have h_k_lt : (k : ℝ) < {float(high)} := by
    linarith [h_pi_lt, h_lt]
  have h_k_gt : {float(low)} < (k : ℝ) := by linarith [h_pi_gt, h_gt]
  have hk_gt : {L_int} < k := by
    exact_mod_cast (by linarith : {L_int} < (k : ℝ))
  have hk_lt : k < {U_int} := by
    exact_mod_cast (by linarith : (k : ℝ) < {U_int})
  omega
"""
    out.append(lemma)

# Write main theorem
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

# Append the 21 cases to the main theorem body
for N in range(1, 22):
    main_theorem += f"      · exact subgoal_case_{N}\n"

main_theorem += """    · sorry
"""

out.append(main_theorem)

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write("".join(out))
print("Spec.lean generated successfully!")
