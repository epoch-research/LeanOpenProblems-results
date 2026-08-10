import decimal
from decimal import Decimal, getcontext

getcontext().prec = 100

n = 50
k = 25

# 1. Generate upper bounds of sqrtTwoAddSeries (for pi_lower_bound)
u = [Fraction(0)] if False else [] # we will import fractions
from fractions import Fraction
u = [Fraction(0)]
u_str = []
for i in range(1, n + 1):
    v = (Decimal(2) + Decimal(u[-1].numerator) / Decimal(u[-1].denominator)).sqrt()
    target = Decimal(2) - v
    den = 10**(int(i * 0.6) + k)
    num = int(target * den)
    u.append(2 - Fraction(num, den))
    u_str.append(f"2-{num}/{den}")
    
# 2. Generate lower bounds of sqrtTwoAddSeries (for pi_upper_bound)
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
  have h_le : Real.pi / (x - x ^ 3 / 4) ≤ Real.pi / x + 2 * x := by
    -- wait, we have 3/4 or 3/3? In test4 it was 3/3
    sorry
"""
