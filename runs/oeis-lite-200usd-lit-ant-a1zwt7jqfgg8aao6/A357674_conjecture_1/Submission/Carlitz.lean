import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Carl

/-- Sign lemma: for `m ≥ 1`, `(-1)^(m+1) * bernoulli (m+1) = bernoulli (m+1)`. -/
lemma sgn_bern (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℝ) ^ (m + 1) * (bernoulli (m + 1) : ℝ) = (bernoulli (m + 1) : ℝ) := by
  rcases Nat.even_or_odd m with he | ho
  · -- m even, m+1 odd ≥ 3, bernoulli (m+1) = 0
    have h3 : Odd (m + 1) := by
      rcases he with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have : bernoulli (m + 1) = 0 := bernoulli_eq_zero_of_odd h3 (by omega)
    rw [this]; simp
  · -- m odd, m+1 even, (-1)^(m+1) = 1
    have : Even (m + 1) := by rcases ho with ⟨k, hk⟩; exact ⟨k+1, by omega⟩
    rw [Even.neg_one_pow this, one_mul]

/-- Integration by parts step for the Bernoulli product integral. -/
lemma ibp_step (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    (∫ x in (0:ℝ)..1, bernoulliFun b x * bernoulliFun a x)
      = - ((b:ℝ)/(a+1)) * ∫ x in (0:ℝ)..1, bernoulliFun (b-1) x * bernoulliFun (a+1) x := by
  have key :
      (∫ x in (0:ℝ)..1, bernoulliFun b x * bernoulliFun a x)
        = bernoulliFun b 1 * (bernoulliFun (a+1) 1 / (a+1))
          - bernoulliFun b 0 * (bernoulliFun (a+1) 0 / (a+1))
          - ∫ x in (0:ℝ)..1, ((b:ℝ) * bernoulliFun (b-1) x) * (bernoulliFun (a+1) x / (a+1)) := by
    have hd : ∀ x : ℝ, HasDerivAt (fun x => bernoulliFun (a+1) x / (a+1)) (bernoulliFun a x) x := by
      intro x; exact antideriv_bernoulliFun a x
    have hu : ∀ x : ℝ, HasDerivAt (bernoulliFun b) ((b:ℝ) * bernoulliFun (b-1) x) x := by
      intro x; exact hasDerivAt_bernoulliFun b x
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (continuous_bernoulliFun b).continuousOn
      ((continuous_bernoulliFun (a+1)).div_const _).continuousOn
      (fun x _ => hu x) (fun x _ => hd x)
      ((continuous_const.mul (continuous_bernoulliFun (b-1))).intervalIntegrable _ _)
      ((continuous_bernoulliFun a).intervalIntegrable _ _)
  rw [key]
  have e1 : bernoulliFun b 1 = bernoulliFun b 0 := bernoulliFun_endpoints_eq_of_ne_one (by omega)
  have e2 : bernoulliFun (a+1) 1 = bernoulliFun (a+1) 0 := bernoulliFun_endpoints_eq_of_ne_one (by omega)
  rw [e1, e2]
  rw [show (∫ x in (0:ℝ)..1, ((b:ℝ) * bernoulliFun (b-1) x) * (bernoulliFun (a+1) x / (a+1)))
        = ((b:ℝ)/(a+1)) * ∫ x in (0:ℝ)..1, bernoulliFun (b-1) x * bernoulliFun (a+1) x from ?_]
  · ring
  · rw [← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring

/-- Base case `n = 1`. -/
lemma intBB_base (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (0:ℝ)..1, bernoulliFun m x * bernoulliFun 1 x)
      = (bernoulli (m+1):ℝ)/(m+1) := by
  have hcomm : (∫ x in (0:ℝ)..1, bernoulliFun m x * bernoulliFun 1 x)
      = ∫ x in (0:ℝ)..1, bernoulliFun 1 x * bernoulliFun m x := by
    simp_rw [mul_comm (bernoulliFun m _) (bernoulliFun 1 _)]
  rw [hcomm]
  have hu1 : ∀ x : ℝ, HasDerivAt (bernoulliFun 1) ((1:ℝ) * bernoulliFun 0 x) x := by
    intro x; simpa using hasDerivAt_bernoulliFun 1 x
  have key :
      (∫ x in (0:ℝ)..1, bernoulliFun 1 x * bernoulliFun m x)
        = bernoulliFun 1 1 * (bernoulliFun (m+1) 1 / (m+1))
          - bernoulliFun 1 0 * (bernoulliFun (m+1) 0 / (m+1))
          - ∫ x in (0:ℝ)..1, ((1:ℝ) * bernoulliFun 0 x) * (bernoulliFun (m+1) x / (m+1)) := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (continuous_bernoulliFun 1).continuousOn
      ((continuous_bernoulliFun (m+1)).div_const _).continuousOn
      (fun x _ => hu1 x) (fun x _ => antideriv_bernoulliFun m x)
      ((continuous_const.mul (continuous_bernoulliFun 0)).intervalIntegrable _ _)
      ((continuous_bernoulliFun m).intervalIntegrable _ _)
  rw [key]
  have e2 : bernoulliFun (m+1) 1 = bernoulliFun (m+1) 0 := bernoulliFun_endpoints_eq_of_ne_one (by omega)
  have hint0 : (∫ x in (0:ℝ)..1, ((1:ℝ) * bernoulliFun 0 x) * (bernoulliFun (m+1) x / (m+1))) = 0 := by
    rw [show (fun x => ((1:ℝ) * bernoulliFun 0 x) * (bernoulliFun (m+1) x / (m+1)))
          = (fun x => (1/(m+1) : ℝ) * bernoulliFun (m+1) x) from ?_]
    · rw [intervalIntegral.integral_const_mul, integral_bernoulliFun_eq_zero (by omega), mul_zero]
    · ext x; simp [bernoulliFun_zero]; ring
  rw [hint0, e2]
  simp only [bernoulliFun_one, bernoulliFun_eval_zero, bernoulli_one]
  push_cast
  ring

/-- The Bernoulli polynomial product integral formula:
`∫₀¹ Bₘ(x)Bₙ(x) dx = (-1)^(m+1) m!n!/(m+n)! · B_{m+n}` for `m,n ≥ 1`. -/
lemma intBB : ∀ n, 1 ≤ n → ∀ m, 1 ≤ m →
    (∫ x in (0:ℝ)..1, bernoulliFun m x * bernoulliFun n x)
      = (-1:ℝ)^(m+1) * ((m.factorial * n.factorial : ℝ)/((m+n).factorial)) * (bernoulli (m+n):ℝ) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _ m hm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- k = 0, base case
      subst hk
      rw [intBB_base m hm]
      have hmf : ((m.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
      have hs := sgn_bern m hm
      simp only [Nat.zero_add, Nat.cast_one, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add]
      field_simp
      linear_combination (-1:ℝ) * hs
    · -- inductive step: k+1 ≥ 2, k ≥ 1
      have hcomm : (∫ x in (0:ℝ)..1, bernoulliFun m x * bernoulliFun (k+1) x)
          = ∫ x in (0:ℝ)..1, bernoulliFun (k+1) x * bernoulliFun m x := by
        simp_rw [mul_comm (bernoulliFun m _) (bernoulliFun (k+1) _)]
      rw [hcomm, ibp_step m (k+1) hm (by omega)]
      simp only [Nat.add_sub_cancel]
      have hcomm2 : (∫ x in (0:ℝ)..1, bernoulliFun k x * bernoulliFun (m+1) x)
          = ∫ x in (0:ℝ)..1, bernoulliFun (m+1) x * bernoulliFun k x := by
        simp_rw [mul_comm (bernoulliFun k _) (bernoulliFun (m+1) _)]
      rw [hcomm2, ih hk (m+1) (by omega)]
      -- now algebra
      have hmn : m + 1 + k = m + (k + 1) := by omega
      rw [hmn, Nat.factorial_succ (m), Nat.factorial_succ k]
      push_cast
      have hf : ((m + (k+1)).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      have hm1 : ((m:ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
/-- The Bernoulli self-convolution polynomial `R_N(x) = Σ_{m=0}^N B_m(x) B_{N-m}(x)`. -/
noncomputable def R (N : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N+1), bernoulliFun m x * bernoulliFun (N - m) x

/-- Derivative recurrence: `R_{N+1}'(x) = (N+2) R_N(x)`. -/
lemma hasDerivAt_R (N : ℕ) (x : ℝ) :
    HasDerivAt (R (N+1)) ((N+2 : ℝ) * R N x) x := by
  have hsum : HasDerivAt (R (N+1))
      (∑ m ∈ Finset.range (N+2),
        (((m:ℝ) * bernoulliFun (m-1) x) * bernoulliFun (N+1-m) x
          + bernoulliFun m x * ((↑(N+1-m):ℝ) * bernoulliFun (N+1-m-1) x))) x := by
    rw [show R (N+1) = ∑ m ∈ Finset.range (N+2),
        (fun y => bernoulliFun m y * bernoulliFun (N+1-m) y) from by
      funext y; rw [Finset.sum_apply]; rfl]
    apply HasDerivAt.sum
    intro m _
    exact (hasDerivAt_bernoulliFun m x).mul (hasDerivAt_bernoulliFun (N+1-m) x)
  -- Rewrite the derivative sum as (N+2) * R N x
  have key : (∑ m ∈ Finset.range (N+2),
        (((m:ℝ) * bernoulliFun (m-1) x) * bernoulliFun (N+1-m) x
          + bernoulliFun m x * ((↑(N+1-m):ℝ) * bernoulliFun (N+1-m-1) x)))
        = (N+2 : ℝ) * R N x := by
    rw [Finset.sum_add_distrib]
    -- first sum reindex
    have h1 : (∑ m ∈ Finset.range (N+2), ((m:ℝ) * bernoulliFun (m-1) x) * bernoulliFun (N+1-m) x)
        = ∑ m ∈ Finset.range (N+1), ((m+1:ℝ) * bernoulliFun m x) * bernoulliFun (N-m) x := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have : N + 1 - (m+1) = N - m := by omega
      rw [this]
      push_cast
      ring
    have h2 : (∑ m ∈ Finset.range (N+2),
          bernoulliFun m x * ((↑(N+1-m):ℝ) * bernoulliFun (N+1-m-1) x))
        = ∑ m ∈ Finset.range (N+1), bernoulliFun m x * ((↑(N+1-m):ℝ) * bernoulliFun (N-m) x) := by
      rw [Finset.sum_range_succ]
      have hz : (↑(N+1-(N+1)):ℝ) = 0 := by norm_num
      rw [hz]
      simp only [zero_mul, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro m hm
      have : N + 1 - m - 1 = N - m := by
        rw [Finset.mem_range] at hm; omega
      rw [this]
    rw [h1, h2, R, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    have hcast : (↑(N+1-m):ℝ) = (N:ℝ) + 1 - m := by
      have : N + 1 - m = N + 1 - m := rfl
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]; ring
  rw [key] at hsum
  exact hsum

/-- `R` is continuous. -/
lemma continuous_R (N : ℕ) : Continuous (R N) := by
  apply continuous_finset_sum
  intro m _
  exact (continuous_bernoulliFun m).mul (continuous_bernoulliFun (N-m))

lemma R_zero_fun (x : ℝ) : R 0 x = 1 := by
  simp [R, Finset.sum_range_one, bernoulliFun_zero]

/-- The integral `J_N = ∫₀¹ R_N`. -/
noncomputable def J (N : ℕ) : ℝ := ∫ x in (0:ℝ)..1, R N x

lemma J_zero : J 0 = 1 := by
  rw [J]
  rw [show (fun x => R 0 x) = (fun _ => (1:ℝ)) from funext R_zero_fun]
  simp

/-- Integrating the recurrence `R_{N+1}' = (N+2) R_N`. -/
lemma J_recurrence (N : ℕ) : (N+2 : ℝ) * J N = R (N+1) 1 - R (N+1) 0 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (R (N+1)) ((N+2)*R N x) x :=
    fun x _ => hasDerivAt_R N x
  have hint : IntervalIntegrable (fun x => (N+2:ℝ)*R N x) MeasureTheory.volume 0 1 :=
    ((continuous_const.mul (continuous_R N))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint,
    intervalIntegral.integral_const_mul]
  rfl

/-- Endpoint difference: for `N ≥ 2`, `R_{N+1}(1) - R_{N+1}(0) = 2 B_N`. -/
lemma R_endpoint (N : ℕ) (hN : 2 ≤ N) :
    R (N+1) 1 - R (N+1) 0 = 2 * (bernoulli N : ℝ) := by
  rw [R, R, ← Finset.sum_sub_distrib]
  have hterm : ∀ m ∈ Finset.range (N+2),
      bernoulliFun m 1 * bernoulliFun (N+1-m) 1 - bernoulliFun m 0 * bernoulliFun (N+1-m) 0
        = (bernoulli m : ℝ) * (if m = N then 1 else 0)
          + (if m = 1 then (1:ℝ) else 0) * (bernoulli (N+1-m) : ℝ)
          + (if m = 1 then (1:ℝ) else 0) * (if m = N then (1:ℝ) else 0) := by
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [bernoulliFun_eval_one, bernoulliFun_eval_zero]
    have he : (N + 1 - m = 1) ↔ (m = N) := by omega
    rw [show (if N + 1 - m = 1 then (1:ℝ) else 0) = (if m = N then (1:ℝ) else 0) from by
      simp only [he]]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : (∑ m ∈ Finset.range (N+2), (bernoulli m : ℝ) * (if m = N then 1 else 0))
      = (bernoulli N : ℝ) := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [show N ∈ Finset.range (N+2) from Finset.mem_range.2 (by omega)]
  have h2 : (∑ m ∈ Finset.range (N+2), (if m = 1 then (1:ℝ) else 0) * (bernoulli (N+1-m) : ℝ))
      = (bernoulli N : ℝ) := by
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp [show 1 ∈ Finset.range (N+2) from Finset.mem_range.2 (by omega),
      show N + 1 - 1 = N from by omega]
  have h3 : (∑ m ∈ Finset.range (N+2), (if m = 1 then (1:ℝ) else 0) * (if m = N then (1:ℝ) else 0))
      = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rcases Classical.em (m = N) with h | h
    · rw [if_neg (show ¬ m = 1 by omega), zero_mul]
    · rw [if_neg h, mul_zero]
  rw [h1, h2, h3]
  ring

/-- The key value `J_N = 2 B_N/(N+2)` for `N ≥ 2`. -/
lemma J_val (N : ℕ) (hN : 2 ≤ N) : J N = 2 * (bernoulli N : ℝ) / (N+2) := by
  have h := J_recurrence N
  rw [R_endpoint N hN] at h
  have hne : (N+2 : ℝ) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith [h]

lemma J_one : J 1 = 0 := by
  rw [J]
  have hfun : (fun x => R 1 x) = (fun x => 2 * bernoulliFun 1 x) := by
    funext x
    rw [R, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.sub_zero, Nat.sub_self, bernoulliFun_zero]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_bernoulliFun_eq_zero (by norm_num), mul_zero]

/-- The basis-expansion candidate `Σ_k C(N+1,k) J_{N-k} B_k(x)`. -/
noncomputable def RHS (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N+1), (Nat.choose (N+1) k : ℝ) * J (N-k) * bernoulliFun k x

lemma continuous_RHS (N : ℕ) : Continuous (RHS N) := by
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul (continuous_bernoulliFun k)

/-- Derivative recurrence for `RHS`: `RHS_{N+1}' = (N+2) RHS_N`. -/
lemma hasDerivAt_RHS (N : ℕ) (x : ℝ) :
    HasDerivAt (RHS (N+1)) ((N+2:ℝ) * RHS N x) x := by
  have hsum : HasDerivAt (RHS (N+1))
      (∑ k ∈ Finset.range (N+2),
        ((Nat.choose (N+2) k : ℝ) * J (N+1-k)) * ((k:ℝ) * bernoulliFun (k-1) x)) x := by
    rw [show RHS (N+1) = ∑ k ∈ Finset.range (N+2),
        (fun y => (Nat.choose (N+2) k : ℝ) * J (N+1-k) * bernoulliFun k y) from by
      funext y; rw [Finset.sum_apply]; rfl]
    apply HasDerivAt.sum
    intro k _
    exact (hasDerivAt_bernoulliFun k x).const_mul ((Nat.choose (N+2) k : ℝ) * J (N+1-k))
  have key : (∑ k ∈ Finset.range (N+2),
        ((Nat.choose (N+2) k : ℝ) * J (N+1-k)) * ((k:ℝ) * bernoulliFun (k-1) x))
        = (N+2:ℝ) * RHS N x := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    rw [RHS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hidx : N+1-(j+1) = N - j := by omega
    rw [hidx, Nat.add_sub_cancel]
    have hnat : (N+2) * Nat.choose (N+1) j = Nat.choose (N+2) (j+1) * (j+1) := by
      have h := Nat.succ_mul_choose_eq (N+1) j
      simpa using h
    have hch : ((Nat.choose (N+2) (j+1):ℝ)) * (j+1) = (N+2) * (Nat.choose (N+1) j) := by
      have := congrArg (Nat.cast (R := ℝ)) hnat
      push_cast at this ⊢
      linarith [this]
    push_cast
    linear_combination (J (N-j) * bernoulliFun j x) * hch
  rw [key] at hsum
  exact hsum

/-- The integral of `RHS_N` equals `J_N` (since `∫ B_k = [k=0]`). -/
lemma integral_RHS (N : ℕ) : (∫ x in (0:ℝ)..1, RHS N x) = J N := by
  have hstep : (∫ x in (0:ℝ)..1, RHS N x)
      = ∑ k ∈ Finset.range (N+1),
          (Nat.choose (N+1) k : ℝ) * J (N-k) * (∫ x in (0:ℝ)..1, bernoulliFun k x) := by
    simp only [RHS]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const_mul]
    · intro k _
      exact (continuous_const.mul (continuous_bernoulliFun k)).intervalIntegrable _ _
  rw [hstep]
  simp_rw [integral_bernoulliFun]
  rw [Finset.sum_eq_single 0]
  · simp [J]
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- **Basis formula**: `R_N(x) = Σ_{k=0}^N C(N+1,k) J_{N-k} B_k(x)`. -/
lemma basis : ∀ N x, R N x = RHS N x := by
  intro N
  induction N with
  | zero =>
    intro x
    rw [R_zero_fun, RHS]
    simp [J_zero, bernoulliFun_zero]
  | succ N ih =>
    intro x
    have hderiv : ∀ y, HasDerivAt (fun y => R (N+1) y - RHS (N+1) y) 0 y := by
      intro y
      have h := (hasDerivAt_R N y).sub (hasDerivAt_RHS N y)
      have he : (↑N+2:ℝ)*R N y - (↑N+2)*RHS N y = 0 := by rw [ih y]; ring
      rwa [he] at h
    have hconst : ∀ y, R (N+1) y - RHS (N+1) y = R (N+1) 0 - RHS (N+1) 0 := by
      intro y
      exact is_const_of_deriv_eq_zero (fun z => (hderiv z).differentiableAt)
        (fun z => (hderiv z).deriv) y 0
    have hintc : (∫ y in (0:ℝ)..1, (R (N+1) y - RHS (N+1) y)) = R (N+1) 0 - RHS (N+1) 0 := by
      rw [show (fun y => R (N+1) y - RHS (N+1) y)
            = (fun _ => R (N+1) 0 - RHS (N+1) 0) from funext hconst]
      simp
    have hint0 : (∫ y in (0:ℝ)..1, (R (N+1) y - RHS (N+1) y)) = 0 := by
      rw [intervalIntegral.integral_sub ((continuous_R (N+1)).intervalIntegrable _ _)
            ((continuous_RHS (N+1)).intervalIntegrable _ _), integral_RHS]
      simp [J]
    have hc0 : R (N+1) 0 - RHS (N+1) 0 = 0 := by rw [← hintc, hint0]
    have hx := hconst x
    rw [hc0] at hx
    linarith [hx]

/-- The convolution identity at `x = 0`. -/
lemma conv_eq (N : ℕ) :
    (∑ m ∈ Finset.range (N+1), (bernoulli m : ℝ) * (bernoulli (N-m) : ℝ))
      = ∑ k ∈ Finset.range (N+1),
          (Nat.choose (N+1) k : ℝ) * J (N-k) * (bernoulli k : ℝ) := by
  have h := basis N 0
  rw [R, RHS] at h
  simp only [bernoulliFun_eval_zero] at h
  exact h

/-- Rational value of `J`. -/
noncomputable def Jq (n : ℕ) : ℚ :=
  if n = 0 then 1 else if n = 1 then 0 else 2 * bernoulli n / (n + 2)

lemma Jq_cast (n : ℕ) : ((Jq n : ℚ) : ℝ) = J n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [Jq, J_zero]
    · simp [Jq, J_one]
  · rw [J_val n hn, Jq, if_neg (by omega), if_neg (by omega)]
    push_cast
    ring

/-- The convolution identity, descended to `ℚ` with `Jq`. -/
lemma conv_q (N : ℕ) :
    (∑ m ∈ Finset.range (N+1), bernoulli m * bernoulli (N-m))
      = ∑ k ∈ Finset.range (N+1), ((N+1).choose k : ℚ) * Jq (N-k) * bernoulli k := by
  have h := conv_eq N
  simp_rw [← Jq_cast] at h
  exact_mod_cast h

end Carl

namespace BPI

open Nat Finset

variable {p : ℕ} [Fact p.Prime]

lemma pn_pow (q : ℚ) (k : ℕ) : padicNorm p (q^k) = (padicNorm p q)^k := by
  induction k with
  | zero => simp [padicNorm.one]
  | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]

/-- Bridge: a sum over `range p` of a function of casts equals the sum over all of `ZMod p`. -/
theorem sum_range_eq_univ {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  have : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  apply Finset.sum_nbij' (fun i => ((i : ℕ) : ZMod p)) ZMod.val
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_natCast_of_lt ha
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro a _; rfl

lemma psum_dvd {m : ℕ} (hm : m < p - 1) :
    (p:ℤ) ∣ ∑ k ∈ Finset.range p, (k:ℤ)^m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [show (∑ k ∈ Finset.range p, ((k:ZMod p))^m) = ∑ x : ZMod p, x^m from
    sum_range_eq_univ (fun x => x^m)]
  rw [FiniteField.sum_pow_lt_card_sub_one]
  rw [ZMod.card p]; omega

/-- **Bernoulli p-integrality** for indices below `p-1`. -/
lemma bern_pInt : ∀ m, m < p - 1 → padicNorm p (bernoulli m) ≤ 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmp
    have hpp : p.Prime := Fact.out
    have hp1 : (1:ℚ) < p := by exact_mod_cast hpp.one_lt
    have hp0 : (0:ℚ) < p := by linarith
    have hpinv : (0:ℚ) < (p:ℚ)⁻¹ := by positivity
    have hpinv1 : (p:ℚ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; linarith
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; rw [bernoulli_zero]; simp [padicNorm.one]
    · -- m ≥ 1
      have hfaul := sum_range_pow p m
      rw [Finset.sum_range_succ] at hfaul
      have hTm : bernoulli m * ((m+1).choose m : ℚ) * (p:ℚ)^(m+1-m) / (m+1) = bernoulli m * p := by
        rw [Nat.choose_succ_self_right, show m+1-m = 1 from by omega, pow_one]
        push_cast
        have hm1 : ((m:ℚ)+1) ≠ 0 := by positivity
        field_simp
      rw [hTm] at hfaul
      have heq : bernoulli m * (p:ℚ)
          = (∑ k ∈ Finset.range p, (k:ℚ)^m)
            - ∑ i ∈ Finset.range m, bernoulli i * ((m+1).choose i:ℚ) * (p:ℚ)^(m+1-i)/(m+1) := by
        rw [hfaul]; ring
      -- bound on the power sum
      have hLHS : padicNorm p (∑ k ∈ Finset.range p, (k:ℚ)^m) ≤ (p:ℚ)⁻¹ := by
        have hcast : (∑ k ∈ Finset.range p, (k:ℚ)^m)
            = (((∑ k ∈ Finset.range p, (k:ℤ)^m : ℤ)) : ℚ) := by push_cast; rfl
        rw [hcast]
        have hdvd : (((p^1:ℕ)):ℤ) ∣ ∑ k ∈ Finset.range p, (k:ℤ)^m := by
          simpa using psum_dvd (p := p) hmp
        have hnorm := (padicNorm.dvd_iff_norm_le (p := p) (n := 1)
          (z := ∑ k ∈ Finset.range p, (k:ℤ)^m)).1 hdvd
        simpa using hnorm
      -- bound on the lower sum
      have hSum : padicNorm p
          (∑ i ∈ Finset.range m, bernoulli i * ((m+1).choose i:ℚ) * (p:ℚ)^(m+1-i)/(m+1))
          ≤ (p:ℚ)⁻¹ := by
        apply padicNorm.sum_le'
        · intro i hi
          rw [Finset.mem_range] at hi
          -- padicNorm of T_i
          have hbi : padicNorm p (bernoulli i) ≤ 1 := ih i hi (by omega)
          have hci : padicNorm p ((m+1).choose i : ℚ) ≤ 1 := by
            have : padicNorm p (((m+1).choose i : ℤ) : ℚ) ≤ 1 := padicNorm.of_int _
            simpa using this
          have hm1ne : ¬ p ∣ (m+1) := by
            intro h; have := Nat.le_of_dvd (by omega) h; omega
          have hden : padicNorm p ((m:ℚ)+1) = 1 := by
            rw [show ((m:ℚ)+1) = ((m+1 : ℕ) : ℚ) from by push_cast; ring]
            exact (padicNorm.nat_eq_one_iff (p := p) (m+1)).2 hm1ne
          have hpk : padicNorm p ((p:ℚ)^(m+1-i)) = ((p:ℚ)⁻¹)^(m+1-i) := by
            rw [pn_pow, padicNorm.padicNorm_p_of_prime]
          rw [padicNorm.div, padicNorm.mul, padicNorm.mul, hpk, hden, div_one]
          have hpk2 : ((p:ℚ)⁻¹)^(m+1-i) ≤ (p:ℚ)⁻¹ := by
            calc ((p:ℚ)⁻¹)^(m+1-i) ≤ ((p:ℚ)⁻¹)^1 := by
                    apply pow_le_pow_of_le_one (le_of_lt hpinv) hpinv1 (by omega)
              _ = (p:ℚ)⁻¹ := pow_one _
          calc padicNorm p (bernoulli i) * padicNorm p (↑((m + 1).choose i))
                  * ((p:ℚ)⁻¹)^(m+1-i)
                ≤ 1 * 1 * (p:ℚ)⁻¹ := by
                  apply mul_le_mul (mul_le_mul hbi hci (padicNorm.nonneg _) (by norm_num)) hpk2
                    (by positivity) (by norm_num)
            _ = (p:ℚ)⁻¹ := by ring
        · exact le_of_lt hpinv
      -- combine
      have hcomb : padicNorm p (bernoulli m * (p:ℚ)) ≤ (p:ℚ)⁻¹ := by
        rw [heq]
        exact le_trans padicNorm.sub (max_le hLHS hSum)
      rw [padicNorm.mul, padicNorm.padicNorm_p_of_prime] at hcomb
      -- padicNorm (bernoulli m) * p⁻¹ ≤ p⁻¹  ⟹  padicNorm (bernoulli m) ≤ 1
      nlinarith [padicNorm.nonneg (p := p) (bernoulli m), hcomb, hpinv]

/-- A `p`-integral rational has denominator coprime to `p`. -/
lemma den_ne_zero {q : ℚ} (h : padicNorm p q ≤ 1) : ((q.den : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have hpp : p.Prime := Fact.out
  have hpn : ¬ (p:ℤ) ∣ q.num := by
    intro hpn
    have h1 : p ∣ q.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hpn
      rwa [Int.natAbs_natCast] at this
    have hg : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hd
    rw [q.reduced] at hg
    have := Nat.le_of_dvd one_pos hg
    have := hpp.two_le
    omega
  have hnum : padicNorm p ((q.num : ℤ) : ℚ) = 1 := (padicNorm.int_eq_one_iff q.num).2 hpn
  have hden_lt : padicNorm p ((q.den : ℕ) : ℚ) < 1 := (padicNorm.nat_lt_one_iff q.den).2 hd
  have hden_pos : 0 < padicNorm p ((q.den : ℕ) : ℚ) := by
    rcases (padicNorm.nonneg ((q.den : ℕ) : ℚ)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have := padicNorm.zero_of_padicNorm_eq_zero heq.symm
      have hdz : q.den ≠ 0 := q.den_nz
      simp only [Nat.cast_eq_zero] at this
      exact hdz this
  have hqeq : q = ((q.num : ℤ) : ℚ) / ((q.den : ℕ) : ℚ) := by
    exact (Rat.num_div_den q).symm
  rw [hqeq, padicNorm.div, hnum] at h
  rw [div_le_one hden_pos] at h
  linarith

/-- If `padicNorm p q < 1` then `q` casts to `0` in `ZMod p`. -/
lemma cast_eq_zero_of_norm_lt_one {q : ℚ} (h : padicNorm p q < 1) : (q : ZMod p) = 0 := by
  have hpp : p.Prime := Fact.out
  have hle : padicNorm p q ≤ 1 := le_of_lt h
  have hden : ((q.den : ℕ) : ZMod p) ≠ 0 := den_ne_zero hle
  -- q = num/den, cast: num cast / den cast; p | num
  have hpnum : (p:ℤ) ∣ q.num := by
    by_contra hpn
    have hnum1 : padicNorm p ((q.num : ℤ):ℚ) = 1 := (padicNorm.int_eq_one_iff q.num).2 hpn
    have hden_le : padicNorm p ((q.den:ℕ):ℚ) ≤ 1 := padicNorm.of_nat q.den
    have hden_pos : 0 < padicNorm p ((q.den : ℕ) : ℚ) := by
      rcases (padicNorm.nonneg ((q.den : ℕ) : ℚ)).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have := padicNorm.zero_of_padicNorm_eq_zero heq.symm
        simp only [Nat.cast_eq_zero] at this
        exact q.den_nz this
    have hqeq : q = ((q.num : ℤ) : ℚ) / ((q.den : ℕ) : ℚ) := by
      exact (Rat.num_div_den q).symm
    rw [hqeq, padicNorm.div, hnum1] at h
    rw [div_lt_one hden_pos] at h
    linarith
  -- now cast
  have hqcast : (q : ZMod p) = ((q.num : ZMod p)) * ((q.den : ZMod p))⁻¹ := by
    rw [Rat.cast_def]; rfl
  rw [hqcast]
  have : (q.num : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpnum
  rw [this, zero_mul]

/-- Binomial congruence: `C(p-2,k) ≡ (-1)^k (k+1) mod p` for `k ≤ p-2`. -/
lemma bchoose2 : ∀ k, k ≤ p - 2 → ((Nat.choose (p-2) k : ZMod p)) = (-1)^k * ((k:ZMod p)+1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hp := (Fact.out : p.Prime)
    have hk' : k ≤ p - 2 := by omega
    have hstep := Nat.choose_succ_right_eq (p-2) k
    have e1 : (((p-2)-k : ℕ) : ZMod p) = -((k:ZMod p)+2) := by
      have hkp : k + 2 ≤ p := by omega
      have he : (p-2) - k = p - (k+2) := by omega
      rw [he, Nat.cast_sub hkp]
      push_cast
      rw [ZMod.natCast_self]
      ring
    have hkunit : ((k:ZMod p)+1) ≠ 0 := by
      have hh : ((k+1:ℕ):ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
      push_cast at hh; exact hh
    have hc : ((Nat.choose (p-2) (k+1):ZMod p)) * ((k:ZMod p)+1)
        = ((Nat.choose (p-2) k:ZMod p)) * (((p-2)-k:ℕ):ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) hstep
      push_cast at this
      convert this using 2
    rw [e1, ih hk'] at hc
    have hc2 : ((Nat.choose (p-2) (k+1):ZMod p)) * ((k:ZMod p)+1)
        = ((-1)^(k+1) * ((k:ZMod p)+2)) * ((k:ZMod p)+1) := by
      rw [hc]; ring
    have hfin := mul_right_cancel₀ hkunit hc2
    rw [hfin]; push_cast; ring

/-- `Jq n` is `p`-integral for `n ≤ p-3`. -/
lemma Jq_pInt {n : ℕ} (hn : n ≤ p - 3) : padicNorm p (Carl.Jq n) ≤ 1 := by
  have hpp : p.Prime := Fact.out
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · rw [Carl.Jq]; simp [padicNorm.one]
    · rw [Carl.Jq]; simp [padicNorm.zero]
  · rw [Carl.Jq, if_neg (by omega), if_neg (by omega)]
    rw [div_eq_mul_inv, padicNorm.mul, padicNorm.mul]
    have h2norm : padicNorm p (2:ℚ) ≤ 1 := by
      have : padicNorm p ((2:ℕ):ℚ) ≤ 1 := padicNorm.of_nat 2
      simpa using this
    have hbn : padicNorm p (bernoulli n) ≤ 1 := bern_pInt n (by omega)
    have hden : padicNorm p (((n:ℚ)+2)⁻¹) ≤ 1 := by
      have hne : ¬ p ∣ (n+2) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
      have h1 : padicNorm p (((n+2:ℕ):ℚ)) = 1 := (padicNorm.nat_eq_one_iff (n+2)).2 hne
      have : padicNorm p (((n:ℚ)+2)) = 1 := by
        rw [show ((n:ℚ)+2) = ((n+2:ℕ):ℚ) from by push_cast; ring]; exact h1
      rw [show (((n:ℚ)+2)⁻¹) = 1 / ((n:ℚ)+2) from by rw [one_div], padicNorm.div, this]
      simp [padicNorm.one]
    calc padicNorm p 2 * padicNorm p (bernoulli n) * padicNorm p (((n:ℚ)+2)⁻¹)
          ≤ 1 * 1 * 1 := by
            apply mul_le_mul (mul_le_mul h2norm hbn (padicNorm.nonneg _) (by norm_num)) hden
              (padicNorm.nonneg _) (by norm_num)
      _ = 1 := by ring

variable (p) in
/-- **The C-gate**: the Bernoulli self-convolution `Σ_{m=0}^{p-3} B_m B_{p-3-m}` is `≡ 0 mod p`. -/
lemma C_norm_lt (hp7 : 7 ≤ p) :
    padicNorm p (∑ m ∈ Finset.range (p-2), bernoulli m * bernoulli (p-3-m)) < 1 := by
  have hpp : p.Prime := Fact.out
  set N := p - 3 with hNdef
  have hN1 : N + 1 = p - 2 := by omega
  have hpinv : (0:ℚ) < (p:ℚ)⁻¹ := by positivity
  have hpinv1 : (p:ℚ)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]; exact_mod_cast hpp.one_lt
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  have hNe : Even N := by rw [hNdef]; exact Nat.Odd.sub_odd hpodd (by decide)
  rw [← hN1]
  -- abbreviation
  set Cv := ∑ m ∈ Finset.range (N+1), bernoulli m * bernoulli (N-m) with hCv
  -- conv_q
  have hconv : Cv = ∑ k ∈ Finset.range (N+1),
      ((N+1).choose k : ℚ) * Carl.Jq (N-k) * bernoulli k := Carl.conv_q N
  -- 3 * Cv = Σ term_k
  have h3C : 3 * Cv = ∑ k ∈ Finset.range (N+1),
      (((N+1).choose k : ℚ) * Carl.Jq (N-k) * bernoulli k + 2 * (bernoulli k * bernoulli (N-k))) := by
    rw [Finset.sum_add_distrib, ← hconv, ← Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (N+1), bernoulli k * bernoulli (N-k)) = Cv from by rw [hCv]]
    ring
  -- per term bound
  have hterm : ∀ k ∈ Finset.range (N+1),
      padicNorm p (((N+1).choose k : ℚ) * Carl.Jq (N-k) * bernoulli k
        + 2 * (bernoulli k * bernoulli (N-k))) ≤ (p:ℚ)⁻¹ := by
    intro k hk
    rw [Finset.mem_range] at hk
    -- factor: term = B_k * bracket
    have hfac : ((N+1).choose k : ℚ) * Carl.Jq (N-k) * bernoulli k
        + 2 * (bernoulli k * bernoulli (N-k))
        = bernoulli k * (((N+1).choose k : ℚ) * Carl.Jq (N-k) + 2 * bernoulli (N-k)) := by ring
    rw [hfac, padicNorm.mul]
    -- p-integrality of B_k and bracket
    have hBk : padicNorm p (bernoulli k) ≤ 1 := bern_pInt k (by omega)
    have hbracket_pInt : padicNorm p (((N+1).choose k : ℚ) * Carl.Jq (N-k) + 2 * bernoulli (N-k)) ≤ 1 := by
      refine le_trans padicNorm.nonarchimedean (max_le ?_ ?_)
      · rw [padicNorm.mul]
        have hc : padicNorm p ((N+1).choose k : ℚ) ≤ 1 := by
          have : padicNorm p (((N+1).choose k : ℤ):ℚ) ≤ 1 := padicNorm.of_int _
          simpa using this
        have hj : padicNorm p (Carl.Jq (N-k)) ≤ 1 := Jq_pInt (by omega)
        calc padicNorm p ((N+1).choose k : ℚ) * padicNorm p (Carl.Jq (N-k)) ≤ 1 * 1 :=
              mul_le_mul hc hj (padicNorm.nonneg _) (by norm_num)
          _ = 1 := by ring
      · rw [padicNorm.mul]
        have h2 : padicNorm p (2:ℚ) ≤ 1 := by
          have : padicNorm p ((2:ℕ):ℚ) ≤ 1 := padicNorm.of_nat 2; simpa using this
        have hb : padicNorm p (bernoulli (N-k)) ≤ 1 := bern_pInt (N-k) (by omega)
        calc padicNorm p 2 * padicNorm p (bernoulli (N-k)) ≤ 1 * 1 :=
              mul_le_mul h2 hb (padicNorm.nonneg _) (by norm_num)
          _ = 1 := by ring
    -- dichotomy: either B_k ≡ 0 or bracket ≡ 0
    rcases Nat.even_or_odd k with hke | hko
    · -- k even: bracket ≡ 0
      have hbr0 : padicNorm p (((N+1).choose k : ℚ) * Carl.Jq (N-k) + 2 * bernoulli (N-k)) ≤ (p:ℚ)⁻¹ := by
        rcases Nat.eq_zero_or_pos (N-k) with hnk0 | hnkpos
        · -- N - k = 0, so k = N
          have hkN : k = N := by omega
          rw [hnk0, hkN]
          have hjq0 : Carl.Jq 0 = 1 := by rw [Carl.Jq]; simp
          rw [hjq0, Nat.choose_succ_self_right, bernoulli_zero]
          rw [show ((N+1:ℕ):ℚ) * 1 + 2 * 1 = (p:ℚ) from by
            have hp3 : p = N + 3 := by omega
            rw [hp3]; push_cast; ring]
          rw [padicNorm.padicNorm_p_of_prime]
        · -- N - k ≥ 2 (even): bracket = (2 B_{N-k}/(N-k+2)) * (C(N+1,k) + (N-k+2))
          have hnk2 : 2 ≤ N - k := by
            have hev : Even (N-k) := (Nat.even_sub' (by omega)).mpr
              (iff_of_false (Nat.not_odd_iff_even.mpr hNe) (Nat.not_odd_iff_even.mpr hke))
            obtain ⟨r, hr⟩ := hev; omega
          rw [Carl.Jq, if_neg (by omega), if_neg (by omega)]
          set d := N - k with hd
          have hdne : ((d:ℚ)+2) ≠ 0 := by positivity
          have hsplit : ((N+1).choose k : ℚ) * (2 * bernoulli d / (↑d + 2)) + 2 * bernoulli d
              = (2 * bernoulli d / (↑d + 2)) * (((N+1).choose k : ℚ) + (↑d + 2)) := by
            field_simp
          rw [hsplit, padicNorm.mul]
          -- first factor ≤ 1, second ≤ p⁻¹
          have hf1 : padicNorm p (2 * bernoulli d / (↑d + 2)) ≤ 1 := by
            rw [div_eq_mul_inv, padicNorm.mul, padicNorm.mul]
            have h2 : padicNorm p (2:ℚ) ≤ 1 := by
              have : padicNorm p ((2:ℕ):ℚ) ≤ 1 := padicNorm.of_nat 2; simpa using this
            have hb : padicNorm p (bernoulli d) ≤ 1 := bern_pInt d (by omega)
            have hde : padicNorm p ((↑d + 2:ℚ)⁻¹) ≤ 1 := by
              have hne : ¬ p ∣ (d+2) := by intro h; have := Nat.le_of_dvd (by omega) h; omega
              have h1 : padicNorm p (((d+2:ℕ):ℚ)) = 1 := (padicNorm.nat_eq_one_iff (d+2)).2 hne
              have : padicNorm p ((↑d+2:ℚ)) = 1 := by
                rw [show ((d:ℚ)+2) = ((d+2:ℕ):ℚ) from by push_cast; ring]; exact h1
              rw [show ((↑d+2:ℚ)⁻¹) = 1/(↑d+2) from by rw [one_div], padicNorm.div, this]
              simp [padicNorm.one]
            calc padicNorm p 2 * padicNorm p (bernoulli d) * padicNorm p ((↑d+2:ℚ)⁻¹)
                  ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h2 hb (padicNorm.nonneg _) (by norm_num)) hde
                    (padicNorm.nonneg _) (by norm_num)
              _ = 1 := by ring
          have hf2 : padicNorm p (((N+1).choose k : ℚ) + (↑d + 2)) ≤ (p:ℚ)⁻¹ := by
            -- C(N+1,k) + (d+2) ≡ 0 mod p (integer)
            have hzero : (((N+1).choose k + (d+2) : ℕ) : ZMod p) = 0 := by
              push_cast
              rw [show ((N+1).choose k : ZMod p) = (-1)^k * ((k:ZMod p)+1) from by
                rw [hN1]; exact bchoose2 k (by omega)]
              have hkev : (-1:ZMod p)^k = 1 := hke.neg_one_pow
              rw [hkev, one_mul]
              -- (k+1) + (d+2) where d = N-k = p-3-k; d+2 = p-1-k; sum = k+1+p-1-k = p ≡ 0
              have hdcast : ((d:ZMod p)) = -(k:ZMod p) - 3 := by
                have : d = p - 3 - k := by rw [hd]
                have hkle : k + 3 ≤ p := by omega
                rw [this, show p - 3 - k = p - (k+3) from by omega, Nat.cast_sub hkle]
                push_cast; rw [ZMod.natCast_self]; ring
              rw [hdcast]; ring
            have hdvdn : p ∣ ((N+1).choose k + (d+2)) := (ZMod.natCast_eq_zero_iff _ _).mp hzero
            have hnorm : padicNorm p ((((N+1).choose k + (d+2):ℕ)):ℚ) ≤ (p:ℚ)⁻¹ := by
              have hdvd : (((p^1:ℕ)):ℤ) ∣ (((N+1).choose k + (d+2) : ℕ):ℤ) := by
                simpa using (Int.natCast_dvd_natCast.mpr hdvdn)
              have h0 := (padicNorm.dvd_iff_norm_le (p := p) (n := 1)
                (z := (((N+1).choose k + (d+2) : ℕ):ℤ))).1 hdvd
              simpa using h0
            calc padicNorm p (((N+1).choose k : ℚ) + (↑d + 2))
                = padicNorm p ((((N+1).choose k + (d+2):ℕ)):ℚ) := by push_cast; ring_nf
              _ ≤ (p:ℚ)⁻¹ := hnorm
          calc padicNorm p (2 * bernoulli d / (↑d + 2)) * padicNorm p (((N+1).choose k : ℚ) + (↑d + 2))
                ≤ 1 * (p:ℚ)⁻¹ := mul_le_mul hf1 hf2 (padicNorm.nonneg _) (by norm_num)
            _ = (p:ℚ)⁻¹ := by ring
      calc padicNorm p (bernoulli k) * padicNorm p (((N+1).choose k : ℚ) * Carl.Jq (N-k) + 2 * bernoulli (N-k))
            ≤ 1 * (p:ℚ)⁻¹ := mul_le_mul hBk hbr0 (padicNorm.nonneg _) (by norm_num)
        _ = (p:ℚ)⁻¹ := by ring
    · -- k odd
      rcases eq_or_ne k 1 with hk1 | hk1
      · -- k = 1: bracket = 0
        subst hk1
        have hNk : N - 1 = p - 4 := by omega
        have hoddNk : Odd (N - 1) := by
          rw [hNk]; exact (Nat.odd_sub (by omega)).mpr (iff_of_true hpodd (by decide))
        have hbn1 : bernoulli (N-1) = 0 := bernoulli_eq_zero_of_odd hoddNk (by omega)
        have hjq : Carl.Jq (N-1) = 0 := by
          rw [Carl.Jq, if_neg (by omega), if_neg (by omega), hbn1]; simp
        have hbr0 : padicNorm p (((N+1).choose 1 : ℚ) * Carl.Jq (N-1) + 2 * bernoulli (N-1)) ≤ (p:ℚ)⁻¹ := by
          rw [hjq, hbn1, mul_zero, mul_zero, add_zero, padicNorm.zero]; positivity
        calc padicNorm p (bernoulli 1) * padicNorm p (((N+1).choose 1 : ℚ) * Carl.Jq (N-1) + 2 * bernoulli (N-1))
              ≤ 1 * (p:ℚ)⁻¹ := mul_le_mul hBk hbr0 (padicNorm.nonneg _) (by norm_num)
          _ = (p:ℚ)⁻¹ := by ring
      · -- k odd, k ≥ 3: B_k = 0
        have hk3 : 1 < k := by obtain ⟨r, hr⟩ := hko; omega
        have hbk0 : bernoulli k = 0 := bernoulli_eq_zero_of_odd hko hk3
        rw [hbk0]
        simp only [padicNorm.zero, zero_mul]
        positivity
  -- combine
  have hsum : padicNorm p (3 * Cv) ≤ (p:ℚ)⁻¹ := by
    rw [h3C]; exact padicNorm.sum_le' hterm (le_of_lt hpinv)
  have h3 : padicNorm p (3:ℚ) = 1 := by
    have : padicNorm p ((3:ℕ):ℚ) = 1 := (padicNorm.nat_eq_one_iff 3).2 (by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  rw [padicNorm.mul, h3, one_mul] at hsum
  calc padicNorm p Cv ≤ (p:ℚ)⁻¹ := hsum
    _ < 1 := hpinv1

-- ===================== Faulhaber connection =====================

/-- Cast of a finite sum of `p`-integral rationals splits termwise. -/
lemma cast_sum_pInt {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∀ i ∈ s, padicNorm p (f i) ≤ 1) →
    (((∑ i ∈ s, f i : ℚ)) : ZMod p) = ∑ i ∈ s, ((f i : ℚ) : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa : padicNorm p (f a) ≤ 1 := h a (Finset.mem_insert_self a s)
    have hrest : ∀ i ∈ s, padicNorm p (f i) ≤ 1 :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hsum : padicNorm p (∑ i ∈ s, f i) ≤ 1 := padicNorm.sum_le' hrest (by norm_num)
    rw [Rat.cast_add_of_ne_zero (den_ne_zero hfa) (den_ne_zero hsum), ih hrest]

/-- Cast of a product of two `p`-integral rationals. -/
lemma cast_mul_pInt {a b : ℚ} (ha : padicNorm p a ≤ 1) (hb : padicNorm p b ≤ 1) :
    ((a * b : ℚ) : ZMod p) = (a : ZMod p) * (b : ZMod p) :=
  Rat.cast_mul_of_ne_zero (den_ne_zero ha) (den_ne_zero hb)

/-- Binomial congruence `C(p-1,j) ≡ (-1)^j mod p`. -/
lemma bchoose1 : ∀ j, j ≤ p - 1 → ((Nat.choose (p-1) j : ZMod p)) = (-1)^j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hp := (Fact.out : p.Prime)
    have hj' : j ≤ p - 1 := by omega
    have hstep := Nat.choose_succ_right_eq (p-1) j
    have e1 : (((p-1)-j : ℕ) : ZMod p) = -((j:ZMod p)+1) := by
      have hkp : j + 1 ≤ p := by omega
      have he : (p-1) - j = p - (j+1) := by omega
      rw [he, Nat.cast_sub hkp]
      push_cast
      rw [ZMod.natCast_self]
      ring
    have hjunit : ((j:ZMod p)+1) ≠ 0 := by
      have hh : ((j+1:ℕ):ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
      push_cast at hh; exact hh
    have hc : ((Nat.choose (p-1) (j+1):ZMod p)) * ((j:ZMod p)+1)
        = ((Nat.choose (p-1) j:ZMod p)) * (((p-1)-j:ℕ):ZMod p) := by
      have := congrArg (Nat.cast (R := ZMod p)) hstep
      push_cast at this
      convert this using 2
    rw [e1, ih hj'] at hc
    have hc2 : ((Nat.choose (p-1) (j+1):ZMod p)) * ((j:ZMod p)+1)
        = ((-1)^(j+1)) * ((j:ZMod p)+1) := by
      rw [hc]; ring
    have hfin := mul_right_cancel₀ hjunit hc2
    rw [hfin]

/-- Full power sum over `ZMod p`: `∑_{x} x^m = -1` if `(p-1)∣m`, else `0` (for `m>0`). -/
lemma powsum (m : ℕ) (hm : 0 < m) :
    (∑ x : ZMod p, x ^ m) = if (p-1) ∣ m then (-1 : ZMod p) else 0 := by
  classical
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ (x:ZMod p), Units.val_injective⟩
  have hmap : Finset.univ.map emb = Finset.univ \ {(0:ZMod p)} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, emb] using isUnit_iff_ne_zero
  have step : (∑ x : ZMod p, x ^ m) = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ m) := by
    rw [show (∑ x : ZMod p, x ^ m) = ∑ x ∈ Finset.univ \ {(0:ZMod p)}, x ^ m from by
        rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
            Finset.sum_singleton, zero_pow (by omega), add_zero]]
    rw [← hmap, Finset.sum_map]; rfl
  rw [step]
  rw [FiniteField.sum_pow_units (ZMod p) m]
  simp only [ZMod.card]

/-- Per-`k` Faulhaber congruence:
`∑_{i<k} i^{p-2} ≡ ∑_{j<p-1} (-1)^{j+1} B_j k^{p-1-j}  (mod p)`. -/
lemma faulhaber_k (k : ℕ) :
    (∑ i ∈ Finset.range k, ((i:ZMod p))^(p-2))
      = ∑ j ∈ Finset.range (p-1),
          ((-1)^(j+1) * (bernoulli j : ZMod p)) * ((k:ZMod p))^(p-1-j) := by
  have hp := (Fact.out : p.Prime)
  have hp2le : 2 ≤ p := hp.two_le
  have hpe : p - 1 = p - 2 + 1 := by omega
  have hne : ((p-2:ℕ):ℚ)+1 ≠ 0 := by positivity
  have hnatcast : ((p-2:ℕ):ℚ)+1 = ((p-1:ℕ):ℚ) := by rw [hpe]; push_cast; ring
  -- p-integrality facts
  have hxpint : ∀ x ∈ Finset.range k, padicNorm p ((x:ℚ)^(p-2)) ≤ 1 := by
    intro x _; rw [pn_pow]; exact pow_le_one₀ (padicNorm.nonneg _) (padicNorm.of_nat x)
  -- cleared-denominator Faulhaber identity (no inverses!)
  have hclear : (((p-2:ℕ):ℚ)+1) * (∑ x ∈ Finset.range k, (x:ℚ)^(p-2))
      = ∑ i ∈ Finset.range (p-2+1),
          bernoulli i * (Nat.choose (p-2+1) i : ℚ) * (k:ℚ)^(p-2+1-i) := by
    rw [sum_range_pow k (p-2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
  -- cast LHS of hclear
  have hLval : (((((p-2:ℕ):ℚ)+1) * (∑ x ∈ Finset.range k, (x:ℚ)^(p-2)) : ℚ) : ZMod p)
      = (-1) * (∑ i ∈ Finset.range k, ((i:ZMod p))^(p-2)) := by
    rw [cast_mul_pInt (by rw [hnatcast]; exact padicNorm.of_nat _)
        (padicNorm.sum_le' hxpint (by norm_num))]
    congr 1
    · rw [hnatcast, show ((((p-1:ℕ):ℚ)) : ZMod p) = ((p-1:ℕ):ZMod p) from by push_cast; rfl]
      rw [Nat.cast_sub (by omega)]; push_cast; rw [ZMod.natCast_self]; ring
    · rw [cast_sum_pInt _ _ hxpint]
      refine Finset.sum_congr rfl (fun x _ => ?_); push_cast; rfl
  -- cast RHS of hclear
  have hRval : ((∑ i ∈ Finset.range (p-2+1),
        bernoulli i * (Nat.choose (p-2+1) i : ℚ) * (k:ℚ)^(p-2+1-i) : ℚ) : ZMod p)
      = ∑ i ∈ Finset.range (p-2+1),
          (bernoulli i : ZMod p) * (-1)^i * ((k:ZMod p))^(p-2+1-i) := by
    rw [cast_sum_pInt _ _ ?_]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have hbi : padicNorm p (bernoulli i) ≤ 1 := bern_pInt i (by omega)
      have hkn : padicNorm p ((k:ℚ)^(p-2+1-i)) ≤ 1 := by
        rw [show ((k:ℚ)^(p-2+1-i)) = (((k^(p-2+1-i):ℕ)):ℚ) from by push_cast; ring]
        exact padicNorm.of_nat _
      have hbc : padicNorm p (bernoulli i * (Nat.choose (p-2+1) i : ℚ)) ≤ 1 := by
        rw [padicNorm.mul]
        calc padicNorm p (bernoulli i) * padicNorm p ((Nat.choose (p-2+1) i:ℚ))
            ≤ 1 * 1 := mul_le_mul hbi (padicNorm.of_nat _) (padicNorm.nonneg _) (by norm_num)
          _ = 1 := by ring
      rw [cast_mul_pInt hbc hkn]
      rw [cast_mul_pInt hbi (padicNorm.of_nat _)]
      rw [show ((((Nat.choose (p-2+1) i):ℚ)) : ZMod p) = ((Nat.choose (p-2+1) i : ℕ) : ZMod p)
            from by push_cast; rfl]
      rw [show ((Nat.choose (p-2+1) i : ℕ) : ZMod p) = (-1)^i from by
            rw [show p-2+1 = p-1 from hpe.symm]; exact bchoose1 i (by omega)]
      rw [show (((k:ℚ)^(p-2+1-i) : ℚ) : ZMod p) = ((k:ZMod p))^(p-2+1-i) from by
            rw [show ((k:ℚ)^(p-2+1-i)) = (((k^(p-2+1-i):ℕ)):ℚ) from by push_cast; ring]
            push_cast; rfl]
    · intro i hi
      rw [Finset.mem_range] at hi
      have hbi : padicNorm p (bernoulli i) ≤ 1 := bern_pInt i (by omega)
      rw [padicNorm.mul, padicNorm.mul]
      have hkn : padicNorm p ((k:ℚ)^(p-2+1-i)) ≤ 1 := by
        rw [show ((k:ℚ)^(p-2+1-i)) = (((k^(p-2+1-i):ℕ)):ℚ) from by push_cast; ring]
        exact padicNorm.of_nat _
      calc padicNorm p (bernoulli i) * padicNorm p ((Nat.choose (p-2+1) i:ℚ))
            * padicNorm p ((k:ℚ)^(p-2+1-i))
          ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hbi (padicNorm.of_nat _)
              (padicNorm.nonneg _) (by norm_num)) hkn (padicNorm.nonneg _) (by norm_num)
        _ = 1 := by ring
  -- combine
  have hc := congrArg (fun q : ℚ => (q : ZMod p)) hclear
  simp only [hLval, hRval] at hc
  -- hc : (-1) * Hbar = ∑ B_i (-1)^i k^...
  have hfin : (∑ i ∈ Finset.range k, ((i:ZMod p))^(p-2))
      = (-1) * (∑ i ∈ Finset.range (p-2+1),
          (bernoulli i : ZMod p) * (-1)^i * ((k:ZMod p))^(p-2+1-i)) := by
    rw [← hc]; ring
  rw [hpe, hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Divisibility selector for the exponent appearing in the double sum. -/
lemma dvd_exp_iff (hp7 : 7 ≤ p) (j l : ℕ) (hj : j ≤ p - 3) (hl : l ≤ p - 3) :
    (p - 1) ∣ ((p-1-j)+(p-1-l)+(p-3)) ↔ j + l = p - 3 := by
  constructor
  · intro hd
    obtain ⟨q, hq⟩ := hd
    have hval : (p-1-j)+(p-1-l)+(p-3) = 3*p-5-j-l := by omega
    rw [hval] at hq
    have hge : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with h | h
      · exfalso; interval_cases q
        · simp at hq; omega
        · rw [mul_one] at hq; omega
      · exact h
    have hle : q ≤ 2 := by
      by_contra h; push_neg at h
      have hq3 : 3 ≤ q := by omega
      have h3 : (p-1)*3 ≤ (p-1)*q := by gcongr
      rw [← hq] at h3; omega
    have : q = 2 := le_antisymm hle hge
    rw [this] at hq; omega
  · intro h
    rw [show (p-1-j)+(p-1-l)+(p-3) = 2*(p-1) from by omega]
    exact dvd_mul_left (p-1) 2

/-- The summand of the Bernoulli double sum. -/
def Fbody (j l : ℕ) : ZMod p :=
  ((-1:ZMod p)^(j+1)*(bernoulli j:ZMod p)) * ((-1:ZMod p)^(l+1)*(bernoulli l:ZMod p))
    * (if (p-1) ∣ ((p-1-j)+(p-1-l)+(p-3)) then (-1:ZMod p) else 0)

/-- Evaluation of the Bernoulli double sum to `-C` (the self-convolution). -/
lemma double_bern_eval (hp7 : 7 ≤ p) :
    ∑ j ∈ Finset.range (p-1), ∑ l ∈ Finset.range (p-1), Fbody (p := p) j l
      = - ∑ m ∈ Finset.range (p-2), (bernoulli m:ZMod p)*(bernoulli (p-3-m):ZMod p) := by
  have hp := (Fact.out : p.Prime)
  have hpe : p-1 = p-2+1 := by omega
  have hodd : Odd (p-2) := by
    have hop : Odd p := hp.odd_of_ne_two (by omega)
    rcases hop with ⟨t, ht⟩; exact ⟨t-1, by omega⟩
  have hep1 : Even (p-1) := by rcases hodd with ⟨t, ht⟩; exact ⟨t+1, by omega⟩
  have hb2 : (bernoulli (p-2):ZMod p) = 0 := by
    rw [show bernoulli (p-2) = 0 from bernoulli_eq_zero_of_odd hodd (by omega)]; simp
  have hFj2 : ∀ l, Fbody (p := p) (p-2) l = 0 := by intro l; simp only [Fbody, hb2]; ring
  have hFl2 : ∀ j, Fbody (p := p) j (p-2) = 0 := by intro j; simp only [Fbody, hb2]; ring
  -- restrict both sums to range (p-2)
  have eA : ∑ j ∈ Finset.range (p-1), ∑ l ∈ Finset.range (p-1), Fbody (p := p) j l
      = ∑ j ∈ Finset.range (p-2), ∑ l ∈ Finset.range (p-2), Fbody (p := p) j l := by
    rw [hpe, Finset.sum_range_succ,
        show (∑ l ∈ Finset.range (p-2+1), Fbody (p := p) (p-2) l) = 0 from
          Finset.sum_eq_zero (fun l _ => hFj2 l), add_zero]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_range_succ, hFl2 j, add_zero]
  rw [eA]
  -- diagonal extraction: inner sum collapses to a single term
  have inner : ∀ j ∈ Finset.range (p-2), ∑ l ∈ Finset.range (p-2), Fbody (p := p) j l
      = (bernoulli j:ZMod p)*(bernoulli (p-3-j):ZMod p) * (-1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_eq_single (p-3-j)]
    · simp only [Fbody]
      rw [if_pos ((dvd_exp_iff hp7 j (p-3-j) (by omega) (by omega)).mpr (by omega))]
      have hsign : ((-1:ZMod p)^(j+1)) * ((-1:ZMod p)^((p-3-j)+1)) = 1 := by
        rw [← pow_add, show (j+1)+((p-3-j)+1) = p-1 from by omega]
        exact Even.neg_one_pow hep1
      calc ((-1:ZMod p)^(j+1)*(bernoulli j:ZMod p))
              * ((-1:ZMod p)^((p-3-j)+1)*(bernoulli (p-3-j):ZMod p)) * (-1)
          = (((-1:ZMod p)^(j+1)) * ((-1:ZMod p)^((p-3-j)+1)))
              * ((bernoulli j:ZMod p)*(bernoulli (p-3-j):ZMod p)) * (-1) := by ring
        _ = (bernoulli j:ZMod p)*(bernoulli (p-3-j):ZMod p) * (-1) := by rw [hsign]; ring
    · intro l hl hne
      rw [Finset.mem_range] at hl
      simp only [Fbody]
      rw [if_neg (fun hd => hne (by
        have := (dvd_exp_iff hp7 j l (by omega) (by omega)).mp hd; omega))]
      ring
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  rw [Finset.sum_congr rfl inner, ← Finset.sum_mul]
  ring

/-- **The weighted square sum vanishes mod p** (this is `2·H(1,1,2)+H(2,2) ≡ -C ≡ 0`). -/
lemma weighted_sq_zero (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.range p,
        (∑ i ∈ Finset.range k, ((i:ZMod p))^(p-2))^2 * ((k:ZMod p))^(p-3) = 0 := by
  have hp := (Fact.out : p.Prime)
  -- Step 1: per-k expansion via Faulhaber
  have key : ∀ k, (∑ i ∈ Finset.range k, ((i:ZMod p))^(p-2))^2 * ((k:ZMod p))^(p-3)
      = ∑ j ∈ Finset.range (p-1), ∑ l ∈ Finset.range (p-1),
          (((-1:ZMod p)^(j+1)*(bernoulli j:ZMod p)) * ((-1:ZMod p)^(l+1)*(bernoulli l:ZMod p)))
            * ((k:ZMod p))^((p-1-j)+(p-1-l)+(p-3)) := by
    intro k
    rw [faulhaber_k k, pow_two, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro l _
    rw [show ((k:ZMod p))^((p-1-j)+(p-1-l)+(p-3))
          = ((k:ZMod p))^(p-1-j) * ((k:ZMod p))^(p-1-l) * ((k:ZMod p))^(p-3) from by
        rw [pow_add, pow_add]]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  -- Step 2: swap order to ∑_j ∑_l ∑_k
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  -- Step 3: evaluate the inner power sum over k
  have inner3 : ∀ j ∈ Finset.range (p-1), ∀ l ∈ Finset.range (p-1),
      ∑ k ∈ Finset.range p,
          (((-1:ZMod p)^(j+1)*(bernoulli j:ZMod p)) * ((-1:ZMod p)^(l+1)*(bernoulli l:ZMod p)))
            * ((k:ZMod p))^((p-1-j)+(p-1-l)+(p-3))
        = Fbody (p := p) j l := by
    intro j hj l hl
    rw [Finset.mem_range] at hj hl
    rw [← Finset.mul_sum, Fbody]
    congr 1
    rw [sum_range_eq_univ (fun x => x ^ ((p-1-j)+(p-1-l)+(p-3)))]
    exact powsum ((p-1-j)+(p-1-l)+(p-3)) (by omega)
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl => inner3 j hj l hl))]
  -- Step 4: apply the Bernoulli evaluation and the C-gate
  rw [double_bern_eval hp7]
  have hCzero : (∑ m ∈ Finset.range (p-2), (bernoulli m:ZMod p)*(bernoulli (p-3-m):ZMod p)) = 0 := by
    have hpint : ∀ m ∈ Finset.range (p-2), padicNorm p (bernoulli m * bernoulli (p-3-m)) ≤ 1 := by
      intro m hm; rw [Finset.mem_range] at hm; rw [padicNorm.mul]
      calc padicNorm p (bernoulli m) * padicNorm p (bernoulli (p-3-m))
          ≤ 1 * 1 := mul_le_mul (bern_pInt m (by omega)) (bern_pInt (p-3-m) (by omega))
              (padicNorm.nonneg _) (by norm_num)
        _ = 1 := by ring
    have h1 : (((∑ m ∈ Finset.range (p-2), bernoulli m * bernoulli (p-3-m)):ℚ):ZMod p) = 0 :=
      cast_eq_zero_of_norm_lt_one (C_norm_lt p hp7)
    rw [cast_sum_pInt _ _ hpint] at h1
    rw [show (∑ m ∈ Finset.range (p-2), (bernoulli m:ZMod p)*(bernoulli (p-3-m):ZMod p))
        = ∑ m ∈ Finset.range (p-2), ((bernoulli m * bernoulli (p-3-m):ℚ):ZMod p) from
        Finset.sum_congr rfl (fun m hm => by
          rw [Finset.mem_range] at hm
          rw [cast_mul_pInt (bern_pInt m (by omega)) (bern_pInt (p-3-m) (by omega))])]
    exact h1
  rw [hCzero, neg_zero]

end BPI
