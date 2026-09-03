import Submission.SmoothCorrelationApprox
import Submission.DivisorCovariance

/-! Quantitative long-divisor tails for the exponential-divisor sum.
The dependence on the smoothing parameter is explicit; these estimates
must not be replaced by a uniform vanishing error as that parameter tends
to zero. -/
namespace Erdos972SmoothDivisorTail

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothCorrelationApprox Erdos972DivisorEnergy
open Erdos972PrimePowerError Erdos972DivisorCovariance Erdos972DivisorPairCount
open Erdos972ExponentialSum

noncomputable def dampedCoefficient (t : ℝ) (d : ℕ) : ℝ :=
  (μ d : ℝ) * Real.exp (-t * Real.log d)

noncomputable def truncatedExpSum (t : ℝ) (D n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ D), dampedCoefficient t d

noncomputable def expTail (t : ℝ) (D n : ℕ) : ℝ :=
  expDivisorSum t n - truncatedExpSum t D n

noncomputable def damping (t : ℝ) (D : ℕ) : ℝ := Real.exp (-t * Real.log D)

lemma damping_pos (t : ℝ) (D : ℕ) : 0 < damping t D := Real.exp_pos _

lemma abs_dampedCoefficient_le_one {t : ℝ} (ht : 0 ≤ t) (d : ℕ) :
    |dampedCoefficient t d| ≤ 1 := by
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
  have he : Real.exp (-t * Real.log d) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Real.log_natCast_nonneg d))
  rw [dampedCoefficient, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul hμ he (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)

lemma expTail_eq (t : ℝ) (D n : ℕ) :
    expTail t D n = ∑ d ∈ n.divisors.filter (fun d => D < d), dampedCoefficient t d := by
  classical
  have hh := sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ D) (dampedCoefficient t)
  simp only [not_le] at hh
  dsimp only [expTail, truncatedExpSum, expDivisorSum, dampedCoefficient] at *
  linarith only [hh]

/-- No sign is assumed for the tail of the signed divisor expansion. -/
theorem abs_expTail_le {t : ℝ} (ht : 0 ≤ t) (D n : ℕ) :
    |expTail t D n| ≤ damping t D * n.divisors.card := by
  classical
  rw [expTail_eq]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => D < d), damping t D := by
      apply sum_le_sum
      intro d hd
      have hDd : D ≤ d := (mem_filter.mp hd).2.le
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      rw [dampedCoefficient, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ 1 * Real.exp (-t * Real.log d) :=
          mul_le_mul_of_nonneg_right hμ (Real.exp_pos _).le
        _ ≤ damping t D := by
          rw [one_mul]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left (monotone_log_natCast hDd) (neg_nonpos.mpr ht)
    _ ≤ ∑ d ∈ n.divisors, damping t D :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => (damping_pos t D).le)
    _ = _ := by simp [mul_comm]

/-- An explicit mean-square tail bound, uniform in N and D. It gives decay
for fixed t>0 and polynomially growing D, not for every vanishing t. -/
theorem expTail_energy_bound {t : ℝ} (ht : 0 ≤ t) (D N : ℕ) :
    (∑ n ∈ Ioc 0 N, (expTail t D n)^2) ≤
      (damping t D)^2 * (N:ℝ) * (1+Real.log N)^3 := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (damping t D * n.divisors.card)^2 := by
      apply sum_le_sum
      intro n hn
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_expTail_le ht D n) 2
    _ = (damping t D)^2 * ∑ n ∈ Ioc 0 N, (n.divisors.card:ℝ)^2 := by
      simp only [mul_pow, mul_sum]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (sum_card_divisors_square_le_log N) (sq_nonneg (damping t D))

lemma expDivisorSum_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : expDivisorSum t n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, expDivisorSum]
  rw [expDivisorSum_product t hn]
  exact prod_le_one (fun p _ => expFactor_nonneg ht p) (fun p _ => expFactor_le_one t p)

lemma truncatedExpSum_eq_polynomial (t : ℝ) (D : ℕ) {n : ℕ} (hn : n ≠ 0) :
    truncatedExpSum t D n = divisorPolynomial D (dampedCoefficient t) n := by
  classical
  unfold truncatedExpSum divisorPolynomial
  rw [← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
  constructor
  · rintro ⟨hdn, hdD⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn.1 (Nat.pos_of_ne_zero hn), hdD⟩, hdn.1⟩
  · rintro ⟨⟨_, hdD⟩, hdn⟩
    exact ⟨⟨hdn, hn⟩, hdD⟩

lemma sum_output_divisors_square_le {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((floorMul α n).divisors.card:ℝ)^2) ≤
      (floorMul α N:ℝ)*(1+Real.log (floorMul α N))^3 := by
  classical
  calc
    _ = ∑ m ∈ (Ioc 0 N).image (floorMul α), (m.divisors.card:ℝ)^2 := by
      rw [sum_image]
      exact (floorMul_strictMono hα).injective.injOn
    _ ≤ ∑ m ∈ Ioc 0 (floorMul α N), (m.divisors.card:ℝ)^2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro m _ _
        exact sq_nonneg _
    _ ≤ _ := sum_card_divisors_square_le_log _

lemma pair_perturbation_bound {f g p q ρ a b : ℝ}
    (hf0 : 0 ≤ f) (hfle : f ≤ 1) (hg0 : 0 ≤ g) (hgle : g ≤ 1)
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hr : |f-p| ≤ ρ*a) (hs : |g-q| ≤ ρ*b) :
    |f*g-p*q| ≤ ρ*(a+b)+ρ^2/2*(a^2+b^2) := by
  have he : f*g-p*q = (f-p)*g+f*(g-q)-(f-p)*(g-q) := by ring
  rw [he]
  calc
    _ ≤ |(f-p)*g+f*(g-q)| + |(f-p)*(g-q)| := abs_sub _ _
    _ ≤ (|(f-p)*g|+|f*(g-q)|)+|(f-p)*(g-q)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = (|f-p| *g+f*|g-q|)+|f-p| *|g-q| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg hf0]
    _ ≤ (ρ*a+ρ*b)+(ρ*a)*(ρ*b) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [mul_one] using mul_le_mul hr hgle hg0 (mul_nonneg hρ ha)
        · simpa only [one_mul] using mul_le_mul hfle hs (abs_nonneg _) zero_le_one
      · exact mul_le_mul hr hs (abs_nonneg _) (mul_nonneg hρ ha)
    _ ≤ _ := by
      have hh := mul_nonneg (sq_nonneg ρ) (sq_nonneg (a-b))
      nlinarith only [hh]

noncomputable def fullExpCorrelation (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, expDivisorSum t n * expDivisorSum t (floorMul α n)

noncomputable def truncatedExpCorrelation (t α : ℝ) (D N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, truncatedExpSum t D n * truncatedExpSum t D (floorMul α n)

noncomputable def divisorTailBudget (t α : ℝ) (D N : ℕ) : ℝ :=
  ((N:ℝ)+floorMul α N) * (damping t D*(1+Real.log (floorMul α N))+
    (damping t D)^2/2*(1+Real.log (floorMul α N))^3)

/-- The full two-coordinate tail is controlled, with its smoothing-parameter
cost retained explicitly. -/
theorem full_truncated_correlation_error {α t : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) (D N : ℕ) :
    |fullExpCorrelation t α N - truncatedExpCorrelation t α D N| ≤ divisorTailBudget t α D N := by
  let M := floorMul α N
  let L := 1+Real.log M
  let ρ := damping t D
  have hρ : 0 ≤ ρ := (damping_pos t D).le
  have hL : 0 ≤ L := by dsimp [L]; positivity [Real.log_natCast_nonneg M]
  have hlog : 1+Real.log N ≤ L := by
    have hh := monotone_log_natCast (self_le_floorMul hα N)
    dsimp only [L, M]
    linarith only [hh]
  have hlocal (n : ℕ) :
      |expDivisorSum t n*expDivisorSum t (floorMul α n)-truncatedExpSum t D n*truncatedExpSum t D (floorMul α n)| ≤
        ρ*((n.divisors.card:ℝ)+(floorMul α n).divisors.card)+
          ρ^2/2*((n.divisors.card:ℝ)^2+((floorMul α n).divisors.card:ℝ)^2) :=
    pair_perturbation_bound (expDivisorSum_nonneg ht n) (expDivisorSum_le_one ht n)
      (expDivisorSum_nonneg ht _) (expDivisorSum_le_one ht _) hρ
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (abs_expTail_le ht D n) (abs_expTail_le ht D _)
  have hsum1 : (∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)+(floorMul α n).divisors.card)) ≤
      ((N:ℝ)+M)*L := by
    rw [sum_add_distrib]
    calc
      _ ≤ (N:ℝ)*(1+Real.log N)+(M:ℝ)*L :=
        add_le_add (sum_card_divisors_le_log N) (sum_output_divisors_le hα N)
      _ ≤ (N:ℝ)*L+(M:ℝ)*L := by gcongr
      _ = _ := by ring
  have hsum2 : (∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)^2+((floorMul α n).divisors.card:ℝ)^2)) ≤
      ((N:ℝ)+M)*L^3 := by
    rw [sum_add_distrib]
    calc
      _ ≤ (N:ℝ)*(1+Real.log N)^3+(M:ℝ)*L^3 :=
        add_le_add (sum_card_divisors_square_le_log N) (sum_output_divisors_square_le hα N)
      _ ≤ (N:ℝ)*L^3+(M:ℝ)*L^3 := by gcongr
      _ = _ := by ring
  unfold fullExpCorrelation truncatedExpCorrelation
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |expDivisorSum t n*expDivisorSum t (floorMul α n)-
        truncatedExpSum t D n*truncatedExpSum t D (floorMul α n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (ρ*((n.divisors.card:ℝ)+(floorMul α n).divisors.card)+
          ρ^2/2*((n.divisors.card:ℝ)^2+((floorMul α n).divisors.card:ℝ)^2)) :=
      sum_le_sum (fun n _ => hlocal n)
    _ = ρ*(∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)+(floorMul α n).divisors.card))+
        ρ^2/2*(∑ n ∈ Ioc 0 N, ((n.divisors.card:ℝ)^2+((floorMul α n).divisors.card:ℝ)^2)) := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ ρ*(((N:ℝ)+M)*L)+ρ^2/2*(((N:ℝ)+M)*L^3) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum1 hρ)
        (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ = divisorTailBudget t α D N := by dsimp [divisorTailBudget, M, L, ρ]; ring

lemma coefficientMass_damped_le {t : ℝ} (ht : 0 ≤ t) (D : ℕ) :
    coefficientMass D (dampedCoefficient t) ≤ D := by
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, (1:ℝ) := sum_le_sum (fun d _ => abs_dampedCoefficient_le_one ht d)
    _ = _ := by simp

/-- The proved finite-divisor count estimates can now be applied to the
proxy, but only together with the explicit full tail budget. -/
theorem full_exp_correlation_error {α t B : ℝ} (hα : 1 ≤ α) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (D N : ℕ)
    (hlocal : ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 D,
      |((divisorPairs α N d e).card:ℝ)-(N:ℝ)/(d*e)| ≤ B) :
    |fullExpCorrelation t α N - (N:ℝ)*(divisorMean D (dampedCoefficient t))^2| ≤
      divisorTailBudget t α D N+B*(D:ℝ)^2 := by
  have heq : truncatedExpCorrelation t α D N =
      ∑ n ∈ Ioc 0 N, divisorPolynomial D (dampedCoefficient t) n *
        divisorPolynomial D (dampedCoefficient t) (floorMul α n) := by
    apply sum_congr rfl
    intro n hn
    rw [truncatedExpSum_eq_polynomial t D (mem_Ioc.mp hn).1.ne',
      truncatedExpSum_eq_polynomial t D (floorMul_pos hα (mem_Ioc.mp hn).1).ne']
  have hp := polynomial_pair_error α N D D (dampedCoefficient t) (dampedCoefficient t) B hlocal
  rw [← heq] at hp
  have hmass0 : 0 ≤ coefficientMass D (dampedCoefficient t) := sum_nonneg fun _ _ => abs_nonneg _
  have hmass := coefficientMass_damped_le ht D
  have hp' : |truncatedExpCorrelation t α D N - (N:ℝ)*(divisorMean D (dampedCoefficient t))^2| ≤ B*(D:ℝ)^2 := by
    have he : (N:ℝ)*divisorMean D (dampedCoefficient t)*divisorMean D (dampedCoefficient t) =
        (N:ℝ)*(divisorMean D (dampedCoefficient t))^2 := by ring
    rw [he] at hp
    apply hp.trans
    nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass0 hmass 2) hB]
  exact (abs_sub_le _ _ _).trans (add_le_add (full_truncated_correlation_error hα ht D N) hp')

lemma full_minus_scaled_smooth {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ) :
    |fullExpCorrelation t α N - t^2*smoothCorrelation t α N| ≤ 1 := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 N) :
      expDivisorSum t n*expDivisorSum t (floorMul α n) =
        t^2*(smoothMangoldt t n*smoothMangoldt t (floorMul α n))+
          if n = 1 then expDivisorSum t (floorMul α 1) else 0 := by
    by_cases hn1 : n = 1
    · subst n
      simp [smoothMangoldt, expDivisorSum]
    · have hqn1 : floorMul α n ≠ 1 := by
        have hn0 := (mem_Ioc.mp hn).1
        have hh := self_le_floorMul hα n
        omega
      rw [if_neg hn1, add_zero, smoothMangoldt, smoothMangoldt,
        expDivisorSum_at_zero, expDivisorSum_at_zero]
      simp only [one_apply, if_neg hn1, if_neg hqn1, sub_zero]
      field_simp
  have he : fullExpCorrelation t α N - t^2*smoothCorrelation t α N =
      if 1 ≤ N then expDivisorSum t (floorMul α 1) else 0 := by
    unfold fullExpCorrelation smoothCorrelation
    rw [sum_congr rfl hpoint, sum_add_distrib, ← mul_sum, add_sub_cancel_left]
    simp only [sum_ite_eq', mem_Ioc, Nat.zero_lt_one, true_and]
  rw [he]
  split_ifs
  · rw [abs_of_nonneg (expDivisorSum_nonneg ht.le _)]
    exact expDivisorSum_le_one ht.le _
  · norm_num

/-- The same finite estimate for the normalized proxy S(t,n), including the
n=1 correction and the cost of dividing by t^2. -/
theorem smooth_correlation_divisor_error {α t B : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (hB : 0 ≤ B)
    (D N : ℕ)
    (hlocal : ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 D,
      |((divisorPairs α N d e).card:ℝ)-(N:ℝ)/(d*e)| ≤ B) :
    |smoothCorrelation t α N - (N:ℝ)*(divisorMean D (dampedCoefficient t)/t)^2| ≤
      (1+divisorTailBudget t α D N+B*(D:ℝ)^2)/t^2 := by
  have hfull := full_exp_correlation_error hα ht.le hB D N hlocal
  have hcorr := full_minus_scaled_smooth hα ht N
  rw [abs_sub_comm] at hcorr
  have hh := (abs_sub_le (t^2*smoothCorrelation t α N) (fullExpCorrelation t α N)
    ((N:ℝ)*(divisorMean D (dampedCoefficient t))^2)).trans (add_le_add hcorr hfull)
  have he : smoothCorrelation t α N - (N:ℝ)*(divisorMean D (dampedCoefficient t)/t)^2 =
      (t^2*smoothCorrelation t α N-(N:ℝ)*(divisorMean D (dampedCoefficient t))^2)/t^2 := by
    field_simp
  rw [he, abs_div, abs_of_nonneg (sq_nonneg t)]
  apply (div_le_div_of_nonneg_right hh (sq_nonneg t)).trans_eq
  ring

#print axioms expTail_energy_bound
#print axioms full_truncated_correlation_error
#print axioms full_exp_correlation_error
#print axioms smooth_correlation_divisor_error

end Erdos972SmoothDivisorTail
