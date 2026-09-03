import Submission.BuchstabEulerSurvivor

/-! An unrestricted quadratic-times-fixed-log-power Jacobsthal upper bound.
The logarithmic exponent is finite but is not asserted to be zero. Thus this
is stronger than every fixed power bound above two, but does not settle the
original quadratic conjecture. All actual sieve error costs are retained. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 2400000

lemma geometric_depth_polynomial_cost (K R : ℝ) (hK : 0 < K) (hR : 1 ≤ R) :
    ∃ d : ℕ, ∃ A > (0 : ℝ), ∀ T : ℝ, 0 < T → ∃ n : ℕ,
      K*(19/20 : ℝ)^n ≤ 1/T ∧ R^n ≤ A*(T+1)^d := by
  obtain ⟨n₀,hn₀⟩ := exists_pow_lt_of_lt_one (show 0 < 1/K by positivity)
    (by norm_num : (19/20 : ℝ) < 1)
  have hseed : K*(19/20 : ℝ)^n₀ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hn₀.le hK.le
    simpa only [mul_one_div_cancel hK.ne'] using hh
  have hq : (19/20 : ℝ)^20 ≤ 1/2 := by norm_num
  obtain ⟨b,hblo,hbhi⟩ := exists_nat_pow_near (one_le_pow₀ hR (n := 20))
    (by norm_num : (1 : ℝ) < 2)
  let d := b+1
  have hb : R^20 ≤ (2 : ℝ)^d := hbhi.le
  let A := R^n₀*(2 : ℝ)^d
  have hR0 : 0 < R := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨d,A,hA,fun T hT => ?_⟩
  obtain ⟨j,hjlo,hjhi⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ T+1 by linarith) (by norm_num : (1 : ℝ) < 2)
  let J := j+1
  have hTpow : T ≤ (2 : ℝ)^J := by linarith only [hjhi]
  have hpowT : (2 : ℝ)^J ≤ 2*(T+1) := by
    dsimp only [J]
    rw [pow_succ]
    linarith only [hjlo]
  refine ⟨n₀+20*J,?_,?_⟩
  · have hdec := pow_le_pow_left₀ (by positivity : 0 ≤ (19/20 : ℝ)^20) hq J
    have hscale := mul_le_mul_of_nonneg_left hdec (show 0 ≤ K*(19/20 : ℝ)^n₀ by positivity)
    have hseed' := mul_le_mul_of_nonneg_right hseed (show 0 ≤ (1/2 : ℝ)^J by positivity)
    have he : (1/2 : ℝ)^J=1/(2 : ℝ)^J := by rw [one_div_pow]
    rw [one_mul,he] at hseed'
    rw [he] at hscale
    have hh := hscale.trans hseed'
    rw [pow_add,pow_mul]
    apply le_trans (by simpa only [mul_assoc] using hh)
    exact one_div_le_one_div_of_le hT hTpow
  · have hp := pow_le_pow_left₀ (pow_nonneg hR0.le 20) hb J
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ)^J) hpowT d
    have he : ((2 : ℝ)^d)^J=((2 : ℝ)^J)^d := by rw [← pow_mul,← pow_mul]; congr 1; ring
    rw [he] at hp
    have hh := mul_le_mul_of_nonneg_left (hp.trans hpow) (show 0 ≤ R^n₀ by positivity)
    rw [pow_add,pow_mul]
    apply hh.trans_eq
    dsimp only [A]
    rw [mul_pow]
    ring

/-- Fully charged prime-indexed bound with one fixed natural logarithmic
exponent, uniform even over the initial prime prefixes. -/
theorem exists_prime_polylogarithmic_bound : ∃ d : ℕ, ∃ A > (0 : ℝ), ∀ k : ℕ,
    (jacobsthalFunction k : ℝ) ≤ A*(nthPrime k : ℝ)^2*log (nthPrime k : ℝ)^d := by
  obtain ⟨C,hC,B,hB0,H,hH,hB,hmain⟩ := exists_quantitative_euler_main
  obtain ⟨A,hA,hbound⟩ := euler_main_survivor_depth_bound C B H hC hB0.le hH.le hB hmain
  let R : ℝ := 3600*exp (2*B)
  have hR : 1 ≤ R := by
    have he : 1 ≤ exp (2*B) := one_le_exp (by positivity)
    dsimp [R]
    linarith only [he]
  obtain ⟨d,G,hG,hdepth⟩ := geometric_depth_polynomial_cost (24000+2*H) R (by positivity) hR
  let F : ℝ := 1+(B+1)/log 2
  have hF : 0 < F := by dsimp [F]; have := log_pos (by norm_num : (1 : ℝ) < 2); positivity
  refine ⟨d,A*G*F^d,by positivity,fun k => ?_⟩
  obtain ⟨n,hn,hcost⟩ := hdepth (eulerCoordinate C k) (eulerCoordinate_pos C hC k)
  have hj := hbound n k hn
  have hlog := eulerCoordinate_plus_one_le_log C B hB0.le hB k
  change eulerCoordinate C k+1 ≤ F*log (nthPrime k : ℝ) at hlog
  have hpow := pow_le_pow_left₀ (by linarith only [eulerCoordinate_pos C hC k] : 0 ≤ eulerCoordinate C k+1) hlog d
  have hcost' := hcost.trans (mul_le_mul_of_nonneg_left hpow hG.le)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost' hA.le)
    (sq_nonneg (nthPrime k : ℝ))
  apply hj.trans
  apply hm.trans_eq
  rw [mul_pow]
  ring

/-- Unrestricted quadratic-times-polylogarithmic growth. The exponent `d`
is a single fixed natural number. This theorem does not set it to zero
and must not be used as a proof of the original quadratic conjecture. -/
theorem exists_quadratic_polylogarithmic_bound : ∃ d : ℕ, ∃ A > (0 : ℝ),
    ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ A*(k : ℝ)^2*log ((k : ℝ)+2)^d := by
  obtain ⟨d,A,hA,hbound⟩ := exists_prime_polylogarithmic_bound
  let G : ℝ := 2+log (160 : ℝ)/log 2
  have hG : 0 < G := by
    have h1 : 0 ≤ log (160 : ℝ) := log_nonneg (by norm_num)
    have h2 : 0 < log 2 := log_pos (by norm_num)
    dsimp [G]
    positivity
  refine ⟨d+2,A*160^2*G^d,by positivity,fun k hk => ?_⟩
  let L := log ((k : ℝ)+2)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 < L := log_pos (by linarith)
  have hp0 : (0 : ℝ) ≤ nthPrime k := Nat.cast_nonneg _
  have hp : (nthPrime k : ℝ) ≤ 160*(k : ℝ)*L := by
    have hh := PrimeCountingLower.nth_prime_mul_log k
    change (nthPrime k : ℝ) ≤ 80*((k : ℝ)+1)*L at hh
    nlinarith only [hh,hk1,hL]
  have hl := nthPrime_log_upper k hk
  change log (nthPrime k : ℝ) ≤ G*L at hl
  have hp2 := pow_le_pow_left₀ hp0 hp 2
  have hlpow := pow_le_pow_left₀ (log_natCast_nonneg _) hl d
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hp2 hA.le) hlpow
    (pow_nonneg (log_natCast_nonneg _) d) (by positivity)
  apply (hbound k).trans
  apply hm.trans_eq
  rw [pow_add]
  simp only [mul_pow]
  ring

#print axioms geometric_depth_polynomial_cost
#print axioms exists_prime_polylogarithmic_bound
#print axioms exists_quadratic_polylogarithmic_bound
end Erdos970.RecursiveSieve.Buchstab
