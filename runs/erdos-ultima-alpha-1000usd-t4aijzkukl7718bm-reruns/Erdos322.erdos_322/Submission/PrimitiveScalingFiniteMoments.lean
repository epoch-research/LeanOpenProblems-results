import Submission.ScalingFiniteMoments

/-! Exact primitive scaling, finitely many linear moments, and polynomial
peaks are compatible for abstract counting functions. This does not concern
the actual number of representations by fourth powers. -/
namespace Erdos322Research.PrimitiveScalingFiniteMoments

open Finset ScalingFiniteMoments Erdos322.MomentReduction
set_option Elab.async false
set_option maxHeartbeats 1000000

/-- A primitive spike supported on `D`th powers of primes. -/
def primitiveSpike (D n : ℕ) : ℕ :=
  let p := maximalPowerDivisor D n
  if p.Prime ∧ p^D=n then p else 0

/-- The exact common-factor decomposition with scaling exponent `k`. -/
def fullSpike (k D n : ℕ) : ℕ :=
  ∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), primitiveSpike D (n/b^k)

lemma primitiveSpike_at_prime_power (D p : ℕ) (hD : 0 < D) (hp : p.Prime) :
    primitiveSpike D (p^D)=p := by
  simp [primitiveSpike,maximalPowerDivisor_at_power D p hD hp.pos,hp]

lemma primitiveSpike_nonzero (D n : ℕ) (h : primitiveSpike D n ≠ 0) :
    (primitiveSpike D n).Prime ∧ (primitiveSpike D n)^D=n := by
  dsimp only [primitiveSpike] at h ⊢
  split_ifs at h ⊢ with hc
  · exact hc
  · exact (h rfl).elim

lemma scaled_prime_power_unique (k D p q b c : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hp : p.Prime) (hq : q.Prime) (hb : 0 < b) (hc : 0 < c)
    (he : p^D*b^k=q^D*c^k) : p=q ∧ b=c := by
  have hpq : p=q := by
    by_contra hpq
    have hv := congrArg (fun n : ℕ => n.factorization p) he
    simp only [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hb.ne'),
      Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hc.ne'),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      hp.factorization_self, hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq),
      mul_one, mul_zero, zero_add] at hv
    apply hD
    have hvmod := congrArg (fun a : ℕ => a % k) hv
    have hz : D % k=0 := by simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] using hvmod
    exact Nat.dvd_of_mod_eq_zero hz
  refine ⟨hpq,?_⟩
  rw [hpq] at he
  have hpow := Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos D) he
  exact Nat.pow_left_injective hk.ne' hpow

lemma fullSpike_le_maximalPowerDivisor (k D n : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) : fullSpike k D n ≤ maximalPowerDivisor D n := by
  classical
  let S := n.divisors.filter (fun b => b^k ∣ n)
  by_cases hs : ∃ b ∈ S, primitiveSpike D (n/b^k) ≠ 0
  · obtain ⟨b,hbS,hbval⟩ := hs
    have hb : 0 < b := Nat.pos_of_mem_divisors (mem_filter.mp hbS).1
    have hn : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp (mem_filter.mp hbS).1).2
    have hbn : b^k ∣ n := (mem_filter.mp hbS).2
    have hbe : (primitiveSpike D (n/b^k))^D*b^k=n := by
      rw [(primitiveSpike_nonzero D (n/b^k) hbval).2]
      exact Nat.div_mul_cancel hbn
    have hsingle : fullSpike k D n=primitiveSpike D (n/b^k) := by
      unfold fullSpike
      change (∑ c ∈ S, primitiveSpike D (n/c^k))=primitiveSpike D (n/b^k)
      apply Finset.sum_eq_single b
      · intro c hcS hcb
        by_contra hcv
        have hc : 0 < c := Nat.pos_of_mem_divisors (mem_filter.mp hcS).1
        have hce : (primitiveSpike D (n/c^k))^D*c^k=n := by
          rw [(primitiveSpike_nonzero D (n/c^k) hcv).2]
          exact Nat.div_mul_cancel (mem_filter.mp hcS).2
        have hh := scaled_prime_power_unique k D
          (primitiveSpike D (n/b^k)) (primitiveSpike D (n/c^k)) b c hk hD
          (primitiveSpike_nonzero D (n/b^k) hbval).1
          (primitiveSpike_nonzero D (n/c^k) hcv).1 hb hc (hbe.trans hce.symm)
        exact hcb hh.2.symm
      · exact fun h => (h hbS).elim
    rw [hsingle]
    apply Finset.le_sup (f := id)
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · apply Nat.mem_divisors.mpr
      refine ⟨?_,hn.ne'⟩
      have hposD : 0 < D := by
        apply Nat.pos_of_ne_zero
        intro h
        apply hD
        rw [h]
        exact dvd_zero _
      exact (dvd_pow_self _ hposD.ne').trans ⟨b^k,hbe.symm⟩
    · exact ⟨b^k,hbe.symm⟩
  · have hz : ∀ b ∈ S, primitiveSpike D (n/b^k)=0 := by simpa using hs
    have hf : fullSpike k D n=0 := Finset.sum_eq_zero hz
    rw [hf]
    exact Nat.zero_le _

lemma primitiveSpike_le_fullSpike (k D n : ℕ) : primitiveSpike D n ≤ fullSpike k D n := by
  by_cases hn : n=0
  · subst n
    simp [primitiveSpike,maximalPowerDivisor,fullSpike]
  · have h1 : 1 ∈ n.divisors.filter (fun b => b^k ∣ n) := by simp [Nat.mem_divisors,hn]
    have hs := Finset.single_le_sum
      (f := fun b => primitiveSpike D (n/b^k)) (fun _ _ => Nat.zero_le _) h1
    simpa only [one_pow,Nat.div_one] using hs

/-- Exact primitive scaling always gives monotonicity under positive kth-power
multiples; this requires no property of the primitive spikes. -/
theorem monotone_under_power_scaling (k D n s : ℕ) (hk : 0 < k) (hs : 0 < s) :
    fullSpike k D n ≤ fullSpike k D (n*s^k) := by
  classical
  by_cases hn : n=0
  · subst n
    simp [fullSpike]
  let S := n.divisors.filter (fun b => b^k ∣ n)
  let T := (n*s^k).divisors.filter (fun b => b^k ∣ n*s^k)
  have hinj : Function.Injective (fun b : ℕ => b*s) := by
    intro b c h
    exact Nat.eq_of_mul_eq_mul_right hs h
  have hsub : S.image (fun b => b*s) ⊆ T := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
    have hpow : (b*s)^k ∣ n*s^k := by
      rw [mul_pow]
      exact Nat.mul_dvd_mul_right (mem_filter.mp hb).2 (s^k)
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_,mul_ne_zero hn (pow_ne_zero _ hs.ne')⟩,hpow⟩
    exact (dvd_pow_self _ hk.ne').trans hpow
  have he (b : ℕ) : primitiveSpike D ((n*s^k)/(b*s)^k)=primitiveSpike D (n/b^k) := by
    rw [mul_pow,Nat.mul_div_mul_right _ _ (pow_pos hs k)]
  calc
    fullSpike k D n = ∑ b ∈ S, primitiveSpike D ((n*s^k)/(b*s)^k) := by
      simp only [he]; rfl
    _ = ∑ c ∈ S.image (fun b => b*s), primitiveSpike D ((n*s^k)/c^k) :=
      (Finset.sum_image (s := S) (f := fun c => primitiveSpike D ((n*s^k)/c^k)) hinj.injOn).symm
    _ ≤ ∑ c ∈ T, primitiveSpike D ((n*s^k)/c^k) := Finset.sum_le_sum_of_subset hsub
    _ = fullSpike k D (n*s^k) := rfl

/-- Arbitrarily many prescribed low moments have a linear summatory bound. -/
theorem low_moments_linear (k D q N : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hq : q+2 ≤ D) :
    countMoment (fullSpike k D) q N ≤ momentConstant*(N : ℝ) := by
  apply le_trans _ (ScalingFiniteMoments.low_moments_linear D q N hq)
  unfold countMoment
  apply Finset.sum_le_sum
  intro n hn
  have hb : (fullSpike k D n : ℝ) ≤ maximalPowerDivisor D n := by
    exact_mod_cast fullSpike_le_maximalPowerDivisor k D n hk hD
  exact pow_le_pow_left₀ (by positivity) hb q

/-- The primitive count itself has power-size peaks at prime-power targets. -/
theorem primitive_polynomial_peaks (D : ℕ) (hD : 0 < D) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (primitiveSpike D n : ℝ)}.Infinite := by
  refine ⟨1/(2*(D : ℝ)),by positivity,?_⟩
  have hinj : Function.Injective (fun p : ℕ => p^D) := Nat.pow_left_injective hD.ne'
  have hset := Nat.infinite_setOf_prime.image hinj.injOn
  apply hset.mono
  rintro n ⟨p,hp,rfl⟩
  change ((p^D : ℕ) : ℝ)^(1/(2*(D : ℝ))) < primitiveSpike D (p^D)
  rw [primitiveSpike_at_prime_power D p hD hp]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpr.le]
  have he : (D : ℝ)*(1/(2*(D : ℝ)))=1/2 := by field_simp
  rw [he]
  simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast hp.one_lt : (1 : ℝ) < p) (by norm_num : (1/2 : ℝ) < 1)

theorem full_polynomial_peaks (k D : ℕ) (hD : 0 < D) :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (fullSpike k D n : ℝ)}.Infinite := by
  obtain ⟨c,hc,hi⟩ := primitive_polynomial_peaks D hD
  refine ⟨c,hc,hi.mono ?_⟩
  intro n hn
  change (n : ℝ)^c < (primitiveSpike D n : ℝ) at hn
  have hb : (primitiveSpike D n : ℝ) ≤ (fullSpike k D n : ℝ) := by
    exact_mod_cast primitiveSpike_le_fullSpike k D n
  exact hn.trans_le hb

/-- Even the exact nonnegative primitive scaling identity does not turn any
finite collection of linear moment estimates into a subpolynomial pointwise
bound. This is a counterexample for abstract counts, not representationCount. -/
theorem exact_scaling_and_finite_moments_do_not_suffice (k Q : ℕ) (hk : 2 ≤ k) :
    ∃ f g : ℕ → ℕ,
      (∀ n, f n=∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), g (n/b^k)) ∧
      (∀ n s, 0 < s → f n ≤ f (n*s^k)) ∧
      (∀ n, g n ≤ f n) ∧
      (∃ C > (0 : ℝ), ∀ q ≤ Q, ∀ N, countMoment f q N ≤ C*(N : ℝ)) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (g n : ℝ)}.Infinite) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (f n : ℝ)}.Infinite) := by
  let D := k*(Q+2)+1
  have hD : ¬ k ∣ D := by
    intro h
    have hm := Nat.mod_eq_zero_of_dvd h
    dsimp [D] at hm
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < k)] at hm
    omega
  have hDQ : Q+2 ≤ D := by dsimp [D]; nlinarith
  have hDpos : 0 < D := by omega
  refine ⟨fullSpike k D,primitiveSpike D,(fun n => rfl),
    (fun n s hs => monotone_under_power_scaling k D n s (by omega) hs),
    primitiveSpike_le_fullSpike k D,⟨momentConstant,momentConstant_pos,?_⟩,
    primitive_polynomial_peaks D hDpos,full_polynomial_peaks k D hDpos⟩
  intro q hq N
  exact low_moments_linear k D q N (by omega) hD (by omega)

end Erdos322Research.PrimitiveScalingFiniteMoments
