import Submission.PrimeSubsetModuli

/-!
# Uniform error bounds for growing prime-subset pools

The modulus cutoff is deliberately well below the square-root level. The
factor count is not fixed in these estimates.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

/-- Both the primitive-character remainder and all proper prime powers are
bounded before choosing a divisor order. -/
theorem small_rough_pool_combined_error (D : Finset ℕ) (b t E : ℕ)
    (ht : 1 ≤ t) (hE : 1 ≤ E) (hbt : 32*b ≤ t)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ progressionScaleN (b*E))
    (hrough : ∀ d ∈ D, ∀ c ∈ d.divisors.erase 1, progressionScaleN E ≤ c) :
    (∑ d ∈ D, compositeProgressionError d (progressionScaleN (t*E)))+
      2*(progressionScaleN (b*E) : ℝ)*Real.sqrt (progressionScaleN (t*E))*
        Real.log (progressionScaleN (t*E)) ≤
      1000000000000000*(((t : ℝ)+1)*((E : ℝ)+1))^6*(2 : ℝ)^((64*t-1)*E) := by
  let Q := progressionScaleN (b*E)
  let N := progressionScaleN (t*E)
  let L := progressionScaleN E
  let F : ℝ := (2 : ℝ)^((64*t-1)*E)
  let z : ℝ := ((t : ℝ)+1)*((E : ℝ)+1)
  have hz : 1 ≤ z := one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) t])
    (by linarith [Nat.cast_nonneg (α := ℝ) E])
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hL : 2 ≤ L := by
    change 2 ≤ 2^(64*E)
    exact Nat.le_pow (by omega : 0 < 64*E)
  have hbt' : b ≤ t := by omega
  have hQF : (Q : ℝ) ≤ F := by
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,F]
    apply pow_le_pow_right₀ (by norm_num)
    simpa only [mul_assoc] using Nat.mul_le_mul_right E (by omega : 64*b ≤ 64*t-1)
  have hQsqrt : (Q : ℝ)*Real.sqrt N ≤ F := by
    change (Q : ℝ)*Real.sqrt (progressionScaleN (t*E)) ≤ F
    rw [sqrt_progressionScaleN]
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have h : 64*b+32*t ≤ 64*t-1 := by omega
    nlinarith only [Nat.mul_le_mul_right E h]
  have hQ1 : (1 : ℝ) ≤ Q := by
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat]
    exact one_le_pow₀ (by norm_num)
  have hzprod : (t : ℝ)*(E : ℝ) ≤ z := by
    dsimp [z]
    nlinarith [Nat.cast_nonneg (α := ℝ) t,Nat.cast_nonneg (α := ℝ) E]
  have hlogN : Real.log N ≤ 64*z := by
    have h := log_two_pow_le (64*(t*E))
    change Real.log N ≤ _ at h
    push_cast at h
    nlinarith only [h,hzprod]
  have hlogQ : Real.log Q ≤ 64*z :=
    (log_nat_mono (progressionScaleN_monotone (Nat.mul_le_mul_right E hbt'))).trans hlogN
  have hlogNat : (Nat.log 2 N : ℝ) ≤ 64*z := by
    simp only [N,progressionScaleN,Nat.log_pow (by decide : 1 < 2),Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [hzprod]
  have hH : (harmonic Q : ℝ) ≤ 65*z := by
    have h := harmonic_le_one_add_log Q
    linarith only [h,hlogQ,hz]
  have hH0 : (0 : ℝ) ≤ harmonic Q := harmonic_real_nonneg Q
  have hmean := wide_primitive_mean_bound (Icc L Q) 1 b t E (by decide) ht
    (by omega) (by omega) (by omega) (by
      intro d hd
      obtain ⟨hdL,hdQ⟩ := mem_Icc.mp hd
      exact ⟨hL.trans hdL,by simpa only [one_mul] using hdL,hdQ⟩)
  have hmean' : primitivePoolMean (Icc L Q) N ≤ 4000000000000*z^5*F := by
    simpa only [wideMeanConstant,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,
      z,mul_pow,mul_assoc,N,F] using hmean
  have hmain : (2*(harmonic Q : ℝ))*primitivePoolMean (Icc L Q) N ≤
      520000000000000*z^6*F := by
    calc
      _ ≤ (2*(65*z))*(4000000000000*z^5*F) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) hmean'
          (primitivePoolMean_nonneg _ _) (by positivity)
      _ = _ := by ring
  have hlift : 2*((Q : ℝ)+1)*(harmonic Q : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q ≤
      1064960*z^3*F := by
    have hQ2 : (Q : ℝ)+1 ≤ 2*F := by linarith only [hQ1,hQF]
    calc
      _ ≤ 2*(2*F)*(65*z)*(64*z)*(64*z) := by
        gcongr
      _ = _ := by ring
  have hpower : 2*(Q : ℝ)*Real.sqrt N*Real.log N ≤ 128*z*F := by
    calc
      _ = 2*((Q : ℝ)*Real.sqrt N)*Real.log N := by ring
      _ ≤ 2*F*(64*z) := by gcongr
      _ = _ := by ring
  have herr := rough_composite_error_le D L Q N hL hD hrough
  have hz36 : z^3*F ≤ z^6*F := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hz (by decide)) hF
  have hz16 : z*F ≤ z^6*F := by
    simpa only [pow_one] using mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hz (by decide : 1 ≤ 6)) hF
  have hnon : 0 ≤ z^6*F := by positivity
  change _ ≤ 1000000000000000*z^6*F
  nlinarith only [herr,hmain,hlift,hpower,hz36,hz16,hnon]

def subsetMomentX (k m : ℕ) : ℕ :=
  progressionScaleN (64*(k*m)*logMomentScale m*logMomentScale m)
def subsetMomentQ (k m : ℕ) : ℕ :=
  progressionScaleN ((k*m)*logMomentTop m*logMomentScale m)
noncomputable def subsetMomentPool (k m : ℕ) : Finset ℕ :=
  primeSubsetModuli (logMomentModuli m) (k*m)

lemma subsetMomentPool_bounds (k m : ℕ) :
    ∀ d ∈ subsetMomentPool k m, 0 < d ∧ d ≤ subsetMomentQ k m := by
  intro d hd
  have hP := logMomentModuli_prime_bound m
  refine ⟨primeSubsetModuli_pos _ (fun p hp => (hP p hp).1) hd,?_⟩
  have h := primeSubsetModuli_le _ _ (fun p hp => (hP p hp).2) hd
  apply h.trans_eq
  simp only [subsetMomentQ,progressionScaleN,← pow_mul]
  apply congrArg (fun e : ℕ => (2 : ℕ)^e)
  ring

lemma subsetMomentPool_card_le (k m : ℕ) : (subsetMomentPool k m).card ≤ subsetMomentQ k m := by
  have hsub : subsetMomentPool k m ⊆ Icc 1 (subsetMomentQ k m) :=
    fun d hd => mem_Icc.mpr (subsetMomentPool_bounds k m d hd)
  exact (card_le_card hsub).trans_eq (by simp)

lemma logMomentModuli_lower (m p : ℕ) (hp : p ∈ logMomentModuli m) :
    progressionScaleN (logMomentScale m) ≤ p := by
  obtain ⟨a,ha,hp⟩ := mem_biUnion.mp hp
  have ha1 := (mem_Icc.mp ha).1
  have h := (mem_widePrimePool.mp hp).2.1
  exact (progressionScaleN_monotone (by nlinarith : logMomentScale m ≤ a*logMomentScale m)).trans h

lemma subsetMomentPool_rough (k m : ℕ) :
    ∀ d ∈ subsetMomentPool k m, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (logMomentScale m) ≤ c := by
  intro d hd c hc
  exact primeSubsetModuli_rough _ _
    (fun p hp => ⟨(logMomentModuli_prime_bound m p hp).1,logMomentModuli_lower m p hp⟩) hd hc

lemma subsetMoment_combined_error_bound (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (∑ d ∈ subsetMomentPool k m, compositeProgressionError d (subsetMomentX k m))+
      2*(subsetMomentQ k m : ℝ)*Real.sqrt (subsetMomentX k m)*Real.log (subsetMomentX k m) ≤
      1000000000000000*(64*(k : ℝ)+1)^6*((logMomentScale m : ℝ)+1)^18*
        (2 : ℝ)^((64*(64*(k*m)*logMomentScale m)-1)*logMomentScale m) := by
  let E := logMomentScale m
  let B := logMomentTop m
  let r := k*m
  let t := 64*r*E
  let b := r*B
  have hE := logMomentScale_ge m
  have hBE := logMomentTop_four m
  have hr : 1 ≤ r := Nat.mul_pos hk hm
  have ht : 1 ≤ t := by dsimp [t,E]; nlinarith
  have hbt : 32*b ≤ t := by
    dsimp [b,t]
    change 4*B=E at hBE
    nlinarith only [congrArg (fun x : ℕ => r*x) hBE]
  have h := small_rough_pool_combined_error (subsetMomentPool k m) b t E ht (by dsimp [E]; omega)
    hbt (subsetMomentPool_bounds k m) (subsetMomentPool_rough k m)
  have hmE : (m : ℝ) ≤ E := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le.trans
      (Nat.pow_le_pow_right (by decide) (by omega : m ≤ m+5))
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hz : ((t : ℝ)+1)*((E : ℝ)+1) ≤ (64*(k : ℝ)+1)*((E : ℝ)+1)^3 := by
    have ht' : (t : ℝ) ≤ 64*(k : ℝ)*(E : ℝ)^2 := by
      dsimp [t,r]
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left hmE (show 0 ≤ 64*(k : ℝ)*(E : ℝ) by positivity)]
    have hEE : (E : ℝ)^2 ≤ ((E : ℝ)+1)^2 := by nlinarith
    have hEE1 : (1 : ℝ) ≤ ((E : ℝ)+1)^2 := by nlinarith
    have ht'' : (t : ℝ)+1 ≤ (64*(k : ℝ)+1)*((E : ℝ)+1)^2 := by
      nlinarith only [ht',hEE1,mul_le_mul_of_nonneg_left hEE (show 0 ≤ 64*(k : ℝ) by positivity)]
    have hh := mul_le_mul_of_nonneg_right ht'' (show 0 ≤ (E : ℝ)+1 by positivity)
    nlinarith only [hh]
  apply h.trans
  calc
    _ ≤ 1000000000000000*((64*(k : ℝ)+1)*((E : ℝ)+1)^3)^6*
        (2 : ℝ)^((64*t-1)*E) := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul]; dsimp [t,r,E]; ring

end Erdos821
