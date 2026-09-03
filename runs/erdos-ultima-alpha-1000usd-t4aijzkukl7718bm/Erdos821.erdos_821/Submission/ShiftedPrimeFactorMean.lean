import Submission.LogarithmicPrimeModuli
import Submission.WideIncidences

/-!
# A quantitative lower mean for the prime factors of shifted primes

This supplies a positive logarithmic growth rate for divisor moments later
on. It is not the sharp fixed-order moment lower bound needed for Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def shiftedPrimeFactorMangoldt (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ)*((p-1).primeFactors.card : ℝ)

lemma family_progression_le_prime_factor_mean (P : Finset ℕ) (N Q : ℕ)
    (hN : 1 ≤ N) (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ Q) :
    (∑ d ∈ P, residueOneMangoldt d N) ≤ shiftedPrimeFactorMangoldt N+
      2*(Q : ℝ)*Real.sqrt N*Real.log N := by
  let I (n : ℕ) := (P.filter (fun d => d ∣ n-1)).card
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (I n : ℝ)*vonMangoldt n ≤
        (if n.Prime then Real.log (n : ℝ)*((n-1).primeFactors.card : ℝ) else 0)+
        (if ¬n.Prime then (Q : ℝ)*vonMangoldt n else 0) := by
    by_cases hp : n.Prime
    · rw [if_pos hp,if_neg (not_not.mpr hp),add_zero,vonMangoldt_apply_prime hp]
      have hsub : P.filter (fun d => d ∣ n-1) ⊆ (n-1).primeFactors := by
        intro d hd
        obtain ⟨hd,hdn⟩ := mem_filter.mp hd
        exact Nat.mem_primeFactors.mpr ⟨hP d hd,hdn,by have := hp.two_le; omega⟩
      have hc : (I n : ℝ) ≤ (n-1).primeFactors.card := by exact_mod_cast card_le_card hsub
      have h := mul_le_mul_of_nonneg_right hc (Real.log_natCast_nonneg n)
      simpa only [mul_comm] using h
    · rw [if_neg hp,if_pos hp,zero_add]
      have hc : (I n : ℝ) ≤ Q := by exact_mod_cast (card_filter_le P _).trans hcard
      exact mul_le_mul_of_nonneg_right hc vonMangoldt_nonneg
  have hpr : (Icc 1 N).filter Nat.Prime = (N+1).primesBelow := by
    ext p
    simp only [mem_filter,mem_Icc,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_,hpN⟩,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.pos,by omega⟩,hp⟩
  calc
    _ = ∑ n ∈ Icc 1 N, (I n : ℝ)*vonMangoldt n := sum_family_progressions_eq_incidence P N
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if n.Prime then Real.log (n : ℝ)*((n-1).primeFactors.card : ℝ) else 0)+
        (if ¬n.Prime then (Q : ℝ)*vonMangoldt n else 0)) := sum_le_sum hpoint
    _ = shiftedPrimeFactorMangoldt N+(Q : ℝ)*∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [sum_add_distrib]
      simp only [← sum_filter,hpr,shiftedPrimeFactorMangoldt,mul_sum]
    _ ≤ shiftedPrimeFactorMangoldt N+(Q : ℝ)*(2*Real.sqrt N*Real.log N) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) (Nat.cast_nonneg _))
    _ = _ := by ring

lemma logMoment_combined_error_bound (m : ℕ) :
    (∑ d ∈ logMomentModuli m, compositeProgressionError d (logMomentX m))+
      2*(progressionScaleN (logMomentTop m*logMomentScale m) : ℝ)*
        Real.sqrt (logMomentX m)*Real.log (logMomentX m) ≤
      5000000000000*((logMomentScale m : ℝ)+1)^11*
        (2 : ℝ)^((64*logMomentScale m-1)*logMomentScale m) := by
  let E := logMomentScale m
  let B := logMomentTop m
  let N := logMomentX m
  let Q := progressionScaleN (B*E)
  let F : ℝ := (2 : ℝ)^((64*E-1)*E)
  have hE : 1 ≤ E := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  have hB : 4*B=E := logMomentTop_four m
  have heq : 64*(B*E) = 16*(E*E) := by nlinarith only [congrArg (fun x : ℕ => 16*x*E) hB]
  have hQ : (Q : ℝ) = (2 : ℝ)^(16*(E*E)) := by
    simp only [Q,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,heq]
  have hQN : (Q : ℝ) ≤ F := by
    rw [hQ]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [F]
    have hs := Nat.sub_add_cancel (show 1 ≤ 64*E by omega)
    nlinarith only [hs,hE]
  have hQs : (Q : ℝ)*Real.sqrt N ≤ F := by
    change (Q : ℝ)*Real.sqrt (progressionScaleN (E*E)) ≤ F
    rw [hQ,sqrt_progressionScaleN,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have hs := Nat.sub_add_cancel (show 1 ≤ 64*E by omega)
    nlinarith only [hs,hE]
  have hlogQ : Real.log (Q : ℝ) ≤ 16*(E : ℝ)^2 := by
    have h := log_two_pow_le (64*(B*E))
    rw [heq] at h
    simpa only [Q,progressionScaleN,heq,Nat.cast_mul,Nat.cast_ofNat,pow_two] using h
  have hlogN : Real.log (N : ℝ) ≤ 64*(E : ℝ)^2 := by
    have h := log_two_pow_le (64*(E*E))
    simpa only [N,logMomentX,progressionScaleN,E,Nat.cast_mul,Nat.cast_ofNat,pow_two] using h
  have hlogNat : (Nat.log 2 N : ℝ) = 64*(E : ℝ)^2 := by
    simp only [N,logMomentX,progressionScaleN,Nat.log_pow (by decide : 1 < 2),
      Nat.cast_mul,Nat.cast_ofNat,E,pow_two]
  have hc : ((logMomentModuli m).card : ℝ) ≤ Q := by exact_mod_cast logMomentModuli_card_le m
  have hz : (1 : ℝ) ≤ (E : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) E]
  have hp4 : (E : ℝ)^4 ≤ ((E : ℝ)+1)^11 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 4).trans (pow_le_pow_right₀ hz (by decide))
  have hp2 : (E : ℝ)^2 ≤ ((E : ℝ)+1)^11 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2).trans (pow_le_pow_right₀ hz (by decide))
  have hlift : 4*((logMomentModuli m).card : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q ≤
      4096*((E : ℝ)+1)^11*F := by
    rw [hlogNat]
    calc
      _ ≤ 4*F*(64*(E : ℝ)^2)*(16*(E : ℝ)^2) := by gcongr; exact hc.trans hQN
      _ = 4096*(E : ℝ)^4*F := by ring
      _ ≤ _ := by gcongr
  have hpower : 2*(Q : ℝ)*Real.sqrt N*Real.log N ≤ 128*((E : ℝ)+1)^11*F := by
    calc
      _ = 2*((Q : ℝ)*Real.sqrt N)*Real.log N := by ring
      _ ≤ 2*F*(64*(E : ℝ)^2) := by gcongr
      _ = 128*(E : ℝ)^2*F := by ring
      _ ≤ _ := by gcongr
  have herr := prime_pool_composite_error_le (logMomentModuli m) N Q (logMomentModuli_prime_bound m)
  have hmean := logMoment_primitive_bound m
  change primitivePoolMean (logMomentModuli m) N ≤ 4000000000000*((E : ℝ)+1)^11*F at hmean
  change _ ≤ 5000000000000*((E : ℝ)+1)^11*F
  have hnon : 0 ≤ ((E : ℝ)+1)^11*F := by dsimp [F]; positivity
  nlinarith only [herr,hmean,hlift,hpower,hnon]

lemma logMomentScale_tendsto : Tendsto logMomentScale atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  change m ≤ 2^(m+5)
  exact (Nat.lt_two_pow_self (n := m)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))

lemma logMomentX_tendsto : Tendsto logMomentX atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) logMomentScale_tendsto
  have hE := logMomentScale_ge m
  apply Nat.lt_two_pow_self.le.trans
  apply Nat.pow_le_pow_right (by decide)
  change logMomentScale m ≤ 64*(logMomentScale m*logMomentScale m)
  nlinarith

lemma eventually_logMoment_combined_error_small :
    ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ logMomentModuli m, compositeProgressionError d (logMomentX m))+
        2*(progressionScaleN (logMomentTop m*logMomentScale m) : ℝ)*
          Real.sqrt (logMomentX m)*Real.log (logMomentX m) ≤ (logMomentX m : ℝ)/16 := by
  have hevent := logMomentScale_tendsto.eventually
    (eventually_nat_poly_le_two_pow 1 (16*5000000000000) 11)
  filter_upwards [hevent] with m hm
  let E := logMomentScale m
  have hp : (16*5000000000000 : ℝ)*((E : ℝ)+1)^11 ≤ (2 : ℝ)^E := by
    exact_mod_cast (show (16*5000000000000)*(E+1)^11 ≤ 2^E by simpa only [one_mul] using hm)
  apply (logMoment_combined_error_bound m).trans
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    _ = ((16*5000000000000 : ℝ)*((E : ℝ)+1)^11)*(2 : ℝ)^((64*E-1)*E) := by ring
    _ ≤ (2 : ℝ)^E*(2 : ℝ)^((64*E-1)*E) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      simp only [logMomentX,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      apply congrArg (fun e : ℕ => (2 : ℝ)^e)
      have hE := logMomentScale_ge m
      have hs := Nat.sub_add_cancel (show 1 ≤ 64*E by dsimp [E]; omega)
      change E+(64*E-1)*E = 64*(E*E)
      nlinarith only [hs]

/-- A lower first moment growing at least linearly in the logarithm of the
logarithmic prime scale. No prime-distribution hypothesis is assumed. -/
theorem eventually_shiftedPrimeFactorMangoldt_lower :
    ∀ᶠ m : ℕ in atTop,
      (logMomentX m : ℝ)*(m : ℝ)/8192 ≤ shiftedPrimeFactorMangoldt (logMomentX m) := by
  filter_upwards [logMomentX_tendsto.eventually eventually_mangoldt_nine_tenths,
    eventually_logMoment_combined_error_small,eventually_ge_atTop 4096] with m hpsi herr hm
  let N := logMomentX m
  let W := poolTotientMass (logMomentModuli m)
  have hW : 0 ≤ W := poolTotientMass_nonneg _
  have hmass := logMomentModuli_mass_lower m
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ (9/10 : ℝ)*(N : ℝ) by positivity)
  have htotal := composite_progression_total_lower (logMomentModuli m)
    (fun d hd => (logMomentModuli_prime_bound m d hd).1.pos) N
  change mangoldtSum N*W-(∑ d ∈ logMomentModuli m, compositeProgressionError d N) ≤ _ at htotal
  have hupper := family_progression_le_prime_factor_mean (logMomentModuli m) N
    (progressionScaleN (logMomentTop m*logMomentScale m))
    (Nat.one_le_of_lt (by dsimp [N,logMomentX,progressionScaleN]; positivity))
    (fun d hd => (logMomentModuli_prime_bound m d hd).1) (logMomentModuli_card_le m)
  have hmR : (4096 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNm := mul_le_mul_of_nonneg_left hmR hN
  change (9/10 : ℝ)*(N : ℝ)*W ≤ mangoldtSum N*W at hmain
  change (9/10 : ℝ)*(N : ℝ)*((m : ℝ)/4096) ≤ (9/10 : ℝ)*(N : ℝ)*W at hmass'
  change _ ≤ (N : ℝ)/16 at herr
  change (N : ℝ)*(m : ℝ)/8192 ≤ _
  nlinarith only [hmain,hmass',htotal,hupper,herr,hNm]

end Erdos821
