import FormalConjecturesUtil

/-! A logarithmic-mass bound for smooth integers. This gives an unconditional
small-largest-prime-factor estimate, not orientation cancellation. -/

namespace Erdos371LogSmoothCount

open Filter
open scoped Topology

abbrev P := Nat.maxPrimeFac

lemma factorial_factorization_sum (p N : ℕ) :
    (∑ n ∈ Finset.range (N+1), n.factorization p) = N.factorial.factorization p := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
        Nat.factorization_mul (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
      simp [add_comm]

lemma div_le_factorial_factorization {p : ℕ} (hp : p.Prime) (K : ℕ) :
    K/p ≤ K.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (show Nat.log p K < Nat.log p K + 2 by omega)]
  have hh := Finset.single_le_sum (f := fun i => K/p^i)
    (fun i (_ : i ∈ Finset.Ico 1 (Nat.log p K+2)) => Nat.zero_le _) 
    (show 1 ∈ Finset.Ico 1 (Nat.log p K+2) by simp)
  simpa using hh

lemma log_factorial_prime_sum (K : ℕ) :
    Real.log (K.factorial : ℝ) =
      ∑ p ∈ (K+1).primesBelow, (K.factorial.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    have hn : K.factorial.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    apply Nat.mem_primesBelow.mpr
    constructor
    · by_contra h
      exact hn (Nat.factorization_factorial_eq_zero_of_lt (by omega))
    · by_contra h
      exact hn (Nat.factorization_eq_zero_of_not_prime _ h)
  · simp

lemma prime_log_sum_bound (K : ℕ) :
    (∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ)) ≤ Real.log 4 * K := by
  have he : (K+1).primesBelow = (Finset.Icc 0 K).filter Nat.Prime := by
    ext p
    simp [Nat.primesBelow, Nat.lt_succ_iff]
  have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) K)
  rw [Chebyshev.theta_eq_sum_Icc] at hh
  simpa [he] using hh

lemma prime_log_div_bound {K : ℕ} (hK : 0 < K) :
    (∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ)/(p:ℝ)) ≤ Real.log K + Real.log 4 := by
  have hfac : (∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ) * (K/p : ℕ)) ≤
      (K:ℝ) * Real.log K := by
    calc
      _ ≤ ∑ p ∈ (K+1).primesBelow, (K.factorial.factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Nat.cast_le (α := ℝ).mpr
          (div_le_factorial_factorization (Nat.prime_of_mem_primesBelow hp) K)
        nlinarith [Real.log_natCast_nonneg p]
      _ = Real.log (K.factorial : ℝ) := (log_factorial_prime_sum K).symm
      _ ≤ _ := by
        have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos K))
          (show (K.factorial:ℝ) ≤ (K:ℝ)^K by exact_mod_cast Nat.factorial_le_pow K)
        simpa using hh
  have hsum : (K:ℝ) * (∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ)/(p:ℝ)) ≤
      (∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ) * (K/p : ℕ)) +
      ∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp0 := (Nat.prime_of_mem_primesBelow hp).pos
    have hcast : (K:ℝ) < (p:ℝ) * ((K/p : ℕ)+1) := by
      exact_mod_cast Nat.lt_mul_div_succ K hp0
    have hdiv : (K:ℝ)/(p:ℝ) ≤ (K/p : ℕ)+1 :=
      ((div_lt_iff₀ (Nat.cast_pos.mpr hp0)).mpr (by nlinarith [hcast])).le
    have hh := mul_le_mul_of_nonneg_left hdiv (Real.log_natCast_nonneg p)
    convert hh using 1 <;> ring
  have hh := prime_log_sum_bound K
  have hk : (0:ℝ) < K := Nat.cast_pos.mpr hK
  apply (mul_le_mul_iff_right₀ hk).mp
  nlinarith

lemma log_smooth_expansion {K n : ℕ} (hn : P n ≤ K) :
    Real.log (n:ℝ) = ∑ p ∈ (K+1).primesBelow, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact Nat.mem_primesBelow.mpr ⟨by
      have hh := Nat.le_maxPrimeFac hp.2.2 hp.1 hp.2.1
      change Nat.maxPrimeFac n ≤ K at hn
      omega, hp.1⟩
  · simp

lemma smooth_log_mass_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (∑ n ∈ ((Finset.range (N+1)).filter fun n => P n ≤ K), Real.log (n:ℝ)) ≤
      2 * N * (Real.log K + Real.log 4) := by
  have hexp : (∑ n ∈ ((Finset.range (N+1)).filter fun n => P n ≤ K), Real.log (n:ℝ)) =
      ∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ) *
        ∑ n ∈ ((Finset.range (N+1)).filter fun n => P n ≤ K), (n.factorization p : ℝ) := by
    rw [Finset.sum_congr rfl (fun n hn => log_smooth_expansion (Finset.mem_filter.mp hn).2), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    simp [Finset.mul_sum, mul_comm]
  rw [hexp]
  calc
    _ ≤ ∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ) * (N.factorial.factorization p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
      have hh : (∑ n ∈ ((Finset.range (N+1)).filter fun n => P n ≤ K), n.factorization p) ≤
          ∑ n ∈ Finset.range (N+1), n.factorization p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      rw [factorial_factorization_sum] at hh
      exact_mod_cast hh
    _ ≤ ∑ p ∈ (K+1).primesBelow, 2*N * (Real.log (p:ℝ)/(p:ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := Nat.prime_of_mem_primesBelow hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp1 : (0:ℝ) < (p:ℝ)-1 := by linarith
      have hv : (N.factorial.factorization p : ℝ) ≤ (N:ℝ)/((p:ℝ)-1) := by
        calc
          _ ≤ ((N/(p-1):ℕ):ℝ) := Nat.cast_le.mpr (Nat.factorization_factorial_le_div_pred hprime N)
          _ ≤ (N:ℝ)/(p-1 : ℕ) := Nat.cast_div_le
          _ = _ := by rw [Nat.cast_sub hprime.one_le]; norm_num
      have hfrac : (N:ℝ)/((p:ℝ)-1) ≤ 2*N/(p:ℝ) := by
        apply (div_le_div_iff₀ hp1 (by linarith : (0:ℝ) < p)).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hh := mul_le_mul_of_nonneg_left (hv.trans hfrac) (Real.log_natCast_nonneg p)
      convert hh using 1 <;> ring
    _ = 2*N * ∑ p ∈ (K+1).primesBelow, Real.log (p:ℝ)/(p:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_log_div_bound hK) (by positivity)


lemma smooth_count_log_bound {K N : ℕ} (hK : 0 < K) (hN : 1 < N) :
    (((Finset.range (N+1)).filter fun n => P n ≤ K).card : ℝ) ≤
      Real.sqrt N + 1 + 4*N*(Real.log K + Real.log 4)/Real.log N := by
  classical
  let S := (Finset.range (N+1)).filter fun n => P n ≤ K
  let B := S.filter fun n => Nat.sqrt N < n
  have hsub : S ⊆ Finset.range (Nat.sqrt N+1) ∪ B := by
    intro n hn
    by_cases h : Nat.sqrt N < n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn,h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  have hc : S.card ≤ Nat.sqrt N+1+B.card := by
    have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa using hh
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hmass : (B.card : ℝ) * (Real.log (N:ℝ)/2) ≤ 2*N*(Real.log K+Real.log 4) := by
    calc
      _ = ∑ _n ∈ B, Real.log (N:ℝ)/2 := by simp
      _ ≤ ∑ n ∈ B, Real.log (n:ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := (Finset.mem_filter.mp hn).2
        have hs : N < n*n := Nat.sqrt_lt.mp hh
        have hlog := Real.log_le_log
          (Nat.cast_pos.mpr (show 0 < N by omega))
          (show (N:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast (by nlinarith : N ≤ n^2))
        rw [Real.log_pow] at hlog
        norm_num at hlog
        linarith
      _ ≤ ∑ n ∈ S, Real.log (n:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun n _ _ => Real.log_natCast_nonneg n)
      _ ≤ _ := smooth_log_mass_bound hK N
  have hb : (B.card : ℝ) ≤ 4*N*(Real.log K + Real.log 4)/Real.log N := by
    apply (le_div_iff₀ hl).mpr
    linarith
  have hc' : (S.card : ℝ) ≤ (Nat.sqrt N : ℝ)+1+B.card := by exact_mod_cast hc
  have hsqrt := Real.nat_sqrt_le_real_sqrt (a := N)
  change (S.card : ℝ) ≤ _
  linarith

lemma moving_smooth_count_tendsto_zero (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ)/Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => P n ≤ K N).card : ℝ)/N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => Real.log 4/Real.log (N:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlog)
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N/(N:ℝ)) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hu : Tendsto (fun N : ℕ => (Real.sqrt N+1)/(N:ℝ) +
      4 * (Real.log (K N : ℝ)/Real.log (N:ℝ) + Real.log 4/Real.log (N:ℝ))) atTop (𝓝 0) := by
    simpa [add_div] using (hsqrt.add tendsto_one_div_atTop_nhds_zero_nat).add
      (tendsto_const_nhds.mul (hL.add hsmall))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [hK, eventually_gt_atTop 1] with N hKN hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hc : ((Finset.range N).filter fun n => P n ≤ K N).card ≤
        ((Finset.range (N+1)).filter fun n => P n ≤ K N).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    calc
      _ ≤ (Real.sqrt N+1+4*N*(Real.log (K N : ℝ)+Real.log 4)/Real.log N)/N :=
        div_le_div_of_nonneg_right ((Nat.cast_le.mpr hc).trans (smooth_count_log_bound hKN hN)) hn.le
      _ = _ := by field_simp

lemma subpower_smooth_set_hasDensity_zero (K : ℕ → ℕ) (hmono : Monotone K)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ)/Real.log (N:ℝ)) atTop (𝓝 0)) :
    {n | P n ≤ K n}.HasDensity 0 := by
  have he (N : ℕ) : {n | P n ≤ K n}.partialDensity Set.univ N =
      (((Finset.range N).filter fun n => P n ≤ K n).card : ℝ)/N := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hh : {n | P n ≤ K n} ∩ Set.Iio N =
        ↑((Finset.range N).filter fun n => P n ≤ K n) := by
      ext n
      simp [and_comm]
    rw [hh, Set.ncard_coe_finset]
  change Tendsto (fun N => {n | P n ≤ K n}.partialDensity Set.univ N) _ _
  simp only [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (moving_smooth_count_tendsto_zero K hK hL)
  · intro N
    positivity
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnN,hp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, hp.trans (hmono (Finset.mem_range.mp hnN).le)⟩

end Erdos371LogSmoothCount

#print axioms Erdos371LogSmoothCount.prime_log_div_bound
#print axioms Erdos371LogSmoothCount.smooth_log_mass_bound

#print axioms Erdos371LogSmoothCount.moving_smooth_count_tendsto_zero
#print axioms Erdos371LogSmoothCount.subpower_smooth_set_hasDensity_zero
