import FormalConjecturesUtil
import Submission.CroppedEnergy

/-! A harmonic counting bound for small largest-prime cofactors, with a growing
cutoff criterion. The signed energy estimate in the criterion is a hypothesis. -/

namespace Erdos371GrowingCofactor

open Erdos371PrimeDiscrepancy Erdos371CroppedEnergy Erdos371PrimeEnergy Filter
open scoped Topology

private def products (K N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).biUnion fun k => ((N/k+1).primesBelow.image fun p => k*p)

lemma cofactor_count_le_prime_sum (K N : ℕ) :
    ((Finset.range (N+1)).filter fun n => n/P n ≤ K).card ≤
      2 + ∑ k ∈ Finset.Icc 1 K, Nat.primeCounting (N/k) := by
  classical
  have hsub : (Finset.range (N+1)).filter (fun n => n/P n ≤ K) ⊆
      insert 0 (insert 1 (products K N)) := by
    intro n hn
    obtain ⟨hnN, hnK⟩ := Finset.mem_filter.mp hn
    by_cases hn0 : n = 0
    · simp [hn0]
    by_cases hn1 : n = 1
    · simp [hn1]
    have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
    have hk : 0 < n/P n := Nat.div_pos Nat.maxPrimeFac_le hp.pos
    have hm : n/P n * P n = n := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨n/P n, Finset.mem_Icc.mpr ⟨hk, hnK⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨P n, Nat.mem_primesBelow.mpr ⟨?_, hp⟩, hm⟩
    have hb : P n ≤ N/(n/P n) := (Nat.le_div_iff_mul_le hk).mpr (by
      have := Finset.mem_range.mp hnN
      nlinarith [hm])
    omega
  have hc : (products K N).card ≤ ∑ k ∈ Finset.Icc 1 K, Nat.primeCounting (N/k) := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro k hk
    calc
      _ ≤ (N/k+1).primesBelow.card := Finset.card_image_le
      _ = Nat.primeCounting (N/k) := by rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  have h1 := Finset.card_insert_le 0 (insert 1 (products K N))
  have h2 := Finset.card_insert_le 1 (products K N)
  have h3 := Finset.card_le_card hsub
  omega

lemma badCount_le_prime_sum (K N : ℕ) :
    badCount K N ≤ 4 + 2 * ∑ k ∈ Finset.Icc 1 K, (Nat.primeCounting (N/k) : ℝ) := by
  classical
  let A := (Finset.range (N+1)).filter fun n => n/P n ≤ K
  let B := (Finset.range N).filter fun n => n/P n ≤ K
  let C := (Finset.range N).filter fun n => (n+1)/P (n+1) ≤ K
  have hB : B.card ≤ A.card := Finset.card_le_card (by
    intro n hn
    obtain ⟨hnN, hnK⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hnN
      omega), hnK⟩)
  have hC : C.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn (fun n => n+1)
    · intro n hn
      change n ∈ C at hn
      change n+1 ∈ A
      obtain ⟨hnN, hnK⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hnN
        omega), hnK⟩
    · intro n hn m hm he
      change n+1 = m+1 at he
      omega
  have he : ((Finset.range N).filter fun n => n/P n ≤ K ∨ (n+1)/P (n+1) ≤ K) = B ∪ C := by
    ext n
    simp [B, C, and_or_left]
  have hh := Finset.card_union_le B C
  have hA := cofactor_count_le_prime_sum K N
  have hb : ((Finset.range N).filter fun n => n/P n ≤ K ∨ (n+1)/P (n+1) ≤ K).card ≤
      4 + 2 * ∑ k ∈ Finset.Icc 1 K, Nat.primeCounting (N/k) := by
    rw [he]
    change A.card ≤ _ at hA
    omega
  unfold badCount
  exact_mod_cast hb

lemma prime_sum_harmonic_bound {K N M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : 2 ≤ M) (hNM : M ≤ N/K)
    (hb : ∀ m : ℕ, M ≤ m → (Nat.primeCounting m : ℝ) ≤ C*m/Real.log m) :
    (∑ k ∈ Finset.Icc 1 K, (Nat.primeCounting (N/k) : ℝ)) ≤
      C*N/Real.log (N/K : ℕ) * (1 + Real.log K) := by
  have hlog : 0 < Real.log (N/K : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N/K))
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, C*N/Real.log (N/K : ℕ) * (1/(k:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
      have hk0 : 0 < k := hk1
      have hdiv : N/K ≤ N/k := Nat.div_le_div_left hkK hk0
      have hlogk : Real.log (N/K : ℕ) ≤ Real.log (N/k : ℕ) :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < N/K)) (Nat.cast_le.mpr hdiv)
      calc
        _ ≤ C*(N/k : ℕ)/Real.log (N/k : ℕ) := hb _ (hNM.trans hdiv)
        _ ≤ C*(N/k : ℕ)/Real.log (N/K : ℕ) :=
          div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg _)) hlog hlogk
        _ ≤ C*((N:ℝ)/k)/Real.log (N/K : ℕ) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left Nat.cast_div_le hC) hlog.le
        _ = _ := by ring
    _ = C*N/Real.log (N/K : ℕ) * ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hlog.le)
      have hh := harmonic_le_one_add_log K
      rw [harmonic_eq_sum_Icc] at hh
      simpa [one_div] using hh

lemma badCount_log_bound {K N M : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : 2 ≤ M) (hNM : M ≤ N/K)
    (hb : ∀ m : ℕ, M ≤ m → (Nat.primeCounting m : ℝ) ≤ C*m/Real.log m) :
    badCount K N ≤ 4 + 2*C*N/Real.log (N/K : ℕ) * (1 + Real.log K) := by
  have hh := prime_sum_harmonic_bound hC hM hNM hb
  have h := badCount_le_prime_sum K N
  have he : 2*C*N/Real.log (N/K : ℕ) * (1 + Real.log K) =
      2 * (C*N/Real.log (N/K : ℕ) * (1 + Real.log K)) := by ring
  rw [he]
  linarith


lemma badCount_growing_mean_tendsto_zero (K : ℕ → ℕ)
    (hdiv : Tendsto (fun N => N/K N) atTop atTop)
    (hlog : Tendsto (fun N => (1 + Real.log (K N : ℝ)) / Real.log (N/K N : ℕ))
      atTop (𝓝 0)) :
    Tendsto (fun N => badCount (K N) N / N) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ᶠ m : ℕ in atTop, (Nat.primeCounting m : ℝ) ≤ C*m/Real.log m := by
    simpa [C] using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hb
  have hu : Tendsto (fun N : ℕ => 4/(N:ℝ) + 2*C *
      ((1 + Real.log (K N : ℝ)) / Real.log (N/K N : ℕ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ)).add
      (tendsto_const_nhds.mul hlog)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => by unfold badCount; positivity
  · filter_upwards [hdiv.eventually (eventually_ge_atTop (max M 2)), eventually_gt_atTop 0]
      with N hNM hN
    have hh := badCount_log_bound hC (le_max_right M 2) hNM
      (fun m hm => hM m ((le_max_left M 2).trans hm))
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hl : 0 < Real.log (N/K N : ℕ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N/K N))
    calc
      _ ≤ (4 + 2*C*N/Real.log (N/K N : ℕ) * (1 + Real.log (K N : ℝ)))/N :=
        div_le_div_of_nonneg_right hh hn.le
      _ = _ := by field_simp

/-- A subpolynomial growing cofactor cutoff can absorb more than one logarithm
of energy loss. All asymptotic assumptions are explicit. -/
theorem density_half_of_growing_cutoff (K : ℕ → ℕ)
    (hdiv : Tendsto (fun N => N/K N) atTop atTop)
    (hlog : Tendsto (fun N => (1 + Real.log (K N : ℝ)) / Real.log (N/K N : ℕ))
      atTop (𝓝 0))
    (hE : Tendsto (fun N => energy N / ((N:ℝ) * K N)) atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  have hpc : ∀ m : ℕ, (Nat.primeCounting m : ℝ) ≤ m+1 := by
    intro m
    have hh : (m+1).primesBelow.card ≤ m+1 := by
      apply (Finset.card_le_card (show (m+1).primesBelow ⊆ Finset.range (m+1) from
        fun p hp => Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1)).trans
      simp
    rw [Nat.primesBelow_card_eq_primeCounting'] at hh
    change Nat.primeCounting m ≤ m+1 at hh
    exact_mod_cast hh
  have hpE : Tendsto (fun N =>
      (Nat.primeCounting (N/K N) : ℝ) * energy N / (N:ℝ)^2) atTop (𝓝 0) := by
    have hu : Tendsto (fun N => 2 * (energy N / ((N:ℝ)*K N))) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hE
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Eventually.of_forall fun N =>
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg N)) (sq_nonneg _)
    · filter_upwards [hdiv.eventually (eventually_ge_atTop 1), eventually_gt_atTop 0]
        with N hNM hN
      have hK : 0 < K N := by
        by_contra h
        have hh : K N = 0 := by omega
        simp [hh] at hNM
      have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
      have hsmall : (Nat.primeCounting (N/K N) : ℝ) ≤ 2 * ((N:ℝ)/K N) := by
        calc
          _ ≤ ((N/K N : ℕ):ℝ)+1 := hpc _
          _ ≤ 2 * ((N/K N : ℕ):ℝ) := by
            have hh : (1:ℝ) ≤ (N/K N : ℕ) := by exact_mod_cast hNM
            linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
      calc
        _ ≤ (2*((N:ℝ)/K N))*energy N/(N:ℝ)^2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (energy_nonneg N)) (sq_nonneg _)
        _ = _ := by field_simp
  have hsqrt : Tendsto (fun N => Real.sqrt (Nat.primeCounting (N/K N) * energy N) / (N:ℝ))
      atTop (𝓝 0) := by
    have hh := hpE.sqrt
    simp only [Real.sqrt_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg N)),
      Real.sqrt_sq (Nat.cast_nonneg N)]
  have hbad := badCount_growing_mean_tendsto_zero K hdiv hlog
  have hu : Tendsto (fun N : ℕ => 1/(N:ℝ) +
      Real.sqrt (Nat.primeCounting (N/K N) * energy N) / (N:ℝ) + badCount (K N) N/N)
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.add hsqrt).add hbad
  apply density_half_iff_total_mean_zero.mpr
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N => abs_nonneg _
  · filter_upwards [hdiv.eventually (eventually_ge_atTop 1), eventually_gt_atTop 0]
      with N hNM hN
    have hK : 0 < K N := by
      by_contra h
      have hh : K N = 0 := by omega
      simp [hh] at hNM
    have hh := div_le_div_of_nonneg_right (total_abs_cropped_bound hK hN) (Nat.cast_nonneg (α := ℝ) N)
    simpa [add_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] using hh

end Erdos371GrowingCofactor

#print axioms Erdos371GrowingCofactor.cofactor_count_le_prime_sum
#print axioms Erdos371GrowingCofactor.badCount_log_bound

#print axioms Erdos371GrowingCofactor.badCount_growing_mean_tendsto_zero
#print axioms Erdos371GrowingCofactor.density_half_of_growing_cutoff
