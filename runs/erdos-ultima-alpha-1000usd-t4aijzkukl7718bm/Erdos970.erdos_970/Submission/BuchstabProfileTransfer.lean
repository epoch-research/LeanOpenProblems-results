import Submission.BuchstabProfileSectors

/-! Actual finite-prime transfer for arbitrary profile partitions. Every omitted
tail and every finite-sector slack is charged explicitly. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1000000

lemma eventually_profile_primes_large (s : ℝ) (hs : 0 < s) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : 0 ≤ v 0) (N H : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N, ∀ p ∈ profileBin (s*L) (v j) (v (j+1)), H ≤ p := by
  have hvN : 0 ≤ v N := hv0.trans (hv (Nat.zero_le N))
  have hh := (expFloor_tendsto (s/(v N+1)) (div_pos hs (by linarith))).eventually_ge_atTop H
  filter_upwards [hh,eventually_ge_atTop (0 : ℝ)] with L hL hL0 j hj p hp
  have hjN : j+1 ≤ N := by have := mem_range.mp hj; omega
  have hcut := profileCut_antitone (s*L) (v (j+1)) (v N) (mul_nonneg hs.le hL0)
    (hv0.trans (hv (Nat.zero_le _))) (hv hjN)
  have hplow := (mem_Ioc.mp (mem_filter.mp hp).1).1
  rw [profileCut_scaled] at hcut
  exact hL.trans (hcut.trans_lt hplow).le

lemma profile_upper_bin_bound (n : ℕ) (L a b B : ℝ) (ha : 0 ≤ a) (p : ℕ)
    (hp : p ∈ profileBin L a b)
    (hnode : referenceUpper n (primeIndex p) (exp (a*log (p : ℝ))) ≤ (1/eulerMass p.primesBelow)*B) :
    primeUpperExcess n L p ≤ (B-1)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  have hh := ((referenceUpper_antitone n (primeIndex p)) (profileBin_child_level L a b ha p hp)).trans hnode
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hh (1/eulerMass p.primesBelow))
    (show (0 : ℝ) ≤ 1/(p : ℝ) by positivity)
  convert hm using 1 <;> ring

lemma profile_lower_bin_bound (n : ℕ) (L a b B : ℝ) (ha : 0 ≤ a) (p : ℕ)
    (hp : p ∈ profileBin L a b)
    (hnode : (1/eulerMass p.primesBelow)*B ≤ referenceLower n (primeIndex p) (exp (a*log (p : ℝ)))) :
    primeDeficit n L p ≤ (1-B)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  have hh := hnode.trans ((referenceLower_monotone n (primeIndex p)) (profileBin_child_level L a b ha p hp))
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hh (1/eulerMass p.primesBelow))
    (show (0 : ℝ) ≤ 1/(p : ℝ) by positivity)
  convert hm using 1 <;> ring

lemma eventually_profile_upper_bins (n H : ℕ) (s : ℝ) (hs : 0 < s) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : 0 ≤ v 0) (N : ℕ) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, H ≤ nthPrime k → ∀ j ∈ range N,
      referenceUpper n k (exp (v j*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*B j) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N, ∀ p ∈ profileBin (s*L) (v j) (v (j+1)),
      primeUpperExcess n (s*L) p ≤ (B j-1)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  filter_upwards [eventually_profile_primes_large s hs v hv hv0 N H] with L hL j hj p hp
  have hpp := (mem_filter.mp hp).2
  apply profile_upper_bin_bound n (s*L) _ _ _ (hv0.trans (hv (Nat.zero_le j))) p hp
  have hh := hgrid (primeIndex p) (by rw [nthPrime_primeIndex p hpp]; exact hL j hj p hp) j hj
  simpa only [nthPrime_primeIndex p hpp,density_primeIndex p hpp] using hh

lemma eventually_profile_lower_bins (n H : ℕ) (s : ℝ) (hs : 0 < s) (v : ℕ → ℝ)
    (hv : Monotone v) (hv0 : 0 ≤ v 0) (N : ℕ) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, H ≤ nthPrime k → ∀ j ∈ range N,
      prefixDensity primeMarginal k*B j ≤ referenceLower n k (exp (v j*log (nthPrime k : ℝ)))) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N, ∀ p ∈ profileBin (s*L) (v j) (v (j+1)),
      primeDeficit n (s*L) p ≤ (1-B j)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  filter_upwards [eventually_profile_primes_large s hs v hv hv0 N H] with L hL j hj p hp
  have hpp := (mem_filter.mp hp).2
  apply profile_lower_bin_bound n (s*L) _ _ _ (hv0.trans (hv (Nat.zero_le j))) p hp
  have hh := hgrid (primeIndex p) (by rw [nthPrime_primeIndex p hpp]; exact hL j hj p hp) j hj
  simpa only [nthPrime_primeIndex p hpp,density_primeIndex p hpp] using hh

/-- General finite-sector transfer, with the terminal tail kept separate. -/
theorem exists_profile_total_bound (s M : ℝ) (hs : 1 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0=s-1) (N : ℕ) (hvN : v N=M-1)
    (f : ℝ → ℕ → ℝ) (hf : ∀ L p, p.Prime → 0 ≤ f L p) (T : ℝ) (c : ℕ → ℝ)
    (htail : ∃ H : ℕ, ∀ k : ℕ, H ≤ nthPrime k →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), f (s*log (nthPrime k : ℝ)) p) ≤ T/s)
    (hbound : ∀ᶠ L : ℝ in atTop, ∀ j ∈ range N, ∀ p ∈ profileBin (s*L) (v j) (v (j+1)),
      f (s*L) p ≤ c j*((1/(p : ℝ))*(1/eulerMass p.primesBelow)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ k : ℕ, H ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, f (s*log (nthPrime k : ℝ)) p) <
      (T+(∑ j ∈ range N, c j*(v (j+1)-v j)))/s+ε := by
  have hs0 : 0 < s := by linarith
  have hstart : 0 ≤ v 0 := by rw [hv0]; linarith
  obtain ⟨H,hH⟩ := htail
  have hsec := eventually_profile_sector_upper s hs0 v hv hstart N c (fun L p => f (s*L) p) hbound ε hε
  have hlog : Tendsto (fun p : ℕ => log (p : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hlog.eventually hsec)
  refine ⟨max J H,fun k hk => ?_⟩
  have hpart := prime_prefix_le_terminal_add_profile s M hs k v hv hv0 N hvN
    (f (s*log (nthPrime k : ℝ))) (hf _)
  have hp := nthPrime_prime k
  have hE := (eulerMass_pos (nthPrime k).primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  have hpart' := mul_le_mul_of_nonneg_left hpart hE
  rw [mul_add] at hpart'
  have ht := hH k ((le_max_right _ _).trans hk)
  have hb := hJ (nthPrime k) ((le_max_left _ _).trans hk)
  have he : expFloor 1 (log (nthPrime k : ℝ)) = nthPrime k := by
    rw [expFloor,one_mul,exp_log (by exact_mod_cast hp.pos),Nat.floor_natCast]
  rw [he] at hb
  have hnonneg : 0 ≤ ∑ j ∈ range N,
      ∑ p ∈ profileBin (s*log (nthPrime k : ℝ)) (v j) (v (j+1)), f (s*log (nthPrime k : ℝ)) p :=
    sum_nonneg (fun j _ => sum_nonneg (fun p hp => hf _ p (mem_filter.mp hp).2))
  have hmass := mul_le_mul_of_nonneg_right (eulerMass_strict_prefix_le (nthPrime k) hp) hnonneg
  change eulerMass (nthPrime k).primesBelow* _ ≤ initialEulerMass (nthPrime k)*_ at hmass
  have hh := hpart'.trans_lt (add_lt_add_of_le_of_lt ht (hmass.trans_lt hb))
  convert hh using 1
  ring

/-- Arbitrary upper-profile nodes control the actual complete upper excess. -/
theorem exists_profile_upper_excess_bound (n H N : ℕ) (s M : ℝ) (hs : 1 ≤ s) (hM : 13 ≤ M)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0=s-1) (hvN : v N=M-1) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, H ≤ nthPrime k → ∀ j ∈ range N,
      referenceUpper n k (exp (v j*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*B j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ k : ℕ, J ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess n (s*log (nthPrime k : ℝ)) p) <
      (terminalAllowance initialTailCoefficient M+(∑ j ∈ range N, (B j-1)*(v (j+1)-v j)))/s+ε := by
  obtain ⟨J,hJ⟩ := exists_variable_upper_tail M hM
  exact exists_profile_total_bound s M hs v hv hv0 N hvN (primeUpperExcess n) (primeUpperExcess_nonneg n)
    (terminalAllowance initialTailCoefficient M) (fun j => B j-1) ⟨J,fun k hk => hJ n k hk s hs⟩
    (eventually_profile_upper_bins n H s (by linarith) v hv (by rw [hv0]; linarith) N B hgrid) ε hε

/-- Arbitrary lower-profile nodes control the actual complete lower deficit. -/
theorem exists_profile_lower_deficit_bound (n H N : ℕ) (s M : ℝ) (hs : 1 ≤ s) (hM : 13 ≤ M)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0=s-1) (hvN : v N=M-1) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, H ≤ nthPrime k → ∀ j ∈ range N,
      prefixDensity primeMarginal k*B j ≤ referenceLower n k (exp (v j*log (nthPrime k : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ k : ℕ, J ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, primeDeficit n (s*log (nthPrime k : ℝ)) p) <
      (terminalAllowance lowerTailCoefficient M+(∑ j ∈ range N, (1-B j)*(v (j+1)-v j)))/s+ε := by
  obtain ⟨J,hJ⟩ := exists_variable_lower_tail M hM
  exact exists_profile_total_bound s M hs v hv hv0 N hvN (primeDeficit n) (primeDeficit_nonneg n)
    (terminalAllowance lowerTailCoefficient M) (fun j => 1-B j) ⟨J,fun k hk => hJ n k hk s hs⟩
    (eventually_profile_lower_bins n H s (by linarith) v hv (by rw [hv0]; linarith) N B hgrid) ε hε

#print axioms exists_profile_upper_excess_bound
#print axioms exists_profile_lower_deficit_bound
end Erdos970.RecursiveSieve.Buchstab
