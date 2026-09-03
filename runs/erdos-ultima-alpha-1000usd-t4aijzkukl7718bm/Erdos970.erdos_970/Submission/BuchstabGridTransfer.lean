import Submission.BuchstabGridSectors

/-! Transfer of actual node bounds to actual prime sums. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
open scoped Topology

noncomputable def primeUpperExcess (n : ℕ) (L : ℝ) (p : ℕ) : ℝ :=
  (1/(p : ℝ))*(referenceUpper n (primeIndex p) (exp L/(p : ℝ))-1/eulerMass p.primesBelow)

lemma primeUpperExcess_eq_indexed (n k : ℕ) (L : ℝ) :
    primeUpperExcess n L (nthPrime k) = primeMarginal k*
      (referenceUpper n k (exp L*primeMarginal k)-prefixDensity primeMarginal k) := by
  simp only [primeUpperExcess,primeIndex_nthPrime,primeMarginal,nthPrime_prefix_density,mul_one_div]

lemma reference_excess_sum (n k : ℕ) (L : ℝ) :
    (∑ i : Fin k, primeMarginal i.val*(referenceUpper n i.val (exp L*primeMarginal i.val)-
      prefixDensity primeMarginal i.val)) =
      ∑ p ∈ (nthPrime k).primesBelow, primeUpperExcess n L p := by
  rw [← nthPrime_prefix_sum (primeUpperExcess n L) k]
  apply sum_congr rfl
  intro i hi
  exact (primeUpperExcess_eq_indexed n i.val L).symm

lemma reference_deficit_sum (k : ℕ) (L : ℝ) :
    (∑ i : Fin k, primeMarginal i.val*(prefixDensity primeMarginal i.val-
      referenceLower 0 i.val (exp L*primeMarginal i.val))) =
      ∑ p ∈ (nthPrime k).primesBelow, primeLowerDeficit L p := by
  rw [← nthPrime_prefix_sum (primeLowerDeficit L) k]
  apply sum_congr rfl
  intro i hi
  exact (primeLowerDeficit_eq_indexed i.val L).symm

lemma primeUpperExcess_zero (L : ℝ) (p : ℕ) (hp : p.Prime) :
    primeUpperExcess 0 L p = scaledPrimeExcess L p := by
  rw [← nthPrime_primeIndex p hp,primeUpperExcess_eq_indexed,scaledPrimeExcess_eq_indexed]
  rfl

lemma primeUpperExcess_nonneg (n : ℕ) (L : ℝ) (p : ℕ) (hp : p.Prime) :
    0 ≤ primeUpperExcess n L p := by
  have hh := (reference_density_bounds n (primeIndex p) (exp L/(p : ℝ))).2
  rw [density_primeIndex p hp] at hh
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hh)

lemma primeLowerDeficit_nonneg (L : ℝ) (p : ℕ) (hp : p.Prime) :
    0 ≤ primeLowerDeficit L p := by
  have hh := (reference_density_bounds 0 (primeIndex p) (exp L/(p : ℝ))).1
  rw [density_primeIndex p hp] at hh
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hh)

lemma referenceUpper_succ_le (n k : ℕ) (D : ℝ) : referenceUpper (n+1) k D ≤ referenceUpper n k D :=
  upperMain_succ_le _ _ _ _ _ _

lemma primeUpperExcess_succ_le (n : ℕ) (L : ℝ) (p : ℕ) :
    primeUpperExcess (n+1) L p ≤ primeUpperExcess n L p :=
  mul_le_mul_of_nonneg_left (sub_le_sub_right (referenceUpper_succ_le n _ _) _) (by positivity)

lemma primeUpperExcess_le_zero (n : ℕ) (L : ℝ) (p : ℕ) :
    primeUpperExcess n L p ≤ primeUpperExcess 0 L p := by
  induction n with
  | zero => rfl
  | succ n ih => exact (primeUpperExcess_succ_le n L p).trans ih

lemma primeUpperExcess_bin_bound (n : ℕ) (L B : ℝ) (j p : ℕ)
    (hp : p ∈ gridPrimeBin L j)
    (hnode : referenceUpper n (primeIndex p) (exp (((j : ℝ)/50)*log (p : ℝ))) ≤
      (1/eulerMass p.primesBelow)*B) :
    primeUpperExcess n L p ≤ (B-1)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  have hh := ((referenceUpper_antitone n (primeIndex p)) (gridPrimeBin_child_level L j p hp)).trans hnode
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hh (1/eulerMass p.primesBelow))
    (show (0 : ℝ) ≤ 1/(p : ℝ) by positivity)
  convert hm using 1
  <;> ring

lemma primeLowerDeficit_bin_bound (L B : ℝ) (j p : ℕ)
    (hp : p ∈ gridPrimeBin L j)
    (hnode : (1/eulerMass p.primesBelow)*B ≤
      referenceLower 0 (primeIndex p) (exp (((j : ℝ)/50)*log (p : ℝ)))) :
    primeLowerDeficit L p ≤ (1-B)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  have hh := hnode.trans ((referenceLower_monotone 0 (primeIndex p)) (gridPrimeBin_child_level L j p hp))
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hh (1/eulerMass p.primesBelow))
    (show (0 : ℝ) ≤ 1/(p : ℝ) by positivity)
  convert hm using 1
  <;> ring

lemma eventually_grid_primes_large (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, j < 600 → ∀ p ∈ gridPrimeBin (s*L) j, N ≤ p := by
  have hh := (expFloor_tendsto (s/13) (by positivity)).eventually_ge_atTop N
  filter_upwards [hh,eventually_ge_atTop (0 : ℝ)] with L hN hL j hj p hp
  rw [← tailPrimeCut_scaled] at hN
  exact hN.trans (gridPrimeBin_above_tail (s*L) (mul_nonneg hs.le hL) j p hj hp).le

lemma eventually_upper_grid_bins (n a b N : ℕ) (hb : b ≤ 600) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico a b,
      referenceUpper n k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))) ≤ prefixDensity primeMarginal k*B j)
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ Ico a b, ∀ p ∈ gridPrimeBin (s*L) j,
      primeUpperExcess n (s*L) p ≤ (B j-1)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  filter_upwards [eventually_grid_primes_large s hs N] with L hL j hj p hp
  have hpp := (mem_filter.mp hp).2
  apply primeUpperExcess_bin_bound n (s*L) (B j) j p hp
  have hh := hgrid (primeIndex p) (by
    rw [nthPrime_primeIndex p hpp]
    exact hL j ((mem_Ico.mp hj).2.trans_le hb) p hp) j hj
  simpa only [nthPrime_primeIndex p hpp,density_primeIndex p hpp] using hh

lemma eventually_lower_grid_bins (a b N : ℕ) (hb : b ≤ 600) (B : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, N ≤ nthPrime k → ∀ j ∈ Ico a b,
      prefixDensity primeMarginal k*B j ≤ referenceLower 0 k (exp (((j : ℝ)/50)*log (nthPrime k : ℝ))))
    (s : ℝ) (hs : 0 < s) :
    ∀ᶠ L : ℝ in atTop, ∀ j ∈ Ico a b, ∀ p ∈ gridPrimeBin (s*L) j,
      primeLowerDeficit (s*L) p ≤ (1-B j)*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
  filter_upwards [eventually_grid_primes_large s hs N] with L hL j hj p hp
  have hpp := (mem_filter.mp hp).2
  apply primeLowerDeficit_bin_bound (s*L) (B j) j p hp
  have hh := hgrid (primeIndex p) (by
    rw [nthPrime_primeIndex p hpp]
    exact hL j ((mem_Ico.mp hj).2.trans_le hb) p hp) j hj
  simpa only [nthPrime_primeIndex p hpp,density_primeIndex p hpp] using hh

/-- Finite bins plus a separately proved tail bound control the complete
strict-prefix sum. Both normalizations are compared, never identified. -/
theorem exists_grid_total_bound (a : ℕ) (ha : 50 ≤ a) (ha' : a ≤ 650)
    (f : ℝ → ℕ → ℝ) (hf : ∀ L p, p.Prime → 0 ≤ f L p) (T : ℝ) (c : ℕ → ℝ)
    (htail : ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k →
      eulerMass (nthPrime k).primesBelow*(∑ p ∈ smallPrimePart k (((a : ℝ)/50)*log (nthPrime k : ℝ)),
        f (((a : ℝ)/50)*log (nthPrime k : ℝ)) p) ≤ T/((a : ℝ)/50))
    (hbound : ∀ᶠ L : ℝ in atTop, ∀ j ∈ Ico (a-50) 600, ∀ p ∈ gridPrimeBin (((a : ℝ)/50)*L) j,
      f (((a : ℝ)/50)*L) p ≤ c j*((1/(p : ℝ))*(1/eulerMass p.primesBelow)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k → eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ (nthPrime k).primesBelow, f (((a : ℝ)/50)*log (nthPrime k : ℝ)) p) <
      (T+(∑ j ∈ Ico (a-50) 600, c j/50))/((a : ℝ)/50)+ε := by
  have haR : (50 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (0 : ℝ) < (a : ℝ)/50 := by linarith
  obtain ⟨N,hN⟩ := htail
  have hsec := eventually_grid_sector_upper ((a : ℝ)/50) hs (a-50) 600 c
    (fun L p => f (((a : ℝ)/50)*L) p) hbound ε hε
  have hlog : Tendsto (fun p : ℕ => log (p : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlog.eventually hsec)
  refine ⟨max M N,fun k hk => ?_⟩
  have hpart := prime_prefix_le_tail_add_bins k a ha ha' (f (((a : ℝ)/50)*log (nthPrime k : ℝ))) (hf _)
  have hp := nthPrime_prime k
  have hE := (eulerMass_pos (nthPrime k).primesBelow (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  have hpart' := mul_le_mul_of_nonneg_left hpart hE
  rw [mul_add] at hpart'
  have ht := hN k ((le_max_right _ _).trans hk)
  have hb := hM (nthPrime k) ((le_max_left _ _).trans hk)
  have he : expFloor 1 (log (nthPrime k : ℝ)) = nthPrime k := by
    rw [expFloor,one_mul,exp_log (by exact_mod_cast hp.pos),Nat.floor_natCast]
  rw [he] at hb
  have hnonneg : 0 ≤ ∑ j ∈ Ico (a-50) 600,
      ∑ p ∈ gridPrimeBin (((a : ℝ)/50)*log (nthPrime k : ℝ)) j,
        f (((a : ℝ)/50)*log (nthPrime k : ℝ)) p :=
    sum_nonneg (fun j _ => sum_nonneg (fun p hp => hf _ p (mem_filter.mp hp).2))
  have hmass := mul_le_mul_of_nonneg_right (eulerMass_strict_prefix_le (nthPrime k) hp) hnonneg
  change eulerMass (nthPrime k).primesBelow* _ ≤ initialEulerMass (nthPrime k)*_ at hmass
  have hh := hpart'.trans_lt (add_lt_add_of_le_of_lt ht (hmass.trans_lt hb))
  convert hh using 1
  ring

#print axioms primeUpperExcess_bin_bound
#print axioms primeLowerDeficit_bin_bound
#print axioms exists_grid_total_bound
end Erdos970.RecursiveSieve.Buchstab
