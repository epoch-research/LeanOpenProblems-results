import Submission.OccupiedPowerPrimeBlocks

/-! Blocks with more than a prescribed fixed number of active primes.
The individual mass budget does not grow with the number of blocks. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def thinPrimeBlockCount (P : Finset ℕ) (k N : ℕ) : ℕ :=
  ((range N).filter (fun n => (activeBlockPrimes P (activePrimeAtoms P n)).card ≤ k)).card

lemma primeDivisorCount_le_activeBlock (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    primeDivisorCountIn P (n+1) ≤ (activeBlockPrimes P (activePrimeAtoms P n)).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hpP,hpd⟩ := mem_filter.mp hp
  rw [activeBlockPrimes_arithmetic P hP n]
  exact mem_filter.mpr ⟨hpP,dvd_mul_of_dvd_right hpd n⟩

lemma thinPrimeBlockCount_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k N : ℕ) (hN : 0 < N) (hA : 0 < primeReciprocalMass P)
    (hk : (k : ℝ) ≤ primeReciprocalMass P/2) :
    (thinPrimeBlockCount P k N : ℝ)/N ≤
      4/primeReciprocalMass P+8*P.card/((N : ℝ)*primeReciprocalMass P) := by
  have hs : (range N).filter (fun n => (activeBlockPrimes P (activePrimeAtoms P n)).card ≤ k) ⊆
      (range N).filter (fun n => (primeDivisorCountIn P (n+1) : ℝ) ≤ primeReciprocalMass P/2) := by
    intro n hn
    obtain ⟨hn,hc⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn,?_⟩
    have hh : (primeDivisorCountIn P (n+1) : ℝ) ≤ k := by
      exact_mod_cast (primeDivisorCount_le_activeBlock P hP n).trans hc
    exact hh.trans hk
  exact (div_le_div_of_nonneg_right (show (thinPrimeBlockCount P k N : ℝ) ≤
      ((range N).filter (fun n => (primeDivisorCountIn P (n+1) : ℝ) ≤ primeReciprocalMass P/2)).card by
        exact_mod_cast card_le_card hs) (Nat.cast_nonneg N)).trans
    (primeDivisorCountIn_low_count_bound P hP N hN hA)

lemma iteratedPrimeBlock_mass_upper (t J i : ℕ) (ht : 1 < t)
    (hlog : 2 ≤ Real.log t/Real.log 2) :
    2*primeReciprocalMass (iteratedPrimeBlock t J i) ≤ 16*(2^J : ℕ) := by
  have hbase := blockCutoff_base_le t J i (by omega)
  have hlogi : 2 ≤ Real.log (blockCutoff t J i)/Real.log 2 := by
    refine hlog.trans (div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by norm_num)))
    exact Real.log_le_log (by exact_mod_cast (show 0 < t by omega)) (by exact_mod_cast hbase)
  change 2*primeReciprocalMass (largePrimeSet (blockCutoff t J i) (blockCutoff t J (i+1))) ≤ _
  rw [blockCutoff_step]
  simpa only [blockCutoff,Nat.mul_one] using
    iteratedPrimeBlocks_total_mass (blockCutoff t J i) J 1 (ht.trans_le hbase) hlogi

lemma iteratedPrimeBlock_thin_bound (t J K i k N : ℕ) (ht : 1 < t) (hJ : 0 < J)
    (hk : 8*k ≤ J) (hN : 0 < N) (hi : i < K)
    (hlog : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log t) :
    (thinPrimeBlockCount (iteratedPrimeBlock t J i) k N : ℝ)/N ≤
      16/(J : ℝ)+32*(blockCutoff t J K+1 : ℝ)/((N : ℝ)*J) := by
  have hm := iteratedPrimeBlock_mass_lower t J i ht hlog
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass : 0 < primeReciprocalMass (iteratedPrimeBlock t J i) := lt_of_lt_of_le (by positivity) hm
  have hkr : (k : ℝ) ≤ primeReciprocalMass (iteratedPrimeBlock t J i)/2 := by
    have hh : 8*(k : ℝ) ≤ J := by exact_mod_cast hk
    linarith
  have hprimes (p : ℕ) (hp : p ∈ iteratedPrimeBlock t J i) := ((mem_largePrimeSet_iff p _ _).mp hp).1
  have hcard : (iteratedPrimeBlock t J i).card ≤ blockCutoff t J K+1 := by
    apply (card_le_card _).trans_eq (card_range _)
    intro p hp
    have h := ((mem_largePrimeSet_iff p _ _).mp
      (iteratedPrimeBlock_subset t J i K (by omega) hi hp)).2.2
    exact mem_range.mpr (by omega)
  have hcardr : ((iteratedPrimeBlock t J i).card : ℝ) ≤ blockCutoff t J K+1 := by exact_mod_cast hcard
  calc
    _ ≤ 4/primeReciprocalMass (iteratedPrimeBlock t J i)+
        8*(iteratedPrimeBlock t J i).card/((N : ℝ)*primeReciprocalMass (iteratedPrimeBlock t J i)) :=
      thinPrimeBlockCount_bound _ hprimes k N hN hmass hkr
    _ ≤ 4/((J : ℝ)/4)+8*(blockCutoff t J K+1 : ℝ)/((N : ℝ)*((J : ℝ)/4)) := by gcongr
    _ = _ := by field_simp; ring

/-- The same power-block construction works for any fixed occupancy
threshold. Upper mass bounds are supplied both for each block and the band. -/
theorem exists_thick_power_prime_blocks (J K k : ℕ) (hJ : 0 < J) (hk : 8*k ≤ J)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ u : ℝ, 0 < u ∧ u ≤ α ∧ ∃ t : ℕ → ℕ, ∀ᶠ N : ℕ in atTop,
      1 < t N ∧ (N : ℝ)^u ≤ t N ∧ (blockCutoff (t N) J K : ℝ) ≤ (N : ℝ)^α ∧
      2*primeReciprocalMass (largePrimeSet (t N) (blockCutoff (t N) J K)) ≤ 16*(2^(J*K) : ℕ) ∧
      ∀ i < K, 2*primeReciprocalMass (iteratedPrimeBlock (t N) J i) ≤ 16*(2^J : ℕ) ∧
        (thinPrimeBlockCount (iteratedPrimeBlock (t N) J i) k N : ℝ)/N ≤ 16/(J : ℝ)+ε := by
  obtain ⟨u,hu,huα,t,hblocks⟩ := exists_occupied_power_prime_blocks J K hJ α ε hα hα1 hε
  have htt : Tendsto (fun N => (t N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hblocks.mono fun N h => h.2.1)
      ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop)
  have htlog := Real.tendsto_log_atTop.comp htt
  have htlog2 := htlog.atTop_div_const (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^α/N) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1-α by linarith)).comp tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    dsimp only [Function.comp_apply]
    rw [show -(1-α)=α-1 by ring,Real.rpow_sub (by exact_mod_cast hN),Real.rpow_one]
  have htail : Tendsto (fun N : ℕ => 32*((N : ℝ)^α+1)/((N : ℝ)*J)) atTop (𝓝 0) := by
    have h := (hpow.add tendsto_one_div_atTop_nhds_zero_nat).const_mul (32/(J : ℝ))
    simp only [add_zero,mul_zero] at h
    convert h using 1
    funext N
    ring
  refine ⟨u,hu,huα,t,?_⟩
  filter_upwards [hblocks,htlog.eventually_ge_atTop (2*(1+primePowerErrorConstant+Real.log 4)),
    htlog2.eventually_ge_atTop 2,htail.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with N hb hl hl2 htailN hN
  obtain ⟨ht,hlo,hupper,hmass,_⟩ := hb
  refine ⟨ht,hlo,hupper,hmass,?_⟩
  intro i hi
  refine ⟨iteratedPrimeBlock_mass_upper (t N) J i ht hl2,?_⟩
  have h := iteratedPrimeBlock_thin_bound (t N) J K i k N ht hJ hk hN hi hl
  have hrem : 32*(blockCutoff (t N) J K+1 : ℝ)/((N : ℝ)*J) ≤
      32*((N : ℝ)^α+1)/((N : ℝ)*J) := by gcongr
  linarith

#print axioms exists_thick_power_prime_blocks
end Erdos371.FiniteSieve
