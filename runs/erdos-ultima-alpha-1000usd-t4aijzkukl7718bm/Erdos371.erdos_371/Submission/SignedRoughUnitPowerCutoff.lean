import Submission.OccupiedPowerPrimeBlocks
import Submission.PrimeBlockSelection
import Submission.RoughUnitWitness

/-! Signed cancellation of the untruncated unit complementary term at a
selected power-growing cutoff. The entire large-divisor tail is not estimated. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

/-- The cutoff can be selected between a positive fixed power and ANY
prescribed upper power. Both powers are fixed before N tends to infinity. -/
theorem exists_power_cutoff_unit_cancellation (ε ρ : ℝ) (hε : 0<ε) (hρ : 0<ρ) :
    ∃ u : ℝ, 0<u ∧ u≤ρ ∧ ∀ᶠ N : ℕ in atTop, ∃ B : ℕ,
      (N : ℝ)^u≤B ∧ (B : ℝ)≤(N : ℝ)^ρ ∧
      |(∑ n ∈ range N, untruncatedRoughUnit B n)/N|<ε := by
  obtain ⟨J,hJ,hJsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((tendsto_const_div_atTop_nhds_zero_nat (16 : ℝ)).eventually_lt_const
      (show (0 : ℝ)<ε/32 by positivity))).exists
  obtain ⟨K,hK,hKsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
      (show (0 : ℝ)<(ε/4)^2/2 by positivity))).exists
  let η : ℝ := (ε/4)^2/4
  let M : ℝ := 16*(2^(J*K) : ℕ)
  have hη : 0<η := by dsimp [η]; positivity
  have hsize : (1 : ℝ)/K+η<(ε/4)^2 := by dsimp [η]; nlinarith [sq_pos_of_pos (show (0 : ℝ)<ε/4 by positivity)]
  obtain ⟨δ,hδ,hselect⟩ := exists_small_power_for_block_selection M η (ε/4) K hK hη (by positivity) hsize
  let α : ℝ := min δ (min ρ (1/2))
  have hα : 0<α := lt_min hδ (lt_min hρ (by norm_num))
  have hαδ : α≤δ := min_le_left _ _
  have hαρ : α≤ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hα1 : α<1 := lt_of_le_of_lt ((min_le_right δ (min ρ (1/2))).trans (min_le_right ρ (1/2))) (by norm_num)
  obtain ⟨u,hu,huα,t,hblocks⟩ := exists_occupied_power_prime_blocks J K hJ α (ε/32) hα hα1 (by positivity)
  refine ⟨u,hu,huα.trans hαρ,?_⟩
  filter_upwards [hblocks,hselect,eventually_ge_atTop (1 : ℕ),
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually_lt_const
      (show (0 : ℝ)<ε/4 by positivity)] with N hblocks hselect hN hsmall
  obtain ⟨ht,hlo,hupper,hmass,hocc⟩ := hblocks
  have ht0 : 0<t N := by omega
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  let P := largePrimeSet (t N) (blockCutoff (t N) J K)
  let A : ℕ → Finset ℕ := fun i => primesThrough (blockCutoff (t N) J i)
  let B : ℕ → Finset ℕ := iteratedPrimeBlock (t N) J
  have hP (p : ℕ) (hp : p∈P) : p.Prime ∧ (p : ℝ)≤(N : ℝ)^δ := by
    obtain ⟨hpp,_,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
    refine ⟨hpp,?_⟩
    exact ((show (p : ℝ)≤blockCutoff (t N) J K by exact_mod_cast hpu).trans hupper).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hαδ)
  obtain ⟨i,hi,hcorr⟩ := hselect P A B fullRadicalParity hP hmass
    (fun i j hij _ => primesThrough_blockCutoff_mono (t N) J ht0 hij.le)
    (fun i j _ hj => primesThrough_blockCutoff_difference (t N) J i j K ht0 hj.le)
    (fun i hi => iteratedPrimeBlock_subset (t N) J i K ht0 hi)
    (fun i j hij _ => iteratedPrimeBlock_disjoint (t N) J i j ht0 hij)
    (fun n _ => (fullRadicalParity_abs n).le)
  refine ⟨blockCutoff (t N) J i,?_,?_,?_⟩
  · exact hlo.trans (by exact_mod_cast blockCutoff_base_le (t N) J i ht0)
  · exact ((show (blockCutoff (t N) J i : ℝ)≤blockCutoff (t N) J K by
      exact_mod_cast blockCutoff_mono (t N) J ht0 hi.le).trans hupper).trans
        (Real.rpow_le_rpow_of_exponent_le hN1 hαρ)
  · have herr := untruncatedRoughUnit_witness_mean_error (blockCutoff (t N) J i)
      (blockCutoff (t N) J (i+1)) N
    have hempty := hocc i hi
    change (emptyPrimeBlockCount (largePrimeSet (blockCutoff (t N) J i)
      (blockCutoff (t N) J (i+1))) N : ℝ)/N≤16/(J : ℝ)+ε/32 at hempty
    change |(∑ n ∈ range N, fullRadicalParity n*primeBlockWitness
      (primesThrough (blockCutoff (t N) J i))
      (largePrimeSet (blockCutoff (t N) J i) (blockCutoff (t N) J (i+1))) n)/N|<ε/4 at hcorr
    have htri := abs_sub_le
      ((∑ n ∈ range N, untruncatedRoughUnit (blockCutoff (t N) J i) n)/N)
      ((∑ n ∈ range N, fullRadicalParity n*primeBlockWitness
        (primesThrough (blockCutoff (t N) J i))
        (largePrimeSet (blockCutoff (t N) J i) (blockCutoff (t N) J (i+1))) n)/N) 0
    simp only [sub_zero] at htri
    have heq : 2*(emptyPrimeBlockCount (largePrimeSet (blockCutoff (t N) J i)
      (blockCutoff (t N) J (i+1))) N : ℝ)/N =
      2*((emptyPrimeBlockCount (largePrimeSet (blockCutoff (t N) J i)
        (blockCutoff (t N) J (i+1))) N : ℝ)/N) := by ring
    rw [heq] at herr
    linarith

#print axioms exists_power_cutoff_unit_cancellation
end Erdos371
