import Submission.WeightedComplementSelection
import Submission.TwoTargetMaximalSelection

/-! Simultaneous arithmetic selection for two prescribed bounded weights. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

theorem exists_power_cutoff_two_weight_maximal_cancellation (k : ℕ) (ε ρ : ℝ)
    (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ u : ℝ, 0 < u ∧ u ≤ ρ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ w : Bool → ℕ → ℝ, (∀ t n, n < N → |w t n| ≤ 1) → ∃ B : ℕ,
      (N : ℝ)^u ≤ B ∧ (B : ℝ) ≤ (N : ℝ)^ρ ∧
      ∀ t : Bool, ∀ X ≤ B^k, |(∑ n ∈ range N, w t n*untruncatedComplementPrefix B X n)/N| < ε := by
  let c : ℝ := 2^(k+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : 0 < ε/(8*c) := by positivity
  obtain ⟨J,hJ,hJk,hJs⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    ((eventually_ge_atTop (8*k)).and
      ((tendsto_const_div_atTop_nhds_zero_nat (16 : ℝ)).eventually_lt_const hsmall))).exists
  let Mb : ℝ := 16*(2^J : ℕ)
  obtain ⟨K,hK,hselect⟩ := exists_small_power_for_two_target_maximal_selection k Mb (ε/4) (by positivity)
  let M : ℝ := 16*(2^(J*K) : ℕ)
  obtain ⟨δ,hδ,hselect⟩ := hselect M
  let α : ℝ := min δ (min ρ (1/2))
  have hα : 0 < α := lt_min hδ (lt_min hρ (by norm_num))
  have hαδ : α ≤ δ := min_le_left _ _
  have hαρ : α ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hα1 : α < 1 := lt_of_le_of_lt ((min_le_right δ (min ρ (1/2))).trans
    (min_le_right ρ (1/2))) (by norm_num)
  obtain ⟨u,hu,huα,t,hblocks⟩ := exists_thick_power_prime_blocks J K k hJ hJk α (ε/(8*c)) hα hα1 hsmall
  refine ⟨u,hu,huα.trans hαρ,?_⟩
  filter_upwards [hblocks,hselect,eventually_ge_atTop (1 : ℕ),
    tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
      (show (0 : ℝ) < ε/4 by positivity)] with N hblocks hselect hN hsmallN
  intro w hw
  obtain ⟨ht,hlo,hupper,hmass,hocc⟩ := hblocks
  have ht0 : 0 < t N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let P := largePrimeSet (t N) (blockCutoff (t N) J K)
  let A : ℕ → Finset ℕ := fun i => primesThrough (blockCutoff (t N) J i)
  let B : ℕ → Finset ℕ := iteratedPrimeBlock (t N) J
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ := by
    obtain ⟨hpp,_,hpu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
    refine ⟨hpp,?_⟩
    exact ((show (p : ℝ) ≤ blockCutoff (t N) J K by exact_mod_cast hpu).trans hupper).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hαδ)
  obtain ⟨i,hi,hcorr⟩ := hselect P A B (fun t n => w t n*nonzeroFullParity n) hP hmass
    (fun i j hij _ => primesThrough_blockCutoff_mono (t N) J ht0 hij.le)
    (fun i j _ hj => primesThrough_blockCutoff_difference (t N) J i j K ht0 hj.le)
    (fun i hi => iteratedPrimeBlock_subset (t N) J i K ht0 hi)
    (fun i j hij _ => iteratedPrimeBlock_disjoint (t N) J i j ht0 hij)
    (fun i hi => (hocc i hi).1)
    (fun t n hn => by rw [abs_mul]; exact mul_le_one₀ (hw t n hn) (abs_nonneg _) (nonzeroFullParity_abs_le n))
  refine ⟨blockCutoff (t N) J i,?_,?_,?_⟩
  · exact hlo.trans (by exact_mod_cast blockCutoff_base_le (t N) J i ht0)
  · exact ((show (blockCutoff (t N) J i : ℝ) ≤ blockCutoff (t N) J K by
      exact_mod_cast blockCutoff_mono (t N) J ht0 hi.le).trans hupper).trans
        (Real.rpow_le_rpow_of_exponent_le hN1 hαρ)
  · intro b X hX
    specialize hcorr b X
    have hbi : 1 < blockCutoff (t N) J i := ht.trans_le (blockCutoff_base_le (t N) J i ht0)
    have hkpow : k ≤ 2^J := by
      have hjpow : J < 2^J := Nat.lt_two_pow_self
      omega
    have hcut : (blockCutoff (t N) J i)^k ≤ blockCutoff (t N) J (i+1) := by
      rw [blockCutoff_step]
      exact Nat.pow_le_pow_right (by omega) hkpow
    have herr := weightedComplementPrefix_witness_mean_error (blockCutoff (t N) J i)
      (blockCutoff (t N) J (i+1)) k X N (w b) (hw b) hbi hX hcut P
      (iteratedPrimeBlock_subset (t N) J i K ht0 hi)
    have hthin := (hocc i hi).2
    have hthinsmall : c*((thinPrimeBlockCount (iteratedPrimeBlock (t N) J i) k N : ℝ)/N) < ε/4 := by
      have hs := mul_lt_mul_of_pos_left hJs hc
      have he : c*(ε/(8*c))=ε/8 := by field_simp
      calc
        _ ≤ c*(16/(J : ℝ)+ε/(8*c)) := mul_le_mul_of_nonneg_left hthin hc.le
        _ < ε/4 := by rw [mul_add,he]; nlinarith
    change |(∑ n ∈ range N, (w b n*nonzeroFullParity n)*
      localPatternWitness (primesThrough (blockCutoff (t N) J i)) P
        (shortComplementPattern (iteratedPrimeBlock (t N) J i) X k) n)/N| < ε/4 at hcorr
    have htri := abs_sub_le
      ((∑ n ∈ range N, w b n*untruncatedComplementPrefix (blockCutoff (t N) J i) X n)/N)
      ((∑ n ∈ range N, (w b n*nonzeroFullParity n)*
        localPatternWitness (primesThrough (blockCutoff (t N) J i)) P
          (shortComplementPattern (iteratedPrimeBlock (t N) J i) X k) n)/N) 0
    simp only [sub_zero] at htri
    change |(∑ n ∈ range N, w b n*untruncatedComplementPrefix (blockCutoff (t N) J i) X n)/N-
      (∑ n ∈ range N, (w b n*nonzeroFullParity n)*
        localPatternWitness (primesThrough (blockCutoff (t N) J i)) P
          (shortComplementPattern (iteratedPrimeBlock (t N) J i) X k) n)/N| ≤
      1/(N : ℝ)+c*(thinPrimeBlockCount (iteratedPrimeBlock (t N) J i) k N : ℝ)/N at herr
    rw [mul_div_assoc] at herr
    linarith


#print axioms exists_power_cutoff_two_weight_maximal_cancellation
end Erdos371
