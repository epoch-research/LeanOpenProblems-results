import Submission.LogCellWindowBudgetExplore
import Submission.ShortSupportSwapTailExplore

/-! Exact harmonic brackets bound every short interval independently of any
representation envelope. This includes intervals near zero. -/
namespace Erdos66BracketWindowOccupancy
open Erdos66Generating Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66ShortSupportSwapTail
  Erdos66ReflectionRoundingPatch Erdos66FlatProfileWindows
  Erdos66CumulativeRoundingError Erdos66Rounding Erdos66LogCellWindowBudget
open scoped Classical
set_option maxHeartbeats 3000000

lemma brackets_window_prefix_bound (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (a w : ℕ) : ((intervalPart A a (a+w)).card : ℝ) ≤ 2+prefixSum profile w := by
  have hc := (abs_le.mp (local_count_error A profile 1
    (brackets_count_discrepancy profile A hbr) a (a+w) (by omega))).2
  have hm : (∑ i∈Finset.Ico a (a+w), profile i) ≤ prefixSum profile w := by
    rw [Finset.sum_Ico_eq_sum_range]
    calc
      _ ≤ ∑ i∈Finset.range (a+w-a), profile i :=
        Finset.sum_le_sum (fun i _ ↦ profile_antitone (by omega))
      _ ≤ prefixSum profile w := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun i _ _ ↦ profile_nonneg i)
  linarith

lemma brackets_log_window_bound (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (N : ℕ) (hN : 3 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) (hwN : windowSize N ≤ N)
    (a : ℕ) : ((intervalPart A a (a+windowSize N)).card : ℝ) ≤ 6*(Real.log N)^5 := by
  let w := windowSize N
  let L := Real.log (N : ℝ)
  have hL : 1 ≤ L := hl
  have hw := (windowSize_bounds N hl).2.2
  have hH := harmonic_le_one_add_log (2*w+1)
  push_cast at hH
  have hnR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<((2*w+1 : ℕ) : ℝ))
    (show ((2*w+1 : ℕ) : ℝ) ≤ (N : ℝ)^2 by
      have hwR : (w : ℝ) ≤ N := by exact_mod_cast hwN
      push_cast
      nlinarith)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hH' : (harmonic (2*w+1) : ℝ) ≤ 3*L := by
    dsimp only [L]
    linarith
  have h8 : 1 ≤ L^8 := one_le_pow₀ hL
  have h5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hcount : ((2*w+1 : ℕ) : ℝ) ≤ 5*L^8 := by
    change (w : ℝ) ≤ 2*L^8 at hw
    push_cast
    linarith
  have hm := mul_le_mul hcount hH' (harmonic_nonneg _) (by positivity : 0 ≤ 5*L^8)
  have hp := (profile_prefix_square_bound w).trans hm
  have h910 : L^9 ≤ L^10 := pow_le_pow_right₀ hL (by norm_num)
  have hp' : (prefixSum profile w)^2 ≤ (4*L^5)^2 := by
    nlinarith only [hp,h910,pow_nonneg (by linarith : 0 ≤ L) 10]
  have hpref : prefixSum profile w ≤ 4*L^5 := by
    nlinarith only [hp',show 0 ≤ 4*L^5 by positivity]
  have hc := brackets_window_prefix_bound A hbr a w
  change ((intervalPart A a (a+w)).card : ℝ) ≤ 6*L^5
  linarith

lemma brackets_log_window_bound_subset (A B : Set ℕ) (hBA : B ⊆ A)
    (hbr : ∀ L, PrefixBrackets profile A L) (N : ℕ) (hN : 3 ≤ N)
    (hl : 1 ≤ Real.log (N : ℝ)) (hwN : windowSize N ≤ N) (a : ℕ) :
    ((intervalPart B a (a+windowSize N)).card : ℝ) ≤ 6*(Real.log N)^5 := by
  have hsub : intervalPart B a (a+windowSize N) ⊆ intervalPart A a (a+windowSize N) := by
    intro i hi
    obtain ⟨hi,hiB⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi,hBA hiB⟩
  have hh : ((intervalPart B a (a+windowSize N)).card : ℝ) ≤
      (intervalPart A a (a+windowSize N)).card := by exact_mod_cast Finset.card_le_card hsub
  exact hh.trans (brackets_log_window_bound A hbr N hN hl hwN a)

end Erdos66BracketWindowOccupancy
