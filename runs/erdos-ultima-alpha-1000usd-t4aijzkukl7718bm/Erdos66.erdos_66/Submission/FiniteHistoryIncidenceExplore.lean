import Submission.LogCellWindowBudgetExplore
import Submission.ShortSupportSwapTailExplore
import Submission.BoundaryPairCountsExplore

/-! Finite history does not cause an accumulating triple-cap constant far
beyond its support. The estimates depend on support width, not edit count. -/
namespace Erdos66FiniteHistoryIncidence
open Filter Erdos66CentralTripleCounts Erdos66BoundaryPairCounts Erdos66BoundaryPairMean
  Erdos66ShortSupportSwapTail Erdos66ReflectionRoundingPatch
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66FlatProfileWindows
open scoped Classical Topology
set_option maxHeartbeats 3500000

lemma small_tail_window (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (U N L : ℕ) (hNL : N ≤ L) (hmass : (U : ℝ)*profile N ≤ 1/2) :
    (intervalPart A L (L+U)).card ≤ 2 := by
  have hh := antitone_window_count profile A 1 profile_antitone
    (brackets_count_discrepancy profile A hbr) L U
  have hp := mul_le_mul_of_nonneg_left (profile_antitone hNL) (Nat.cast_nonneg U)
  by_contra hc
  have h3 : (3 : ℝ) ≤ (intervalPart A L (L+U)).card := by
    exact_mod_cast (show 3 ≤ (intervalPart A L (L+U)).card by omega)
  linarith

lemma fiber_tail_subset (A B : Set ℕ) (U N n z : ℕ) (hUN : U ≤ N)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    fiber B N n z ⊆ fiber A N n z ∪
      intervalPart A (max N (z+1-U)) (max N (z+1-U)+U) := by
  intro a ha
  obtain ⟨han,hNa,hNb,haz,haB,hbB,hcB⟩ := mem_fiber.mp ha
  have haA := (hagree a (by omega)).mp haB
  have hbA := (hagree (n-a) (by omega)).mp hbB
  by_cases hc : U ≤ z-a
  · exact Finset.mem_union_left _ (mem_fiber.mpr
      ⟨han,hNa,hNb,haz,haA,hbA,(hagree (z-a) hc).mp hcB⟩)
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,haA⟩

lemma fiber_after_history (A B : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (U N n z : ℕ) (hUN : U ≤ N) (hmass : (U : ℝ)*profile N ≤ 1/2)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    (fiber B N n z).card ≤ (fiber A N n z).card+2 := by
  have hh := (Finset.card_le_card (fiber_tail_subset A B U N n z hUN hagree)).trans
    (Finset.card_union_le _ _)
  have hw := small_tail_window A hbr U N (max N (z+1-U)) (le_max_left _ _) hmass
  omega

lemma boundary_tail_difference (A B : Set ℕ) (U N d n : ℕ)
    (hUN : U ≤ N) (hn : 2*N ≤ n) (hd : 2 ≤ d)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    ((boundary B d n)\(boundary A d n)).card ≤
      (intervalPart A (n+1-U) (n+1-U+U)).card := by
  apply Finset.card_le_card_of_injOn (fun a : ℕ ↦ n-a)
  · intro a ha
    change a∈boundary B d n\boundary A d n at ha
    obtain ⟨ha,haold⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨har,haB,hbB⟩ := Finset.mem_filter.mp ha
    have har' := Finset.mem_range.mp har
    have hhalf := quotient_half d n hd
    have hbN : N ≤ n-a := by omega
    have hbA := (hagree (n-a) (by omega)).mp hbB
    have haU : a < U := by
      by_contra hh
      apply haold
      exact Finset.mem_filter.mpr ⟨har,(hagree a (by omega)).mp haB,hbA⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hbA⟩
  · intro a ha b hb he
    change a∈boundary B d n\boundary A d n at ha
    change b∈boundary B d n\boundary A d n at hb
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).1
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).1
    have hhalf := quotient_half d n hd
    dsimp only at he
    omega

lemma boundary_after_history (A B : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (U N d n : ℕ) (hUN : U ≤ N) (hn : 2*N ≤ n) (hd : 2 ≤ d)
    (hmass : (U : ℝ)*profile N ≤ 1/2)
    (hagree : ∀ a, U ≤ a → (a∈B ↔ a∈A)) :
    (boundary B d n).card ≤ (boundary A d n).card+2 := by
  have hdif := (boundary_tail_difference A B U N d n hUN hn hd hagree).trans
    (small_tail_window A hbr U N (n+1-U) (by omega) hmass)
  have hc := Finset.card_le_card (show boundary B d n ⊆
      boundary A d n ∪ (boundary B d n\boundary A d n) from by
    intro a ha
    by_cases hh : a∈boundary A d n
    · exact Finset.mem_union_left _ hh
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha,hh⟩))
  have hu := Finset.card_union_le (boundary A d n) (boundary B d n\boundary A d n)
  omega

/-- A deliberately generous polynomial waiting scale, uniform over every
history cutoff U at most W and every larger central cutoff N. -/
lemma eventually_history_mass : ∀ᶠ W : ℕ in atTop, ∀ U N : ℕ,
    U ≤ W → W^32 ≤ N → U ≤ N ∧ (U : ℝ)*profile N ≤ 1/2 := by
  filter_upwards [eventually_ge_atTop 32,eventually_harmonic_polynomial_bound]
    with W hW hH
  intro U N hUW hWN
  have hWp : 0 < W := by omega
  have hW1 : 1 ≤ W := by omega
  have h32 : W ≤ W^32 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hWp (show 1 ≤ 32 by norm_num)
  have h15 : 2*W ≤ W^15 := by
    have hp := Nat.pow_le_pow_right hWp (show 2 ≤ 15 by norm_num)
    have hh : 2*W ≤ W^2 := by nlinarith
    exact hh.trans hp
  have hp := (profile_polynomial_bounds W (by omega) hH).1
  have hsmall : (2*(U : ℝ))*profile N ≤ (W : ℝ)^15*profile (W^32) := by
    apply mul_le_mul
    · exact_mod_cast (show 2*U ≤ W^15 by omega)
    · exact profile_antitone hWN
    · exact profile_nonneg N
    · positivity
  exact ⟨by omega,by nlinarith only [hsmall,hp]⟩

/-- Arbitrarily many earlier edits cost at most TWO extra incidences once
one waits beyond their support. No bracket assumption on B is needed. -/
theorem uniformly_eventually_history_incidence : ∀ᶠ W : ℕ in atTop,
    ∀ A B : Set ℕ, (∀ L, PrefixBrackets profile A L) →
      ∀ U : ℕ, U ≤ W → (∀ a, U ≤ a → (a∈B ↔ a∈A)) →
        ∀ N : ℕ, W^32 ≤ N →
          (∀ n z, (fiber B N n z).card ≤ (fiber A N n z).card+2) ∧
          ∀ d n, 2 ≤ d → 2*N ≤ n → (boundary B d n).card ≤ (boundary A d n).card+2 := by
  filter_upwards [eventually_history_mass] with W hW
  intro A B hbr U hUW hagree N hWN
  obtain ⟨hUN,hmass⟩ := hW U N hUW hWN
  exact ⟨fun n z ↦ fiber_after_history A B hbr U N n z hUN hmass hagree,
    fun d n hd hn ↦ boundary_after_history A B hbr U N d n hUN hn hd hmass hagree⟩

/-- A cubic, rather than thirty-second-power, waiting scale already suffices. -/
lemma eventually_cubic_history_mass : ∀ᶠ W : ℕ in atTop, ∀ U N : ℕ,
    U ≤ W → W^3 ≤ N → U ≤ N ∧ (U : ℝ)*profile N ≤ 1/2 := by
  have hlog : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop 1,
    (Erdos66LogCellWindowBudget.log_power_sqrt_decay 1).eventually_le_const
      (by norm_num : (0 : ℝ)<1/12)] with W hW hl hdec
  intro U N hUW hWN
  have hWp : 0 < W := by omega
  have hWr : (0 : ℝ)<W := by exact_mod_cast hWp
  have hsp := Real.sqrt_pos.mpr hWr
  have h3 : W ≤ W^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hWp (show 1 ≤ 3 by norm_num)
  have hl3 : 1 ≤ Real.log ((W^3 : ℕ) : ℝ) := hl.trans
    (Real.log_le_log hWr (by exact_mod_cast h3))
  have hp := Erdos66LogCellWindowBudget.profile_sqrt_upper (W^3) (by omega) hl3
  have hroot : Real.sqrt ((W^3 : ℕ) : ℝ)=(W : ℝ)*Real.sqrt W := by
    rw [Nat.cast_pow,show (W : ℝ)^3=(W : ℝ)^2*W by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg W)]
  rw [hroot,Nat.cast_pow,Real.log_pow] at hp
  norm_num at hp
  have hsmall : (W : ℝ)*profile (W^3) ≤ 6*Real.log W/Real.sqrt W :=
    (le_div_iff₀ hsp).mpr (by nlinarith only [hp])
  simp only [pow_one] at hdec
  rw [mul_div_assoc] at hsmall
  have hmul : (U : ℝ)*profile N ≤ (W : ℝ)*profile (W^3) :=
    mul_le_mul (by exact_mod_cast hUW) (profile_antitone hWN)
      (profile_nonneg N) (Nat.cast_nonneg W)
  exact ⟨by omega,by nlinarith only [hmul,hsmall,hdec]⟩

theorem uniformly_eventually_cubic_history_incidence : ∀ᶠ W : ℕ in atTop,
    ∀ A B : Set ℕ, (∀ L, PrefixBrackets profile A L) →
      ∀ U : ℕ, U ≤ W → (∀ a, U ≤ a → (a∈B ↔ a∈A)) →
        ∀ N : ℕ, W^3 ≤ N →
          (∀ n z, (fiber B N n z).card ≤ (fiber A N n z).card+2) ∧
          ∀ d n, 2 ≤ d → 2*N ≤ n → (boundary B d n).card ≤ (boundary A d n).card+2 := by
  filter_upwards [eventually_cubic_history_mass] with W hW
  intro A B hbr U hUW hagree N hWN
  obtain ⟨hUN,hmass⟩ := hW U N hUW hWN
  exact ⟨fun n z ↦ fiber_after_history A B hbr U N n z hUN hmass hagree,
    fun d n hd hn ↦ boundary_after_history A B hbr U N d n hUN hn hd hmass hagree⟩

end Erdos66FiniteHistoryIncidence
