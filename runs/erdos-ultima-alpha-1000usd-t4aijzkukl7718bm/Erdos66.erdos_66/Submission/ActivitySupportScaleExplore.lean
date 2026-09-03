import Submission.ActivityMassCarryExplore
import Submission.ActivityBudgetLimitExplore

/-! The mass-sensitive certificate requires growing coarse quotients when its
coarse mass has a positive normalized limit. This is a limitation of the
certificate, not a lower bound for the actual carry error. -/
namespace Erdos66ActivitySupportScale
open Erdos66ActivityMassCarry Erdos66AntitonePairIntervals
  Erdos66ShortOrbitCarry Erdos66FiniteLogMassBudget Erdos66ActivityBudgetLimit Filter
open scoped Topology Classical
set_option maxHeartbeats 1200000

lemma active_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C D : ℕ → Finset G) (q : ℕ) (z a : G) :
    (active C D q z a).card ≤ q+1 := by
  calc
    _ ≤ (Finset.range (q+1)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = q+1 := Finset.card_range _

lemma support_le_mass (M : ℕ) [NeZero M]
    (C D : ℕ → Finset (ZMod M)) (b : ZMod M) (q t : ℕ) :
    supportCount M C D b q t ≤ mixedPhaseMass M C D b q t := by
  rw [mixedPhaseMass,count_sum_eq_active,←sum_active_card_on_support]
  unfold supportCount
  calc
    _ = ∑ a ∈ activeSupport C D q ((t : ZMod M)-b*q), (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      exact_mod_cast Finset.one_le_card.mpr ((mem_activeSupport C D q _ a).mp ha)

lemma mass_le_horizon_support (M : ℕ) [NeZero M]
    (C D : ℕ → Finset (ZMod M)) (b : ZMod M) (q t : ℕ) :
    mixedPhaseMass M C D b q t ≤ (q+1 : ℝ)*supportCount M C D b q t := by
  rw [mixedPhaseMass,count_sum_eq_active,←sum_active_card_on_support]
  calc
    _ ≤ ∑ a ∈ activeSupport C D q ((t : ZMod M)-b*q), (q+1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact_mod_cast active_card_le C D q _ a
    _ = _ := by simp [supportCount]; ring

lemma thirty_support_le_budget (K P : ℝ) : 30*K ≤ budget K P := by
  unfold budget
  have h := Real.sqrt_nonneg (K*P)
  linarith

/-- Under a bounded normalized coarse mass, subscale support is also necessary
for this particular budget to vanish. Actual cancellation can be better. -/
theorem budget_div_limit_iff_support (K P L : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hL : ∀ᶠ n in atTop, 0<L n)
    (hbound : ∀ᶠ n in atTop, P n ≤ C*L n) :
    Tendsto (fun n ↦ budget (K n) (P n)/L n) atTop (𝓝 0) ↔
      Tendsto (fun n ↦ K n/L n) atTop (𝓝 0) := by
  constructor
  · intro hb
    have hb' := hb.div_const 30
    simp only [zero_div] at hb'
    apply squeeze_zero' ?_ ?_ hb'
    · filter_upwards [hK,hL] with n hk hl
      exact div_nonneg hk hl.le
    · filter_upwards [hL] with n hl
      have hh := div_le_div_of_nonneg_right (thirty_support_le_budget (K n) (P n)) hl.le
      apply (le_div_iff₀ (by norm_num : (0 : ℝ)<30)).mpr
      convert hh using 1
      ring
  · exact fun hk ↦ budget_div_limit_of_bound K P L C hC hK hL hk hbound

/-- Positive normalized mass and subscale active support force the quotient
q to tend to infinity, without any monotonicity assumption on q. -/
theorem quotient_tendsto_atTop (K P L : ℕ → ℝ) (q : ℕ → ℕ) (c : ℝ) (hc : 0<c)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hL : ∀ᶠ n in atTop, 0<L n)
    (hbound : ∀ᶠ n in atTop, P n ≤ (q n+1 : ℝ)*K n)
    (hk : Tendsto (fun n ↦ K n/L n) atTop (𝓝 0))
    (hp : Tendsto (fun n ↦ P n/L n) atTop (𝓝 c)) :
    Tendsto q atTop atTop := by
  apply tendsto_atTop.mpr
  intro Q
  have hQ : (0 : ℝ)<(Q : ℝ)+1 := by positivity
  have hsmall := hk.eventually_lt_const (show (0 : ℝ)<c/(2*((Q : ℝ)+1)) by positivity)
  have hlarge := hp.eventually_const_lt (show c/2<c by linarith)
  filter_upwards [hK,hL,hbound,hsmall,hlarge] with n hkn hln hbn hsn hpn
  by_contra hn
  have hqn : (q n : ℝ) ≤ Q := by exact_mod_cast (show q n ≤ Q by omega)
  have hle : P n/L n ≤ ((Q : ℝ)+1)*(K n/L n) := by
    calc
      _ ≤ ((q n : ℝ)+1)*K n/L n := div_le_div_of_nonneg_right hbn hln.le
      _ ≤ ((Q : ℝ)+1)*K n/L n := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : (q n : ℝ)+1 ≤ (Q : ℝ)+1) hkn) hln.le
      _ = _ := by ring
  have hs' := (lt_div_iff₀ (show (0 : ℝ)<2*((Q : ℝ)+1) by positivity)).mp hsn
  nlinarith

end Erdos66ActivitySupportScale
