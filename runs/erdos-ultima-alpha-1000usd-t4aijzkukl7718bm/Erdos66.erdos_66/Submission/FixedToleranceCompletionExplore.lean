import Submission.DeficitWeightedCompletionExplore
import Submission.SummableExceptionalSetExplore
import Submission.SuperquadraticCostsExplore

/-! A fixed-tolerance formulation of the weighted-deficit completion criterion.
The power exponents may depend on tolerance; each must exceed one half.
No base satisfying the new criterion is constructed here. -/
namespace Erdos66FixedToleranceCompletion
open Filter AdditiveCombinatorics Erdos66ClippedRepair
  Erdos66MultiplicityMatchingSpikes Erdos66DeficitWeightedCompletion
  Erdos66SummableExceptionalSet Erdos66SuperquadraticCosts
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def repairWeight (n : ℕ) : ℝ := logScale n*packetWeight n

lemma repairWeight_nonneg (n : ℕ) : 0≤repairWeight n :=
  mul_nonneg (logScale_pos n).le (packetWeight_nonneg n)

/-- Allowing sublogarithmic deficits does not require a uniform threshold in
all tolerances. Weighted diagonalization produces one suitable allowance. -/
lemma allowance_of_fixed_tolerance_costs (A : Set ℕ) (c : ℝ) (hc : 0≤c)
    (h : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if (sumRep A n : ℝ)≤(c-ε)*logScale n then repairWeight n else 0)) :
    ∃ d : ℕ → ℝ, (∀ n, 0≤d n) ∧
      Tendsto (fun n ↦ d n/logScale n) atTop (𝓝 0) ∧
      Summable (fun n ↦ deficit A c d n*packetWeight n) := by
  let f : ℕ → ℝ := fun n ↦ max 0 (c-(sumRep A n : ℝ)/logScale n)
  have hf (n : ℕ) : 0≤f n := le_max_left _ _
  have he (ε : ℝ) (hε : 0<ε) (n : ℕ) :
      ε≤|f n-0| ↔ (sumRep A n : ℝ)≤(c-ε)*logScale n := by
    rw [sub_zero,abs_of_nonneg (hf n)]
    change ε ≤ max 0 (c-(sumRep A n : ℝ)/logScale n) ↔ _
    rw [le_max_iff]
    constructor
    · rintro (hh | hh)
      · linarith
      · apply (div_le_iff₀ (logScale_pos n)).mp
        linarith
    · intro hh
      right
      have hd := (div_le_iff₀ (logScale_pos n)).mpr hh
      linarith
  have hs : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε≤|f n-0| then repairWeight n else 0) := by
    intro ε hε
    simpa only [he ε hε] using h ε hε
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set f 0 repairWeight repairWeight_nonneg hs
  let d : ℕ → ℝ := fun n ↦ if n∈E then 0 else f n*logScale n
  have hd (n : ℕ) : 0≤d n := by dsimp [d]; split_ifs; exact le_rfl; exact mul_nonneg (hf n) (logScale_pos n).le
  refine ⟨d,hd,?_,?_⟩
  · convert hlim using 1
    funext n
    dsimp [d]
    split_ifs <;> simp only [zero_div,mul_div_cancel_right₀ _ (logScale_pos n).ne']
  · apply (hE.mul_left c).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (show 0≤deficit A c d n from le_max_left _ _) (packetWeight_nonneg n))]
    by_cases hn : n∈E
    · simp only [if_pos hn,deficit,d,sub_zero]
      have hb : max 0 (c*logScale n-(sumRep A n : ℝ))≤c*logScale n :=
        max_le (mul_nonneg hc (logScale_pos n).le) (by linarith [Nat.cast_nonneg (α := ℝ) (sumRep A n)])
      have hh := mul_le_mul_of_nonneg_right hb (packetWeight_nonneg n)
      simpa only [repairWeight,mul_assoc] using hh
    · have hh : c*logScale n-d n-(sumRep A n : ℝ)≤0 := by
        have hl : c-(sumRep A n : ℝ)/logScale n≤f n := le_max_right _ _
        have hm := mul_le_mul_of_nonneg_right hl (logScale_pos n).le
        rw [sub_mul,div_mul_cancel₀ _ (logScale_pos n).ne'] at hm
        dsimp [d]
        rw [if_neg hn]
        linarith
      simp only [if_neg hn,deficit,max_eq_left hh,zero_mul,mul_zero,le_refl]

/-- Conversely, summable actual deficits imply summable weighted bad sets at
every fixed positive tolerance. -/
lemma fixed_tolerance_costs_of_allowance (A : Set ℕ) (c : ℝ) (d : ℕ → ℝ)
    (hdlim : Tendsto (fun n ↦ d n/logScale n) atTop (𝓝 0))
    (hs : Summable (fun n ↦ deficit A c d n*packetWeight n)) :
    ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if (sumRep A n : ℝ)≤(c-ε)*logScale n then repairWeight n else 0) := by
  intro ε hε
  apply (hs.mul_left (2/ε)).of_norm_bounded_eventually_nat
  filter_upwards [hdlim.eventually_lt_const (show (0:ℝ)<ε/2 by positivity)] with n hn
  by_cases hb : (sumRep A n : ℝ)≤(c-ε)*logScale n
  · simp only [if_pos hb,Real.norm_eq_abs,abs_of_nonneg (repairWeight_nonneg n)]
    have hd := (div_lt_iff₀ (logScale_pos n)).mp hn
    have hm : (ε/2)*logScale n≤deficit A c d n := by
      have hh := le_max_right 0 (c*logScale n-d n-(sumRep A n : ℝ))
      change _≤deficit A c d n at hh
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hm (show (0:ℝ)≤2/ε by positivity)
    have he : (2/ε)*((ε/2)*logScale n)=logScale n := by field_simp
    rw [he] at hh
    have hh' := mul_le_mul_of_nonneg_right hh (packetWeight_nonneg n)
    simpa only [repairWeight,mul_assoc] using hh'
  · simp only [if_neg hb,norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (le_max_left _ _) (packetWeight_nonneg n))

/-- An exact reformulation of the actual-deficit hypothesis, independent of
any upper bound. -/
theorem allowance_iff_fixed_tolerance_costs (A : Set ℕ) (c : ℝ) (hc : 0≤c) :
    (∃ d : ℕ → ℝ, (∀ n, 0≤d n) ∧
      Tendsto (fun n ↦ d n/logScale n) atTop (𝓝 0) ∧
      Summable (fun n ↦ deficit A c d n*packetWeight n)) ↔
    (∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if (sumRep A n : ℝ)≤(c-ε)*logScale n then repairWeight n else 0)) := by
  constructor
  · rintro ⟨d,_,hd,hs⟩
    exact fixed_tolerance_costs_of_allowance A c d hd hs
  · exact allowance_of_fixed_tolerance_costs A c hc

/-- No common exceptional set, power exponent, or tolerance threshold is
required in the input. The all-target upper asymptotic bound is required. -/
theorem completion_of_fixed_tolerance_costs (A : Set ℕ) (c : ℝ) (hc : 0≤c)
    (hu : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep A n : ℝ)≤(c+ε)*logScale n)
    (hl : ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if (sumRep A n : ℝ)≤(c-ε)*logScale n then repairWeight n else 0)) :
    ∃ B : Set ℕ, A⊆B ∧
      Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨d,hd,hdlim,hs⟩ := allowance_of_fixed_tolerance_costs A c hc hl
  exact completion_of_upper_tail_and_summable_deficit A c hu d hd hdlim hs

lemma repairWeight_le_power (α : ℝ) (hα : 1/2<α) (hα1 : α<1) :
    ∀ᶠ n : ℕ in atTop, repairWeight n≤2/((n:ℝ)+2)^(1-α : ℝ) := by
  filter_upwards [eventually_logScale_pow_le_rpow 2 (α-1/2) (by linarith),
    logScale_atTop.eventually_ge_atTop 1] with n hn hl
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hnq : (0:ℝ)<(n:ℝ)+2 := by positivity
  have hs : 0<1-α := by linarith
  have hroot : Real.sqrt (logScale n)≤logScale n :=
    Real.sqrt_le_iff.mpr ⟨(logScale_pos n).le,by nlinarith⟩
  have hnum : logScale n*Real.sqrt (logScale n)≤((n:ℝ)+1)^(α-1/2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hroot (logScale_pos n).le
    nlinarith
  have hden : ((n:ℝ)+2)^(1-α : ℝ)≤2*((n:ℝ)+1)^(1-α : ℝ) := by
    have hh := Real.rpow_le_rpow hnq.le
      (show (n:ℝ)+2≤2*((n:ℝ)+1) by linarith [Nat.cast_nonneg (α := ℝ) n]) hs.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hnp.le] at hh
    have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 1-α≤1 by linarith)
    rw [Real.rpow_one] at ht
    exact hh.trans (mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hnp.le _))
  calc
    repairWeight n = logScale n*Real.sqrt (logScale n)/Real.sqrt ((n:ℝ)+1) := by
      simp only [repairWeight,packetWeight,mul_div_assoc]
    _ ≤ ((n:ℝ)+1)^(α-1/2 : ℝ)/Real.sqrt ((n:ℝ)+1) :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    _ = 1/((n:ℝ)+1)^(1-α : ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_sub hnp,
        show α-1/2-1/2=-(1-α) by ring,Real.rpow_neg hnp.le,one_div]
    _ ≤ 2/((n:ℝ)+2)^(1-α : ℝ) := by
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hnp _) (Real.rpow_pos_of_pos hnq _)).mpr
      simpa only [one_mul] using hden

lemma repair_cost_of_power_cost (E : Set ℕ) (α : ℝ) (hα : 1/2<α) (hα1 : α<1)
    (hs : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) :
    Summable (fun n : ℕ ↦ if n∈E then repairWeight n else 0) := by
  apply (hs.mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [repairWeight_le_power α hα hα1] with n hn
  by_cases he : n∈E
  · simpa only [if_pos he,Real.norm_eq_abs,abs_of_nonneg (repairWeight_nonneg n),mul_one_div] using hn
  · simp only [if_neg he,norm_zero,mul_zero,le_refl]

/-- It suffices that every fixed lower tolerance has its own power exponent
strictly above 1/2. The exponents can approach 1/2 as the tolerance shrinks. -/
theorem completion_of_tolerance_dependent_power_costs (A : Set ℕ) (c : ℝ) (hc : 0≤c)
    (hu : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep A n : ℝ)≤(c+ε)*logScale n)
    (hl : ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 1/2<α ∧ α<1 ∧
      Summable (fun n : ℕ ↦ if (sumRep A n : ℝ)≤(c-ε)*logScale n
        then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) :
    ∃ B : Set ℕ, A⊆B ∧
      Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  apply completion_of_fixed_tolerance_costs A c hc hu
  intro ε hε
  obtain ⟨α,hα,hα1,hs⟩ := hl ε hε
  exact repair_cost_of_power_cost {n | (sumRep A n : ℝ)≤(c-ε)*logScale n} α hα hα1 hs

end Erdos66FixedToleranceCompletion
