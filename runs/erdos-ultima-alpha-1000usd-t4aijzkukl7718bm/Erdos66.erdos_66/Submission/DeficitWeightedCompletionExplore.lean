import Submission.MultiplicityMatchingSpikesExplore
import Submission.SparseRepairExplore

/-! Completion using the actual weighted lower deficit, after allowing any
uniformly sublogarithmic error. This is a conditional construction: it does
not supply a base satisfying the weighted deficit hypothesis. -/
namespace Erdos66DeficitWeightedCompletion
open Filter AdditiveCombinatorics Erdos66ClippedRepair
  Erdos66MultiplicityMatchingSpikes Erdos66SparseRepair
open scoped Classical Topology

lemma correction_profile_bounds (r t : ℝ) :
    t-2 < r+2*correction r t ∧ r+2*correction r t ≤ max r t := by
  by_cases htr : t ≤ r
  · have hz : correction r t = 0 := by
      simp [correction,max_eq_left (show (t-r)/2 ≤ 0 by linarith)]
    rw [hz,Nat.cast_zero,mul_zero,add_zero,max_eq_left htr]
    constructor <;> linarith
  · have hrt : r ≤ t := by linarith
    have hd : 0 ≤ (t-r)/2 := by linarith
    have hfloor := Nat.floor_le hd
    have hlt := Nat.lt_floor_add_one ((t-r)/2)
    dsimp [correction]
    rw [max_eq_right hd,max_eq_right hrt]
    constructor <;> linarith

lemma correction_le_deficit (r t : ℝ) :
    (correction r t : ℝ) ≤ max 0 (t-r) := by
  have hh := Nat.floor_le (le_max_left 0 ((t-r)/2))
  apply hh.trans
  apply max_le (le_max_left _ _)
  have h₁ := le_max_left 0 (t-r)
  have h₂ := le_max_right 0 (t-r)
  linarith

noncomputable def deficit (A : Set ℕ) (c : ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 0 (c*logScale n-d n-(sumRep A n : ℝ))

/-- An upper-correct base can be completed if the weighted positive deficit
is summable, after subtracting an arbitrary sublogarithmic allowance `d`. -/
theorem completion_of_summable_deficit (A : Set ℕ) (c K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (d : ℕ → ℝ) (hd : ∀ z, 0 ≤ d z)
    (hdlim : Tendsto (fun z ↦ d z/logScale z) atTop (𝓝 0))
    (hs : Summable (fun z ↦ deficit A c d z*packetWeight z)) :
    ∃ B : Set ℕ, A ⊆ B ∧
      Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  let m (z : ℕ) := correction (sumRep A z : ℝ) (c*logScale z-d z)
  have hm : Summable (fun z ↦ (m z : ℝ)*packetWeight z) := by
    apply Summable.of_nonneg_of_le (fun z ↦ mul_nonneg (Nat.cast_nonneg _) (packetWeight_nonneg z)) _ hs
    intro z
    exact mul_le_mul_of_nonneg_right
      (correction_le_deficit (sumRep A z : ℝ) (c*logScale z-d z)) (packetWeight_nonneg z)
  obtain ⟨B,hAB,hBl,hBu⟩ := asymptotic_multiplicity_spikes A K C hK hC hA m hm
  have hprofile (z : ℕ) := correction_profile_bounds (sumRep A z : ℝ) (c*logScale z-d z)
  change ∀ z, c*logScale z-d z-2 < (sumRep A z : ℝ)+2*m z ∧
    (sumRep A z : ℝ)+2*m z ≤ max (sumRep A z : ℝ) (c*logScale z-d z) at hprofile
  refine ⟨B,hAB,tendsto_of_logScale_tails B c ?_ ?_⟩
  · intro ε hε
    filter_upwards [hu (ε/2) (by positivity),hBu (ε/2) (by positivity)] with z hzu hzb
    have htarget : c*logScale z-d z ≤ (c+ε/2)*logScale z := by
      have hdz := hd z
      have hp := mul_nonneg hε.le (logScale_pos z).le
      nlinarith
    have hm' := (hprofile z).2.trans (max_le hzu htarget)
    linarith
  · intro ε hε
    have hdsmall := hdlim.eventually_lt_const (show (0 : ℝ) < ε/2 by positivity)
    have htwo := (logScale_atTop.const_div_atTop (2 : ℝ)).eventually_lt_const
      (show (0 : ℝ) < ε/2 by positivity)
    filter_upwards [hBl,hdsmall,htwo] with z hzb hzd hz2
    have hd' := (div_lt_iff₀ (logScale_pos z)).mp hzd
    have htwo' := (div_lt_iff₀ (logScale_pos z)).mp hz2
    have hl := (hprofile z).1
    linarith

/-- An asymptotic logarithmic upper bound automatically supplies the global
envelope required by the packet-selection theorem. -/
lemma global_envelope_of_upper_tail (A : Set ℕ) (c : ℝ)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep A z : ℝ) ≤ (c+ε)*logScale z) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu 1 (by norm_num))
  refine ⟨(N : ℝ)+1,|c|+1,by positivity,by positivity,?_⟩
  intro z
  by_cases hz : N ≤ z
  · have hh := hN z hz
    have hcoeff := mul_le_mul_of_nonneg_right
      (show c+1 ≤ |c|+1 by linarith [le_abs_self c]) (logScale_pos z).le
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  · have hb : (sumRep A z : ℝ) ≤ (z : ℝ)+1 := by
      exact_mod_cast Erdos66Counting.sumRep_le_succ A z
    have hz' : (z : ℝ) ≤ N := by exact_mod_cast (show z ≤ N by omega)
    have hp : 0 ≤ (|c|+1)*logScale z := mul_nonneg (by positivity) (logScale_pos z).le
    linarith

/-- The actual-deficit criterion needs only the asymptotic upper bound; no
separate global envelope or exceptional-target enumeration is required. -/
theorem completion_of_upper_tail_and_summable_deficit (A : Set ℕ) (c : ℝ)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (d : ℕ → ℝ) (hd : ∀ z, 0 ≤ d z)
    (hdlim : Tendsto (fun z ↦ d z/logScale z) atTop (𝓝 0))
    (hs : Summable (fun z ↦ deficit A c d z*packetWeight z)) :
    ∃ B : Set ℕ, A ⊆ B ∧
      Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  obtain ⟨K,C,hK,hC,hA⟩ := global_envelope_of_upper_tail A c hu
  exact completion_of_summable_deficit A c K C hK hC hA hu d hd hdlim hs

end Erdos66DeficitWeightedCompletion
