import Submission.BernoulliCostSelectionExplore
import Submission.HarmonicExceptionalProfileExplore

/-! Fixed-coefficient constructions with a polynomial saving in the
exceptional set for each fixed tolerance. The saving depends on tolerance. -/
namespace Erdos66PowerExceptionalProfile
open Filter AdditiveCombinatorics Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli
  Erdos66BiasedTailPotential Erdos66ScaledFractionalTail Erdos66HarmonicExceptionalProfile
  Erdos66BernoulliCostSelection
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def saving (c δ : ℝ) : ℝ := δ^2*c/256

noncomputable def powerCost (c δ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((n:ℝ)+2)^(saving c δ) * (potential δ (c*Real.log n) x/((n:ℝ)+2))

noncomputable def powerTail (c δ : ℝ) (n : ℕ) : ℝ :=
  2/((n:ℝ)+2)^(1+saving c δ : ℝ)

lemma saving_pos (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) : 0<saving c δ := by
  unfold saving
  positivity

lemma powerCost_nonneg (c δ : ℝ) (n : ℕ) (x : ℝ) : 0≤powerCost c δ n x := by
  unfold powerCost
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (div_nonneg (potential_nonneg _ _ _) (by positivity))

lemma powerTail_summable (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) : Summable (powerTail c δ) := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 (1+saving c δ)).mpr
    (by have hh := saving_pos c δ hc hδ; linarith)
  have hh := hs.mul_left 2
  simpa only [powerTail,abs_of_nonneg (by positivity : (0:ℝ)≤(↑(_:ℕ):ℝ)+2),mul_one_div]
    using hh

lemma tilted_tail_identity (c δ : ℝ) (n : ℕ) :
    ((n:ℝ)+2)^(saving c δ)*tailBound c δ n = powerTail c δ n := by
  unfold tailBound powerTail
  rw [show 1+δ^2*c/128=(1+saving c δ)+saving c δ by unfold saving; ring,
    Real.rpow_add (by positivity)]
  have hs : ((n:ℝ)+2)^(saving c δ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hs' : ((n:ℝ)+2)^(1+saving c δ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  field_simp

lemma uniform_powerCost_bound (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0<c)
    (ht : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c))
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∀ᶠ n : ℕ in atTop, ∀ L, n≤L → expect (fun i : Fin (L+1) ↦ p i.val)
      (fun ω ↦ powerCost c δ n (sumRep (selected L ω) n)) ≤ powerTail c δ n := by
  obtain ⟨N,hN,hmean⟩ := uniform_weighted_potential_bound p hp c hc ht δ hδ hδ1
  filter_upwards [eventually_ge_atTop N] with n hn
  intro L hL
  unfold powerCost
  rw [expect_const_mul,←tilted_tail_identity]
  exact mul_le_mul_of_nonneg_left (hmean n hn L hL) (Real.rpow_nonneg (by positivity) _)

/-- One fixed-c set has summable power-tilted potentials at all reciprocal
integer tolerances. -/
theorem exists_power_potentials (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, ∀ j : ℕ, Summable (fun n ↦
      powerCost c (1/((j:ℝ)+1)) n (sumRep A n)) := by
  obtain ⟨p,hp,hconv⟩ := exists_scaled_probability_profile c hc
  apply exists_summable_rep_costs p hp
    (fun j n x ↦ powerCost c (1/((j:ℝ)+1)) n x)
    (fun j n ↦ powerTail c (1/((j:ℝ)+1)) n)
  · intro j n
    unfold powerCost
    exact continuous_const.mul ((potential_continuous _ _).div_const _)
  · intro j n x
    exact powerCost_nonneg _ _ _ _
  · intro j
    exact powerTail_summable _ _ hc (by positivity)
  · intro j
    exact uniform_powerCost_bound p hp c hc hconv _ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j]))

lemma weight_identity (α : ℝ) (n : ℕ) :
    1/((n:ℝ)+2)^(1-α : ℝ) = ((n:ℝ)+2)^α/((n:ℝ)+2) := by
  rw [Real.rpow_sub (by positivity),Real.rpow_one]
  field_simp

lemma harmonic_potential_of_power (A : Set ℕ) (c δ : ℝ) (hc : 0<c) (hδ : 0<δ)
    (hs : Summable (fun n ↦ powerCost c δ n (sumRep A n))) :
    Summable (fun n : ℕ ↦ potential δ (c*Real.log n) (sumRep A n)/((n:ℝ)+2)) := by
  apply Summable.of_nonneg_of_le (fun n ↦ div_nonneg (potential_nonneg _ _ _) (by positivity)) _ hs
  intro n
  have hb := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) n])
    (saving_pos c δ hc hδ).le
  rw [Real.rpow_zero] at hb
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0≤potential δ (c*Real.log n) (sumRep A n)/((n:ℝ)+2) from
      div_nonneg (potential_nonneg _ _ _) (by positivity))
  simpa only [one_mul] using hh

lemma power_exceptions_of_potentials (A : Set ℕ) (c : ℝ) (hc : 0<c)
    (hA : ∀ j : ℕ, Summable (fun n ↦ powerCost c (1/((j:ℝ)+1)) n (sumRep A n))) :
    ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
  intro ε hε
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const c
  simp only [zero_mul] at hlim
  obtain ⟨j,hj⟩ := (hlim.eventually_lt_const hε).exists
  let δ : ℝ := 1/((j:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  let α := min (saving c δ) (1/2)
  have hα : 0<α := lt_min (saving_pos c δ hc hδ) (by norm_num)
  have hα1 : α<1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨α,hα,hα1,(hA j).of_norm_bounded_eventually ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 2] with n hn
  by_cases hb : ε≤|(sumRep A n : ℝ)/Real.log n-c|
  · simp only [if_pos hb,Real.norm_eq_abs,abs_of_nonneg (by positivity :
      (0:ℝ)≤1/((n:ℝ)+2)^(1-α : ℝ))]
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hbad : δ*(c*Real.log n) ≤ |(sumRep A n : ℝ)-c*Real.log n| := by
      have hh := mul_le_mul_of_nonneg_right (hj.le.trans hb) hln.le
      have he : (sumRep A n : ℝ)-c*Real.log n =
          ((sumRep A n : ℝ)/Real.log n-c)*Real.log n := by field_simp
      rw [he,abs_mul,abs_of_pos hln]
      dsimp [δ]
      nlinarith
    have hone := one_le_potential δ (c*Real.log n) (sumRep A n) hδ.le hbad
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) n])
      (min_le_left (saving c δ) (1/2))
    rw [weight_identity]
    calc
      _ ≤ ((n:ℝ)+2)^(saving c δ)/((n:ℝ)+2) := div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ powerCost c δ n (sumRep A n) := by
        unfold powerCost
        rw [←mul_div_assoc]
        have hh := mul_le_mul_of_nonneg_left hone
          (Real.rpow_nonneg (by positivity : (0:ℝ)≤(n:ℝ)+2) (saving c δ))
        simpa only [mul_one] using div_le_div_of_nonneg_right hh (by positivity : (0:ℝ)≤(n:ℝ)+2)
  · simp only [if_neg hb,norm_zero]
    exact powerCost_nonneg _ _ _ _

/-- Every fixed tolerance admits a positive power saving, for the SAME set
and the SAME prescribed coefficient. The power may tend to zero with tolerance. -/
theorem exists_power_summable_exceptions (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧ Summable (fun n : ℕ ↦
      if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
  obtain ⟨A,hA⟩ := exists_power_potentials c hc
  exact ⟨A,power_exceptions_of_potentials A c hc hA⟩

end Erdos66PowerExceptionalProfile
