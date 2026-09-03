import Submission.WeightedIntervalDiscrepancy
import Submission.RationalRotationCount

/-! Ordinary irrational-rotation interval means, proved from the finite
Fejer discrepancy estimate and bounded geometric sums. All natural cutoffs
are allowed. No primality statement is asserted. -/
namespace Erdos972OrdinaryRotationMean

open Finset Filter Complex
open scoped Topology
open Erdos972ExponentialSum Erdos972DiscreteFejer Erdos972WeightedIntervalDiscrepancy
open Erdos972RationalRotationCount

lemma phase_ne_one_of_irrational {θ : ℝ} (hθ : Irrational θ) : phase θ ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hi := congrArg Complex.im hk
  have hi' : 2*Real.pi*θ = (k : ℝ)*(2*Real.pi) := by
    simpa [phase, Complex.mul_im] using hi
  apply hθ.ne_int k
  nlinarith only [hi', Real.pi_pos]

lemma ordinary_geometric_bound {θ : ℝ} (hθ : Irrational θ) (K : ℕ) :
    ‖∑ n ∈ range K, phase (θ*n)‖ ≤ 2/‖phase θ-1‖ := by
  simp_rw [phase_nat_mul]
  rw [geom_sum_eq (phase_ne_one_of_irrational hθ), norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have hh := norm_sub_le (phase θ^K) (1 : ℂ)
  norm_num only [norm_pow, norm_phase, one_pow, norm_one] at hh
  exact hh

noncomputable def frequencyBudget (θ : ℝ) (H : ℕ) : ℝ :=
  ∑ i ∈ range H, ∑ j ∈ range H, 2/‖phase (((i : ℝ)-j)*θ)-1‖

lemma frequencyBudget_nonneg (θ : ℝ) (H : ℕ) : 0 ≤ frequencyBudget θ H := by
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

lemma ordinary_fourier_bound {θ : ℝ} (hθ : Irrational θ) (β : ℝ)
    (K H : ℕ) {i j : ℕ} (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ‖weightedFourier (range K) (fun _ => 1) (fun n => θ*n+β) ((i : ℝ)-j)‖ ≤
      frequencyBudget θ H := by
  have hz : (i : ℤ)-j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  have hirr : Irrational (((i : ℝ)-j)*θ) := by
    simpa only [Int.cast_sub, Int.cast_natCast] using hθ.intCast_mul hz
  have he : weightedFourier (range K) (fun _ => 1) (fun n => θ*n+β) ((i : ℝ)-j) =
      phase (((i : ℝ)-j)*β) * ∑ n ∈ range K, phase ((((i : ℝ)-j)*θ)*n) := by
    unfold weightedFourier
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    simp only [Complex.ofReal_one, one_mul]
    rw [show ((i : ℝ)-j)*(θ*n+β) = ((i : ℝ)-j)*β+(((i : ℝ)-j)*θ)*n by ring,
      phase_add]
  rw [he, norm_mul, norm_phase, one_mul]
  apply (ordinary_geometric_bound hirr K).trans
  unfold frequencyBudget
  have hinner : 2/‖phase (((i : ℝ)-j)*θ)-1‖ ≤
      ∑ k ∈ range H, 2/‖phase (((i : ℝ)-k)*θ)-1‖ :=
    single_le_sum (f := fun k : ℕ => (2 : ℝ)/‖phase (((i : ℝ)-k)*θ)-1‖)
      (fun k _ => by positivity) (mem_range.mpr hj)
  have houter : (∑ k ∈ range H, 2/‖phase (((i : ℝ)-k)*θ)-1‖) ≤
      ∑ l ∈ range H, ∑ k ∈ range H, 2/‖phase (((l : ℝ)-k)*θ)-1‖ :=
    single_le_sum (f := fun l : ℕ => ∑ k ∈ range H, (2 : ℝ)/‖phase (((l : ℝ)-k)*θ)-1‖)
      (fun l _ => sum_nonneg fun k _ => by positivity) (mem_range.mpr hi)
  exact hinner.trans houter

noncomputable def ordinaryArc (θ β a b : ℝ) (K : ℕ) : Finset ℕ :=
  (range K).filter (fun n => a ≤ Int.fract (θ*n+β) ∧ Int.fract (θ*n+β) < b)

lemma ordinary_arc_discrepancy {θ : ℝ} (hθ : Irrational θ) (β : ℝ) (K : ℕ)
    {H : ℕ} [NeZero H] {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hδa : δ ≤ a) (hδb : δ ≤ 1-b) :
    |((ordinaryArc θ β a b K).card : ℝ)-(b-a)*K| ≤
      (2*δ+1/(H : ℝ)+4/((4*δ)^2*H))*K+H*frequencyBudget θ H := by
  have hh := weighted_interval_discrepancy (range K) (fun _ => 1) (fun n => θ*n+β)
    (fun _ _ => by norm_num) a b δ (frequencyBudget θ H) hab hδ hδa hδb
    (frequencyBudget_nonneg θ H) (fun _ _ hi hj hij => ordinary_fourier_bound hθ β K H hi hj hij)
  simpa only [ordinaryArc, sum_const, nsmul_eq_mul, mul_one, card_range] using hh

/-- Every proper interval strictly inside the circle has its expected
ordinary mean, at every fixed starting phase. -/
theorem ordinary_arc_mean {θ : ℝ} (hθ : Irrational θ) (β : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun K : ℕ => ((ordinaryArc θ β a b K).card : ℝ)/(K : ℝ)) atTop (𝓝 (b-a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min a (min (1-b) (ε/8))
  have hδ : 0 < δ := lt_min ha (lt_min (by linarith) (by positivity))
  have hδa : δ ≤ a := min_le_left _ _
  have hδb : δ ≤ 1-b := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hlim : Tendsto (fun H : ℕ => (1+4/(4*δ)^2)/(H : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨H, hH, hH0⟩ := (((tendsto_order.mp hlim).2 (ε/4) (by positivity)).and
    (eventually_ge_atTop (1 : ℕ))).exists
  letI : NeZero H := ⟨Nat.ne_of_gt hH0⟩
  have hlimK : Tendsto (fun K : ℕ => (H : ℝ)*frequencyBudget θ H/(K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.mp hlimK).2 (ε/4) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with K hK hK0
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK0
  have hh := div_le_div_of_nonneg_right (ordinary_arc_discrepancy (H := H) hθ β K hab hδ hδa hδb) hKR.le
  have he : |((ordinaryArc θ β a b K).card : ℝ)/(K : ℝ)-(b-a)| =
      |((ordinaryArc θ β a b K).card : ℝ)-(b-a)*K|/(K : ℝ) := by
    have hquot : ((ordinaryArc θ β a b K).card : ℝ)/(K : ℝ)-(b-a) =
        (((ordinaryArc θ β a b K).card : ℝ)-(b-a)*K)/(K : ℝ) := by field_simp
    rw [hquot, abs_div, abs_of_pos hKR]
  have he2 : ((2*δ+1/(H : ℝ)+4/((4*δ)^2*H))*K+H*frequencyBudget θ H)/(K : ℝ) =
      2*δ+(1+4/(4*δ)^2)/(H : ℝ)+(H : ℝ)*frequencyBudget θ H/(K : ℝ) := by
    field_simp
    ring
  rw [he2] at hh
  rw [Real.dist_eq, he]
  linarith only [hh, hH, hK, hδε, hε]

lemma fract_shift_arc {x s t : ℝ} (hs : 0 < s) (hst : s+t < 1) (ht : 0 ≤ t) :
    (s ≤ Int.fract (x+s) ∧ Int.fract (x+s) < s+t) ↔ Int.fract x < t := by
  have he : Int.fract (x+s) = Int.fract (Int.fract x+s) := by
    have hh : x+s = (Int.fract x+s)+(⌊x⌋ : ℝ) := by linarith only [Int.fract_add_floor x]
    rw [hh, Int.fract_add_intCast]
  rw [he]
  by_cases hw : Int.fract x+s < 1
  · rw [Int.fract_eq_self.mpr ⟨by linarith only [Int.fract_nonneg x, hs], hw⟩]
    constructor
    · intro h; linarith only [h.2]
    · intro h; constructor <;> linarith only [h, Int.fract_nonneg x]
  · have hf : Int.fract (Int.fract x+s) = Int.fract x+s-1 := by
      rw [show Int.fract x+s = (Int.fract x+s-1)+1 by ring, Int.fract_add_one, add_sub_cancel_right]
      apply Int.fract_eq_self.mpr
      constructor <;> linarith only [hw, Int.fract_lt_one x, hst, ht]
    rw [hf]
    constructor
    · intro h; linarith only [h.1, Int.fract_lt_one x]
    · intro h; exfalso; linarith only [h, hw, hst]

/-- Initial fractional-part arcs, including the exact endpoint convention
used by the divisor rows. -/
theorem rotationInterval_mean {θ t : ℝ} (hθ : Irrational θ) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun K : ℕ => ((rotationInterval θ K 0 t).card : ℝ)/(K : ℝ)) atTop (𝓝 t) := by
  let s := (1-t)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hst : s+t < 1 := by dsimp [s]; linarith
  have he (K : ℕ) : ordinaryArc θ s s (s+t) K = rotationInterval θ K 0 t := by
    ext n
    simp only [ordinaryArc, rotationInterval, mem_filter, Int.fract_nonneg, true_and,
      fract_shift_arc hs hst ht.le]
  have hh := ordinary_arc_mean hθ s hs (show s ≤ s+t by linarith) hst
  simpa only [he, add_sub_cancel_left] using hh

#print axioms ordinary_arc_mean
#print axioms rotationInterval_mean

end Erdos972OrdinaryRotationMean
