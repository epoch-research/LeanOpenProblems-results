import Submission.ParityRepresentationExplore
import Submission.TauberianProfileExplore

/-! Positivity transfers a logarithmic-square Abel little-o estimate to
ordinary prefix sums. No pointwise or exceptional-set sparsity rate follows. -/
namespace Erdos66AbelSquarePrefix
open Erdos66TwistedEnergy Erdos66WitnessAutocorrelation Erdos66TauberianProfile
  Erdos66ParityRepresentation Erdos66WitnessTwistedEnergy
  Erdos66Generating Erdos66Counting
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2200000

lemma squareKernel_radius (N : ℕ) :
    squareKernel (radius N)=1/((N : ℝ)*(Real.log N)^2) := by
  simp only [squareKernel,radius,sub_sub_cancel,one_div,Real.log_inv,neg_neg]
  field_simp

lemma prefix_weighted_bound (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (k N : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : Summable (fun n ↦ f n*r^(k*(n+1)))) :
    (∑ n∈Finset.range N, f n)*r^(k*N) ≤ ∑' n, f n*r^(k*(n+1)) := by
  calc
    _ = ∑ n∈Finset.range N, f n*r^(k*N) := Finset.sum_mul ..
    _ ≤ ∑ n∈Finset.range N, f n*r^(k*(n+1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0 hr1 (Nat.mul_le_mul_left k (Finset.mem_range.mp hn))) (hf n)
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ ↦ mul_nonneg (hf n) (pow_nonneg hr0 _))

/-- A vanishing weighted nonnegative energy implies vanishing cumulative
energy at scale N log² N. The exponent includes a possible fixed shift. -/
theorem prefix_zero_of_weighted_zero (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (k : ℕ)
    (hs : ∀ r : ℝ, 0<r → r<1 → Summable (fun n ↦ f n*r^(k*(n+1))))
    (h : Tendsto (fun r : ℝ ↦ (∑' n, f n*r^(k*(n+1)))*squareKernel r)
      (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (∑ n∈Finset.range N, f n)/((N : ℝ)*(Real.log N)^2))
      atTop (𝓝 0) := by
  have hh := (h.comp radius_tendsto).div (radius_pow_tendsto.pow k)
    (pow_ne_zero k (Real.exp_ne_zero _))
  simp only [zero_div] at hh
  apply squeeze_zero' _ _ hh
  · exact Eventually.of_forall (fun N ↦ div_nonneg
      (Finset.sum_nonneg (fun n _ ↦ hf n)) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hr := radius_bounds hN
    have hb := mul_le_mul_of_nonneg_right
      (prefix_weighted_bound f hf k N hr.1.le hr.2.le (hs _ hr.1 hr.2))
      (squareKernel_nonneg hr.2)
    have hp : 0<(radius N^N)^k := pow_pos (pow_pos hr.1 N) k
    apply (le_div_iff₀ hp).mpr
    simpa only [Function.comp_apply,squareKernel_radius,one_div,← pow_mul,
      Nat.mul_comm N k,div_eq_mul_inv,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb

noncomputable def parityDifference (A : Set ℕ) (n : ℕ) : ℝ :=
  (sumRep (evenSet A) (n+1) : ℝ)-(sumRep (oddSet A) n : ℝ)

lemma parityImbalanceEnergy_eq (A : Set ℕ) (r : ℝ) :
    parityImbalanceEnergy A r=∑' n, parityDifference A n^2*r^(4*(n+1)) := by
  apply tsum_congr
  intro n
  simp only [parityDifference,mul_pow,← pow_mul]
  congr 1
  congr 1
  omega

lemma summable_parityDifference (A : Set ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n ↦ parityDifference A n^2*r^(4*(n+1))) := by
  have hi : Function.Injective (fun n : ℕ ↦ 2*(n+1)) := by intro i j he; dsimp at he; omega
  have hh := ((witness_twisted_bound A (c := 0) (by norm_num) hr0 hr1).1).comp_injective hi
  have he (n : ℕ) : (twistConv (indicator A) (2*(n+1))*r^(2*(n+1)))^2=
      parityDifference A n^2*r^(4*(n+1)) := by
    rw [twist_even_sumRep,mul_pow,← pow_mul]
    congr 1
    congr 1
    omega
  change Summable (fun n ↦ (twistConv (indicator A) (2*(n+1))*r^(2*(n+1)))^2) at hh
  simpa only [he] using hh

/-- The parity imbalance has vanishing ordinary mean-square mass at scale
N log² N, not just vanishing Abel mass. -/
theorem witness_parity_prefix_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ (∑ n∈Finset.range N, parityDifference A n^2)/
      ((N : ℝ)*(Real.log N)^2)) atTop (𝓝 0) := by
  apply prefix_zero_of_weighted_zero (fun n ↦ parityDifference A n^2) (fun _ ↦ sq_nonneg _) 4
    (fun r hr0 hr1 ↦ summable_parityDifference A hr0 hr1)
  simpa only [parityImbalanceEnergy_eq] using witness_normalized_parity_imbalance_zero h

end Erdos66AbelSquarePrefix
