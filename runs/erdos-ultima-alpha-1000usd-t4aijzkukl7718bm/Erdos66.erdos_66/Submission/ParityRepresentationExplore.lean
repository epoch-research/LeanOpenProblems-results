import Submission.WitnessTwistedEnergyExplore

/-! Exact natural parity splitting, retaining the carry between two odd
summands. The energy conclusion is mean-square, not pointwise. -/
namespace Erdos66ParityRepresentation
open Erdos66TwistedEnergy Erdos66WitnessTwistedEnergy
  Erdos66WitnessAutocorrelation Erdos66Generating Erdos66Rounding
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2200000

lemma sum_range_double (u : ℕ → ℝ) (n : ℕ) :
    (∑ k∈Finset.range (2*n), u k)=
      (∑ k∈Finset.range n, u (2*k))+(∑ k∈Finset.range n, u (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih]
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    ring

lemma sum_range_double_succ (u : ℕ → ℝ) (n : ℕ) :
    (∑ k∈Finset.range (2*n+1), u k)=
      (∑ k∈Finset.range (n+1), u (2*k))+(∑ k∈Finset.range n, u (2*k+1)) := by
  rw [Finset.sum_range_succ,sum_range_double,Finset.sum_range_succ]
  ring

noncomputable def evenPart (f : ℕ → ℝ) (n : ℕ) : ℝ := f (2*n)
noncomputable def oddPart (f : ℕ → ℝ) (n : ℕ) : ℝ := f (2*n+1)

lemma sumConv_range (f g : ℕ → ℝ) (n : ℕ) :
    sumConv f g n=∑ k∈Finset.range (n+1), f k*g (n-k) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

lemma sumConv_odd (f g : ℕ → ℝ) (n : ℕ) :
    sumConv f g (2*n+1)=sumConv (evenPart f) (oddPart g) n+
      sumConv (oddPart f) (evenPart g) n := by
  rw [sumConv_range,show 2*n+1+1=2*(n+1) by omega,sum_range_double]
  rw [sumConv_range,sumConv_range]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 2*n+1-2*k=2*(n-k)+1 := by omega
    simp only [evenPart,oddPart,he]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 2*n+1-(2*k+1)=2*(n-k) := by omega
    simp only [evenPart,oddPart,he]

lemma sumConv_even_succ (f g : ℕ → ℝ) (n : ℕ) :
    sumConv f g (2*(n+1))=sumConv (evenPart f) (evenPart g) (n+1)+
      sumConv (oddPart f) (oddPart g) n := by
  rw [sumConv_range,sum_range_double_succ]
  rw [sumConv_range,sumConv_range]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 2*(n+1)-2*k=2*(n+1-k) := by omega
    simp only [evenPart,he]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 2*(n+1)-(2*k+1)=2*(n-k)+1 := by omega
    simp only [oddPart,he]

lemma evenPart_alt (f : ℕ → ℝ) : evenPart (alt f)=evenPart f := by
  funext n
  simp [evenPart,alt]

lemma oddPart_alt (f : ℕ → ℝ) : oddPart (alt f)=fun n ↦ -oddPart f n := by
  funext n
  simp [oddPart,alt,pow_add]

lemma sumConv_neg_right (f g : ℕ → ℝ) (n : ℕ) :
    sumConv f (fun k ↦ -g k) n= -sumConv f g n := by
  simp only [sumConv,mul_neg,Finset.sum_neg_distrib]

lemma twist_odd (f : ℕ → ℝ) (n : ℕ) : twistConv f (2*n+1)=0 := by
  rw [twistConv,sumConv_odd,evenPart_alt,oddPart_alt,sumConv_neg_right,
    sumConv_comm_real (oddPart f) (evenPart f)]
  ring

lemma twist_even_succ (f : ℕ → ℝ) (n : ℕ) :
    twistConv f (2*(n+1))=sumConv (evenPart f) (evenPart f) (n+1)-
      sumConv (oddPart f) (oddPart f) n := by
  rw [twistConv,sumConv_even_succ,evenPart_alt,oddPart_alt,sumConv_neg_right,sub_eq_add_neg]

noncomputable def evenSet (A : Set ℕ) : Set ℕ := {n | 2*n∈A}
noncomputable def oddSet (A : Set ℕ) : Set ℕ := {n | 2*n+1∈A}

lemma sumConv_indicator (A : Set ℕ) (n : ℕ) :
    sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) := sum_indicator_antidiagonal A n

lemma evenPart_indicator (A : Set ℕ) : evenPart (indicator A)=indicator (evenSet A) := rfl
lemma oddPart_indicator (A : Set ℕ) : oddPart (indicator A)=indicator (oddSet A) := rfl

/-- At a positive even target the odd/odd term has a carry. -/
theorem sumRep_even_succ (A : Set ℕ) (n : ℕ) :
    sumRep A (2*(n+1))=sumRep (evenSet A) (n+1)+sumRep (oddSet A) n := by
  have hh := sumConv_even_succ (indicator A) (indicator A) n
  simp only [evenPart_indicator,oddPart_indicator,sumConv_indicator] at hh
  exact_mod_cast hh

theorem sumRep_odd (A : Set ℕ) (n : ℕ) :
    (sumRep A (2*n+1) : ℝ)=2*sumConv (indicator (evenSet A)) (indicator (oddSet A)) n := by
  have hh := sumConv_odd (indicator A) (indicator A) n
  simp only [evenPart_indicator,oddPart_indicator,sumConv_indicator,
    sumConv_comm_real (indicator (oddSet A)) (indicator (evenSet A))] at hh
  linarith

theorem twist_even_sumRep (A : Set ℕ) (n : ℕ) :
    twistConv (indicator A) (2*(n+1))=
      (sumRep (evenSet A) (n+1) : ℝ)-(sumRep (oddSet A) n : ℝ) := by
  simpa only [evenPart_indicator,oddPart_indicator,sumConv_indicator] using
    twist_even_succ (indicator A) n

/-- Odd targets give a genuine pointwise mixed limit. -/
theorem witness_mixed_parity_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ sumConv (indicator (evenSet A)) (indicator (oddSet A)) n/Real.log n)
      atTop (𝓝 (c/2)) := by
  have hh := (Erdos66ResidueSeries.affine_log_limit 2 h 1).div_const 2
  apply hh.congr'
  filter_upwards [] with n
  rw [Nat.mul_comm n 2,sumRep_odd]
  ring

/-- Even targets give a pointwise limit of the SUM of the two self-counts,
not separate pointwise limits. -/
theorem witness_parity_self_sum_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ ((sumRep (evenSet A) (n+1) : ℝ)+(sumRep (oddSet A) n : ℝ))/Real.log n)
      atTop (𝓝 c) := by
  have hh := Erdos66ResidueSeries.affine_log_limit 2 h 2
  apply hh.congr'
  filter_upwards [] with n
  rw [show n*2+2=2*(n+1) by omega,sumRep_even_succ,Nat.cast_add]

noncomputable def parityImbalanceEnergy (A : Set ℕ) (r : ℝ) : ℝ :=
  ∑' n, (((sumRep (evenSet A) (n+1) : ℝ)-(sumRep (oddSet A) n : ℝ))*r^(2*(n+1)))^2

lemma parityImbalanceEnergy_le (A : Set ℕ) {r : ℝ} (hr0 : 0<r) (hr1 : r<1) :
    parityImbalanceEnergy A r ≤ twistEnergy A r := by
  have ht := (witness_twisted_bound A (c := 0) (by norm_num) hr0 hr1).1
  have hi : Function.Injective (fun n : ℕ ↦ 2*(n+1)) := by intro i j he; dsimp at he; omega
  have hs := ht.comp_injective hi
  have hsub := Summable.tsum_le_tsum_of_inj (fun n : ℕ ↦ 2*(n+1)) hi
    (fun n _ ↦ sq_nonneg (twistConv (indicator A) n*r^n))
    (fun n ↦ le_rfl) hs ht
  simpa only [Function.comp_apply,twist_even_sumRep,parityImbalanceEnergy,twistEnergy] using hsub

/-- A mean-square parity consequence of the witness, with the exact carry.
It does not rule out a sparse collection of imbalanced targets. -/
theorem witness_normalized_parity_imbalance_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun r : ℝ ↦ parityImbalanceEnergy A r*squareKernel r) (𝓝[<] 1) (𝓝 0) := by
  apply squeeze_zero' _ _ (witness_normalized_twist_zero h)
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_nonneg (tsum_nonneg (fun _ ↦ sq_nonneg _)) (squareKernel_nonneg hr.2)
  · filter_upwards [unit_interval_eventually] with r hr
    exact mul_le_mul_of_nonneg_right (parityImbalanceEnergy_le A hr.1 hr.2)
      (squareKernel_nonneg hr.2)

end Erdos66ParityRepresentation
