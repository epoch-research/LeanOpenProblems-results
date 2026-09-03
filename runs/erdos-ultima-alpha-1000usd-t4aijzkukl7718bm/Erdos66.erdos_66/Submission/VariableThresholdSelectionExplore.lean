import Submission.VarianceMatchingExponentialExplore

/-! A finite two-sided exponential selector with a separate tilt and
threshold for every row. -/
namespace Erdos66VariableThresholdSelection
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 2400000
variable {Ω κ ι : Type*} [Fintype Ω] [Nonempty Ω]

/-- Each requested row keeps its own scale. The finite lists remain explicit. -/
theorem exists_variable_thresholds (S : Finset κ) (T : Finset ι)
    (X : κ → ι → Ω → ℝ) (t R : κ → ℝ) (ell : ℝ)
    (ht : ∀ k∈S, 0<t k)
    (hplus : ∀ k∈S, ∀ q∈T,
      mean (fun ω ↦ Real.exp (t k*X k q ω-t k*R k))≤Real.exp (-ell))
    (hminus : ∀ k∈S, ∀ q∈T,
      mean (fun ω ↦ Real.exp (-t k*X k q ω-t k*R k))≤Real.exp (-ell))
    (hbudget : 2*(S.card:ℝ)*T.card*Real.exp (-ell)<1) :
    ∃ ω : Ω, ∀ k∈S, ∀ q∈T, |X k q ω|<R k := by
  let P (k : κ) (q : ι) (ω : Ω) :=
    Real.exp (t k*X k q ω-t k*R k)+Real.exp (-t k*X k q ω-t k*R k)
  let total (ω : Ω) := ∑ k∈S, ∑ q∈T, P k q ω
  have hp0 (k q ω) : 0≤P k q ω := by dsimp [P]; positivity
  have hm (k : κ) (hk : k∈S) (q : ι) (hq : q∈T) : mean (P k q)≤2*Real.exp (-ell) := by
    change mean (fun ω ↦ Real.exp (t k*X k q ω-t k*R k)+
      Real.exp (-t k*X k q ω-t k*R k))≤_
    rw [mean_add]
    linarith only [hplus k hk q hq,hminus k hk q hq]
  have htot : mean total<1 := by
    unfold total
    rw [mean_sum]
    simp_rw [mean_sum]
    calc
      _ ≤ ∑ k∈S, ∑ q∈T, 2*Real.exp (-ell) :=
        Finset.sum_le_sum (fun k hk ↦ Finset.sum_le_sum (fun q hq ↦ hm k hk q hq))
      _ = 2*(S.card:ℝ)*T.card*Real.exp (-ell) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ < 1 := hbudget
  obtain ⟨ω,hω⟩ := exists_lt_of_mean_lt total 1 htot
  refine ⟨ω,fun k hk q hq ↦ ?_⟩
  have hrow : P k q ω≤total ω := by
    apply le_trans (Finset.single_le_sum (fun j _ ↦ hp0 k j ω) hq)
    exact Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hp0 i j ω)) hk
  have hp : Real.exp (t k*X k q ω-t k*R k)<1 :=
    (le_add_of_nonneg_right (Real.exp_pos _).le).trans_lt (hrow.trans_lt hω)
  have hn : Real.exp (-t k*X k q ω-t k*R k)<1 :=
    (le_add_of_nonneg_left (Real.exp_pos _).le).trans_lt (hrow.trans_lt hω)
  have hp' := Real.exp_lt_one_iff.mp hp
  have hn' := Real.exp_lt_one_iff.mp hn
  rw [abs_lt]
  constructor <;> nlinarith only [hp',hn',ht k hk]

end Erdos66VariableThresholdSelection
