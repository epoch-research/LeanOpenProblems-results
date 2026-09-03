import FormalConjecturesUtil

/-! Finite aggregation of logarithmic errors by total expected mass. -/
namespace Erdos66FiniteLogMassBudget
open scoped Classical

lemma log_one_add_le_two_sqrt (x : ℝ) (hx : 0≤x) :
    Real.log (x+1)≤2*Real.sqrt x := by
  have hs := Real.sq_sqrt hx
  have hsn := Real.sqrt_nonneg x
  have harg : x+1≤(Real.sqrt x+1)^2 := by nlinarith
  have hl := Real.log_le_log (show 0<x+1 by positivity) harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hh := Real.log_le_sub_one_of_pos (show 0<Real.sqrt x+1 by positivity)
  linarith

lemma sum_sqrt_le_sqrt_card_mass {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S, 0≤f i) :
    (∑ i∈S, Real.sqrt (f i)) ≤ Real.sqrt ((S.card : ℝ)*∑ i∈S, f i) := by
  apply (Real.le_sqrt (Finset.sum_nonneg (fun _ _ ↦ Real.sqrt_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg hf))).mpr
  have hh := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i ↦ Real.sqrt (f i))
  have he : (∑ i∈S, (Real.sqrt (f i))^2)=∑ i∈S, f i :=
    Finset.sum_congr rfl (fun i hi ↦ Real.sq_sqrt (hf i hi))
  simpa only [he] using hh

noncomputable def budget (K P : ℝ) : ℝ := 30*K+100*Real.sqrt (K*P)

lemma budget_nonneg (K P : ℝ) (hK : 0≤K) : 0≤budget K P := by
  unfold budget
  positivity

lemma budget_mono_mass (K P R : ℝ) (hK : 0≤K) (hPR : P≤R) :
    budget K P≤budget K R := by
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPR hK)
  unfold budget
  linarith

lemma log_budget_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S, 0≤f i) :
    (∑ i∈S, (30+50*Real.log (f i+1))) ≤ budget S.card (∑ i∈S, f i) := by
  calc
    _ ≤ ∑ i∈S, (30+100*Real.sqrt (f i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := log_one_add_le_two_sqrt (f i) (hf i hi)
      linarith
    _ = 30*(S.card : ℝ)+100*∑ i∈S, Real.sqrt (f i) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
      ring
    _ ≤ budget S.card (∑ i∈S, f i) := by
      unfold budget
      have hh := sum_sqrt_le_sqrt_card_mass S f hf
      linarith

end Erdos66FiniteLogMassBudget
