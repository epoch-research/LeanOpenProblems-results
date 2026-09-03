import Submission.CofinalMangoldtUnit
import Submission.IntervalPrimeWeights

/-!
# Unit-slope good cutoffs in every bounded-ratio interval

The bounded error in the logarithmic mean gives more than cofinality:
for each c<1, a fixed K suffices to find theta(N)>c*N between A and K*A
for every positive A. No claim of a pointwise prime number theorem is made.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma reciprocal_interval_le_of_prefix_linear (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (A B : ℕ) (hA : 1 ≤ A) (hAB : A < B) (c : ℝ) (hc : 0 ≤ c)
    (H : ∀ n ∈ Icc A B, (∑ i ∈ range n, f i) ≤ c*n) :
    (∑ i ∈ Ico A B, f i/((i : ℝ)+1)) ≤ c*(1+Real.log ((B : ℝ)/A)) := by
  let w : ℕ → ℝ := fun i => 1/((i : ℝ)+1)
  let P : ℕ → ℝ := fun n => ∑ i ∈ range n, f i
  have hP (n : ℕ) : 0 ≤ P n := sum_nonneg (fun i _ => hf i)
  have hw0 (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hwmono : Antitone w := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hab := sum_Ico_by_parts w f hAB
  simp only [smul_eq_mul] at hab
  have he : (∑ i ∈ Ico A B, f i/((i : ℝ)+1)) =
      w (B-1)*P B + ∑ i ∈ Ico A (B-1), (w i-w (i+1))*P (i+1) - w A*P A := by
    have hs : (∑ i ∈ Ico A (B-1), (w i-w (i+1))*P (i+1)) =
        -(∑ i ∈ Ico A (B-1), (w (i+1)-w i)*P (i+1)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hs]
    simpa only [w,P,div_eq_mul_inv,one_mul,mul_comm,sub_eq_add_neg,add_assoc,add_left_comm,add_comm]
      using hab
  have hfirst : w (B-1)*P B ≤ c := by
    have hb := H B (mem_Icc.mpr ⟨hAB.le,le_rfl⟩)
    have hh := mul_le_mul_of_nonneg_left hb (hw0 (B-1))
    have hB1 : 1 ≤ B := by omega
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB1
    have heq : w (B-1)*(c*B)=c := by
      dsimp [w]
      rw [Nat.cast_sub hB1,Nat.cast_one,sub_add_cancel]
      field_simp
    exact hh.trans_eq heq
  have hterm (i : ℕ) (hi : i ∈ Ico A (B-1)) :
      (w i-w (i+1))*P (i+1) ≤ c/((i : ℝ)+1) := by
    obtain ⟨hAi,hiB⟩ := mem_Ico.mp hi
    have hb := H (i+1) (mem_Icc.mpr ⟨by omega,by omega⟩)
    have hd : 0 ≤ w i-w (i+1) := sub_nonneg.mpr (hwmono (Nat.le_succ i))
    have heq : (w i-w (i+1))*(c*(i+1 : ℕ)) = c/((i : ℝ)+2) := by
      dsimp [w]
      push_cast
      field_simp
      ring
    calc
      _ ≤ (w i-w (i+1))*(c*(i+1 : ℕ)) := mul_le_mul_of_nonneg_left hb hd
      _ = _ := heq
      _ ≤ _ := div_le_div_of_nonneg_left hc (by positivity) (by linarith)
  have hsum : (∑ i ∈ Ico A (B-1), (w i-w (i+1))*P (i+1)) ≤
      c*Real.log ((B : ℝ)/A) := by
    calc
      _ ≤ ∑ i ∈ Ico A (B-1), c/((i : ℝ)+1) := sum_le_sum hterm
      _ ≤ ∑ i ∈ Ico A B, c/((i : ℝ)+1) :=
        sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (Nat.sub_le B 1))
          (fun i _ _ => by positivity)
      _ = c*∑ i ∈ Icc (A+1) B, (i : ℝ)⁻¹ := by
        rw [mul_sum,← Ico_add_one_right_eq_Icc,← sum_Ico_add' (fun i : ℕ => c*(i : ℝ)⁻¹) A B 1]
        simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Sieve.sum_inv_interval_le_log_ratio A B hA hAB.le) hc
  rw [he]
  have hlast : 0 ≤ w A*P A := mul_nonneg (hw0 A) (hP A)
  nlinarith only [hfirst,hsum,hlast]

lemma prime_log_reciprocal_interval (A B : ℕ) (hAB : A ≤ B) :
    (∑ i ∈ Ico A B, (if (i+1).Prime then Real.log (i+1 : ℕ) else 0)/((i : ℝ)+1)) =
      primeLogMass B-primeLogMass A := by
  rw [← prime_log_shift_reciprocal_sum B,← prime_log_shift_reciprocal_sum A]
  have h := sum_range_add_sum_Ico
    (fun i => (if (i+1).Prime then Real.log (i+1 : ℕ) else 0)/((i : ℝ)+1)) hAB
  linarith only [h]

/-- A fixed ratio K works uniformly for all starting points A>=1. -/
theorem exists_bounded_gap_theta_unit (c : ℝ) (hc : c < 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ A : ℕ, 1 ≤ A →
      ∃ N ∈ Icc A (K*A), c*N < Chebyshev.theta (N : ℝ) := by
  let c' := max 0 c
  have hc' : 0 ≤ c' := le_max_left _ _
  have hc'1 : c' < 1 := max_lt (by norm_num) hc
  obtain ⟨C,hC,HC⟩ := exists_primeLogMass_log_bound
  have hlim : Tendsto (fun K : ℕ => (1-c')*Real.log (K : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (sub_pos.mpr hc'1)
  obtain ⟨K,hK,hlarge⟩ := ((eventually_ge_atTop 2).and
    (hlim.eventually (eventually_gt_atTop (2*C+c')))).exists
  refine ⟨K,hK,?_⟩
  intro A hA
  by_contra hnot
  push_neg at hnot
  have hbound (N : ℕ) (hN : N ∈ Icc A (K*A)) : Chebyshev.theta (N : ℝ) ≤ c'*N :=
    (hnot N hN).trans
      (mul_le_mul_of_nonneg_right (le_max_right 0 c) (Nat.cast_nonneg _))
  have hAB : A < K*A := by nlinarith
  have hu := reciprocal_interval_le_of_prefix_linear
    (fun i => if (i+1).Prime then Real.log (i+1 : ℕ) else 0)
    (fun i => by dsimp only; split_ifs; exact Real.log_natCast_nonneg _; exact le_rfl)
    A (K*A) hA hAB c' hc' (by
      intro N hN
      rw [prime_log_shift_sum]
      exact hbound N hN)
  rw [prime_log_reciprocal_interval A (K*A) hAB.le] at hu
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  rw [Nat.cast_mul,mul_div_cancel_right₀ _ hAR] at hu
  have hlo := (abs_le.mp (HC (K*A) (by nlinarith))).1
  have hhi := (abs_le.mp (HC A hA)).2
  rw [Nat.cast_mul,Real.log_mul hKR hAR] at hlo
  nlinarith only [hu,hlo,hhi,hlarge]

lemma theta_nat_le_mangoldtSum (N : ℕ) : Chebyshev.theta (N : ℝ) ≤ mangoldtSum N := by
  rw [Sieve.theta_nat_eq_sum_primesBelow]
  have he : (∑ p ∈ (N+1).primesBelow, Real.log p) =
      ∑ p ∈ (N+1).primesBelow, vonMangoldt p := by
    apply sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hp).2]
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpr.pos,by omega⟩
  · exact fun p _ _ => vonMangoldt_nonneg

theorem exists_bounded_gap_mangoldt_unit (c : ℝ) (hc : c < 1) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ A : ℕ, 1 ≤ A →
      ∃ N ∈ Icc A (K*A), c*N < mangoldtSum N := by
  obtain ⟨K,hK,HK⟩ := exists_bounded_gap_theta_unit c hc
  refine ⟨K,hK,?_⟩
  intro A hA
  obtain ⟨N,hN,hgood⟩ := HK A hA
  exact ⟨N,hN,hgood.trans_le (theta_nat_le_mangoldtSum N)⟩

end Erdos821
