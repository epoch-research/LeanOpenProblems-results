import Submission.MertensPrimeLog
import Submission.RefinedDyadicPartition

/-!
# Bounded harmonic Mangoldt error and discrete weighted differences

The harmonic Mangoldt mass is log N plus a bounded error. Summation by
parts keeps that error at the endpoints instead of charging it once per
geometric interval.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def harmonicMangoldtMass (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, vonMangoldt n/(n : ℝ)

lemma primeLogMass_le_harmonicMangoldtMass (N : ℕ) :
    Erdos821.primeLogMass N ≤ harmonicMangoldtMass N := by
  have he : Erdos821.primeLogMass N =
      ∑ p ∈ (N+1).primesBelow, vonMangoldt p/(p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Nat.mem_primesBelow.mp hp).2]
  rw [he]
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  intro p hp
  obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
  exact mem_Icc.mpr ⟨hpr.pos,by omega⟩

lemma exists_harmonicMangoldtMass_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |harmonicMangoldtMass N-Real.log (N : ℝ)| ≤ C := by
  obtain ⟨C,hC,HC⟩ := Erdos821.exists_primeLogMass_log_bound
  let S : ℝ := ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun n => by
    split_ifs <;> positivity [vonMangoldt_nonneg (n := n)])
  refine ⟨C+S,by positivity,?_⟩
  intro N hN
  have hl := primeLogMass_le_harmonicMangoldtMass N
  have hu := Erdos821.mangoldt_harmonic_le_primeLogMass_add N
  change harmonicMangoldtMass N ≤ Erdos821.primeLogMass N+S at hu
  have hh := abs_le.mp (HC N hN)
  apply abs_le.mpr
  constructor <;> linarith only [hh,hl,hu,hS]

lemma exists_harmonicMangoldtMass_dyadic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      |harmonicMangoldtMass (2^k)-(k : ℝ)*Real.log 2| ≤ C := by
  obtain ⟨C,hC,HC⟩ := exists_harmonicMangoldtMass_log_bound
  refine ⟨C,hC,?_⟩
  intro k
  have hh := HC (2^k) (Nat.one_le_pow _ _ (by decide))
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using hh

lemma weighted_difference_identity (e w : ℕ → ℝ) (R : ℕ) :
    (∑ j ∈ range R, (e (j+1)-e j)*w j) =
      e R*w R-e 0*w 0+∑ j ∈ range R, e (j+1)*(w j-w (j+1)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ,sum_range_succ,ih]
    ring

lemma sum_range_differences (w : ℕ → ℝ) (R : ℕ) :
    (∑ j ∈ range R, (w j-w (j+1))) = w 0-w R := by
  induction R with
  | zero => simp
  | succ R ih => rw [sum_range_succ,ih]; ring

lemma weighted_difference_error_bound (e w : ℕ → ℝ) (R : ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (he : ∀ j ≤ R, |e j| ≤ C) (hw : ∀ j ≤ R, 0 ≤ w j)
    (hmono : ∀ j < R, w (j+1) ≤ w j) :
    |∑ j ∈ range R, (e (j+1)-e j)*w j| ≤ 2*C*w 0 := by
  rw [weighted_difference_identity]
  apply (abs_add_le _ _).trans
  have hend : |e R*w R-e 0*w 0| ≤ C*w R+C*w 0 := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (hw R le_rfl),abs_of_nonneg (hw 0 (Nat.zero_le _))]
    exact _root_.add_le_add (mul_le_mul_of_nonneg_right (he R le_rfl) (hw R le_rfl))
      (mul_le_mul_of_nonneg_right (he 0 (Nat.zero_le _)) (hw 0 (Nat.zero_le _)))
  have hsum : |∑ j ∈ range R, e (j+1)*(w j-w (j+1))| ≤ C*(w 0-w R) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j ∈ range R, C*(w j-w (j+1)) := by
        apply sum_le_sum
        intro j hj
        have hjR := mem_range.mp hj
        have hd : 0 ≤ w j-w (j+1) := sub_nonneg.mpr (hmono j hjR)
        rw [abs_mul,abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (he (j+1) (by omega)) hd
      _ = _ := by rw [← mul_sum,sum_range_differences]
  apply (_root_.add_le_add hend hsum).trans_eq
  ring

end Erdos821.AnalyticSieve
