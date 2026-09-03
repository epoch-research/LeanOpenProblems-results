import Submission.MatchingNaturalPatternExplore
import Submission.PatternSparsePowerProfileExplore
import Submission.SummableTailBudgetExplore

/-! A universal polynomial weight imposes countably many positive patterns.
Linear independent means yield quartic Boolean bounds in the test index. -/
namespace Erdos66PolynomialPatternBudget
open Erdos66NaturalPositivePattern Erdos66MatchingNaturalPattern
  Erdos66PatternSparsePowerProfile Erdos66SummableTailBudget Erdos66Fractional
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000

lemma exists_index_tail_budget : ∃ M : ℕ, ∀ S : Finset ℕ,
    (∑ m∈S, 3/((m:ℝ)+M+2)^3) < 1/4 := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 (3:ℕ)).mpr (by norm_num)
  have hs' : Summable (fun m : ℕ ↦ 3/((m:ℝ)+2)^3) := by
    simpa only [Real.rpow_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (↑(_:ℕ):ℝ)+2),mul_one_div]
      using hs.mul_left (3:ℝ)
  obtain ⟨M,hM⟩ := exists_tail_budget _ hs' (1/4) (by norm_num)
  refine ⟨M,?_⟩
  intro S
  have hh := hM (S.image (fun m ↦ m+M)) (by
    intro m hm
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
    omega)
  rw [Finset.sum_image (by intro a ha b hb he; change a+M=b+M at he; omega)] at hh
  simpa only [Nat.cast_add] using hh

 theorem exists_polynomial_pattern_bounds (P : ℕ → Pattern)
    (hP : ∀ m, (P m).eval profile ≤ 3*((m:ℝ)+2)) :
    ∃ (A : Set ℕ) (M : ℕ),
      (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
      (∀ m, (P m).value (fun i ↦ decide (i∈A)) ≤ ((m:ℝ)+M+2)^4) ∧
      (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) := by
  obtain ⟨M,hM⟩ := exists_index_tail_budget
  let Q : ℕ → Pattern := fun m ↦ scalePattern (1/((m:ℝ)+M+2)^4) (by positivity) (P m)
  have hQ (S : Finset ℕ) : (∑ m∈S, (Q m).eval profile) ≤ 1/4 := by
    apply (Finset.sum_le_sum (fun m hm ↦ ?_)).trans (hM S).le
    dsimp only [Q]
    rw [scalePattern_eval]
    have hx : 0 < (m:ℝ)+M+2 := by positivity
    calc
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (hP m) (by positivity)
      _ ≤ (1/((m:ℝ)+M+2)^4)*(3*((m:ℝ)+M+2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [Nat.cast_nonneg (α := ℝ) M]
      _ = 3/((m:ℝ)+M+2)^3 := by field_simp <;> ring
  obtain ⟨A,hbr,hbounds,hcost⟩ := exists_pattern_sparse_power_potentials Q hQ
  refine ⟨A,M,hbr,?_,hcost⟩
  intro m
  have hh := hbounds {m}
  simp only [Finset.sum_singleton,Q,scalePattern_value] at hh
  have hx : 0 < ((m:ℝ)+M+2)^4 := by positivity
  rw [one_div,mul_comm,←div_eq_mul_inv] at hh
  exact (div_le_one hx).mp hh

end Erdos66PolynomialPatternBudget
