import Submission.PolynomialDimensionTorusRecurrence
import Submission.SimultaneousPolynomialRecurrence

/-! Simultaneous recurrence in all degrees up to K. Induction is on the degree,
not on the number of coordinates, preserving polynomial dimension dependence. -/
namespace Erdos3PolynomialDimensionMixedRecurrence
open Erdos3PolynomialDimensionTorusRecurrence Erdos3SimultaneousPolynomialRecurrence
open scoped Classical
set_option maxHeartbeats 4000000

def mixedTupleConstant : ℕ → ℕ → ℕ
  | 0,_ => 0
  | K+1,m => mixedTupleConstant K m*((K+1)*tupleRecurrenceConstant K m+1)+tupleRecurrenceConstant K m

/-- Every coordinate returns simultaneously for every positive degree <=K. -/
theorem simultaneous_all_degrees {I : Type*} [Fintype I]
    (K : ℕ) (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (s : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(mixedTupleConstant K (Fintype.card I)*(s+1)) ∧
      ∀ i, ∀ e : ℕ, 0 < e → e ≤ K → ‖(v i)^(d^e)-1‖ ≤ (1/2:ℝ)^s := by
  induction K generalizing s with
  | zero =>
    refine ⟨1,by decide,by simp [mixedTupleConstant],?_⟩
    intro i e he heK
    omega
  | succ K ih =>
    let C := tupleRecurrenceConstant K (Fintype.card I)
    obtain ⟨a,ha,hab,hrec⟩ := ih (s+(K+1)*(C*(s+1)))
    obtain ⟨b,hb,hbb,hnew⟩ := simultaneous_unit_monomial_recurrence
      (fun i ↦ (v i)^(a^(K+1))) (fun i ↦ by rw [norm_pow,hv,one_pow]) K s
    refine ⟨a*b,Nat.mul_pos ha hb,?_,?_⟩
    · calc
        _ ≤ 2^(mixedTupleConstant K (Fintype.card I)*(s+(K+1)*(C*(s+1))+1))*2^(C*(s+1)) :=
          Nat.mul_le_mul hab hbb
        _ = _ := by rw [← pow_add]; congr 1; rw [mixedTupleConstant]; dsimp only [C]; ring
    · intro i e he heK
      by_cases heq : e = K+1
      · subst e
        simpa only [← pow_mul,← mul_pow] using hnew i
      · apply polynomial_dilate_bound (v i) (hv i) a b e (K+1) s (C*(s+1)) heK hbb
        exact hrec i e he (by omega)

theorem simultaneous_mixed_degrees {I : Type*} [Fintype I]
    (K : ℕ) (e : I → ℕ) (he : ∀ i, 0 < e i ∧ e i ≤ K)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) (s : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 2^(mixedTupleConstant K (Fintype.card I)*(s+1)) ∧
      ∀ i, ‖(v i)^(d^(e i))-1‖ ≤ (1/2:ℝ)^s := by
  obtain ⟨d,hd,hdb,hrec⟩ := simultaneous_all_degrees K v hv s
  exact ⟨d,hd,hdb,fun i ↦ hrec i (e i) (he i).1 (he i).2⟩

#print axioms simultaneous_mixed_degrees
end Erdos3PolynomialDimensionMixedRecurrence
