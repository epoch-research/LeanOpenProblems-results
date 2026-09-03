import Submission.NearLinearProgressionPartition

/-! Exact binomial-coordinate formulas for a quadratic phase on a dilated
progression. These identities allow a two-level, density-preserving partition. -/
namespace Erdos3QuadraticSequenceDilation
open Erdos3QuadraticProgressionCurvature
open scoped Classical
set_option maxHeartbeats 3000000

lemma choose_two_dilate (a n d : ℕ) :
    (a+n*d).choose 2 = a.choose 2+n*(a*d+d.choose 2)+(n.choose 2)*d^2 := by
  have h₀ := two_choose_two_add a
  have h₁ := congrArg (fun k : ℕ ↦ k*n) (two_choose_two_add d)
  have h₂ := congrArg (fun k : ℕ ↦ k*d^2) (two_choose_two_add n)
  have h₃ := two_choose_two_add (a+n*d)
  nlinarith only [h₀,h₁,h₂,h₃]

lemma binomial_phase_dilate (A u v : ℂ) (a n d : ℕ) :
    A*u^(a+n*d)*v^((a+n*d).choose 2) =
      (A*u^a*v^(a.choose 2))*(u^d*v^(a*d+d.choose 2))^n*
        (v^(d^2))^(n.choose 2) := by
  have hu : u^(a+n*d) = u^a*(u^d)^n := by
    rw [← pow_mul,← pow_add]
    congr 1
    ring
  have hv : v^((a+n*d).choose 2) =
      v^(a.choose 2)*(v^(a*d+d.choose 2))^n*(v^(d^2))^(n.choose 2) := by
    rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
    congr 1
    rw [choose_two_dilate]
    ring
  rw [hu,hv,mul_pow]
  ring

#print axioms binomial_phase_dilate
end Erdos3QuadraticSequenceDilation
