import Submission.AveragedPrimeWinnerEnergy

/-! Exact signed cross-term formula for cumulative prime-winner energy.
The triangular weight is retained; its cancellation is not asserted. -/
namespace Erdos371
open Finset

lemma triangular_prefix_sum_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (N+1), ((N+1-n : ℕ) : ℝ)*f n) =
      (∑ n ∈ range N, ((N-n : ℕ) : ℝ)*f n)+∑ n ∈ range (N+1), f n := by
  rw [sum_range_succ,sum_range_succ]
  have he (n : ℕ) (hn : n ∈ range N) :
      ((N+1-n : ℕ) : ℝ)*f n = ((N-n : ℕ) : ℝ)*f n+f n := by
    have hh : N+1-n = (N-n)+1 := by have := mem_range.mp hn; omega
    rw [hh,Nat.cast_add,Nat.cast_one]
    ring
  rw [sum_congr rfl he,sum_add_distrib]
  simp only [Nat.add_sub_cancel_left,Nat.cast_one,one_mul]
  ring

noncomputable def triangularPrimeWinnerCrossSum (X : ℕ) : ℝ :=
  ∑ n ∈ range X, ((X-n : ℕ) : ℝ)*(factorSign n*primeWinnerSum (primeWinner n) n)

lemma triangularPrimeWinnerCrossSum_succ (N : ℕ) :
    triangularPrimeWinnerCrossSum (N+1) =
      triangularPrimeWinnerCrossSum N+primeWinnerCrossSum (N+1) :=
  triangular_prefix_sum_succ (fun n => factorSign n*primeWinnerSum (primeWinner n) n) N

/-- Each earlier signed collision receives the number of later endpoints
that still include it. The diagonal part has size X(X+1)/2 exactly. -/
theorem cumulativePrimeWinnerEnergy_eq_triangular_cross (X : ℕ) :
    cumulativePrimeWinnerEnergy X = (X : ℝ)*(X+1)/2+2*triangularPrimeWinnerCrossSum X := by
  induction X with
  | zero => simp [cumulativePrimeWinnerEnergy,primeWinnerEnergy,primeWinnerSum,
      triangularPrimeWinnerCrossSum]
  | succ X ih =>
    have hc : cumulativePrimeWinnerEnergy (X+1) =
        cumulativePrimeWinnerEnergy X+primeWinnerEnergy (X+1) := by
      simp only [cumulativePrimeWinnerEnergy,sum_range_succ]
    rw [hc,ih,primeWinnerEnergy_eq_diagonal_add_cross,triangularPrimeWinnerCrossSum_succ]
    push_cast
    ring

/-- This equivalence isolates the one-sided signed estimate needed for a
chosen cumulative energy budget; it supplies no bound for the cross term. -/
theorem cumulativePrimeWinnerEnergy_le_iff (X : ℕ) (T : ℝ) :
    cumulativePrimeWinnerEnergy X ≤ T ↔
      triangularPrimeWinnerCrossSum X ≤ (T-(X : ℝ)*(X+1)/2)/2 := by
  rw [cumulativePrimeWinnerEnergy_eq_triangular_cross]
  constructor <;> intro h <;> linarith

#print axioms cumulativePrimeWinnerEnergy_eq_triangular_cross
#print axioms cumulativePrimeWinnerEnergy_le_iff
end Erdos371
