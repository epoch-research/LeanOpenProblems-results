import FormalConjectures.Util.ProblemImports
import Submission.Dev4
open scoped Nat
noncomputable section

-- generic division helpers
theorem ratio_le_helper (A B P Q c : ℝ) (heq : A*P = B*Q) (hP : 0 < P) (hB : 0 ≤ B)
    (hQ : Q ≤ c*P) : A ≤ c*B := by
  have h1 : B*Q ≤ B*(c*P) := mul_le_mul_of_nonneg_left hQ hB
  have h2 : A*P ≤ (c*B)*P := by rw [heq]; nlinarith [h1]
  exact le_of_mul_le_mul_right (by linarith [h2]) hP

theorem ratio_ge_helper (A B P Q c : ℝ) (heq : A*P = B*Q) (hP : 0 < P) (hB : 0 ≤ B)
    (hQ : c*P ≤ Q) : c*B ≤ A := by
  have h1 : B*(c*P) ≤ B*Q := mul_le_mul_of_nonneg_left hQ hB
  have h2 : (c*B)*P ≤ A*P := by rw [heq]; nlinarith [h1]
  exact le_of_mul_le_mul_right (by linarith [h2]) hP

-- Real inequalities (proven earlier)
theorem ineq_monodec (N J s : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hlo : (5-s)*N ≤ 10*J) :
    (N-2*J)*(N-2*J-1) ≤ (N-J)*(J+1) := by
  have hsN : 0 ≤ s*N := by positivity
  have key : 0 ≤ s*N - (5*N-10*J) := by linarith
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  nlinarith [mul_nonneg key (by linarith : (0:ℝ) ≤ s*N + (5*N-10*J)), hsN2, hN, hJ0, hJn]

theorem ineq_monoinc (N J s : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hhi : 10*J ≤ (5-s)*N - 10) :
    (N-J)*(J+1) ≤ (N-2*J)*(N-2*J-1) := by
  have hsN : 0 ≤ s*N := by positivity
  have key : 0 ≤ (5*N-10*J) - s*N := by nlinarith [hs0, hN]
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  nlinarith [mul_nonneg key (by linarith : (0:ℝ) ≤ (5*N-10*J) + s*N), hsN2, hN, hJ0, hJn]

theorem ineq_strongdec (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : (5-s)*N + 10*β*N ≤ 10*J) :
    β*s/2 * N^2 ≤ (N-J)*(J+1) - (N-2*J)*(N-2*J-1) := by
  have key : 10*β*N ≤ s*N - (5*N-10*J) := by linarith
  have h2 : 0 ≤ s*N + (5*N-10*J) := by nlinarith [hs0, hN]
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ 10*β*N*(5*N-10*J) := mul_nonneg hbN (by linarith)
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]

theorem ineq_stronginc (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : 10*J ≤ (5-s)*N - 10*β*N) :
    β*s/2 * N^2 - 2*N ≤ (N-2*J)*(N-2*J-1) - (N-J)*(J+1) := by
  have key : 10*β*N ≤ (5*N-10*J) - s*N := by linarith
  have h2 : 0 ≤ s*N := by positivity
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ ((5*N-10*J)-s*N)*(5*N-10*J) := by
    apply mul_nonneg; nlinarith [hs0,hN]; linarith
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]
