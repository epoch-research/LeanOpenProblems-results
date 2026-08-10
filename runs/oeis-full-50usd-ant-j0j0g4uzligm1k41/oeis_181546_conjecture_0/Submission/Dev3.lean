import FormalConjectures.Util.ProblemImports

example (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : (5-s)*N + 10*β*N ≤ 10*J) :
    β*s/2 * N^2 ≤ (N-J)*(J+1) - (N-2*J)*(N-2*J-1) := by
  have key : 10*β*N ≤ s*N - (5*N-10*J) := by linarith
  have h2 : 0 ≤ s*N + (5*N-10*J) := by nlinarith [hs0, hN]
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2  -- 10βN*(..) ≤ (sN-(..))*(..)
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ 10*β*N*(5*N-10*J) := by
    apply mul_nonneg hbN; linarith
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]

-- strong inc: J ≤ (astar-β)N  => (N-2J)(N-2J-1) - (N-J)(J+1) ≥ (β s/2) N^2 - 2N
example (N J s β : ℝ) (hs : s^2 = 5) (hs0 : 0 < s) (hN : 2 ≤ N)
    (hJ0 : 0 ≤ J) (hJn : 2*J ≤ N) (hb : 0 < β)
    (hstr : 10*J ≤ (5-s)*N - 10*β*N) :
    β*s/2 * N^2 - 2*N ≤ (N-2*J)*(N-2*J-1) - (N-J)*(J+1) := by
  have key : 10*β*N ≤ (5*N-10*J) - s*N := by linarith
  have h2 : 0 ≤ s*N := by positivity
  have hbN : 0 ≤ 10*β*N := by positivity
  have hprod := mul_le_mul_of_nonneg_right key h2  -- 10βN*sN ≤ ((5N-10J)-sN)*sN
  have hsN2 : s^2 * N^2 = 5 * N^2 := by rw [hs]
  have hextra : 0 ≤ ((5*N-10*J)-s*N)*(5*N-10*J) := by
    apply mul_nonneg; nlinarith [hs0,hN]; linarith
  nlinarith [hprod, hsN2, hN, hJ0, hJn, hextra]
