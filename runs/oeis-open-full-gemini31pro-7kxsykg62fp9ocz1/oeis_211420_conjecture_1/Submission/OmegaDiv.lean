import Mathlib

lemma div_ineq_mod (u v M : ℕ) (hM : 0 < M) (hu : u < M) (hv : v < M) (huv : v ≤ 4 * u)
  (q1 r1 : ℕ) (hq1 : 4 * u - v = q1 * M + r1) (hr1 : r1 < M)
  (q2 r2 : ℕ) (hq2 : 3 * u = q2 * M + r2) (hr2 : r2 < M)
  (q3 r3 : ℕ) (hq3 : 2 * u = q3 * M + r3) (hr3 : r3 < M)
  (p1 s1 : ℕ) (hp1 : 8 * u - 2 * v = p1 * M + s1) (hs1 : s1 < M)
  (p2 s2 : ℕ) (hp2 : 8 * v = p2 * M + s2) (hs2 : s2 < M) :
    q1 + q2 + q3 ≤ p1 + p2 := by
  omega
