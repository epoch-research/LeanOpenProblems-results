import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

lemma gcd_witness (A B G u v : ℤ) (hA : G ∣ A) (hB : G ∣ B) (h_lin : A * u + B * v = G) (hG : 0 ≤ G) :
  Int.gcd A B = G.natAbs := by
  sorry
