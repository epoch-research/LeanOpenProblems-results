import FormalConjectures.Util.ProblemImports

lemma gcd_witness (A B G u v mA mB : ℤ)
  (hA : A = G * mA)
  (hB : B = G * mB)
  (h_lin : A * u + B * v = G)
  (hG : 0 ≤ G) :
  Int.gcd A B = G.natAbs := by
  have dvd_A : G ∣ A := ⟨mA, hA⟩
  have dvd_B : G ∣ B := ⟨mB, hB⟩
  have dvd_G : (Int.gcd A B : ℤ) ∣ G := by
    rw [← h_lin]
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left A B) u) (dvd_mul_of_dvd_left (Int.gcd_dvd_right A B) v)
  have G_dvd_gcd : G ∣ (Int.gcd A B : ℤ) := Int.dvd_gcd dvd_A dvd_B
  have eq_abs := Int.dvd_antisymm G_dvd_gcd dvd_G
  -- Since `Int.gcd A B ≥ 0` and `G ≥ 0`, they are equal.
  sorry

