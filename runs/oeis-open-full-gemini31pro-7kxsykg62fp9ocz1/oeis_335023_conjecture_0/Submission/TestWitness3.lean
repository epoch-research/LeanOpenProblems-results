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
    apply dvd_add
    · exact dvd_mul_of_dvd_left (Int.gcd_dvd_left A B) u
    · exact dvd_mul_of_dvd_left (Int.gcd_dvd_right A B) v
  have G_dvd_gcd : G ∣ (Int.gcd A B : ℤ) := by
    exact Int.dvd_natCast.mpr (Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (by
      have h1 : (G.natAbs : ℤ) ∣ A := by
        rw [Int.natAbs_dvd]
        exact dvd_A
      sorry
    )) sorry)
  sorry
