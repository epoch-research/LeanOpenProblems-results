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
  have G_dvd_gcd : G ∣ (Int.gcd A B : ℤ) := Int.dvd_gcd dvd_A dvd_B
  have eq_abs := Int.dvd_antisymm G_dvd_gcd dvd_G
  -- eq_abs gives `G = Int.gcd A B` or `G = - Int.gcd A B`
  have H_nat : (Int.gcd A B : ℤ) = G.natAbs := by
    cases eq_abs with
    | inl h =>
      rw [h]
      exact (Int.natAbs_of_nonneg hG).symm
    | inr h =>
      have h_nonneg : 0 ≤ (Int.gcd A B : ℤ) := Int.natCast_nonneg _
      have h_zero : G = 0 := by linarith
      subst h_zero
      exact h.symm
  exact Int.natCast_inj.mp H_nat
