import FormalConjectures.Util.ProblemImports

lemma nat_gcd_eq_of_prime_mul {p t den : ℕ} (hp : p.Prime) (htpos : 0 < t)
    (htden : t ∣ den) (hpden : ¬ p ∣ den) : Nat.gcd den (p * t) = t := by
  apply Nat.dvd_antisymm
  · obtain ⟨u, rfl⟩ := htden
    rw [mul_comm p t, Nat.gcd_mul_left]
    -- gcd (t*u) (t*p)= t*gcd u p
    have hcop : Nat.Coprime u p := by
      exact (hp.coprime_iff_not_dvd.mpr (by
        intro hpu
        apply hpden
        exact dvd_mul_of_dvd_right hpu t)).symm
    rw [hcop.gcd_eq_one]
    simp
  · exact Nat.dvd_gcd htden (dvd_mul_left t p)

lemma rat_num_natAbs_prime_mul_div {p t den : ℕ} (hp : p.Prime) (htpos : 0 < t)
    (hdenpos : 0 < den) (htden : t ∣ den) (hpden : ¬ p ∣ den) :
    (((((p * t : ℕ) : ℤ) : ℚ) / (((den : ℕ) : ℤ) : ℚ)).num.natAbs = p) := by
  have hg : Nat.gcd den (p*t) = t := nat_gcd_eq_of_prime_mul hp htpos htden hpden
  have hcop : Nat.Coprime p (den / t) := by
    exact hp.coprime_iff_not_dvd.mpr (by
      intro hpdt
      apply hpden
      obtain ⟨u, hu⟩ := htden
      subst den
      rw [Nat.mul_div_right u htpos] at hpdt
      exact dvd_mul_of_dvd_right hpdt t)
  have htden' : den = t * (den / t) := by exact (Nat.mul_div_cancel' htden).symm
  have hq : ((((p * t : ℕ) : ℤ) : ℚ) / (((den : ℕ) : ℤ) : ℚ)) = ((p : ℤ) : ℚ) / (((den / t : ℕ) : ℤ) : ℚ) := by
    rw [htden']
    have htq : (((t:ℕ):ℤ):ℚ) ≠ 0 := by positivity
    norm_num [Nat.cast_mul, Int.cast_mul]
    field_simp [htq]
  rw [hq]
  have hden_div_pos : 0 < ((den / t : ℕ) : ℤ) := by
    have : 0 < den / t := by
      obtain ⟨u, hu⟩ := htden
      subst den
      rw [Nat.mul_div_right u htpos]
      have hu_pos : 0 < u := by
        by_contra hz
        have : u = 0 := by omega
        subst u
        simp at hdenpos
      exact hu_pos
    exact_mod_cast this
  have hcop2 : Nat.Coprime ((p:ℤ).natAbs) ((((den/t:ℕ):ℤ).natAbs)) := by
    simpa using hcop
  have hnum := Rat.num_div_eq_of_coprime (a := (p:ℤ)) (b := ((den/t:ℕ):ℤ)) hden_div_pos hcop2
  rw [hnum]
  simp
