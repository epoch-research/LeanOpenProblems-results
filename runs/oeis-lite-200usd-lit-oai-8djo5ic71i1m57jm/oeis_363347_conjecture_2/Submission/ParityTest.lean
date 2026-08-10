import FormalConjectures.Util.ProblemImports

example (p m r:ℕ) (hpodd:Odd p) (hre:Even r) (hN: r*r - 5 = p*m) (hrge:4≤r) : Odd m := by
  rw [← Nat.not_even_iff_odd]
  intro hme
  have hpme : Even (p*m) := by exact hme.mul_left p
  have hleft_odd : Odd (r*r - 5) := by
    have hr2e : Even (r*r) := hre.mul_left r
    exact Nat.Even.sub_odd (by nlinarith) hr2e (by norm_num : Odd 5)
  rw [hN] at hleft_odd
  exact (Nat.not_even_iff_odd.mpr hleft_odd) hpme

example (p m r:ℕ) (hpodd:Odd p) (hro:Odd r) (hN: r*r - 5 = p*m) (hrge:4≤r) : ∃ u, m=4*u ∧ Odd u := by
  have h4dvd_left : 4 ∣ r*r - 5 := by
    rcases hro with ⟨a, ha⟩
    subst r
    use a*a + a - 1
    ring_nf
    omega
  have h4dvd_pm : 4 ∣ p*m := by rwa [← hN]
  have hcop : Nat.Coprime 4 p := by
    change Nat.Coprime (2^2) p
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
    simpa [Nat.coprime_two_left] using hpodd
  have h4m : 4 ∣ m := (hcop.dvd_mul_left).mp h4dvd_pm
  rcases h4m with ⟨u, hu⟩
  use u
  constructor
  · exact hu
  · rw [← Nat.not_even_iff_odd]
    intro hue
    have h8m : 8 ∣ m := by
      rw [hu]
      rcases hue with ⟨v, hv⟩
      subst u
      use v
      ring
    have h8left : ¬ 8 ∣ r*r - 5 := by
      rcases hro with ⟨a, ha⟩
      subst r
      intro hd
      let q := a*a + a - 1
      have hformula : (2 * a + 1) * (2 * a + 1) - 5 = 4 * q := by
        dsimp [q]
        ring_nf
        omega
      have hqodd : Odd q := by
        dsimp [q]
        have he : Even (a*a + a) := by
          simpa [pow_two, Nat.mul_succ, mul_comm, mul_left_comm, mul_assoc] using Nat.even_mul_succ_self a
        exact Nat.Even.sub_odd (by omega) he (by norm_num : Odd 1)
      rw [hformula] at hd
      rcases hd with ⟨t, ht⟩
      have h2q : 2 ∣ q := by
        use t
        omega
      exact (Nat.not_even_iff_odd.mpr hqodd) ((even_iff_two_dvd).mpr h2q)
    have h8pm : 8 ∣ p * m := dvd_mul_of_dvd_right h8m p
    rw [← hN] at h8pm
    exact h8left h8pm
