import FormalConjectures.Util.ProblemImports

lemma coprime_const_3389154437772 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    Nat.Coprime p 3389154437772 := by
  norm_num [Nat.coprime_iff_not_dvd]
  constructor
  · exact hp.ne_of_gt (by omega)
  constructor
  · exact hp.ne_of_gt (by omega)
  · exact hp.ne_of_gt (by omega)

example (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-7) :
    Nat.Coprime p (3389154437772 * (n+2) * (3*n+1)^3 * (3*n+2)^3) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : p ≠ 2 := hp.ne_of_gt (by omega)
  have hp3 : p ≠ 3 := hp.ne_of_gt (by omega)
  rw [Nat.coprime_mul_iff_right]
  constructor
  · rw [Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_mul_iff_right]
      constructor
      · exact coprime_const_3389154437772 p hp hp5
      · rw [Nat.coprime_comm]
        exact hp.coprime_iff_not_dvd.mpr (by
          intro h
          have hp_le : p ≤ n + 2 := Nat.le_of_dvd (by omega) h
          omega)
    · rw [Nat.coprime_pow_right_iff, Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr (by
        intro h
        rcases h with ⟨t, ht⟩
        have htpos : 0 < t := by
          by_contra htz
          have : t = 0 := by omega
          omega
        have ht3 : t < 3 := by nlinarith [hhi, ht]
        have ht2 : 2 < t := by nlinarith [hlo, ht]
        omega)
  · rw [Nat.coprime_pow_right_iff, Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      rcases h with ⟨t, ht⟩
      have htpos : 0 < t := by
        by_contra htz
        have : t = 0 := by omega
        omega
      have ht3 : t < 3 := by nlinarith [hhi, ht]
      have ht2 : 2 < t := by nlinarith [hlo, ht]
      omega)
