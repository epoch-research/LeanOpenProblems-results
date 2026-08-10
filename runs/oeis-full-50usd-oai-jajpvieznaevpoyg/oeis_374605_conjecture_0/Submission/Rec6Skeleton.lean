import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

def P60 (n : ℕ) : ℕ :=
  74384733888 + 1041386274432*n + 6025163444928*n^2 + 18577587288528*n^3
  + 32761826231796*n^4 + 32761826231796*n^5 + 16945772188860*n^6 + 3389154437772*n^7

-- coefficient as factored integer polynomial over Nat (same as P60; not yet proven)
def Q60 (n : ℕ) : ℕ := 3389154437772 * (n+2) * (3*n+1)^3 * (3*n+2)^3

example (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-7) : Nat.Coprime p (Q60 n) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rw [Q60]
  repeat' apply Nat.Coprime.mul_right
  · -- constant = 2^2 * 3^25, just decide factorization? use norm_num and hp
    norm_num [Nat.coprime_comm]
    constructor <;> omega
  · rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hp_le : p ≤ n + 2 := Nat.le_of_dvd (by omega) h
      omega)
  · rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hmod : (3*n+1) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      omega)
  · rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hmod : (3*n+2) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      omega)
