import FormalConjectures.Util.ProblemImports

example (p n k : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-1) (hk : k ≤ n) :
    p ∣ (Nat.choose n k) ^ 2 * (Nat.choose (n+k) k) * (Nat.choose (3*n+2*k) n) := by
  have hp0 : 0 < p := hp.pos
  by_cases hkmp : k ≤ p - 1 - n
  · -- use last binomial; Kummer/carry: n + (2n+2k) crosses p
    apply dvd_mul_of_dvd_right
    apply hp.dvd_choose
    · omega
    · -- (3n+2k)-n = 2n+2k, need b-a < p? not true maybe for hp.dvd_choose condition uses a<p and b-a<p and p≤b
      omega
    · omega
  · -- use choose(n+k,k), since k + n crosses p
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    apply hp.dvd_choose
    · omega
    · omega
    · omega
