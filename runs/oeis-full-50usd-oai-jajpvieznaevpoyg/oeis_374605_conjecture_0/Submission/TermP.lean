import FormalConjectures.Util.ProblemImports

example (p n k : ℕ) (hp : Nat.Prime p) (h1 : (2*p+3)/3 ≤ n) (h2 : n ≤ p-1) (hk : k ∈ Finset.range (n+1)) :
    p ∣ (Nat.choose n k) ^ 2 * (Nat.choose (n+k) k) * (Nat.choose (3*n+2*k) n) := by
  have hk_le : k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  -- Try cases whether k <= p-1-n etc.; use Nat.Prime.dvd_choose lemmas
  by_cases hkn : k ≤ p-1-n
  · -- then last choose crosses p? top=3n+2k, bottom n; need p in interval top-n+1..top maybe
    have : p ≤ 3*n+2*k := by omega
    -- Nat.Prime.dvd_choose hp ha hab h: p ∣ choose b a if a<p, b-a<p, p≤b
    exact dvd_mul_of_dvd_right (hp.dvd_choose (by omega) (by omega) (by omega) : p ∣ Nat.choose (3*n+2*k) n) _
  · -- otherwise n+k choose k crosses p
    have : p ≤ n+k := by omega
    have hpgt : k < p := by omega
    have hdiff : n+k-k < p := by omega
    have hd : p ∣ Nat.choose (n+k) k := hp.dvd_choose hpgt hdiff this
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd ((Nat.choose n k)^2)) _
