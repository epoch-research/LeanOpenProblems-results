import FormalConjectures.Util.ProblemImports

open scoped Nat

example (p n k : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-1) (hk : k ≤ n)
    (hsmall : k ≤ p - 1 - n) :
    p ∣ Nat.choose (3*n+2*k) n := by
  have hp0 : 0 < p := hp.pos
  have hnlt : n < p := by omega
  have hNlt : 3*n+2*k < p^2 := by nlinarith [hhi, hk, hp5]
  have hnlt2 : n < p^2 := by nlinarith [hnlt, hp5]
  -- Lucas with a=2: choose N n ≡ prod digits; since n/p=0, product is choose (N%p) (n%p) * 1.
  have hLucas := Choose.choose_modEq_prod_range_choose_nat (p:=p) (n:=3*n+2*k) (k:=n) (a:=2) hNlt hnlt2
  -- if N%p < n, the product is zero mod p
  have hrem : (3*n+2*k) % p < n := by
    omega
  -- Maybe simplify hLucas
  rw [Nat.modEq_zero_iff_dvd]
  -- exact? from hLucas and hrem
  sorry
