import FormalConjectures.Util.ProblemImports

example (p n : ℕ) (hp : Nat.Prime p) (hnp : n < p) (hp_le : p ≤ (3*n)/2) :
    p ^ 3 ∣ Nat.choose (3*n) n * (Nat.choose (2*n) n)^2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- Just ask exact?/apply? for factorization route
  have h1 : p ∣ Nat.choose (2*n) n := by
    apply hp.dvd_choose (a:=n) (b:=2*n)
    · omega
    · omega
    · omega
  have h2 : p ∣ Nat.choose (3*n) n := by
    -- choose 3n n crosses 2p? use choose_symm maybe choose 3n (2n)
    have h2p : 2*p ≤ 3*n := by omega
    have hlt : 2*n < 2*p := by omega
    -- Need prime divisor criterion not directly for crossing multiple 2p.
    exact hp.dvd_choose (a:=n) (b:=3*n) (by omega) (by omega) (by omega)
  exact dvd_mul_of_dvd_left (mul_dvd_mul h2 (pow_dvd_pow_of_dvd h1 2)) _
