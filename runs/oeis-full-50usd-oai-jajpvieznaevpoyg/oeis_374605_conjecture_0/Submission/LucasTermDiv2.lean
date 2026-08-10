import FormalConjectures.Util.ProblemImports

example (p n k : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hlo : (2*p+3)/3 ≤ n) (hhi : n ≤ p-1) (hk : k ≤ n)
    (hsmall : k ≤ p - 1 - n) :
    p ∣ Nat.choose (3*n+2*k) n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hnlt : n < p := by omega
  set m := p - 1 - n with hm
  have hn_eq : n = p - 1 - m := by omega
  have hk_m : k ≤ m := by omega
  have hm_bound : 3*m + 4 ≤ p := by
    -- stronger form of lower bound after substituting n=p-1-m
    omega
  have hrem_expr : (3*n + 2*k) % p = p - (3 + 3*m - 2*k) := by
    have hpos : 3 + 3*m - 2*k ≤ p := by omega
    have hpos2 : 2*k ≤ 3 + 3*m := by omega
    have hdecomp : 3*n + 2*k = 2*p + (p - (3 + 3*m - 2*k)) := by omega
    rw [hdecomp]
    have hlt : p - (3 + 3*m - 2*k) < p := by omega
    have hpmod : (2*p) % p = 0 := by rw [mul_comm]; exact Nat.mul_mod_right p 2
    have : (2*p + (p - (3 + 3*m - 2*k))) % p = (p - (3 + 3*m - 2*k)) % p := by
      rw [Nat.add_mod, hpmod, zero_add, Nat.mod_mod]
    rw [this, Nat.mod_eq_of_lt hlt]
  have hrem : (3*n+2*k) % p < n := by
    rw [hrem_expr, hn_eq]
    omega
  have hNlt : 3*n+2*k < p^2 := by nlinarith [hnlt, hk, hp5]
  have hnlt2 : n < p^2 := by nlinarith [hnlt, hp5]
  have hLucas := Choose.choose_modEq_prod_range_choose_nat (p:=p) (n:=3*n+2*k) (k:=n) (a:=2) hNlt hnlt2
  -- product over i=0,1 has first factor choose ((N%p)) n = 0
  apply (Nat.modEq_zero_iff_dvd).mp
  apply Nat.ModEq.trans hLucas
  -- show product is 0 mod p
  apply (Nat.modEq_zero_iff_dvd).mpr
  rw [Finset.prod_range_succ]
  apply dvd_mul_of_dvd_left
  have hfac : ((3 * n + 2 * k) % p).choose (n % p) = 0 := by
    rw [Nat.mod_eq_of_lt hnlt]
    exact Nat.choose_eq_zero_of_lt hrem
  simp [Finset.prod_range_one, hfac]
