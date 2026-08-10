import FormalConjectures.Util.ProblemImports

-- Target theorem to explore: primes p with p=2 or p%8=1,3 are x^2+2y^2.
#check ZMod.exists_sq_eq_neg_two_iff
#check Nat.Prime.sq_add_sq
#check Nat.exists_eq_mul_left_of_dvd
#check ZMod.natCast_zmod_val

example (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : p % 8 = 1 ∨ p % 8 = 3) :
    IsSquare (-2 : ZMod p) := by
  exact (ZMod.exists_sq_eq_neg_two_iff (p:=p) hp2).2 hp

-- If k^2 ≡ -2 mod p then p ∣ k^2+2. This part is easy.
example (p k : ℕ) [Fact p.Prime] (hk : (k : ZMod p)^2 = -2) : p ∣ k^2 + 2 := by
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hk]
  norm_num
