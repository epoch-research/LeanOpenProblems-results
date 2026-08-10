import FormalConjectures.Util.ProblemImports

lemma lt_pow_self_of_two_le {p r : ℕ} (hp : 2 ≤ p) (hr : 0 < r) : r < p ^ r := by
  have h2 : r < 2 ^ r := Nat.lt_two_pow_self
  have hle : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp r
  exact lt_of_lt_of_le h2 hle

example (f : ℕ → ℕ) (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  f (n * p ^ r) ≡ f (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hrne : r ≠ p ^ r := ne_of_lt (lt_pow_self_of_two_le (p:=p) (r:=r) (by omega) hr)
  have hpowne : p ^ r ≠ p ^ (r-1) := by
    apply ne_of_gt
    have hlt : r - 1 < r := Nat.sub_one_lt hr
    exact Nat.pow_lt_pow_right (by omega : 1 < p) hlt
  grind [Nat.ModEq]
