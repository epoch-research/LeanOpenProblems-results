import FormalConjectures.Util.ProblemImports

lemma k_lt_n_of_le (n k : ℕ) (h : 3 + 2 * k ≤ n) : k < n := by omega

lemma le_mul_self_of_ge_one (k : ℕ) : 3 + 2 * k ≤ (3 + 2 * k) * (3 + 2 * k) := by
  have : 1 ≤ 3 + 2 * k := by omega
  exact Nat.le_mul_self (3 + 2 * k)

def has_odd_divisor_from (n : ℕ) (d : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if d * d > n then false
    else if n % d == 0 then true
    else has_odd_divisor_from n (d + 2) f

def is_prime_custom (n : ℕ) : Bool :=
  if n ≤ 1 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else !(has_odd_divisor_from n 3 n)

-- Test speed of is_prime_custom on 15727
#eval is_prime_custom 15727
