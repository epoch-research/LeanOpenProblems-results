import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  b_prev + b_prev * 2 / (p - 1)

noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

set_option maxRecDepth 10000000
lemma a_fifty_eq_eleven : a 50 = 11 := by rfl
