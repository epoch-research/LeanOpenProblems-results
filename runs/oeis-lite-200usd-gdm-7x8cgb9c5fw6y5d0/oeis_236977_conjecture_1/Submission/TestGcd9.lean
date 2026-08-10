import FormalConjectures.Util.ProblemImports

open Nat

theorem test : totient 10000 = 4000 := by
  have h_prime2 : Nat.Prime 2 := by decide
  have h_prime5 : Nat.Prime 5 := by decide
  have h_coprime : Coprime (2^4) (5^4) := by decide
  have h1 : totient (2^4) = 8 := by
    have := totient_prime_pow h_prime2 (by decide : 0 < 4)
    exact this
  have h2 : totient (5^4) = 500 := by
    have := totient_prime_pow h_prime5 (by decide : 0 < 4)
    exact this
  rw [show 10000 = 2^4 * 5^4 by decide]
  rw [totient_mul h_coprime]
  rw [h1, h2]
