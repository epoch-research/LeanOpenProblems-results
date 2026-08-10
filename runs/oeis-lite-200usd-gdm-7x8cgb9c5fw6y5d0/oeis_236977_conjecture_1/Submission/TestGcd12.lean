import FormalConjectures.Util.ProblemImports

open Nat

theorem tot9000 : totient 9000 = 2400 := by
  have h_p2 : Nat.Prime 2 := by decide
  have h_p3 : Nat.Prime 3 := by decide
  have h_p5 : Nat.Prime 5 := by decide

  have s1 : totient (2 * 4500) = 2 * totient 4500 := totient_mul_of_prime_of_dvd h_p2 (by decide : 2 ∣ 4500)
  have s2 : totient (2 * 2250) = 2 * totient 2250 := totient_mul_of_prime_of_dvd h_p2 (by decide : 2 ∣ 2250)
  have s3 : totient (2 * 1125) = (2 - 1) * totient 1125 := totient_mul_of_prime_of_not_dvd h_p2 (by decide : ¬ 2 ∣ 1125)
  have s4 : totient (3 * 375) = 3 * totient 375 := totient_mul_of_prime_of_dvd h_p3 (by decide : 3 ∣ 375)
  have s5 : totient (3 * 125) = (3 - 1) * totient 125 := totient_mul_of_prime_of_not_dvd h_p3 (by decide : ¬ 3 ∣ 125)
  have s6 : totient (5 * 25) = 5 * totient 25 := totient_mul_of_prime_of_dvd h_p5 (by decide : 5 ∣ 25)
  have s7 : totient (5 * 5) = 5 * totient 5 := totient_mul_of_prime_of_dvd h_p5 (by decide : 5 ∣ 5)
  have s8 : totient (5 * 1) = (5 - 1) * totient 1 := totient_mul_of_prime_of_not_dvd h_p5 (by decide : ¬ 5 ∣ 1)

  rw [show 9000 = 2 * 4500 by decide]
  rw [s1]
  rw [show 4500 = 2 * 2250 by decide]
  rw [s2]
  rw [show 2250 = 2 * 1125 by decide]
  rw [s3]
  rw [show 1125 = 3 * 375 by decide]
  rw [s4]
  rw [show 375 = 3 * 125 by decide]
  rw [s5]
  rw [show 125 = 5 * 25 by decide]
  rw [s6]
  rw [show 25 = 5 * 5 by decide]
  rw [s7]
  rw [show 5 = 5 * 1 by decide]
  rw [s8]
  rw [totient_one]
  decide
