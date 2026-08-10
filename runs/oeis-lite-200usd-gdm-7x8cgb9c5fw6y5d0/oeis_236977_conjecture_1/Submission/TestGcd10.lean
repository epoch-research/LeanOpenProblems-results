import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

theorem a_pos_of_exists (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < (n - 1) / 2 + 1)
    (hsq : sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)) : a n > 0 := by
  have hk : k ∈ Ico 1 ((n - 1) / 2 + 1) := mem_Ico.2 ⟨hk1, hk2⟩
  have h_le : (if sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k) then 1 else 0) ≤ a n := by
    apply single_le_sum (fun i _ => Nat.zero_le _) hk
  rw [hsq] at h_le
  simp only [if_true] at h_le
  exact h_le

theorem sqrt_eq_of_sq (M r : ℕ) (h : r ^ 2 = M) : sqrt M ^ 2 = M := by
  rw [← h]
  rw [sqrt_eq']

-- Let's prove totient 1000 = 400 algebraically
theorem tot1000 : totient 1000 = 400 := by
  have h_prime2 : Nat.Prime 2 := by decide
  have h_prime5 : Nat.Prime 5 := by decide
  have h_coprime : Coprime (2^3) (5^3) := by decide
  have h1 : totient (2^3) = 4 := by
    have := totient_prime_pow h_prime2 (by decide : 0 < 3)
    exact this
  have h2 : totient (5^3) = 100 := by
    have := totient_prime_pow h_prime5 (by decide : 0 < 3)
    exact this
  rw [show 1000 = 2^3 * 5^3 by decide]
  rw [totient_mul h_coprime]
  rw [h1, h2]

-- Let's prove totient 9000 = 2400 algebraically
theorem tot9000 : totient 9000 = 2400 := by
  have h_prime2 : Nat.Prime 2 := by decide
  have h_prime3 : Nat.Prime 3 := by decide
  have h_prime5 : Nat.Prime 5 := by decide
  have h_coprime1 : Coprime (2^3) (3^2) := by decide
  have h_coprime2 : Coprime (2^3 * 3^2) (5^3) := by decide
  have h1 : totient (2^3) = 4 := by
    have := totient_prime_pow h_prime2 (by decide : 0 < 3)
    exact this
  have h2 : totient (3^2) = 6 := by
    have := totient_prime_pow h_prime3 (by decide : 0 < 2)
    exact this
  have h3 : totient (5^3) = 100 := by
    have := totient_prime_pow h_prime5 (by decide : 0 < 3)
    exact this
  rw [show 9000 = (2^3 * 3^2) * 5^3 by decide]
  rw [totient_mul h_coprime2]
  rw [totient_mul h_coprime1]
  rw [h1, h2, h3]

-- Now prove a 10000 > 0 using the algebraic proofs!
theorem proof_10000 : a 10000 > 0 := by
  have hsq : sqrt (totient 1000 * totient (10000 - 1000)) ^ 2 = totient 1000 * totient (10000 - 1000) := by
    rw [show 10000 - 1000 = 9000 by decide]
    rw [tot1000, tot9000]
    -- Goal is now: sqrt (400 * 2400) ^ 2 = 400 * 2400
    -- which is: sqrt 960000 ^ 2 = 960000
    exact sqrt_eq_of_sq 960000 979 (by decide)
  exact a_pos_of_exists 10000 1000 (by decide) (by decide) hsq
