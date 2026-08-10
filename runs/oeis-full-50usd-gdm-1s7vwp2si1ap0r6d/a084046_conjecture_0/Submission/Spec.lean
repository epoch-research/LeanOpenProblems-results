import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A084046: Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
I.e., smallest prime of the form $k^n - n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- S_n is the set of primes p such that p + n is an n-th power, i.e., p = k^n - n.
  let S_n : Set ℕ := { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ n = p + n }
  -- sInf S_n returns the smallest element of S_n. For Nat, sInf ∅ = 0, fitting the problem statement.
  sInf S_n

theorem cubic_identity (y : ℕ) :
  (y + 3)^3 = y * ((y + 3)^2 + 3 * (y + 3) + 9) + 27 := by
  ring

theorem cubic_identity_sub (x : ℕ) (hx : x ≥ 3) :
  x^3 = (x - 3) * (x^2 + 3 * x + 9) + 27 := by
  have h_cancel : (x - 3) + 3 = x := Nat.sub_add_cancel hx
  have h_id := cubic_identity (x - 3)
  rw [h_cancel] at h_id
  exact h_id

theorem full_identity (k : ℕ) (hk : k ≥ 2) :
  k^27 = (k^9 - 3) * (k^18 + 3 * k^9 + 9) + 27 := by
  have h_k9_ge : k^9 ≥ 2^9 := Nat.pow_le_pow_left hk 9
  have h_2_9 : 2^9 = 512 := rfl
  have h1 : k^9 ≥ 3 := by omega
  have h_id := cubic_identity_sub (k^9) h1
  have h_27 : 27 = 9 * 3 := by rfl
  have h_18 : 18 = 9 * 2 := by rfl
  have h_pow27 : k^27 = (k^9)^3 := by
    rw [h_27, pow_mul]
  have h_pow18 : k^18 = (k^9)^2 := by
    rw [h_18, pow_mul]
  rw [h_pow27, h_pow18]
  exact h_id

theorem not_prime_27 (k : ℕ) (p : ℕ) (hp : Nat.Prime p) (h : k^27 = p + 27) : False := by
  by_cases hk : k ≥ 2
  · have h_k9_ge : k^9 ≥ 2^9 := Nat.pow_le_pow_left hk 9
    have h_2_9 : 2^9 = 512 := rfl
    have h1 : k^9 ≥ 3 := by omega
    have h_id := full_identity k hk
    rw [h] at h_id
    have hp_prod : p = (k^9 - 3) * (k^18 + 3 * k^9 + 9) := by omega
    have h_dvd : (k^9 - 3) ∣ p := by
      use (k^18 + 3 * k^9 + 9)
    rcases Nat.Prime.eq_one_or_self_of_dvd hp (k^9 - 3) h_dvd with h_one | h_self
    · have h_k9_eq4 : k^9 = 4 := by omega
      omega
    · have h_eq : p * 1 = p * (k^18 + 3 * k^9 + 9) := by
        calc
          p * 1 = p := by ring
          _ = (k^9 - 3) * (k^18 + 3 * k^9 + 9) := hp_prod
          _ = p * (k^18 + 3 * k^9 + 9) := by rw [h_self]
      have h_cancel : 1 = k^18 + 3 * k^9 + 9 := Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos hp) h_eq
      omega
  · -- here hk is ¬(k ≥ 2), so k < 2
    have hk_lt : k < 2 := by omega
    interval_cases k
    · -- k = 0
      have h0 : 0^27 = 0 := rfl
      rw [h0] at h
      omega
    · -- k = 1
      have h1 : 1^27 = 1 := rfl
      rw [h1] at h
      omega

theorem S_27_empty : { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ 27 = p + 27 } = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h_mem
  rcases h_mem with ⟨hp, k, hk⟩
  exact not_prime_27 k p hp hk

theorem a_27_eq_zero : a 27 = 0 := by
  unfold a
  dsimp only
  rw [S_27_empty]
  exact Nat.sInf_empty

theorem not_even_square_27 (m : ℕ) : 27 ≠ (2 * m) ^ 2 := by
  have h_eq : (2 * m) ^ 2 = 4 * m^2 := by ring
  rw [h_eq]
  omega

/-- Conjecture disproof: there is a k which is not an even square for which a(k) = 0. -/
theorem a084046_conjecture_0.disproof :
  ¬ (∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2) := by
  intro h
  have h27 := h 27 a_27_eq_zero
  rcases h27 with ⟨m, hm⟩
  exact not_even_square_27 m hm

