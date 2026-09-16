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

/-- Conjecture: if a(k) = 0 then k is an even square. -/
theorem a084046_conjecture_0 :
  ∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2 :=
by sorry

lemma k9_ge_3 {k : ℕ} (hk : k ≥ 2) : k ^ 9 ≥ 3 := by
  have : k ^ 9 ≥ 2 ^ 9 := Nat.pow_le_pow_left hk 9
  omega

lemma factor_27 (k : ℕ) (hk : k ≥ 2) : k ^ 27 = (k ^ 9 - 3) * (k ^ 18 + 3 * k ^ 9 + 9) + 27 := by
  let X := k ^ 9
  have hX : X ≥ 3 := k9_ge_3 hk
  have hX2 : k ^ 18 = X ^ 2 := by
    calc k ^ 18 = k ^ (9 * 2) := by rfl
      _ = (k ^ 9) ^ 2 := by rw [Nat.pow_mul]
  have hX3 : k ^ 27 = X ^ 3 := by
    calc k ^ 27 = k ^ (9 * 3) := by rfl
      _ = (k ^ 9) ^ 3 := by rw [Nat.pow_mul]
  rw [hX2, hX3]
  change X ^ 3 = (X - 3) * (X ^ 2 + 3 * X + 9) + 27
  zify [hX]
  ring

lemma p_eq_prod (p k : ℕ) (hk : k ≥ 2) (heq : k ^ 27 = p + 27) : p = (k ^ 9 - 3) * (k ^ 18 + 3 * k ^ 9 + 9) := by
  have h1 := factor_27 k hk
  omega

lemma not_prime_27_aux (p k : ℕ) (h1 : k ^ 27 = p + 27) : ¬ Nat.Prime p := by
  by_cases hk : k ≥ 2
  · intro hp
    have hp_eq : p = (k ^ 9 - 3) * (k ^ 18 + 3 * k ^ 9 + 9) := p_eq_prod p k hk h1
    have hX : k ^ 9 ≥ 3 := k9_ge_3 hk
    have hF1 : k ^ 9 - 3 ≥ 2 := by
      have : k ^ 9 ≥ 2 ^ 9 := Nat.pow_le_pow_left hk 9
      omega
    have hF2 : k ^ 18 + 3 * k ^ 9 + 9 ≥ 2 := by omega
    have h_div : (k ^ 9 - 3) ∣ p := by
      rw [hp_eq]
      exact dvd_mul_right (k ^ 9 - 3) (k ^ 18 + 3 * k ^ 9 + 9)
    have h_eq := Nat.Prime.eq_one_or_self_of_dvd hp _ h_div
    rcases h_eq with h | h
    · omega
    · have : k ^ 18 + 3 * k ^ 9 + 9 = 1 := by
        nlinarith
      omega
  · intro hp
    have hk_lt : k < 2 := by omega
    have h0 : k = 0 ∨ k = 1 := by omega
    rcases h0 with rfl | rfl
    · revert h1; norm_num
    · revert h1; norm_num

lemma a_27_eq_0 : a 27 = 0 := by
  unfold a
  have hS : { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ 27 = p + 27 } = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    intro hp k heq
    exact not_prime_27_aux p k heq hp
  rw [hS]
  exact sInf_empty

lemma not_even_square_27 : ¬ ∃ m : ℕ, 27 = (2 * m) ^ 2 := by
  intro h
  rcases h with ⟨m, hm⟩
  have hm2 : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
  rw [hm2] at hm
  have : 27 % 4 = (4 * m ^ 2) % 4 := by rw [hm]
  have h1 : 27 % 4 = 3 := by rfl
  have h2 : (4 * m ^ 2) % 4 = 0 := by exact Nat.mul_mod_right 4 (m ^ 2)
  rw [h1, h2] at this
  contradiction

theorem a084046_conjecture_0.disproof : ¬ (type_of% @a084046_conjecture_0) := by
  intro h
  have h27 := h 27 a_27_eq_0
  exact not_even_square_27 h27
