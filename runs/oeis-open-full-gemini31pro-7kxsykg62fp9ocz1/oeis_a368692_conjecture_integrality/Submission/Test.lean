import FormalConjectures.Util.ProblemImports
open Finset Nat

lemma dvd_of_factorization_le {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0)
  (h : ∀ p : ℕ, p.Prime → padicValNat p D ≤ padicValNat p N) : D ∣ N := by
  rw [← Nat.factorization_le_iff_dvd hD hN]
  intro p
  by_cases hp : p.Prime
  · have h1 : D.factorization p = padicValNat p D := Nat.factorization_def D hp
    have h2 : N.factorization p = padicValNat p N := Nat.factorization_def N hp
    rw [h1, h2]
    exact h p hp
  · have h1 : D.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime D hp
    rw [h1]
    exact Nat.zero_le _

-- Include all other lemmas as sorry just to check the final theorem structure.
lemma padic_108_2 : padicValNat 2 108 = 2 := sorry
lemma padic_108_3 : padicValNat 3 108 = 3 := sorry
lemma padic_108_p {p : ℕ} (hp : p.Prime) (hp_gt : 3 < p) : padicValNat p 108 = 0 := sorry

lemma padic_N_ge_padic_D_two (n : ℕ) :
  padicValNat 2 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) + 2
    ≤ padicValNat 2 ((12 * n + 6).factorial * (6 * n + 9).factorial) := sorry

lemma padic_N_ge_padic_D_three (n : ℕ) :
  padicValNat 3 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) + 3
    ≤ padicValNat 3 ((12 * n + 6).factorial * (6 * n + 9).factorial) := sorry

lemma padic_N_ge_padic_D_prime (n p : ℕ) (hp : p.Prime) :
  padicValNat p ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2)
    ≤ padicValNat p ((12 * n + 6).factorial * (6 * n + 9).factorial) := sorry

theorem oeis_a368692_conjecture_integrality (n : ℕ) :
  108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ∣ (12 * n + 6)! * (6 * n + 9)! := by
  let D' := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  let D := 108 * D'
  let N := (12 * n + 6)! * (6 * n + 9)!
  
  have hD' : D' ≠ 0 := mul_ne_zero (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (pow_ne_zero 2 (factorial_ne_zero _))
  have hD : D ≠ 0 := mul_ne_zero (by decide) hD'
  have hN : N ≠ 0 := mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
  
  apply dvd_of_factorization_le hD hN
  intro p hp
  have fact_p : Fact p.Prime := ⟨hp⟩
  have h_mul : padicValNat p D = padicValNat p 108 + padicValNat p D' := padicValNat.mul (by decide) hD'
  rw [h_mul]

  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  rcases eq_or_lt_of_le hp2 with rfl | hp3
  · -- p = 2
    have H1 := padic_108_2
    have H2 := padic_N_ge_padic_D_two n
    dsimp [D', N] at *
    omega
  · rcases eq_or_lt_of_le (show 3 ≤ p by omega) with rfl | hp4
    · -- p = 3
      have H1 := padic_108_3
      have H2 := padic_N_ge_padic_D_three n
      dsimp [D', N] at *
      omega
    · -- p > 3
      have H1 := padic_108_p hp hp4
      have H2 := padic_N_ge_padic_D_prime n p hp
      dsimp [D', N] at *
      omega

