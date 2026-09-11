import Mathlib
open Nat Finset padicValRat ArithmeticFunction

def invSigma : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else (1 : ℚ) / (↑((sigma 1) n) : ℚ), if_pos rfl⟩

lemma invSigma_mult : IsMultiplicative invSigma := by
  constructor
  · simp [invSigma]
  · intro m n hm
    dsimp [invSigma]
    by_cases h : m * n = 0
    · rcases Nat.mul_eq_zero.mp h with hm0 | hn0
      · simp [hm0]
      · simp [hn0]
    · have hm0 : m ≠ 0 := fun h1 => h (by simp [h1])
      have hn0 : n ≠ 0 := fun h1 => h (by simp [h1])
      simp [h, hm0, hn0]
      have hs : (sigma 1) (m * n) = (sigma 1) m * (sigma 1) n := IsMultiplicative.map_mul_of_coprime (isMultiplicative_sigma) hm
      rw [hs]
      push_cast
      rw [mul_inv]

def zetaRat : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else 1, if_pos rfl⟩

lemma zetaRat_mult : IsMultiplicative zetaRat := by
  constructor
  · simp [zetaRat]
  · intro m n hm
    dsimp [zetaRat]
    by_cases h : m * n = 0
    · rcases Nat.mul_eq_zero.mp h with hm0 | hn0
      · simp [hm0]
      · simp [hn0]
    · have hm0 : m ≠ 0 := fun h1 => h (by simp [h1])
      have hn0 : n ≠ 0 := fun h1 => h (by simp [h1])
      simp [h, hm0, hn0]

def S_func : ArithmeticFunction ℚ := invSigma * zetaRat

lemma S_func_eq (n : ℕ) (hn : n ≠ 0) : S_func n = n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ) := by
  dsimp [S_func, ArithmeticFunction.mul_apply]
  have h1 : (∑ x ∈ n.divisorsAntidiagonal, invSigma x.1 * zetaRat x.2) = ∑ x ∈ n.divisorsAntidiagonal, invSigma x.1 := by
    apply sum_congr rfl
    intro x hx
    have hx2_ne_zero : x.2 ≠ 0 := by
      rw [mem_divisorsAntidiagonal] at hx
      intro h
      have hx_mul : x.1 * x.2 = n := hx.1
      rw [h, mul_zero] at hx_mul
      exact hn hx_mul.symm
    have h2 : zetaRat x.2 = 1 := by
      dsimp [zetaRat]
      rw [if_neg hx2_ne_zero]
    rw [h2, mul_one]
  rw [h1]
  have h3 : ∑ x ∈ n.divisorsAntidiagonal, invSigma x.1 = ∑ d ∈ n.divisors, invSigma d := by
    exact sum_divisorsAntidiagonal (fun x y => invSigma x)
  rw [h3]
  apply sum_congr rfl
  intro d hd
  have hd_ne_zero : d ≠ 0 := by
    rintro rfl
    simp [hn] at hd
  simp [invSigma, hd_ne_zero]

lemma S_func_mult : IsMultiplicative S_func := IsMultiplicative.mul invSigma_mult zetaRat_mult

theorem oeis_265709_conjecture_0 : ∃ (n : ℕ), 1 < n ∧ ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1 := by
  sorry

theorem oeis_265709_conjecture_0_disproof : ¬ (∃ (n : ℕ), 1 < n ∧ ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  sorry
