import FormalConjectures.Util.ProblemImports
open Nat

lemma square_ne_prime_cube {p n : ℕ} (hp : Nat.Prime p) : n ^ 2 ≠ p ^ 3 := by
  intro h
  have hf := congrArg (fun m : ℕ => m.factorization p) h
  have hnfac : (n ^ 2).factorization p = 2 * n.factorization p := by
    rw [Nat.factorization_pow]
    rfl
  have hpfac : (p ^ 3).factorization p = 3 := by
    rw [Nat.factorization_pow, hp.factorization]
    simp
  change (n ^ 2).factorization p = (p ^ 3).factorization p at hf
  rw [hnfac, hpfac] at hf
  omega

lemma int_square_ne_prime_cube {p n : ℕ} (hp : Nat.Prime p) : ((n : ℤ) ^ 2) ≠ ((p : ℤ) ^ 3) := by
  intro h
  have hn : n ^ 2 = p ^ 3 := by exact_mod_cast h
  exact square_ne_prime_cube hp hn

#check square_ne_prime_cube
