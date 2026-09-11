import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

/--
oeis_189409_conjecture_0:
It is conjectured that numbers in this sequence are always squarefree,
and that there are infinitely many primes in this sequence.
-/
theorem oeis_a189409_conjectures :
  (∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)} :=
by sorry

lemma nth_prime_0 : nth Nat.Prime 0 = 2 := by have h : 0 = count Nat.Prime 2 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 2)
lemma nth_prime_1 : nth Nat.Prime 1 = 3 := by have h : 1 = count Nat.Prime 3 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 3)
lemma nth_prime_2 : nth Nat.Prime 2 = 5 := by have h : 2 = count Nat.Prime 5 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 5)
lemma nth_prime_3 : nth Nat.Prime 3 = 7 := by have h : 3 = count Nat.Prime 7 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 7)
lemma nth_prime_4 : nth Nat.Prime 4 = 11 := by have h : 4 = count Nat.Prime 11 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 11)
lemma nth_prime_5 : nth Nat.Prime 5 = 13 := by have h : 5 = count Nat.Prime 13 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 13)
lemma nth_prime_6 : nth Nat.Prime 6 = 17 := by have h : 6 = count Nat.Prime 17 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 17)
lemma nth_prime_7 : nth Nat.Prime 7 = 19 := by have h : 7 = count Nat.Prime 19 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 19)
lemma nth_prime_8 : nth Nat.Prime 8 = 23 := by have h : 8 = count Nat.Prime 23 := rfl; rw [h]; exact nth_count (by decide : Nat.Prime 23)

theorem a_9_eq : a 9 = 49770428644836901 := by
  dsimp [a]
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ]
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ]
  rw [prod_range_succ, prod_range_zero]
  rw [nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4]
  rw [nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8]
  rfl

theorem not_squarefree_a9 : ¬ Squarefree (a 9) := by
  rw [a_9_eq]
  intro h
  have h1 : 29 * 29 ∣ 49770428644836901 := by
    use 59180057841661
  have h2 := h 29 h1
  have h3 : 29 = 1 := Nat.isUnit_iff.mp h2
  revert h3
  decide

theorem oeis_a189409_conjectures.disproof : ¬ (type_of% @oeis_a189409_conjectures) := by
  intro h
  rcases h with ⟨h1, h2⟩
  exact not_squarefree_a9 (h1 9)
