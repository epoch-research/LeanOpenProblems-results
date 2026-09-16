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

lemma nth_val (p k : ℕ) (h_prime : Nat.Prime p) (h_count : count Nat.Prime p = k) :
    nth Nat.Prime k = p := by
  rw [← h_count]
  exact nth_count h_prime

lemma a_9_val : a 9 = 49770428644836901 := by
  unfold a
  have h0 : nth Nat.Prime 0 = 2 := nth_val 2 0 (by decide) (by rfl)
  have h1 : nth Nat.Prime 1 = 3 := nth_val 3 1 (by decide) (by rfl)
  have h2 : nth Nat.Prime 2 = 5 := nth_val 5 2 (by decide) (by rfl)
  have h3 : nth Nat.Prime 3 = 7 := nth_val 7 3 (by decide) (by rfl)
  have h4 : nth Nat.Prime 4 = 11 := nth_val 11 4 (by decide) (by rfl)
  have h5 : nth Nat.Prime 5 = 13 := nth_val 13 5 (by decide) (by rfl)
  have h6 : nth Nat.Prime 6 = 17 := nth_val 17 6 (by decide) (by rfl)
  have h7 : nth Nat.Prime 7 = 19 := nth_val 19 7 (by decide) (by rfl)
  have h8 : nth Nat.Prime 8 = 23 := nth_val 23 8 (by decide) (by rfl)
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ,
      prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ,
      prod_range_succ, prod_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num

lemma not_squarefree_a9 : ¬ Squarefree (a 9) := by
  rw [a_9_val]
  intro h
  have h1 : 29 ^ 2 ∣ 49770428644836901 := by decide
  have h2 := h 29 h1
  have h3 : ¬ IsUnit (29 : ℕ) := by
    rw [Nat.isUnit_iff]
    decide
  exact h3 h2

theorem oeis_a189409_conjectures.disproof : ¬ (type_of% @oeis_a189409_conjectures) := by
  intro h
  have h1 := h.1
  have h2 := h1 9
  exact not_squarefree_a9 h2
