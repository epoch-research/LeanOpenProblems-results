import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A189409: $a(n) = \text{prime}(n)\#^2 + 1$, where $\text{prime}(n)\#$ is the $n$-th primorial (A002110),
interpreted as the product of the first $n$ primes.
Specifically, $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$, where $p_k$ is the $k$-th prime ($p_0=2, p_1=3, \ldots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k : ℕ => Nat.nth Nat.Prime k)) ^ 2 + 1

theorem nth_prime_5 : nth Nat.Prime 5 = 13 := by
  have h := nth_count (p := Nat.Prime) (n := 13) (by decide)
  have hcount : count Nat.Prime 13 = 5 := rfl
  rwa [hcount] at h

theorem nth_prime_6 : nth Nat.Prime 6 = 17 := by
  have h := nth_count (p := Nat.Prime) (n := 17) (by decide)
  have hcount : count Nat.Prime 17 = 6 := rfl
  rwa [hcount] at h

theorem nth_prime_7 : nth Nat.Prime 7 = 19 := by
  have h := nth_count (p := Nat.Prime) (n := 19) (by decide)
  have hcount : count Nat.Prime 19 = 7 := rfl
  rwa [hcount] at h

theorem nth_prime_8 : nth Nat.Prime 8 = 23 := by
  have h := nth_count (p := Nat.Prime) (n := 23) (by decide)
  have hcount : count Nat.Prime 23 = 8 := rfl
  rwa [hcount] at h

theorem a_nine_eq : a 9 = 49770428644836901 := by
  unfold a
  simp only [prod_range_succ, prod_range_zero, one_mul]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five,
      nth_prime_three_eq_seven, nth_prime_four_eq_eleven, nth_prime_5,
      nth_prime_6, nth_prime_7, nth_prime_8]
  rfl

theorem not_squarefree_mul (a' aa b n : ℕ) (ha : a' * a' = aa) (hb : aa * b = n) (h₁ : 1 < a') :
    ¬Squarefree n := by
  rw [← hb, ← ha]
  exact fun H => _root_.ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)

theorem not_squarefree_a_nine : ¬ Squarefree (a 9) := by
  have h_mul : 29 * 29 = 841 := rfl
  have h_eq : 841 * 59180057841661 = a 9 := by
    rw [a_nine_eq]
  exact not_squarefree_mul 29 841 59180057841661 (a 9) h_mul h_eq (by decide)

theorem oeis_a189409_conjectures.disproof :
  ¬ ((∀ (n : ℕ), Squarefree (a n)) ∧ Set.Infinite {n : ℕ | Nat.Prime (a n)}) := by
  intro h
  have h_sf := h.1 9
  exact not_squarefree_a_nine h_sf

