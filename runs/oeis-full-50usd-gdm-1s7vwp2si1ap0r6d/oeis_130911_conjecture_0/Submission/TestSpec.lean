import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat Finset

/--
A130911: $a(n)$ is the number of primes with odd binary weight among the first $n$ primes minus the number with an even binary weight.
Primes with odd binary weight are called odious primes (A027697); primes with even binary weight are called evil primes (A027699).
$$a(n) = \sum_{k=1}^n \left( \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is odd}\} } - \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is even}\} } \right)$$
where $p_k$ is the $k$-th prime number.
-/
noncomputable def A130911 (n : ℕ) : ℤ :=
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
  let weight_parity_sign (p : ℕ) : ℤ :=
    if (binary_weight p).bodd then 1 else -1
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

theorem A130911_step (n : ℕ) : A130911 (n+1) = A130911 n +
  (let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum
   let weight_parity_sign (p : ℕ) : ℤ := if (binary_weight p).bodd then 1 else -1
   weight_parity_sign (Nat.nth Nat.Prime n)) := by
  dsimp [A130911]
  rw [sum_range_succ]

theorem count_prime_0 : count Nat.Prime 0 = 0 := rfl
theorem count_prime_1 : count Nat.Prime 1 = 0 := by rw [count_succ, count_prime_0]; rfl
theorem count_prime_2 : count Nat.Prime 2 = 0 := by rw [count_succ, count_prime_1]; rfl
theorem count_prime_3 : count Nat.Prime 3 = 1 := by rw [count_succ, count_prime_2]; rfl
theorem count_prime_4 : count Nat.Prime 4 = 2 := by rw [count_succ, count_prime_3]; rfl
theorem count_prime_5 : count Nat.Prime 5 = 2 := by rw [count_succ, count_prime_4]; rfl
theorem count_prime_6 : count Nat.Prime 6 = 3 := by rw [count_succ, count_prime_5]; rfl
theorem count_prime_7 : count Nat.Prime 7 = 3 := by rw [count_succ, count_prime_6]; rfl
theorem count_prime_8 : count Nat.Prime 8 = 4 := by rw [count_succ, count_prime_7]; rfl
theorem count_prime_9 : count Nat.Prime 9 = 4 := by rw [count_succ, count_prime_8]; rfl
theorem count_prime_10 : count Nat.Prime 10 = 4 := by rw [count_succ, count_prime_9]; rfl

