import FormalConjectures.Util.ProblemImports

open Nat

/--
A182126: $a(n) = \text{prime}(n) \cdot \text{prime}(n+1) \bmod \text{prime}(n+2)$.
The function $\text{prime}(k)$ is the $k$-th prime number, with $\text{prime}(1)=2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0 -- Handle the 0 case for the otherwise 1-indexed sequence
  else (p_n n * p_n (n + 1)) % p_n (n + 2)


/-- Conjecture: Are 2, 7, 11, 13, 29 the only primes in this sequence? -/
theorem oeis_182126_conjecture_3 :
  ∀ n : ℕ, n > 0 → (Nat.Prime (a n) ↔ a n ∈ ([2, 7, 11, 13, 29] : List ℕ)) :=
by sorry
