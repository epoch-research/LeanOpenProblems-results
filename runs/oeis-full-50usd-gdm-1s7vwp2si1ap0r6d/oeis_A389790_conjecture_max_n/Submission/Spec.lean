import FormalConjectures.Util.ProblemImports
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  -- Iterate over pairs (p, q) from R x R
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-- The statement that $n_{max}$ is the conjectured largest value of $n$ such that $a(n) = k$. -/
def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

/-- Computable version of `next_prime`. -/
def next_prime_computable (n : ℕ) : ℕ :=
  have h : ∃ k, Nat.Prime k ∧ n < k := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp2, hp1⟩
  Nat.find h

/-- Proof of equivalence of noncomputable and computable definitions of `next_prime`. -/
theorem next_prime_eq (r : ℕ) : next_prime r = next_prime_computable r := by
  have h : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (r + 1)
    exact ⟨p, hp2, hp1⟩
  have h_comp : ∃ k, Nat.Prime k ∧ r < k := h
  have h1 : next_prime r ≤ next_prime_computable r := by
    have h_mem : next_prime_computable r ∈ {k : ℕ | Nat.Prime k ∧ r < k} := by
      exact Nat.find_spec h_comp
    exact Nat.sInf_le h_mem
  have h2 : next_prime_computable r ≤ next_prime r := by
    have h_mem : next_prime r ∈ {k : ℕ | Nat.Prime k ∧ r < k} := by
      exact sInf_mem h
    exact Nat.find_min' h_comp h_mem
  exact le_antisymm h1 h2

/-- Computable version of `S_sum`. -/
def S_sum_computable (r : ℕ) : ℕ := r + next_prime_computable r

theorem S_sum_eq (r : ℕ) : S_sum r = S_sum_computable r := by
  unfold S_sum S_sum_computable
  rw [next_prime_eq]

/-- Computable version of `a`. -/
def a_computable (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum_computable p + S_sum_computable q = target
  ) (R ×ˢ R)

theorem a_eq (n : ℕ) : a n = a_computable n := by
  unfold a a_computable
  simp only [S_sum_eq]

/-- Highly optimized version of `a_computable` for fast kernel reduction. -/
def a_computable_fast (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range target
  let primes := Finset.filter Nat.Prime R
  Finset.card $ Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    p ≤ q ∧ S_sum_computable p + S_sum_computable q = target
  ) (primes ×ˢ primes)

theorem a_computable_eq_fast (n : ℕ) : a_computable n = a_computable_fast n := by
  unfold a_computable a_computable_fast
  have h_eq : Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum_computable p + S_sum_computable q = 2 * n
  ) (Finset.range (2 * n) ×ˢ Finset.range (2 * n)) =
  Finset.filter (fun pr : ℕ × ℕ =>
    let (p, q) := pr
    p ≤ q ∧ S_sum_computable p + S_sum_computable q = 2 * n
  ) (Finset.filter Nat.Prime (Finset.range (2 * n)) ×ˢ Finset.filter Nat.Prime (Finset.range (2 * n))) := by
    ext ⟨p, q⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  exact congr_arg Finset.card h_eq

/--
  A389790 Conjecture: a(n) = k for a largest value of n given by the table below.

  k     conjectured largest value of n for which a(n) = k
----------------
  2      833
  3     1487
  4     1411
  5     1523
  6     1747
  7     2621
  8     2153
  9     3091
  10     3238
-/
theorem oeis_A389790_conjecture_max_n :
  is_conjectured_largest_value 833 2 ∧
  is_conjectured_largest_value 1487 3 ∧
  is_conjectured_largest_value 1411 4 ∧
  is_conjectured_largest_value 1523 5 ∧
  is_conjectured_largest_value 1747 6 ∧
  is_conjectured_largest_value 2621 7 ∧
  is_conjectured_largest_value 2153 8 ∧
  is_conjectured_largest_value 3091 9 ∧
  is_conjectured_largest_value 3238 10
:= by sorry



