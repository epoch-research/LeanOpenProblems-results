import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat Finset List

/--
A003958 is a multiplicative function defined by $A003958(p^e) = (p-1)^e$ for a prime power $p^e$.
For $n = \prod p_i^{e_i}$, $A003958(n) = \prod (p_i - 1)^{e_i}$.
-/
def A003958 (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => (p - 1) ^ e

/--
A351442: $a(n) = A003958(\sigma(n))$, where $A003958$ is multiplicative with $a(p^e) = (p-1)^e$
and $\sigma$ is the sum of divisors function.
-/
def a (n : ℕ) : ℕ :=
  A003958 (ArithmeticFunction.sigma 1 n)

def N_counter : ℕ := 28996592704045424640
def M_sigma : ℕ := 140078688585537333726

def L_factors : List ℕ := [2, 3, 3, 29, 43, 127, 307, 1093, 4733, 30941]

theorem prime_of_no_divisors_bound (n : ℕ) (h_sqrt : ℕ) (h_sqrt_eq : h_sqrt = sqrt n) (hn : 2 ≤ n)
    (h_all : ∀ m ∈ List.range (h_sqrt + 1), 2 ≤ m → ¬ m ∣ n) : Nat.Prime n := by
  rw [prime_def_le_sqrt]
  refine ⟨hn, ?_⟩
  intro m h2 h_le h_div
  have h_lt : m < h_sqrt + 1 := by
    rw [h_sqrt_eq]
    omega
  have h_mem : m ∈ List.range (h_sqrt + 1) := List.mem_range.mpr h_lt
  exact h_all m h_mem h2 h_div

theorem prime_30941 : Nat.Prime 30941 := by
  apply prime_of_no_divisors_bound 30941 175 (eq_sqrt.mpr ⟨by decide, by decide⟩) (by decide)
  decide

theorem prime_4733 : Nat.Prime 4733 := by
  apply prime_of_no_divisors_bound 4733 68 (eq_sqrt.mpr ⟨by decide, by decide⟩) (by decide)
  decide

theorem prime_1093 : Nat.Prime 1093 := by
  apply prime_of_no_divisors_bound 1093 33 (eq_sqrt.mpr ⟨by decide, by decide⟩) (by decide)
  decide

theorem prime_307 : Nat.Prime 307 := by
  apply prime_of_no_divisors_bound 307 17 (eq_sqrt.mpr ⟨by decide, by decide⟩) (by decide)
  decide

theorem prime_127 : Nat.Prime 127 := by decide
theorem prime_43 : Nat.Prime 43 := by decide
theorem prime_29 : Nat.Prime 29 := by decide
theorem prime_17 : Nat.Prime 17 := by decide
theorem prime_13 : Nat.Prime 13 := by decide
theorem prime_7 : Nat.Prime 7 := by decide
theorem prime_5 : Nat.Prime 5 := by decide
theorem prime_3 : Nat.Prime 3 := by decide
theorem prime_2 : Nat.Prime 2 := by decide

theorem L_factors_primes : ∀ p ∈ L_factors, Nat.Prime p := by
  intro p hp
  simp only [L_factors, List.mem_cons] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hp
  · exact prime_2
  · exact prime_3
  · exact prime_3
  · exact prime_29
  · exact prime_43
  · exact prime_127
  · exact prime_307
  · exact prime_1093
  · exact prime_4733
  · exact prime_30941
  · contradiction

theorem L_factors_sorted : L_factors.SortedLE := by decide

theorem L_factors_prod : L_factors.prod = M_sigma := by decide

theorem M_sigma_factors : primeFactorsList M_sigma = L_factors := by
  have perm : L_factors ~ primeFactorsList M_sigma := primeFactorsList_unique L_factors_prod L_factors_primes
  have s1 : L_factors.SortedLE := L_factors_sorted
  have s2 : (primeFactorsList M_sigma).SortedLE := primeFactorsList_sorted M_sigma
  exact Perm.eq_of_sortedLE s2 s1 perm.symm

theorem sigma_mul {a b : ℕ} (h : Nat.Coprime a b) :
    ArithmeticFunction.sigma 1 (a * b) = ArithmeticFunction.sigma 1 a * ArithmeticFunction.sigma 1 b := by
  exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime ArithmeticFunction.isMultiplicative_sigma h

def x0 : ℕ := 17^2
def x1 : ℕ := 13^4
def x2 : ℕ := 7^6
def x3 : ℕ := 5^1
def x4 : ℕ := 3^6
def x5 : ℕ := 2^13

def n1 : ℕ := x0
def n2 : ℕ := n1 * x1
def n3 : ℕ := n2 * x2
def n4 : ℕ := n3 * x3
def n5 : ℕ := n4 * x4
def n6 : ℕ := n5 * x5

theorem n6_eq : n6 = N_counter := by decide

theorem sigma_N_counter : ArithmeticFunction.sigma 1 N_counter = 140078688585537333726 := by
  rw [← n6_eq]
  have h2 : ArithmeticFunction.sigma 1 n2 = ArithmeticFunction.sigma 1 n1 * ArithmeticFunction.sigma 1 x1 := sigma_mul (by decide)
  have h3 : ArithmeticFunction.sigma 1 n3 = ArithmeticFunction.sigma 1 n2 * ArithmeticFunction.sigma 1 x2 := sigma_mul (by decide)
  have h4 : ArithmeticFunction.sigma 1 n4 = ArithmeticFunction.sigma 1 n3 * ArithmeticFunction.sigma 1 x3 := sigma_mul (by decide)
  have h5 : ArithmeticFunction.sigma 1 n5 = ArithmeticFunction.sigma 1 n4 * ArithmeticFunction.sigma 1 x4 := sigma_mul (by decide)
  have h6 : ArithmeticFunction.sigma 1 n6 = ArithmeticFunction.sigma 1 n5 * ArithmeticFunction.sigma 1 x5 := sigma_mul (by decide)
  rw [h6, h5, h4, h3, h2]
  have hs0 : ArithmeticFunction.sigma 1 n1 = ∑ k ∈ Finset.range 3, 17 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_17
  have hs1 : ArithmeticFunction.sigma 1 x1 = ∑ k ∈ Finset.range 5, 13 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_13
  have hs2 : ArithmeticFunction.sigma 1 x2 = ∑ k ∈ Finset.range 7, 7 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_7
  have hs3 : ArithmeticFunction.sigma 1 x3 = ∑ k ∈ Finset.range 2, 5 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_5
  have hs4 : ArithmeticFunction.sigma 1 x4 = ∑ k ∈ Finset.range 7, 3 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_3
  have hs5 : ArithmeticFunction.sigma 1 x5 = ∑ k ∈ Finset.range 14, 2 ^ k := by
    exact ArithmeticFunction.sigma_one_apply_prime_pow prime_2
  rw [hs0, hs1, hs2, hs3, hs4, hs5]
  decide

theorem A003958_M_sigma : A003958 M_sigma = N_counter := by
  rw [A003958]
  rw [prod_factorization_eq_prod_primeFactors]
  rw [primeFactors, M_sigma_factors]
  have h_count : ∀ p, M_sigma.factorization p = L_factors.count p := by
    intro p
    rw [← primeFactorsList_count_eq, M_sigma_factors]
  simp_rw [h_count]
  decide

/--
oeis_351442_conjecture_0: Question: Are there more fixed points than 1, 2, 8, 128, 288, 720, 32768, 29719872, ..., 2147483648 ?
This theorem conjectures that these numbers are exactly the positive fixed points of the sequence $a(n)$.
The list of fixed points is taken verbatim from the OEIS entry.
-/
theorem oeis_351442_conjecture_0.disproof :
  ¬ (∀ n : ℕ, n > 0 → (a n = n ↔ n ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ))) := by
  intro h
  have h_counter : a N_counter = N_counter ↔ N_counter ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ) := h N_counter (by decide)
  have h_a_eq : a N_counter = N_counter := by
    rw [a]
    rw [sigma_N_counter]
    exact A003958_M_sigma
  have h_in : N_counter ∈ ({1, 2, 8, 128, 288, 720, 32768, 29719872, 2147483648} : Finset ℕ) := h_counter.mp h_a_eq
  revert h_in
  decide
