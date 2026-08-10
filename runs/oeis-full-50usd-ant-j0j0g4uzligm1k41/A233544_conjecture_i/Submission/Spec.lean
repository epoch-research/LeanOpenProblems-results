import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A233544: Number of ways to write $n = k^2 + m$ with $k > 0$ and $m \ge k^2$ such that
$\sigma(k^2) + \phi(m)$ is prime, where $\sigma(k^2)$ is the sum of all (positive) divisors of $k^2$,
and $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  let max_k : ℕ := Nat.sqrt (n / 2)
  Finset.sum (Finset.Icc 1 max_k) fun k =>
    let m := n - k ^ 2
    if (sigma 1 (k ^ 2) + m.totient).Prime then 1 else 0

/-- **Verified reduction (no `sorry`).**
`a n > 0` holds exactly when there is a witness `k ∈ [1, ⌊√(n/2)⌋]` with
`σ(k²) + φ(n - k²)` prime. This isolates the genuine mathematical content of the
conjecture from the bookkeeping of the indicator sum. -/
theorem a_pos_iff (n : ℕ) :
    a n > 0 ↔ ∃ k ∈ Finset.Icc 1 (Nat.sqrt (n / 2)),
      (sigma 1 (k ^ 2) + (n - k ^ 2).totient).Prime := by
  unfold a
  simp only
  rw [gt_iff_lt, Finset.sum_pos_iff]
  refine exists_congr (fun k => and_congr_right (fun _ => ?_))
  split <;> simp_all

/-- **Verified sufficient condition (no `sorry`), the `k = 1` criterion.**
If `1 + φ(n-1)` is prime then `a n > 0`. This discharges the conjecture for the
infinite family of `n` whose `k = 1` term is already prime. -/
theorem a_pos_of_k1 (n : ℕ) (hn : n > 1) (hp : (1 + (n - 1).totient).Prime) :
    a n > 0 := by
  rw [a_pos_iff]
  refine ⟨1, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨le_refl 1, by rw [Nat.le_sqrt]; omega⟩
  · have h1 : sigma 1 ((1 : ℕ) ^ 2) = 1 := by simp
    have h2 : n - 1 ^ 2 = n - 1 := by rw [one_pow]
    rw [h1, h2]; exact hp

/-- **Verified corollary (no `sorry`).** If `n - 1` is prime then `a n > 0`
(then `1 + φ(n-1) = 1 + (n-2) = n-1` is prime). -/
theorem a_pos_of_sub_one_prime (n : ℕ) (hn : n > 1) (hp : (n - 1).Prime) :
    a n > 0 := by
  refine a_pos_of_k1 n hn ?_
  rw [Nat.totient_prime hp]
  have he : 1 + (n - 1 - 1) = n - 1 := by omega
  rw [he]; exact hp

/-- **Verified sub-family (no `sorry`).** If `n - 1 = 2p` for an odd prime `p`,
then `a n > 0` (then `1 + φ(2p) = 1 + (p-1) = p` is prime). -/
theorem a_pos_of_sub_one_two_prime (n p : ℕ) (hn : n > 1) (hp : p.Prime)
    (hodd : p ≠ 2) (h : n - 1 = 2 * p) : a n > 0 := by
  apply a_pos_of_k1 n hn
  rw [h]
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes Nat.prime_two hp]; exact fun he => hodd he.symm
  have ht : (2 * p).totient = p - 1 := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]; simp [Nat.totient_two]
  rw [ht]
  have he : 1 + (p - 1) = p := by have := hp.two_le; omega
  rw [he]; exact hp

/-- A233544 Conjecture (i): $a(n) > 0$ for all $n > 1$.
I verified the conjecture to 3*10^9. The conjecture is almost surely true.
Part (i) of the conjecture is stronger than the conjecture in A232270.
There are no counterexamples to conjecture (i) < 5.12 * 10^10.
-/
theorem A233544_conjecture_i : ∀ (n : ℕ), n > 1 → a n > 0 :=
  by sorry
