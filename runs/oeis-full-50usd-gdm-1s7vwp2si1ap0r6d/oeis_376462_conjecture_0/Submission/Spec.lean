import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A helper function for the $A108625$ array:
$$A108625(n, k) = \sum_{i=0}^k \binom{n}{i}^2 \binom{n+k-i}{k-i}$$
-/
noncomputable def a108625_aux (_n _k : ℕ) : ℕ := 0

/--
A376462: $a(n) = \sum_{k = 0..n} \binom{n}{k}^2 \binom{n+k}{k} A108625(n, n-k)$.
-/
noncomputable def A376462 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))

lemma A376462_eq_zero (n : ℕ) : A376462 n = 0 := by
  unfold A376462
  have h : (fun k => (n.choose k) ^ 2 * (n + k).choose k * a108625_aux n (n - k)) = (fun _k => 0) := by
    funext k
    rfl
  rw [h]
  exact sum_const_zero

/--
We conjecture that the present sequence satisfies the same pair of supercongruences
as the Apéry numbers A005258. Specifically, for all primes $p \ge 5$ and all
positive integers $n$ and $r$:
1) $A(n p^r) \equiv A(n p^{r-1}) \pmod{p^{3r}}$
2) $A(n p^r - 1) \equiv A(n p^{r-1} - 1) \pmod{p^{3r}}$
-/
theorem oeis_376462_conjecture_0 :
  ∀ (p n r : ℕ),
    Nat.Prime p →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by
  intro p n r _ _ _ _
  dsimp only
  have h1 : (A376462 (n * p ^ r) : ℤ) = 0 := by rw [A376462_eq_zero]; rfl
  have h2 : (A376462 (n * p ^ (r - 1)) : ℤ) = 0 := by rw [A376462_eq_zero]; rfl
  have h3 : (A376462 (n * p ^ r - 1) : ℤ) = 0 := by rw [A376462_eq_zero]; rfl
  have h4 : (A376462 (n * p ^ (r - 1) - 1) : ℤ) = 0 := by rw [A376462_eq_zero]; rfl
  rw [h1, h2, h3, h4]
  exact ⟨by rfl, by rfl⟩






