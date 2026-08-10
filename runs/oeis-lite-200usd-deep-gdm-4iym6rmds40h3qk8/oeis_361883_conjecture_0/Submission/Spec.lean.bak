import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n


lemma term_identity (n k : ℕ) (hn : 0 < n) :
    (n + 2 * k) * Nat.choose (n + k - 1) (n - 1) =
    n * (Nat.choose (n + k - 1) (n - 1) + 2 * Nat.choose (n + k - 1) n) := by
  have h_sub : (n + k - 1) - (n - 1) = k := by
    omega
  have h_succ_right : Nat.choose (n + k - 1) (n - 1 + 1) * (n - 1 + 1) = Nat.choose (n + k - 1) (n - 1) * ((n + k - 1) - (n - 1)) := by
    apply Nat.choose_succ_right_eq
  have h_simpl : n - 1 + 1 = n := by
    omega
  rw [h_simpl, h_sub] at h_succ_right
  calc
    (n + 2 * k) * Nat.choose (n + k - 1) (n - 1)
    _ = n * Nat.choose (n + k - 1) (n - 1) + 2 * (Nat.choose (n + k - 1) (n - 1) * k) := by ring
    _ = n * Nat.choose (n + k - 1) (n - 1) + 2 * (Nat.choose (n + k - 1) n * n) := by rw [← h_succ_right]
    _ = n * (Nat.choose (n + k - 1) (n - 1) + 2 * Nat.choose (n + k - 1) n) := by ring

def a_divfree (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose (n + k - 1) (n - 1)) ^ 2 * (Nat.choose (n + k - 1) (n - 1) + 2 * Nat.choose (n + k - 1) n)

lemma S_eq_n_mul_divfree (n : ℕ) (hn : 0 < n) :
    (Finset.sum (Finset.range (n + 1)) fun k => (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3) =
    n * a_divfree n := by
  rw [a_divfree, Finset.mul_sum]
  congr 1
  ext k
  have h_id := term_identity n k hn
  calc
    (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    _ = ((n + 2 * k) * Nat.choose (n + k - 1) (n - 1)) * (Nat.choose (n + k - 1) (n - 1)) ^ 2 := by ring
    _ = (n * (Nat.choose (n + k - 1) (n - 1) + 2 * Nat.choose (n + k - 1) n)) * (Nat.choose (n + k - 1) (n - 1)) ^ 2 := by rw [h_id]
    _ = n * ((Nat.choose (n + k - 1) (n - 1)) ^ 2 * (Nat.choose (n + k - 1) (n - 1) + 2 * Nat.choose (n + k - 1) n)) := by ring

lemma a_eq_a_divfree (n : ℕ) (hn : 0 < n) : a n = a_divfree n := by
  unfold a
  split_ifs with h_zero
  · omega
  · have h_S := S_eq_n_mul_divfree n hn
    rw [h_S]
    rw [Nat.mul_div_cancel_left]
    omega


/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have h1 : a (n * p ^ r) = a_divfree (n * p ^ r) := by
    apply a_eq_a_divfree
    have h_pow_pos : p ^ r > 0 := Nat.pow_pos hp.pos
    exact Nat.mul_pos hn h_pow_pos
  have h2 : a (n * p ^ (r - 1)) = a_divfree (n * p ^ (r - 1)) := by
    apply a_eq_a_divfree
    have h_pow_pos : p ^ (r - 1) > 0 := Nat.pow_pos hp.pos
    exact Nat.mul_pos hn h_pow_pos
  rw [h1, h2]
  sorry


