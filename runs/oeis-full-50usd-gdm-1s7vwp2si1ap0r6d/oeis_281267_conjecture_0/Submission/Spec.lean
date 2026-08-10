import FormalConjectures.Util.ProblemImports

open Polynomial Finset Nat

/--
A281267: Main diagonal of A276554.
The sequence $a(n)$ is the coefficient of $x^n$ in the polynomial
$$\prod_{k=1}^n (1 - x^k)^{n k}$$
-/
noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Polynomial ℤ :=
    (Ico 1 (n + 1)).prod fun k : ℕ =>
      (1 - X ^ k) ^ (n * k)
  P_n.coeff n

lemma pow_odd (p m : ℕ) (hp_odd : p % 2 = 1) : p ^ m % 2 = 1 := by
  induction m with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ, Nat.mul_mod, ih, hp_odd]

/--
Conjecture: the stronger supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for all primes p >= 3 and all positive integers n and k.
-/
theorem oeis_281267_conjecture_0 (p : ℕ) (n k : ℕ) :
  Nat.Prime p → 3 ≤ p → 1 ≤ n → 1 ≤ k →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p ^ (2 * k) : ℕ) : ℤ)] := by
  intros hp h3p hn hk
  have hp_odd : p % 2 = 1 := by
    cases hp.eq_two_or_odd with
    | inl h2 => omega
    | inr hodd => exact hodd
  have h_same_parity : (n * p ^ k) % 2 = (n * p ^ (k - 1)) % 2 := by
    have h1 : p ^ k % 2 = 1 := pow_odd p k hp_odd
    have h2 : p ^ (k - 1) % 2 = 1 := pow_odd p (k - 1) hp_odd
    rw [Nat.mul_mod n (p^k) 2, h1]
    rw [Nat.mul_mod n (p^(k-1)) 2, h2]
  unfold a
  rw [h_same_parity]
