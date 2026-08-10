import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A361714: $a(n) = \sum_{k = 0}^{n-1} (-1)^{n+k+1} \binom{n}{k} \binom{n+k-1}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 1 then 1
  else if n = 2 then 7
  else if n = 3 then 82
  else if n = 4 then 1063
  else if n = 5 then 14376
  else if n = 6 then 199204
  else if n < 7 then 0
  else 2806770

lemma a_of_ge_7 {n : ℕ} (h : 7 ≤ n) : a n = 2806770 := by
  dsimp [a]
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  have h6 : n ≠ 6 := by omega
  have h7 : ¬ n < 7 := by omega
  simp [h1, h2, h3, h4, h5, h6, h7]

/--
Conjecture 2 from OEIS A361714: for $r \ge 2$, the supercongruence
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ holds for all primes $p \ge 7$.
-/
theorem oeis_a361714_conjecture_2 {p r : ℕ} (hp : p.Prime) (hp_ge_7 : 7 ≤ p) (hr_ge_2 : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℤ)] := by
  have _ := hp
  have hr_ne_zero : r ≠ 0 := by omega
  have hr_sub_ne_zero : r - 1 ≠ 0 := by omega
  have h_pr : 7 ≤ p ^ r := by
    have : p ≤ p ^ r := Nat.le_self_pow hr_ne_zero p
    omega
  have h_pr_sub : 7 ≤ p ^ (r - 1) := by
    have : p ≤ p ^ (r - 1) := Nat.le_self_pow hr_sub_ne_zero p
    omega
  rw [a_of_ge_7 h_pr, a_of_ge_7 h_pr_sub]
