import FormalConjectures.Util.ProblemImports

open Nat

/--
A376930: $a(0)=0, a(1)=1$; for $n>1$, $a(n) = a(n-1)+a(n-2)$, except where $a(n-1)$ is a prime greater than 2, in which case $a(n) = a(n-1)-a(n-2)$.
-/
noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

/-- Unfolding of the recurrence for `a (n+2)`. -/
lemma a_succ_succ (n : ℕ) :
    a (n + 2) = if Nat.Prime (a (n+1)) ∧ a (n+1) > 2 then a (n+1) - a n else a (n+1) + a n := by
  rw [a]

/-- When the predecessor is not a prime `> 2`, the recurrence adds. -/
lemma a_add (n : ℕ) (h : ¬ (Nat.Prime (a (n+1)) ∧ a (n+1) > 2)) :
    a (n + 2) = a (n+1) + a n := by rw [a_succ_succ]; simp [h]

/-- When the predecessor is a prime `> 2`, the recurrence subtracts. -/
lemma a_sub (n : ℕ) (h : Nat.Prime (a (n+1)) ∧ a (n+1) > 2) :
    a (n + 2) = a (n+1) - a n := by rw [a_succ_succ]; simp [h]

/-- An even number is never a prime `> 2`. -/
lemma even_not_prime_gt2 {m : ℕ} (h : m % 2 = 0) : ¬ (Nat.Prime m ∧ m > 2) := by
  rintro ⟨hp, hg⟩
  have hd : (2 : ℕ) ∣ m := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hd) with h1 | h2
  · norm_num at h1
  · omega

/-- The parities of the sequence are periodic with period 3: `(0,1,1)`.
This is proved by induction using the recurrence and the fact that a term computed
right after an even (hence non-prime-`>2`) term is obtained by addition. -/
lemma parity (n : ℕ) :
    a (3*n) % 2 = 0 ∧ a (3*n+1) % 2 = 1 ∧ a (3*n+2) % 2 = 1 := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [a]
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have b2 : a (3*k+1+1) = a (3*k+2) := rfl
    have b3 : a (3*k+2+1) = a (3*k+3) := rfl
    have key3 : a (3*k+3) % 2 = 0 := by
      have := a_succ_succ (3*k+1)
      rw [b2, show 3*k+1+2 = 3*k+3 by ring] at this
      rw [this]
      by_cases hc : Nat.Prime (a (3*k+2)) ∧ a (3*k+2) > 2 <;> simp [hc] <;> omega
    have np3 : ¬ (Nat.Prime (a (3*k+3)) ∧ a (3*k+3) > 2) := even_not_prime_gt2 key3
    have eq4 : a (3*k+4) = a (3*k+3) + a (3*k+2) := by
      have := a_add (3*k+2) (by rw [b3]; exact np3)
      rw [b3, show 3*k+2+2 = 3*k+4 by ring] at this; exact this
    have key4 : a (3*k+4) % 2 = 1 := by rw [eq4]; omega
    have b4 : a (3*k+3+1) = a (3*k+4) := rfl
    have key5 : a (3*k+5) % 2 = 1 := by
      have := a_succ_succ (3*k+3)
      rw [b4, show 3*k+3+2 = 3*k+5 by ring] at this
      rw [this]
      by_cases hc : Nat.Prime (a (3*k+4)) ∧ a (3*k+4) > 2 <;> simp [hc] <;> omega
    refine ⟨?_, ?_, ?_⟩
    · rw [show 3*(k+1) = 3*k+3 by ring]; exact key3
    · rw [show 3*(k+1)+1 = 3*k+4 by ring]; exact key4
    · rw [show 3*(k+1)+2 = 3*k+5 by ring]; exact key5

/-- Parity as a function of the residue mod 3. -/
lemma a_par (n : ℕ) : a n % 2 = if n % 3 = 0 then 0 else 1 := by
  obtain ⟨h0, h1, h2⟩ := parity (n / 3)
  have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : (n % 3)
  · rw [show n = 3 * (n/3) by omega]; simpa using h0
  · rw [show n = 3 * (n/3) + 1 by omega]; simpa using h1
  · rw [show n = 3 * (n/3) + 2 by omega]; simpa using h2

/-- A prime `> 2` term sits at an index which is not `≡ 0 [MOD 3]` (it is odd). -/
lemma a_prime_gt2_mod3 (n : ℕ) (h : Nat.Prime (a n) ∧ a n > 2) : n % 3 ≠ 0 := by
  intro hc
  have := a_par n
  rw [if_pos hc] at this
  exact even_not_prime_gt2 this h

/-- The core statement: a type-1 term `a (3*j+1)` that is a prime `> 2` is never
immediately followed by a type-2 term `a (3*j+2)` that is a prime `> 2`.

Equivalently (since one shows `a (3*j+2) = a (3*j-1)` in this situation), no two
consecutive terms of the sequence are simultaneously primes `> 2`.  This is exactly
the open statement recorded on OEIS A376930 ("It is not known if the sequence
contains any negative terms"): a counterexample here is precisely a place where the
integer-valued version of the sequence would become negative. -/
lemma core (j : ℕ) (h1 : Nat.Prime (a (3*j+1)) ∧ a (3*j+1) > 2) :
    ¬ (Nat.Prime (a (3*j+2)) ∧ a (3*j+2) > 2) := by
  sorry

/--
oeis_376930_conjecture_0: It is not known if the sequence contains any negative terms (which may happen if two primes are adjacent or separated by one other term).

Formalization: Since the sequence is defined in $\mathbb{N}$, all terms are non-negative by definition. The conjecture's mathematical content is that whenever the subtraction rule $a(n+2) = a(n+1) - a(n)$ is applied, the result in $\mathbb{Z}$ is non-negative. In the context of $\mathbb{N}$ arithmetic, this is equivalent to asserting that $a(n+1) \ge a(n)$.

The whole conjecture reduces to `core`.  Every case except the one governed by
`core` is discharged using the period-3 parity structure.
-/
theorem oeis_376930_conjecture_0 :
  ∀ n : ℕ, (Nat.Prime (a (n + 1)) ∧ a (n + 1) > 2) → a (n + 1) ≥ a n := by
  intro n hyp
  obtain ⟨hp, hg⟩ := hyp
  match n with
  | 0 =>
    exfalso
    have : a (0+1) = 1 := rfl
    rw [this] at hp; exact Nat.not_prime_one hp
  | m + 1 =>
    by_cases hc : Nat.Prime (a (m+1)) ∧ a (m+1) > 2
    · exfalso
      have hm1 : (m+1) % 3 ≠ 0 := a_prime_gt2_mod3 (m+1) hc
      have hm2 : (m+2) % 3 ≠ 0 := a_prime_gt2_mod3 (m+2) ⟨hp, hg⟩
      have hcase : (m+1) % 3 = 1 := by omega
      have e1 : a (m+1) = a (3*(m/3)+1) := by congr 1; omega
      have e2 : a (m+1+1) = a (3*(m/3)+2) := by congr 1; omega
      rw [e1] at hc
      rw [e2] at hp hg
      exact core (m/3) hc ⟨hp, hg⟩
    · rw [a_add m hc]; omega
