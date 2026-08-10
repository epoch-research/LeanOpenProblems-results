import FormalConjectures.Util.ProblemImports

open Nat Set

/-- The number $b_k$, consisting of $k$ threes. $b_k = (10^k - 1)/3$. -/
def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3

/-- The number of decimal digits of $p$. -/
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length

/-- Concatenation of $b_k$ and $p$. -/
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p

/-- The $n$-th prime (1-indexed). -/
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/--
A242775: Let $b_k=3\dots3$ consist of $k\ge 1$ 3's. Then $a(n)$ is the smallest $k$ such that the concatenation $b_k$ and $\operatorname{prime}(n)$ is prime, or $a(n)=0$ if there is no such prime.
-/
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n

    -- The set S of all k >= 1 such that the concatenated number is prime.
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }

    -- Nat.sInf S is the minimum element of S. If S is empty, Nat.sInf S = 0 is the convention for ℕ.
    sInf S

/-- OEIS A242775 Conjecture: for $n \ge 4$, $a(n)>0$.

Reduction: since the set `S = {k > 0 | Nat.Prime (concatenate k (prime_of_index n))}`
consists only of positive naturals, `sInf S > 0` holds exactly when `S` is nonempty.
Hence the conjecture is equivalent to the core existence statement
`∀ n ≥ 4, ∃ k > 0, Nat.Prime (concatenate k (prime_of_index n))`,
i.e. every prime (from the 4th on) becomes prime after prepending some run of 3's. -/
theorem oeis_242775_conjecture_0 : ∀ n, 4 ≤ n → A242775 n > 0 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  -- The essential content of the conjecture: existence of a prime concatenation.
  have hcore : ∃ k, k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) := by
    sorry
  simp only [A242775, hn0, if_false]
  obtain ⟨k, hk, hkp⟩ := hcore
  set S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) } with hS
  have hne : S.Nonempty := ⟨k, hk, hkp⟩
  exact (Nat.sInf_mem hne).1
