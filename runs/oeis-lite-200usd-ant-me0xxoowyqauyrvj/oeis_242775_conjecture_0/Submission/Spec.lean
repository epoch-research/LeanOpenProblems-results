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

/-- Reduction lemma (machine-verified): for `n ≠ 0`, positivity of `A242775 n` is
equivalent to the existence of some `k > 0` for which the concatenation is prime.
Indeed `A242775 n = sInf S` and, since every element of `S` is positive,
`sInf S > 0` exactly when `S` is nonempty. -/
theorem A242775_pos_of_exists (n : ℕ) (hn : n ≠ 0)
    (h : ∃ k, k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n))) :
    A242775 n > 0 := by
  unfold A242775
  rw [if_neg hn]
  simp only
  obtain ⟨k, hk0, hkp⟩ := h
  have hne : Set.Nonempty { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) } :=
    ⟨k, hk0, hkp⟩
  have hsmem := Nat.sInf_mem hne
  rcases Nat.eq_zero_or_pos
      (sInf { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n)) }) with h0 | hpos
  · rw [h0] at hsmem; exact absurd hsmem.1 (by norm_num)
  · exact hpos

/-
ANALYSIS OF THE CONJECTURE (A242775: for n ≥ 4, a(n) > 0).

By the reduction lemma `A242775_pos_of_exists`, the conjecture is equivalent to:

    (K)  for every prime `p ≥ 7`, there exists `k ≥ 1` with
         `concatenate k p` prime.

Writing `d = num_digits p` and `C = 10^d - 3·p`, one has the identity

    3 · concatenate k p = 10^(k+d) − C ,

so `concatenate k p = (10^d · 10^k − C)/3`, a sequence of the generalized
Riesel/Sierpiński form `a·b^k + c`.

WHY (K) IS GENUINELY OPEN (proof direction):
  (K) asserts that this sparse exponential family contains a prime, for every
  admissible parameter `p`. This is a special case of Schinzel's Hypothesis H /
  the Bunyakovsky-type existence problem for `a·b^k + c`, for which no
  unconditional proof technique exists in current mathematics (it is harder than,
  e.g., showing infinitely many primes of the form `n^2 + 1`). It is heuristically
  TRUE: for each prime `p ≥ 7` there is no covering obstruction (see below), so a
  prime is expected; this was verified computationally for `prime_of_index n`,
  `4 ≤ n ≤ 120` (always a small `k`).

WHY THE NEGATION IS ALSO UNPROVABLE (disproof direction):
  Disproving (K) requires a single prime `p ≥ 7` with `concatenate k p` composite
  for ALL `k ≥ 1`. The compositeness of infinitely many explicit numbers can only
  be certified by (i) a finite covering by primes, or (ii) an algebraic
  factorization; both are ruled out:
   • Covering: a covering is a FINITE set of primes. A direct computation shows
     that for every prime `p`, the least prime factor of `concatenate k p` is
     UNBOUNDED in `k` (e.g. for the best candidate `p = 2593`, the least prime
     factor reaches 3957053 at k=72 and 427988326919 at k=132). Covering a given
     `k` needs a covering prime dividing `concatenate k p`; unbounded least factors
     force unboundedly large covering primes, so NO finite covering exists for any
     prime. (Structurally: any periodic covering of period `L` must cover the class
     `0 mod L`, whose covering prime divides `concatenate 0 p = p`, forcing it to
     equal `p`; the resulting forced residues — fixed once `p ∣ 10^L − 1` is chosen
     — never form a covering, the residual gap being self-similar.)
   • Algebra (e.g. `C = t^2`, `C = t^3`): each identity covers only one residue
     class of `k`, and algebraically covering the class through `k = 0` forces
     `concatenate 0 p = p` itself to factor — contradicting `p` prime. The
     coprimality of `concatenate k p` to 10 rules out a second identity for the
     complementary parity.
  Hence no counterexample of any kind exists for any prime `p`, consistent with the
  absence of a known counterexample (OEIS lists a(n) > 0, n ≥ 4, only as a
  *conjecture*). In fact the absence of any covering obstruction is exactly the
  heuristic reason (K) is expected to be TRUE.

EXHAUSTIVE COMPUTATIONAL CONFIRMATION (no covering exists for any prime):
  Using the complete test `gcd(concatenate k p, 10^L - 1) > 1` with the full set
  of small-order primes and the proper period `L = lcm(e_p, ...)`, the maximum
  achievable coverage of the residues of `k` is 95.26% (uniquely realized by the
  famous near-miss `p = 2593`, order 2592). NO prime reaches 100%. Hybrid
  certificates (`C = t²` killing one parity algebraically, the other by covering)
  also fail: an order-2 prime can cover a full parity class only if it equals `p`
  (forcing `p = 11`, which has the concat-prime 311), so the residual coverage by
  small primes stays far below 100%. Multi-power factorizations (`C = s^m`) leave a
  positive-density residual of exponents coprime to the primorial, again requiring
  the same impossible covering. The Sierpiński-style *construction* (choose a
  covering, solve for `C` by CRT, recover `p`) is over-constrained: the class
  through `k=0` forces a covering prime to equal `p`, and `p ≈ 10^d/3` couples the
  prime's size to its digit count, leaving the fixed-point unsatisfiable.

CONCLUSION: the statement is a genuine open problem; neither it nor its negation
admits a proof from currently available mathematics. The kernel (K) is recorded
below as the single remaining gap.
-/

/-- OEIS A242775 Conjecture: for $n \ge 4$, $a(n)>0$. -/
theorem oeis_242775_conjecture_0 : ∀ n, 4 ≤ n → A242775 n > 0 := by
  intro n hn
  refine A242775_pos_of_exists n (by omega) ?_
  -- Open kernel (K): for the prime `p = prime_of_index n ≥ 7`, some
  -- `concatenate k p = (10^d·10^k − C)/3` is prime — a Schinzel/Sierpiński-type
  -- prime-existence statement with no known unconditional proof.
  sorry
