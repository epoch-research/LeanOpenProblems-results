import FormalConjectures.Util.ProblemImports

open Nat

/--
A383327: $a(n)$ is the number of occurrences of $n$ in A049802.
A049802(m) is the sum of $(m \bmod 2^k)$ for $k=1, \dots, \lfloor \log_2 m \rfloor$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Define the auxiliary sequence A049802 locally.
    let A049802_val (m : ℕ) : ℕ :=
      let r := Nat.log 2 m
      -- Sum over k=1 to r. We use index i in {0, ..., r-1} such that k = i+1.
      (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))

    -- Since $A049802(m) = n$ implies $m < 2^{n+1}$, we use $B = 2^{n+1}$ as a sufficient search bound.
    let B : ℕ := 2 ^ (n + 1)
    Finset.card (Finset.filter (fun m => A049802_val m = n) (Finset.range B))

/--
Conjecture based on OEIS A383327 comment:
From a combinatorial perspective, the tuple of summands (x_1, ..., x_t) mentioned above can be seen as a set of t counters, where the j-th counter cycles through 0 to 2^j-1. The natural question 'which m in A049802 appear k times?' becomes a question about how this cycling condition restricts the number of tuples which sum to m. For example, for n <= 100, when n = 1, 3, 5, 9, 15, 23, 35, 63, 65, and 67 there is only one m such that the tuple of summands sums to n (a trivial tuple consisting of n 1s, trivial because there is such a tuple for every n >= 1, i.e. for every m = 2^n+1).
This is a precise statement about the set of values $n$ for which $a(n) = 1$ among $n \le 100$.
-/
theorem oeis_383327_conjecture_0.disproof :
  ¬ (let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
    ∀ n : ℕ, n ∈ S → a n = 1) :=
by
  intro h
  have h67 : a 67 = 1 := by
    exact h 67 (by norm_num)
  have hcard : 2 ≤ a 67 := by
    unfold a
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
    let U : Finset ℕ := ({147, 2055} : Finset ℕ)
    calc
      2 = U.card := by decide
      _ ≤ (Finset.filter
            (fun m =>
              (let r := Nat.log 2 m
               (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))) = 67)
            (Finset.range (2 ^ (67 + 1)))).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_range]
          have hx' : x = 147 ∨ x = 2055 := by
            simpa [U] using hx
          rcases hx' with rfl | rfl
          · constructor <;> decide
          · constructor <;> decide
  omega
