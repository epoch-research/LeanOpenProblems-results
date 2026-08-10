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
lemma card_ne_one_of_mem_of_mem_of_ne {α : Type*} [DecidableEq α] {s : Finset α} {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : s.card ≠ 1 := by
  intro h
  rw [Finset.card_eq_one] at h
  rcases h with ⟨a, rfl⟩
  rw [Finset.mem_singleton] at hx hy
  subst hx
  subst hy
  exact hne rfl

lemma a_67_ne_one : a 67 ≠ 1 := by
  unfold a
  split
  · rename_i h
    contradiction
  · apply card_ne_one_of_mem_of_mem_of_ne (x := 147) (y := 2055)
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        decide
      · decide
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        decide
      · decide
    · decide

theorem oeis_383327_conjecture_0.disproof :
  ¬ (let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
     ∀ n : ℕ, n ∈ S → a n = 1) := by
  intro h
  have h_mem : 67 ∈ ({1, 3, 5, 9, 15, 23, 35, 63, 65, 67} : Finset ℕ) := by decide
  have h_eq : a 67 = 1 := h 67 h_mem
  exact a_67_ne_one h_eq
