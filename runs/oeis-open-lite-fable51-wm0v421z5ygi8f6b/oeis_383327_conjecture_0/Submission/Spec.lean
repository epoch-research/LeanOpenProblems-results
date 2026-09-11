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
theorem oeis_383327_conjecture_0 :
  let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
  ∀ n : ℕ, n ∈ S → a n = 1 :=
by sorry

theorem a_67_ne_one : a 67 ≠ 1 := by
  have h1 : (Finset.range (Nat.log 2 147)).sum (fun i => 147 % (2 ^ (i + 1))) = 67 := by
    have : Nat.log 2 147 = 7 := by
      rw [Nat.log_eq_iff] <;> norm_num
    rw [this]; decide
  have h2 : (Finset.range (Nat.log 2 (2^67+1))).sum (fun i => (2^67+1) % (2 ^ (i + 1))) = 67 := by
    have hl : Nat.log 2 (2^67+1) = 67 := by
      rw [Nat.log_eq_iff] <;> norm_num
    rw [hl]
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      have h2i : 2 ^ (i+1) ∣ 2 ^ 67 := Nat.pow_dvd_pow 2 (by omega)
      have hz : 2 ^ 67 % 2 ^ (i+1) = 0 := Nat.mod_eq_zero_of_dvd h2i
      rw [Nat.add_mod, hz, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
      exact Nat.one_lt_two_pow (by omega)
  simp only [a, if_neg (show (67:ℕ) ≠ 0 by norm_num)]
  intro hc
  have hsub : ({147, 2^67+1} : Finset ℕ) ⊆
      Finset.filter (fun m => (Finset.range (Nat.log 2 m)).sum (fun i => m % (2 ^ (i + 1))) = 67)
        (Finset.range (2 ^ (67 + 1))) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl
    · exact ⟨by norm_num, h1⟩
    · exact ⟨by norm_num, h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair (by norm_num), hc] at hcard
  omega

theorem oeis_383327_conjecture_0.disproof : ¬ (type_of% @oeis_383327_conjecture_0) := by
  intro h
  exact a_67_ne_one (h 67 (by decide))

