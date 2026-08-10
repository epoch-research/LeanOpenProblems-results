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

namespace oeis_383327_conjecture_0_aux

/-- The same auxiliary sequence as the local one in `a`. -/
def A049802_val (m : ℕ) : ℕ :=
  let r := Nat.log 2 m
  (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))

lemma A049802_val_147 : A049802_val 147 = 67 := by norm_num [A049802_val]

lemma log_pow_add_one_67 : Nat.log 2 (2 ^ 67 + 1) = 67 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact Nat.le_add_right _ _
  · norm_num [pow_succ]

lemma A049802_val_pow_add_one_67 : A049802_val (2 ^ 67 + 1) = 67 := by
  unfold A049802_val
  rw [log_pow_add_one_67]
  trans (Finset.range 67).sum (fun _ : ℕ => 1)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hpow_dvd : 2 ^ (i + 1) ∣ 2 ^ 67 := by
      exact pow_dvd_pow 2 (Nat.succ_le_of_lt hi)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpow_dvd, zero_add]
    have hone : 1 < 2 ^ (i + 1) := by
      exact Nat.one_lt_pow (by omega : i + 1 ≠ 0) (by norm_num : 1 < 2)
    rw [Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hone]
  · norm_num

lemma two_le_a_67 : 2 ≤ a 67 := by
  let T : Finset ℕ := {147, 2 ^ 67 + 1}
  have h147mem : 147 ∈ Finset.filter (fun m => A049802_val m = 67) (Finset.range (2 ^ (67 + 1))) := by
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      norm_num
    · exact A049802_val_147
  have hbigmem : 2 ^ 67 + 1 ∈ Finset.filter (fun m => A049802_val m = 67) (Finset.range (2 ^ (67 + 1))) := by
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      norm_num
    · exact A049802_val_pow_add_one_67
  have hsub : T ⊆ Finset.filter (fun m => A049802_val m = 67) (Finset.range (2 ^ (67 + 1))) := by
    intro m hm
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact h147mem
    · exact hbigmem
  have hcardT : T.card = 2 := by
    simp [T]
  have hle : 2 ≤ (Finset.filter (fun m => A049802_val m = 67) (Finset.range (2 ^ (67 + 1)))).card := by
    simpa [hcardT] using Finset.card_le_card hsub
  unfold a
  rw [if_neg (by norm_num : ¬ 67 = 0)]
  change 2 ≤ (Finset.filter (fun m => A049802_val m = 67) (Finset.range (2 ^ (67 + 1)))).card
  exact hle

lemma a_67_ne_one : a 67 ≠ 1 := by
  have h := two_le_a_67
  omega

end oeis_383327_conjecture_0_aux

/--
Conjecture based on OEIS A383327 comment:
From a combinatorial perspective, the tuple of summands (x_1, ..., x_t) mentioned above can be seen as a set of t counters, where the j-th counter cycles through 0 to 2^j-1. The natural question 'which m in A049802 appear k times?' becomes a question about how this cycling condition restricts the number of tuples which sum to m. For example, for n <= 100, when n = 1, 3, 5, 9, 15, 23, 35, 63, 65, and 67 there is only one m such that the tuple of summands sums to n (a trivial tuple consisting of n 1s, trivial because there is such a tuple for every n >= 1, i.e. for every m = 2^n+1).
This is a precise statement about the set of values $n$ for which $a(n) = 1$ among $n \le 100$.
-/
theorem oeis_383327_conjecture_0.disproof :
  ¬ (let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
  ∀ n : ℕ, n ∈ S → a n = 1) := by
  intro h
  have h67 : a 67 = 1 := h 67 (by norm_num)
  exact oeis_383327_conjecture_0_aux.a_67_ne_one h67
