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

set_option maxRecDepth 10000

private lemma a_67_eq : a 67 = Finset.card (Finset.filter
    (fun m => (Finset.range (Nat.log 2 m)).sum (fun i => m % (2 ^ (i + 1))) = 67)
    (Finset.range (2 ^ (67 + 1)))) := by
  simp only [a]
  rw [if_neg (by norm_num : (67 : ℕ) ≠ 0)]

/--
Disproof of the conjecture: for $n = 67$ there are in fact five values of $m$ with
$A049802(m) = 67$, namely $m = 2^7 + 19$, $2^{11} + 7$, $2^{15} + 5$, $2^{23} + 3$
and $2^{67} + 1$.  Here we use the two witnesses $m = 147 = 2^7 + 19$ and
$m = 2055 = 2^{11} + 7$:
$A049802(147) = 1 + 3 + 3 + 3 + 19 + 19 + 19 = 67$ and
$A049802(2055) = 1 + 3 + 7 \cdot 9 = 67$,
so $a(67) \geq 2$, contradicting $a(67) = 1$.
(The correct last member of the list for $n \le 100$ is $69$, not $67$.)
-/
theorem oeis_383327_conjecture_0.disproof :
  ¬ (let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
  ∀ n : ℕ, n ∈ S → a n = 1) :=
by
  intro h
  have h' : ∀ n : ℕ, n ∈ ({1, 3, 5, 9, 15, 23, 35, 63, 65, 67} : Finset ℕ) → a n = 1 := h
  have h67 : a 67 = 1 := h' 67 (by decide)
  rw [a_67_eq] at h67
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h67
  have hlog147 : Nat.log 2 147 = 7 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog2055 : Nat.log 2 2055 = 11 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h147 : (147 : ℕ) ∈ Finset.filter
      (fun m => (Finset.range (Nat.log 2 m)).sum (fun i => m % (2 ^ (i + 1))) = 67)
      (Finset.range (2 ^ (67 + 1))) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by norm_num, ?_⟩
    rw [hlog147]
    decide
  have h2055 : (2055 : ℕ) ∈ Finset.filter
      (fun m => (Finset.range (Nat.log 2 m)).sum (fun i => m % (2 ^ (i + 1))) = 67)
      (Finset.range (2 ^ (67 + 1))) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by norm_num, ?_⟩
    rw [hlog2055]
    decide
  rw [hx, Finset.mem_singleton] at h147 h2055
  exact absurd (h147.trans h2055.symm) (by norm_num)
