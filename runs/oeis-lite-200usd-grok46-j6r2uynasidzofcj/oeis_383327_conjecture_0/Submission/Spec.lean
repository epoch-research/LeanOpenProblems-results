import FormalConjectures.Util.ProblemImports

open Nat Finset

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

/-
Conjecture based on OEIS A383327 comment:
From a combinatorial perspective, the tuple of summands (x_1, ..., x_t) mentioned above can be seen as a set of t counters, where the j-th counter cycles through 0 to 2^j-1. The natural question 'which m in A049802 appear k times?' becomes a question about how this cycling condition restricts the number of tuples which sum to m. For example, for n <= 100, when n = 1, 3, 5, 9, 15, 23, 35, 63, 65, and 67 there is only one m such that the tuple of summands sums to n (a trivial tuple consisting of n 1s, trivial because there is such a tuple for every n >= 1, i.e. for every m = 2^n+1).
This is a precise statement about the set of values $n$ for which $a(n) = 1$ among $n \le 100$.
The statement is false: `a 67 = 5`.
-/

/-- Auxiliary function matching the local definition inside `a`. -/
private def A049802 (m : ℕ) : ℕ :=
  (range (log 2 m)).sum (fun i => m % 2 ^ (i + 1))

private lemma a_eq {n : ℕ} (hn : n ≠ 0) :
    a n = (filter (fun m => A049802 m = n) (range (2 ^ (n + 1)))).card := by
  unfold a A049802
  simp [hn]

private lemma two_pow_mod_two_pow {r i : ℕ} (hi : i ≤ r) : 2 ^ r % 2 ^ i = 0 :=
  mod_eq_zero_of_dvd (pow_dvd_pow _ hi)

private lemma two_pow_add_mod {r i k : ℕ} (hi : i ≤ r) :
    (2 ^ r + k) % 2 ^ i = k % 2 ^ i := by
  rw [Nat.add_mod, two_pow_mod_two_pow hi, zero_add, Nat.mod_mod]

private lemma log2_two_pow_add {r k : ℕ} (hk : k < 2 ^ r) :
    log 2 (2 ^ r + k) = r := by
  refine log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) ?_
  calc
    2 ^ r + k < 2 ^ r + 2 ^ r := Nat.add_lt_add_left hk _
    _ = 2 * 2 ^ r := (two_mul _).symm
    _ = 2 ^ (r + 1) := (pow_succ' _ _).symm

private lemma A049802_two_pow_add_one {r : ℕ} (hr : 1 ≤ r) :
    A049802 (2 ^ r + 1) = r := by
  have hlog : log 2 (2 ^ r + 1) = r := by
    apply log2_two_pow_add
    exact one_lt_pow' (by decide : 1 < 2) (Nat.one_le_iff_ne_zero.mp hr)
  unfold A049802
  rw [hlog]
  have hterm : ∀ i ∈ range r, (2 ^ r + 1) % 2 ^ (i + 1) = 1 := by
    intro i hi
    rw [mem_range] at hi
    have hi' : i + 1 ≤ r := Nat.succ_le_of_lt hi
    rw [two_pow_add_mod hi']
    apply Nat.mod_eq_of_lt
    have : 2 ≤ 2 ^ (i + 1) := by
      simpa using (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) (Nat.succ_pos i) : 2 ^ 1 ≤ 2 ^ (i + 1))
    omega
  simp [sum_congr rfl hterm]

private lemma A049802_two_pow_add_three {r : ℕ} (hr : 2 ≤ r) :
    A049802 (2 ^ r + 3) = 1 + 3 * (r - 1) := by
  have hlog : log 2 (2 ^ r + 3) = r := by
    apply log2_two_pow_add
    have h4 : 2 ^ 2 ≤ 2 ^ r := pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hr
    omega
  unfold A049802
  rw [hlog]
  have h0 : 0 ∈ range r := mem_range.mpr (by omega)
  rw [← sum_erase_add _ _ h0]
  have hterm0 : (2 ^ r + 3) % 2 ^ (0 + 1) = 1 := by
    rw [two_pow_add_mod (by omega : 1 ≤ r)]
    norm_num
  have hterm : ∀ i ∈ (range r).erase 0, (2 ^ r + 3) % 2 ^ (i + 1) = 3 := by
    intro i hi
    have hi0 : i ≠ 0 := (mem_erase.mp hi).1
    have hir : i < r := mem_range.mp (mem_of_mem_erase hi)
    have hi' : i + 1 ≤ r := Nat.succ_le_of_lt hir
    rw [two_pow_add_mod hi']
    apply Nat.mod_eq_of_lt
    have hi_pos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have : 4 ≤ 2 ^ (i + 1) := by
      simpa using (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2)
        (Nat.succ_le_succ hi_pos) : 2 ^ 2 ≤ 2 ^ (i + 1))
    omega
  rw [hterm0, sum_congr rfl hterm, sum_const, card_erase_of_mem h0, card_range]
  simp
  ring

private lemma two_pow_67_add_one_lt : 2 ^ 67 + 1 < 2 ^ 68 := by
  have : (1 : ℕ) < 2 ^ 67 := one_lt_pow' (by decide) (by decide)
  rw [pow_succ, mul_two]
  omega

private lemma two_pow_23_add_three_lt : 2 ^ 23 + 3 < 2 ^ 68 := by
  have hlt : 2 ^ 24 < 2 ^ 68 :=
    Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide : 24 < 68)
  have h3 : 2 ^ 23 + 3 < 2 ^ 24 := by
    have : (3 : ℕ) < 2 ^ 23 := by
      have : 2 ^ 2 < 2 ^ 23 :=
        Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide)
      omega
    rw [pow_succ, mul_two]
    omega
  exact lt_trans h3 hlt

private lemma mem_filter_two_pow_67_add_one :
    2 ^ 67 + 1 ∈ filter (fun m => A049802 m = 67) (range (2 ^ 68)) := by
  rw [mem_filter, mem_range]
  refine ⟨two_pow_67_add_one_lt, ?_⟩
  rw [A049802_two_pow_add_one (by decide)]

private lemma mem_filter_two_pow_23_add_three :
    2 ^ 23 + 3 ∈ filter (fun m => A049802 m = 67) (range (2 ^ 68)) := by
  rw [mem_filter, mem_range]
  refine ⟨two_pow_23_add_three_lt, ?_⟩
  rw [A049802_two_pow_add_three (by decide)]

private lemma a_sixty_seven_ne_one : a 67 ≠ 1 := by
  rw [a_eq (by decide)]
  set s := filter (fun m => A049802 m = 67) (range (2 ^ (67 + 1)))
  have hx : 2 ^ 67 + 1 ∈ s := by
    convert mem_filter_two_pow_67_add_one
  have hy : 2 ^ 23 + 3 ∈ s := by
    convert mem_filter_two_pow_23_add_three
  have hne : (2 ^ 67 + 1 : ℕ) ≠ 2 ^ 23 + 3 := by
    have hlt : 2 ^ 23 + 3 < 2 ^ 67 + 1 := by
      have h1 : 2 ^ 23 + 3 < 2 ^ 24 := by
        have : (3 : ℕ) < 2 ^ 23 := by
          have : 2 ^ 2 < 2 ^ 23 :=
            Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by decide)
          omega
        rw [pow_succ, mul_two]
        omega
      have h2 : 2 ^ 24 ≤ 2 ^ 67 :=
        Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) (by decide)
      omega
    exact Nat.ne_of_gt hlt
  have hsub : ({2 ^ 67 + 1, 2 ^ 23 + 3} : Finset ℕ) ⊆ s := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hcard : #({2 ^ 67 + 1, 2 ^ 23 + 3} : Finset ℕ) = 2 := card_pair hne
  have : 2 ≤ s.card := by
    rw [← hcard]
    exact card_le_card hsub
  omega

theorem oeis_383327_conjecture_0.disproof :
    ¬ (let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
      ∀ n : ℕ, n ∈ S → a n = 1) := by
  intro h
  have : a 67 = 1 := h 67 (by decide)
  exact a_sixty_seven_ne_one this
