import FormalConjectures.Util.ProblemImports

open Nat Finset List

/--
A237271: Number of parts in the symmetric representation of $\sigma(n)$.
a(n) is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is $1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$, which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

-- List of divisors of n, sorted ascendingly.
def sorted_divisors_list (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num_2_dense_sublists (n : ℕ) : ℕ :=
  let divs_list := sorted_divisors_list n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps


private lemma countP_congr_mem {α : Type*} (l : List α) {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : p a = q a := h a (by simp)
      have ht : ∀ x ∈ l, p x = q x := by
        intro x hx
        exact h x (by simp [hx])
      rw [List.countP_cons, List.countP_cons, ih ht, ha]

private lemma no_between_of_adjacent_pairwise {l : List ℕ} {x y z : ℕ}
    (hs : l.Pairwise (· ≤ ·)) (hn : l.Nodup)
    (hxy : (x, y) ∈ l.zip l.tail) (hz : z ∈ l) : ¬ (x < z ∧ z < y) := by
  induction l with
  | nil => simp at hxy
  | cons a l ih =>
      cases l with
      | nil => simp at hxy
      | cons b t =>
          change (x, y) ∈ (a, b) :: (b :: t).zip (b :: t).tail at hxy
          simp only [List.mem_cons] at hxy hz
          rcases hxy with hhead | htail
          · have hxab : x = a ∧ y = b := by simpa using hhead
            rcases hxab with ⟨rfl, rfl⟩
            intro hbetween
            rcases hbetween with ⟨haz, hzb⟩
            rcases hz with rfl | hz
            · omega
            · rcases hz with rfl | hzt
              · omega
              · have hs_tail : (y :: t).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
                have hbz : y ≤ z := (List.pairwise_cons.mp hs_tail).1 z hzt
                omega
          · intro hbetween
            rcases hbetween with ⟨hxz, hzy⟩
            rcases hz with rfl | hz_tail
            · have hx_mem_tail : x ∈ b :: t := (List.of_mem_zip htail).1
              have hzx : z ≤ x := (List.pairwise_cons.mp hs).1 x hx_mem_tail
              omega
            · have hs_tail : (b :: t).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
              have hn_tail : (b :: t).Nodup := List.Nodup.of_cons hn
              exact ih hs_tail hn_tail htail (by simpa [List.mem_cons] using hz_tail) ⟨hxz, hzy⟩

private lemma adjacent_divisor_condition_iff (n : ℕ) {x y : ℕ}
    (hxy : (x, y) ∈ (sorted_divisors_list n).zip (sorted_divisors_list n).tail) :
    (Odd y ∧ y ≥ 2 * x) ↔ y > 2 * x := by
  constructor
  · intro h
    rcases h with ⟨hyodd, hyge⟩
    have hne : y ≠ 2 * x := by
      intro hy
      subst y
      have : ¬ Odd (2 * x) := by
        rw [Nat.not_odd_iff_even]
        rw [even_iff_exists_two_mul]
        exact ⟨x, rfl⟩
      exact this hyodd
    omega
  · intro hygt
    have hy_mem : y ∈ sorted_divisors_list n := by
      exact List.mem_of_mem_tail (List.of_mem_zip hxy).2
    have hy_info : y ∣ n ∧ n ≠ 0 := by
      simpa [sorted_divisors_list, Nat.mem_divisors] using
        (Finset.mem_sort (s := n.divisors) (r := (· ≤ ·)) (a := y)).1 hy_mem
    refine ⟨?_, by omega⟩
    by_contra hyodd_not
    have hyeven : Even y := Nat.not_odd_iff_even.mp hyodd_not
    obtain ⟨k, hyk⟩ := (even_iff_exists_two_mul.mp hyeven)
    have hydiv' : (2 * k) ∣ n := by simpa [hyk] using hy_info.1
    have hkdiv : k ∣ n := dvd_trans (dvd_mul_left k 2) hydiv'
    have hk_mem : k ∈ sorted_divisors_list n := by
      have hk_fin : k ∈ n.divisors := by
        rw [Nat.mem_divisors]
        exact ⟨hkdiv, hy_info.2⟩
      simpa [sorted_divisors_list] using
        (Finset.mem_sort (s := n.divisors) (r := (· ≤ ·)) (a := k)).2 hk_fin
    have hxk : x < k := by omega
    have hky : k < y := by omega
    have hs : (sorted_divisors_list n).Pairwise (· ≤ ·) := by
      simpa [sorted_divisors_list] using
        (Finset.pairwise_sort (s := n.divisors) (r := (· ≤ ·)))
    have hn : (sorted_divisors_list n).Nodup := by
      simpa [sorted_divisors_list] using
        (Finset.sort_nodup (s := n.divisors) (r := (· ≤ ·)))
    exact no_between_of_adjacent_pairwise hs hn hxy hk_mem ⟨hxk, hky⟩

/--
A237271 Conjecture 2: a(n) is the number of 2-dense sublists of divisors of n.
We call "2-dense sublists of divisors of n" to the maximal sublists of divisors of n
whose terms increase by a factor of at most 2.
The conjecture 2 is essentially the same as the second conjecture in the Comments of A384149.
-/
theorem oeis_a237271_conjecture_2 (n : ℕ) : a n = num_2_dense_sublists n := by
  simp [a, num_2_dense_sublists, sorted_divisors_list]
  apply countP_congr_mem
  intro pair hpair
  have hiff : (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1) ↔ pair.2 > 2 * pair.1 :=
    adjacent_divisor_condition_iff n hpair
  by_cases hO : Odd pair.2
  · by_cases hL : 2 * pair.1 ≤ pair.2
    · by_cases hG : 2 * pair.1 < pair.2
      · simp [hO, hL, hG]
      · simp [hO, hL, hG] at hiff
    · by_cases hG : 2 * pair.1 < pair.2
      · simp [hO, hL, hG] at hiff
      · simp [hO, hL, hG]
  · by_cases hL : 2 * pair.1 ≤ pair.2
    · by_cases hG : 2 * pair.1 < pair.2
      · simp [hO, hL, hG] at hiff
      · simp [hO, hL, hG]
    · by_cases hG : 2 * pair.1 < pair.2
      · simp [hO, hL, hG] at hiff
      · simp [hO, hL, hG]
