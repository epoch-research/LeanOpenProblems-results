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

/--
A237271 Conjecture 2: a(n) is the number of 2-dense sublists of divisors of n.
We call "2-dense sublists of divisors of n" to the maximal sublists of divisors of n
whose terms increase by a factor of at most 2.
The conjecture 2 is essentially the same as the second conjecture in the Comments of A384149.
-/
private theorem mem_zip_tail {α : Type*} {a b : α} :
    ∀ {L : List α}, (a, b) ∈ L.zip L.tail → ∃ l₁ l₂, L = l₁ ++ a :: b :: l₂ := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons x xs ih =>
    cases xs with
    | nil => intro h; simp at h
    | cons y rest =>
      intro h
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rest, rfl⟩
      · have h' : (a, b) ∈ (y :: rest).zip (y :: rest).tail := h
        obtain ⟨l₁, l₂, hl⟩ := ih h'
        exact ⟨x :: l₁, l₂, by rw [hl]; rfl⟩

/--
Key per-pair fact: for two consecutive divisors `a, b` of `n` (i.e. an adjacent pair in the
sorted list of divisors), the condition defining `a n` (namely `b` odd and `b ≥ 2 a`) is
equivalent to the condition defining `num_2_dense_sublists n` (namely `b > 2 a`).

The non-trivial direction uses that if `b` is even and `b > 2 a`, then `b / 2` would be a
divisor of `n` lying strictly between `a` and `b`, contradicting that `a, b` are consecutive.
-/
private theorem pair_condition_iff (n : ℕ) {a b : ℕ}
    (hmem : (a, b) ∈ (n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail) :
    (Odd b ∧ 2 * a ≤ b) ↔ 2 * a < b := by
  have hsorted0 : (n.divisors.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hnodup0 : (n.divisors.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  obtain ⟨l₁, l₂, hL⟩ := mem_zip_tail hmem
  have haL : a ∈ n.divisors.sort (· ≤ ·) := by rw [hL]; simp
  have hbL : b ∈ n.divisors.sort (· ≤ ·) := by rw [hL]; simp
  have ha_div : a ∈ n.divisors := by simpa using haL
  have hb_div : b ∈ n.divisors := by simpa using hbL
  have hn0 : n ≠ 0 := (Nat.mem_divisors.1 ha_div).2
  have hbdvd : b ∣ n := (Nat.mem_divisors.1 hb_div).1
  have hbpos : 0 < b := Nat.pos_of_mem_divisors hb_div
  rw [hL] at hsorted0 hnodup0
  have hpair : (a :: b :: l₂).Pairwise (· ≤ ·) := (List.pairwise_append.1 hsorted0).2.1
  have hab_le : a ≤ b := (List.pairwise_cons.1 hpair).1 b (by simp)
  have hab_ne : a ≠ b := by
    have hnd : (a :: b :: l₂).Nodup := (List.nodup_append.1 hnodup0).2.1
    intro h; subst h
    exact (List.nodup_cons.1 hnd).1 (by simp)
  have hbetween : ∀ c, c ∣ n → a < c → c < b → False := by
    intro c hcdvd hac hcb
    have hcdiv : c ∈ n.divisors := Nat.mem_divisors.2 ⟨hcdvd, hn0⟩
    have hcL : c ∈ n.divisors.sort (· ≤ ·) := by simpa using hcdiv
    rw [hL] at hcL
    rcases List.mem_append.1 hcL with hc1 | hc2
    · have hca : c ≤ a := (List.pairwise_append.1 hsorted0).2.2 c hc1 a (by simp)
      exact absurd hac (not_lt.2 hca)
    · rcases List.mem_cons.1 hc2 with rfl | hc3
      · exact lt_irrefl _ hac
      · rcases List.mem_cons.1 hc3 with rfl | hc4
        · exact lt_irrefl _ hcb
        · have hbl2 : (b :: l₂).Pairwise (· ≤ ·) := (List.pairwise_cons.1 hpair).2
          have hbc : b ≤ c := (List.pairwise_cons.1 hbl2).1 c hc4
          exact absurd hcb (not_lt.2 hbc)
  constructor
  · rintro ⟨hodd, hge⟩
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      omega
  · intro hlt
    refine ⟨?_, le_of_lt hlt⟩
    by_contra hnotodd
    rw [Nat.not_odd_iff_even] at hnotodd
    obtain ⟨e, he⟩ := hnotodd
    have hb2e : b = 2 * e := by omega
    have he_dvd : e ∣ n := dvd_trans ⟨2, by omega⟩ hbdvd
    have hae : a < e := by omega
    have heb : e < b := by omega
    exact hbetween e he_dvd hae heb

/--
A237271 Conjecture 2: a(n) is the number of 2-dense sublists of divisors of n.
We call "2-dense sublists of divisors of n" to the maximal sublists of divisors of n
whose terms increase by a factor of at most 2.
The conjecture 2 is essentially the same as the second conjecture in the Comments of A384149.
-/
theorem oeis_a237271_conjecture_2 (n : ℕ) : a n = num_2_dense_sublists n := by
  unfold a num_2_dense_sublists sorted_divisors_list
  simp only
  congr 1
  apply List.countP_congr
  intro x hx
  obtain ⟨c, d⟩ := x
  simp only [decide_eq_true_eq, ge_iff_le, gt_iff_lt]
  exact pair_condition_iff n hx
