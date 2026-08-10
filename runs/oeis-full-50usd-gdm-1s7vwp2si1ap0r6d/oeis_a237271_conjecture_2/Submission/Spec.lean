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

lemma mem_of_mem_zip {α β : Type _} {l1 : List α} {l2 : List β} {x : α} {y : β} (h : (x, y) ∈ List.zip l1 l2) : x ∈ l1 ∧ y ∈ l2 := by
  induction l1 generalizing l2 with
  | nil =>
    simp at h
  | cons a t1 ih =>
    cases l2 with
    | nil =>
      simp at h
    | cons b t2 =>
      simp [List.zip_cons_cons] at h
      rcases h with ⟨rfl, rfl⟩ | h_zip
      · simp
      · have ih_res := ih h_zip
        simp [ih_res.1, ih_res.2]

lemma pairwise_zip_tail {l : List ℕ} (hp : List.Pairwise (· < ·) l) {u v : ℕ} (h : (u, v) ∈ List.zip l l.tail) :
    u < v ∧ (∀ z ∈ l, u < z → v ≤ z) := by
  induction l generalizing u v with
  | nil =>
    simp at h
  | cons u_lst t ih =>
    cases t with
    | nil =>
      simp at h
    | cons v_lst t' =>
      -- List is u_lst :: v_lst :: t'
      have hp_cons : List.Pairwise (· < ·) (v_lst :: t') := List.Pairwise.of_cons hp
      have h_all : ∀ z ∈ v_lst :: t', u_lst < z := fun z hz => List.rel_of_pairwise_cons hp hz
      simp [List.zip_cons_cons] at h
      rcases h with ⟨rfl, rfl⟩ | h_zip_tail
      · -- Case 1: (u, v) = (u_lst, v_lst). rcases substitutes u_lst -> u and v_lst -> v
        have huv : u < v := h_all v (by simp)
        refine ⟨huv, ?_⟩
        intro z hz h_lt
        cases hz with
        | head =>
          -- z = u
          omega
        | tail b hz_tail =>
          -- z ∈ v :: t'
          cases hz_tail with
          | head =>
            -- z = v
            omega
          | tail b' hz_t' =>
            have hvz : v < z := List.rel_of_pairwise_cons hp_cons hz_t'
            omega
      · -- Case 2: (u, v) ∈ zip (v_lst :: t') t'
        have ih_res := ih hp_cons h_zip_tail
        refine ⟨ih_res.1, ?_⟩
        intro z hz h_lt
        cases hz with
        | head =>
          -- z = u_lst
          have h_xu : u_lst < u := by
            have h_mem : u ∈ v_lst :: t' := (mem_of_mem_zip h_zip_tail).1
            exact h_all u h_mem
          omega
        | tail b hz_tail =>
          -- z ∈ v_lst :: t'
          exact ih_res.2 z hz_tail h_lt

lemma key_lemma (n : ℕ) (x y : ℕ) (hx : x ∈ n.divisors) (hy : y ∈ n.divisors)
    (h_consec : x < y ∧ ∀ z ∈ n.divisors, z > x → z ≥ y) :
    (Odd y ∧ y ≥ 2 * x) ↔ y > 2 * x := by
  constructor
  · rintro ⟨h_odd, h_ge⟩
    rcases eq_or_lt_of_le h_ge with rfl | h_lt
    · exfalso
      rcases h_odd with ⟨k, hk⟩
      omega
    · exact h_lt
  · intro h_gt
    have h_ge : y ≥ 2 * x := le_of_lt h_gt
    refine ⟨?_, h_ge⟩
    -- Now prove Odd y
    rw [Nat.odd_iff]
    by_contra h_mod
    have h_mod0 : y % 2 = 0 := by omega
    have h_dvd : 2 ∣ y := Nat.dvd_of_mod_eq_zero h_mod0
    rcases h_dvd with ⟨m, rfl⟩
    have hn0 : n ≠ 0 := by
      have := mem_divisors.mp hy
      exact this.2
    have hm_dvd : m ∣ n := by
      have := dvd_of_mem_divisors hy
      have hmy : m ∣ 2 * m := dvd_mul_left m 2
      exact dvd_trans hmy this
    have hm_mem : m ∈ n.divisors := by
      rw [mem_divisors]
      refine ⟨hm_dvd, hn0⟩
    have hm_gt : m > x := by
      omega
    have := h_consec.2 m hm_mem hm_gt
    have hx_pos : x > 0 := pos_of_mem_divisors hx
    have hm_pos : m > 0 := by omega
    omega

/--
A237271 Conjecture 2: a(n) is the number of 2-dense sublists of divisors of n.
We call "2-dense sublists of divisors of n" to the maximal sublists of divisors of n
whose terms increase by a factor of at most 2.
The conjecture 2 is essentially the same as the second conjecture in the Comments of A384149.
-/
theorem oeis_a237271_conjecture_2 (n : ℕ) : a n = num_2_dense_sublists n := by
  dsimp [a, num_2_dense_sublists, sorted_divisors_list]
  congr 1
  apply List.countP_congr
  intro pair h_mem
  rcases pair with ⟨d_k, d_k_succ⟩
  simp only [decide_eq_true_iff]
  -- Let's define divs_list
  let divs_list := n.divisors.sort (· ≤ ·)
  have h_zip_tail : (d_k, d_k_succ) ∈ List.zip divs_list divs_list.tail := h_mem
  -- Since divs_list is sorted by LT
  have h_sorted : divs_list.SortedLT := Finset.sortedLT_sort n.divisors
  have h_pairwise_lt : List.Pairwise (· < ·) divs_list := List.SortedLT.pairwise h_sorted
  -- Apply pairwise_zip_tail
  have h_res := pairwise_zip_tail h_pairwise_lt h_zip_tail
  -- We have d_k ∈ divs_list and d_k_succ ∈ divs_list
  have h_m_zip := mem_of_mem_zip h_zip_tail
  have h_dk_mem : d_k ∈ divs_list := h_m_zip.1
  have h_dks_mem : d_k_succ ∈ divs_list := by
    -- divs_list.tail is a sublist of divs_list
    have h_sub : divs_list.tail <+ divs_list := List.tail_sublist divs_list
    exact h_sub.subset h_m_zip.2
  -- Convert to membership in n.divisors
  have hx : d_k ∈ n.divisors := by
    rwa [← Finset.mem_sort (fun a b => a ≤ b)]
  have hy : d_k_succ ∈ n.divisors := by
    rwa [← Finset.mem_sort (fun a b => a ≤ b)]
  -- Formulate the h_consec parameter for key_lemma
  have h_consec : d_k < d_k_succ ∧ ∀ z ∈ n.divisors, z > d_k → z ≥ d_k_succ := by
    refine ⟨h_res.1, ?_⟩
    intro z hz hz_gt
    have hz_sort : z ∈ divs_list := by
      rwa [Finset.mem_sort (fun a b => a ≤ b)]
    exact h_res.2 z hz_sort hz_gt
  -- Now apply key_lemma
  exact key_lemma n d_k d_k_succ hx hy h_consec
