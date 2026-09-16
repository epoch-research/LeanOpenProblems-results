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

theorem mem_sorted_divisors_list {n x : ℕ} : x ∈ sorted_divisors_list n ↔ x ∈ n.divisors := by
  dsimp [sorted_divisors_list]
  exact Finset.mem_sort (· ≤ ·)

def IsAdj {α : Type*} (a b : α) : List α → Prop
| [] => False
| [_] => False
| x :: y :: xs => (x = a ∧ y = b) ∨ IsAdj a b (y :: xs)

theorem mem_of_isAdj_left {α : Type*} {a b : α} {l : List α} :
  IsAdj a b l → a ∈ l := by
  induction l with
  | nil => simp [IsAdj]
  | cons x xs ih =>
    cases xs with
    | nil => simp [IsAdj]
    | cons y ys =>
      intro h
      cases h with
      | inl h => simp [h.1]
      | inr h => right; exact ih h

theorem mem_of_isAdj_right {α : Type*} {a b : α} {l : List α} :
  IsAdj a b l → b ∈ l := by
  induction l with
  | nil => simp [IsAdj]
  | cons x xs ih =>
    cases xs with
    | nil => simp [IsAdj]
    | cons y ys =>
      intro h
      cases h with
      | inl h => simp [h.2]
      | inr h => right; exact ih h

theorem isAdj_pairwise {a b : ℕ} {l : List ℕ} (hs : List.Pairwise (· < ·) l) (h : IsAdj a b l) :
  a < b ∧ ∀ z ∈ l, z < b → z ≤ a := by
  induction l with
  | nil => simp [IsAdj] at h
  | cons head xs ih =>
    cases xs with
    | nil => simp [IsAdj] at h
    | cons y ys =>
      cases h with
      | inl h =>
        have h_head : head = a := h.1
        have h_y : y = b := h.2
        have h_lt : a < b := by
          cases hs with
          | cons ha hys =>
            have h_mem : y ∈ y :: ys := by simp
            have lt_head_y := ha y h_mem
            omega
        refine ⟨h_lt, ?_⟩
        intro z hz hz_lt
        simp at hz
        cases hz with
        | inl hz => omega
        | inr hz =>
          cases hz with
          | inl hz => omega
          | inr hz =>
            cases hs with
            | cons ha hys =>
              cases hys with
              | cons hb hz_rest =>
                have z_gt_b : y < z := hb z hz
                omega
      | inr h =>
        cases hs with
        | cons ha hys =>
          have ih_res := ih hys h
          refine ⟨ih_res.1, ?_⟩
          intro z hz hz_lt
          simp at hz
          cases hz with
          | inl hz =>
            have h_a_in : a ∈ y :: ys := mem_of_isAdj_left h
            have hxa : head < a := ha a h_a_in
            omega
          | inr hz =>
            have hz_in : z ∈ y :: ys := by
              cases hz with
              | inl hz2 => simp [hz2]
              | inr hz2 => simp [hz2]
            exact ih_res.2 z hz_in hz_lt

theorem isAdj_of_mem_zip_tail {α : Type*} [DecidableEq α] {a b : α} {l : List α} :
  (a, b) ∈ List.zip l l.tail → IsAdj a b l := by
  induction l with
  | nil => simp [IsAdj, List.zip]
  | cons x xs ih =>
    cases xs with
    | nil => simp [IsAdj, List.zip]
    | cons y ys =>
      intro h
      simp [List.zip, List.tail] at h
      cases h with
      | inl h => left; exact ⟨h.1.symm, h.2.symm⟩
      | inr h => right; exact ih h

theorem countP_congr {α : Type*} (l : List α) (p q : α → Bool) 
  (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.countP_cons]
    have h1 : p x = q x := h x (by simp)
    have h2 : xs.countP p = xs.countP q := ih (fun y hy => h y (by simp [hy]))
    rw [h1, h2]

theorem div_gt_two_mul_odd {n a b : ℕ} (hb : b ∣ n) (ha_lt_hb : a < b)
  (h_adj : ∀ z, z ∣ n → z < b → z ≤ a) (h_gt : b > 2 * a) :
  Odd b := by
  have heven : ¬ Even b → Odd b := Nat.not_even_iff_odd.mp
  by_cases h : Even b
  · rcases h with ⟨k, hk⟩
    have hb_pos : b > 0 := by omega
    have hk_lt_b : k < b := by omega
    have hk_div_b : k ∣ b := ⟨2, by omega⟩
    have hk_div_n : k ∣ n := Nat.dvd_trans hk_div_b hb
    have hk_le_a : k ≤ a := h_adj k hk_div_n hk_lt_b
    omega
  · exact heven h

theorem b_gt_two_a_iff {n a b : ℕ} (hb : b ∣ n) (ha_lt_hb : a < b)
  (h_adj : ∀ z, z ∣ n → z < b → z ≤ a) :
  b > 2 * a ↔ Odd b ∧ b ≥ 2 * a := by
  constructor
  · intro h
    exact ⟨div_gt_two_mul_odd hb ha_lt_hb h_adj h, by omega⟩
  · intro h
    have h1 := h.1
    have h2 := h.2
    have h_neq : b ≠ 2 * a := by
      intro h_eq
      subst h_eq
      rcases h1 with ⟨k, hk⟩
      omega
    omega

theorem eq_of_adj_divisors {n d_k d_k_succ : ℕ} 
  (h_adj : (d_k, d_k_succ) ∈ List.zip (sorted_divisors_list n) (sorted_divisors_list n).tail) :
  d_k_succ > 2 * d_k ↔ Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [sorted_divisors_list] at h_adj
  have hn_pos : n > 0 := by omega
  have h_adj_2 := isAdj_of_mem_zip_tail h_adj
  have hs : List.Pairwise (· < ·) (sorted_divisors_list n) := (Finset.sortedLT_sort n.divisors).pairwise
  have h_res := isAdj_pairwise hs h_adj_2
  have h_lt : d_k < d_k_succ := h_res.1
  have hb_in : d_k_succ ∈ sorted_divisors_list n := mem_of_isAdj_right h_adj_2
  have hb : d_k_succ ∣ n := by
    have h_mem_divs : d_k_succ ∈ n.divisors := mem_sorted_divisors_list.mp hb_in
    exact Nat.dvd_of_mem_divisors h_mem_divs
  have h_adj_cond : ∀ (z : ℕ), z ∣ n → z < d_k_succ → z ≤ d_k := by
    intro z hz hz_lt
    have hz_in : z ∈ sorted_divisors_list n := by
      have h_mem_divs : z ∈ n.divisors := Nat.mem_divisors.mpr ⟨hz, by omega⟩
      exact mem_sorted_divisors_list.mpr h_mem_divs
    exact h_res.2 z hz_in hz_lt
  exact b_gt_two_a_iff hb h_lt h_adj_cond

theorem bool_eq_of_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q := by
  cases h' : decide P
  · simp at h'
    have hq : ¬ Q := fun hq => h' (h.mpr hq)
    simp [hq]
  · simp at h'
    have hq : Q := h.mp h'
    simp [hq]

/--
A237271 Conjecture 2: a(n) is the number of 2-dense sublists of divisors of n.
We call "2-dense sublists of divisors of n" to the maximal sublists of divisors of n
whose terms increase by a factor of at most 2.
The conjecture 2 is essentially the same as the second conjecture in the Comments of A384149.
-/
theorem oeis_a237271_conjecture_2 (n : ℕ) : a n = num_2_dense_sublists n := by
  dsimp [a, num_2_dense_sublists]
  have h_congr := countP_congr (List.zip (sorted_divisors_list n) (sorted_divisors_list n).tail)
    (fun pair => decide (Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst))
    (fun pair => decide (pair.snd > 2 * pair.fst))
  have h_eq : (List.countP (fun pair => decide (Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst))
      (List.zip (sorted_divisors_list n) (sorted_divisors_list n).tail)) =
    (List.countP (fun pair => decide (pair.snd > 2 * pair.fst))
      (List.zip (sorted_divisors_list n) (sorted_divisors_list n).tail)) := by
    apply h_congr
    intro pair h_pair
    have heq := eq_of_adj_divisors h_pair
    exact bool_eq_of_iff heq.symm
  exact congrArg (HAdd.hAdd 1) h_eq

theorem oeis_a237271_conjecture_2.disproof : ¬ (type_of% @oeis_a237271_conjecture_2) := sorry
