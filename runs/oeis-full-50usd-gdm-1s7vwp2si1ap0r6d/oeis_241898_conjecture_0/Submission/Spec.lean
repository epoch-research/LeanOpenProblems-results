import FormalConjectures.Util.ProblemImports

open List Nat Finset Classical WithBot

/--
A241898: $a(n)$ is the largest integer such that $n = a(n)^2 + \dots$ is a decomposition of $n$ into a sum of at most four nondecreasing squares.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let P (k : ℕ) : Prop :=
    k > 0 ∧
    ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = n ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k -- Qualified 'some' to resolve ambiguity

  -- We explicitly provide the DecidablePred instance using classical logic, which is sound
  -- because the existential quantifier is over a finite, bounded search space.
  have dec : DecidablePred P := fun k => Classical.dec (P k)

  -- Filter the range of possible bases k up to $\lfloor\sqrt{n}\rfloor$.
  let S : Finset ℕ := @Finset.filter _ P dec (range (n.sqrt + 1))

  -- Finset.max returns `WithBot ℕ`. We use `rec 0 id` to convert to `ℕ`,
  -- mapping ⊥ (empty set max) to 0 and a successful max to its value.
  (S.max).rec 0 id

set_option maxRecDepth 200000

def my_sqrt_aux (n : ℕ) (guess : ℕ) : ℕ :=
  match guess with
  | 0 => 0
  | g + 1 => if (g + 1) * (g + 1) ≤ n then g + 1 else my_sqrt_aux n g

def my_sqrt (n : ℕ) : ℕ := my_sqrt_aux n n

lemma my_sqrt_aux_le (n guess : ℕ) : my_sqrt_aux n guess ≤ guess := by
  induction guess with
  | zero => rfl
  | succ g ih =>
    unfold my_sqrt_aux
    split_ifs with h
    · omega
    · linarith [ih]

lemma my_sqrt_aux_sq_le (n guess : ℕ) : my_sqrt_aux n guess * my_sqrt_aux n guess ≤ n := by
  induction guess with
  | zero =>
    simp [my_sqrt_aux]
  | succ g ih =>
    unfold my_sqrt_aux
    split_ifs with h
    · exact h
    · exact ih

lemma my_sqrt_aux_lt_succ_sq (n guess : ℕ) (h_guess : n < (guess + 1) * (guess + 1)) : n < (my_sqrt_aux n guess + 1) * (my_sqrt_aux n guess + 1) := by
  induction guess with
  | zero =>
    simp [my_sqrt_aux] at *
    omega
  | succ g ih =>
    unfold my_sqrt_aux
    split_ifs with h
    · exact h_guess
    · have h_lt : n < (g + 1) * (g + 1) := by omega
      exact ih h_lt

lemma my_sqrt_eq_sqrt (n : ℕ) : my_sqrt n = n.sqrt := by
  have h1 : my_sqrt n * my_sqrt n ≤ n := my_sqrt_aux_sq_le n n
  have h2 : n < (my_sqrt n + 1) * (my_sqrt n + 1) := by
    apply my_sqrt_aux_lt_succ_sq
    calc n < n + 1 := by omega
         _ ≤ (n + 1) * (n + 1) := Nat.le_mul_self (n + 1)
  exact eq_sqrt.2 ⟨h1, h2⟩

def can_sum (count : ℕ) (min_val : ℕ) (target : ℕ) : Bool :=
  match count with
  | 0 => target == 0
  | count + 1 =>
    (target == 0) ||
    ((List.range (my_sqrt target + 1)).any (fun x =>
      min_val ≤ x && can_sum count x (target - x^2)
    ))

lemma can_sum_of_list (count : ℕ) (min_val : ℕ) (target : ℕ) (s : List ℕ)
  (h_len : s.length ≤ count)
  (h_sort : s.Sorted (· ≤ ·))
  (h_min : ∀ x ∈ s, min_val ≤ x)
  (h_sum : (s.map (fun b => b^2)).sum = target) :
  can_sum count min_val target = true := by
  induction s generalizing count min_val target with
  | nil =>
    have h_target : target = 0 := by
      rw [← h_sum]
      rfl
    subst h_target
    cases count with
    | zero => rfl
    | succ c => rfl
  | cons hd tl ih =>
    cases count with
    | zero =>
      simp only [List.length_cons] at h_len
      omega
    | succ c =>
      have h_sort_tl : tl.Sorted (· ≤ ·) := List.Sorted.of_cons h_sort
      have h_hd_le_tl : ∀ x ∈ tl, hd ≤ x := (List.pairwise_cons.1 h_sort).1
      have h_sum' : hd^2 + (tl.map (fun b => b^2)).sum = target := by
        simp only [List.map_cons, List.sum_cons] at h_sum
        exact h_sum
      have h_sum_tl : (tl.map (fun b => b^2)).sum = target - hd^2 := by omega
      have h_len_tl : tl.length ≤ c := by
        simp only [List.length_cons] at h_len
        omega
      have h_hd_min : min_val ≤ hd := h_min hd (by simp)
      have h_min_tl : ∀ x ∈ tl, hd ≤ x := h_hd_le_tl
      have h_ih := ih c hd (target - hd^2) h_len_tl h_sort_tl h_min_tl h_sum_tl
      
      -- Unfold the definition of can_sum (c + 1)
      unfold can_sum
      rw [my_sqrt_eq_sqrt]
      rw [Bool.or_eq_true]
      right
      apply List.any_eq_true.2
      use hd
      constructor
      · -- Show hd ∈ List.range (target.sqrt + 1)
        apply List.mem_range.2
        have h_hd2_le : hd^2 ≤ target := by omega
        have h_hd_le : hd ≤ target.sqrt := le_sqrt'.2 h_hd2_le
        omega
      · -- Show (min_val ≤ hd && can_sum c hd (target - hd^2)) = true
        rw [Bool.and_eq_true]
        constructor
        · exact decide_eq_true h_hd_min
        · exact h_ih

lemma le_of_mem_of_sorted_head {s : List ℕ} {x k : ℕ}
  (h_sort : s.Sorted (· ≤ ·)) (h_head : s.head? = Option.some k) (h_mem : x ∈ s) : k ≤ x := by
  cases s with
  | nil =>
    simp only [List.head?_nil] at h_head
    contradiction
  | cons hd tl =>
    simp only [List.head?_cons] at h_head
    injection h_head with h_eq
    subst h_eq
    simp only [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem_tl
    · rfl
    · have h_le_tl : ∀ y ∈ tl, hd ≤ y := (List.pairwise_cons.1 h_sort).1
      exact h_le_tl x h_mem_tl

lemma test_rec_le (S : Finset ℕ) (h_S : ∀ k ∈ S, k ≤ 7) : (S.max).rec 0 id ≤ 7 := by
  cases h : S.max with
  | bot =>
    decide
  | coe k =>
    have hk : k ∈ S := mem_of_max h
    exact h_S k hk

lemma a_736_le : a 736 ≤ 7 := by
  unfold a
  apply test_rec_le
  intro k hk
  simp only [Finset.mem_filter] at hk
  rcases hk with ⟨_, hk_P⟩
  rcases hk_P with ⟨_, s, _, h_len, h_sum, h_sort, h_head⟩
  by_contra hc
  have hk_ge_8 : k ≥ 8 := by omega
  have h_min : ∀ x ∈ s, 8 ≤ x := by
    intro x hx
    have : k ≤ x := le_of_mem_of_sorted_head h_sort h_head hx
    omega
  have h_can_sum := can_sum_of_list 4 8 736 s h_len h_sort h_min h_sum
  have h_can_sum_false : can_sum 4 8 736 = false := by decide
  rw [h_can_sum_false] at h_can_sum
  contradiction

theorem oeis_241898_conjecture_0.disproof : ¬ (∀ n : ℕ, 599 < n → a n > 7) := by
  intro h
  have h_736 := h 736 (by decide)
  have h_736_le := a_736_le
  omega
