import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

private lemma length_takeWhile_le (p : α → Bool) (l : List α) : (takeWhile p l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [takeWhile]
    split
    · simp
      omega
    · simp

private lemma run_lengths_nat_sum : (l : List ℕ) → (run_lengths_nat l).sum = l.length
  | [] => by unfold run_lengths_nat; rfl
  | h :: t => by
    unfold run_lengths_nat
    simp
    let P := (takeWhile (fun x => x = h) t).length
    have ih := run_lengths_nat_sum (drop P t)
    have h_le := length_takeWhile_le (fun x => x = h) t
    rw [ih]
    rw [List.length_drop]
    omega
termination_by l => l.length

private lemma length_le_sum_of_pos (l : List ℕ) (h : ∀ x ∈ l, 1 ≤ x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp
    have h_head : 1 ≤ head := h head (by simp)
    have h_tail : ∀ x ∈ tail, 1 ≤ x := by
      intro x hx
      apply h x
      simp [hx]
    have ih_val := ih h_tail
    omega


private lemma run_lengths_nat_pos : (l : List ℕ) → ∀ x ∈ run_lengths_nat l, 1 ≤ x
  | [] => by
    unfold run_lengths_nat
    simp
  | h :: t => by
    unfold run_lengths_nat
    simp
    let P := (takeWhile (fun x => x = h) t).length
    exact run_lengths_nat_pos (drop P t)
termination_by l => l.length

private lemma run_lengths_nat_length_le (l : List ℕ) : (run_lengths_nat l).length ≤ l.length := by
  have h_pos := run_lengths_nat_pos l
  have h_le := length_le_sum_of_pos (run_lengths_nat l) h_pos
  rw [run_lengths_nat_sum l] at h_le
  exact h_le

private lemma takeWhile_append_of_not_all (p : ℕ → Bool) (t : List ℕ) (B : List ℕ)
    (h_all : (t.takeWhile p).length < t.length) :
    (t ++ B).takeWhile p = t.takeWhile p := by
  induction t with
  | nil =>
    simp at h_all
  | cons h t ih =>
    simp [takeWhile] at h_all ⊢
    by_cases hp : p h
    · simp [hp] at h_all ⊢
      apply ih
      omega
    · simp [hp]

private lemma drop_append_of_not_all (p : ℕ → Bool) (t : List ℕ) (B : List ℕ)
    (h_all : (t.takeWhile p).length < t.length) :
    (t ++ B).drop (t.takeWhile p).length = (t.drop (t.takeWhile p).length) ++ B := by
  induction t with
  | nil =>
    simp at h_all
  | cons h t ih =>
    simp [takeWhile] at h_all ⊢
    by_cases hp : p h
    · simp [hp] at h_all ⊢
      apply ih
      omega
    · simp [hp]

private lemma run_lengths_nat_cons (h : ℕ) (t : List ℕ) :
    run_lengths_nat (h :: t) = (takeWhile (fun x => x = h) (h :: t)).length :: run_lengths_nat (drop (takeWhile (fun x => x = h) (h :: t)).length (h :: t)) := by
  rw [run_lengths_nat]

private lemma run_lengths_nat_append_length_le : (A : List ℕ) → (_B : List ℕ) →
    (run_lengths_nat A).length ≤ (run_lengths_nat (A ++ _B)).length
  | [], _B => by simp [run_lengths_nat]
  | h :: t, _B => by
    have h_le_len := length_takeWhile_le (fun x => x = h) t
    have h_cases : (t.takeWhile (fun x => x = h)).length < t.length ∨ (t.takeWhile (fun x => x = h)).length = t.length := by omega
    rcases h_cases with h_lt | h_eq
    · have h_tw := takeWhile_append_of_not_all (fun x => x = h) t _B h_lt
      have h_dr := drop_append_of_not_all (fun x => x = h) t _B h_lt
      rw [run_lengths_nat_cons h t]
      have h_append_eq : (h :: t) ++ _B = h :: (t ++ _B) := rfl
      rw [h_append_eq, run_lengths_nat_cons h (t ++ _B)]
      simp
      rw [h_tw, h_dr]
      have ih := run_lengths_nat_append_length_le (drop (t.takeWhile (fun x => x = h)).length t) _B
      exact ih
    · rw [run_lengths_nat_cons h t]
      have h_len_eq : (takeWhile (fun x => x = h) (h :: t)).length = t.length + 1 := by
        simp [takeWhile, h_eq]
      have h_drop : drop (t.length + 1) (h :: t) = [] := by
        have : (h :: t).length = t.length + 1 := by simp
        rw [← this, drop_length]
      rw [h_len_eq, h_drop]
      simp [run_lengths_nat]
termination_by A _B => A.length



private lemma takeWhile_append_of_all (p : ℕ → Bool) (t : List ℕ) (B : List ℕ)
    (h_all : (t.takeWhile p).length = t.length) :
    (t ++ B).takeWhile p = t ++ B.takeWhile p := by
  induction t with
  | nil => simp
  | cons h t ih =>
    simp [takeWhile] at h_all ⊢
    by_cases hp : p h
    · simp [hp] at h_all ⊢
      apply ih
      omega
    · simp [hp] at h_all

private lemma drop_append_all_len (t B : List ℕ) (k : ℕ) :
    (t ++ B).drop (t.length + k) = B.drop k := by
  induction t with
  | nil => simp
  | cons h t ih =>
    have h_eq : t.length + 1 + k = (t.length + k) + 1 := by omega
    change drop (t.length + 1 + k) (h :: (t ++ B)) = B.drop k
    rw [h_eq]
    simp [ih]

private lemma drop_append_of_all (p : ℕ → Bool) (t : List ℕ) (B : List ℕ)
    (h_all : (t.takeWhile p).length = t.length) :
    (t ++ B).drop ((t ++ B).takeWhile p).length = B.drop (B.takeWhile p).length := by
  rw [takeWhile_append_of_all p t B h_all]
  simp [drop_append_all_len]

private lemma run_lengths_nat_drop_takeWhile_le (h : ℕ) (B : List ℕ) :
    (run_lengths_nat B).length ≤ (run_lengths_nat (B.drop (B.takeWhile (fun x => x = h)).length)).length + 1 := by
  cases B with
  | nil =>
    simp [run_lengths_nat]
  | cons h' t' =>
    by_cases heq : h' = h
    · rw [run_lengths_nat_cons h' t']
      subst heq
      simp
    · have h_tw : (takeWhile (fun x => x = h) (h' :: t')).length = 0 := by
        dsimp [takeWhile]
        split
        · rename_i hc
          simp at hc
          contradiction
        · rfl
      rw [h_tw]
      simp

private lemma run_lengths_nat_append_length_add_one_ge : (A : List ℕ) → (B : List ℕ) →
    (run_lengths_nat A).length + (run_lengths_nat B).length ≤ (run_lengths_nat (A ++ B)).length + 1
  | [], B => by simp [run_lengths_nat]
  | h :: t, B => by
    have h_le_len := length_takeWhile_le (fun x => x = h) t
    have h_cases : (t.takeWhile (fun x => x = h)).length < t.length ∨ (t.takeWhile (fun x => x = h)).length = t.length := by omega
    rcases h_cases with h_lt | h_eq
    · have h_tw := takeWhile_append_of_not_all (fun x => x = h) t B h_lt
      have h_dr := drop_append_of_not_all (fun x => x = h) t B h_lt
      rw [run_lengths_nat_cons h t]
      have h_append_eq : (h :: t) ++ B = h :: (t ++ B) := rfl
      rw [h_append_eq, run_lengths_nat_cons h (t ++ B)]
      simp
      rw [h_tw, h_dr]
      have ih := run_lengths_nat_append_length_add_one_ge (drop (t.takeWhile (fun x => x = h)).length t) B
      omega
    · rw [run_lengths_nat_cons h t]
      have h_len_eq : (takeWhile (fun x => x = h) (h :: t)).length = t.length + 1 := by
        simp [takeWhile, h_eq]
      have h_drop : drop (t.length + 1) (h :: t) = [] := by
        have : (h :: t).length = t.length + 1 := by simp
        rw [← this, drop_length]
      rw [h_len_eq, h_drop]
      simp [run_lengths_nat]
      have h_eq_all : (t.takeWhile (fun x => x = h)).length = t.length := h_eq
      have h_dr := drop_append_of_all (fun x => x = h) t B h_eq_all
      rw [h_dr]
      have h_le := run_lengths_nat_drop_takeWhile_le h B
      omega
termination_by A B => A.length

private def run_lengths_helper : List ℕ → ℕ → ℕ → List ℕ
  | [], _, cnt => [cnt]
  | h :: t, curr, cnt =>
    if h = curr then
      run_lengths_helper t curr (cnt + 1)
    else
      cnt :: run_lengths_helper t h 1

private def run_lengths_struct : List ℕ → List ℕ
  | [] => []
  | h :: t => run_lengths_helper t h 1

private def A381587_T_struct : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T_struct (k + 3)
    run_lengths_struct prev_T.reverse ++ prev_T

private lemma run_lengths_helper_eq (t : List ℕ) (h : ℕ) (cnt : ℕ) :
    run_lengths_helper t h cnt = (cnt + (takeWhile (fun x => x = h) t).length) :: run_lengths_nat (drop (takeWhile (fun x => x = h) t).length t) := by
  induction t generalizing h cnt with
  | nil =>
    simp [run_lengths_helper, run_lengths_nat]
  | cons h' t ih =>
    simp [run_lengths_helper]
    split_ifs with heq
    · subst heq
      simp [ih]
      omega
    · simp [heq]
      have ih_special := ih h' 1
      rw [ih_special]
      rw [run_lengths_nat]
      simp
      omega

private lemma run_lengths_struct_eq (l : List ℕ) : run_lengths_struct l = run_lengths_nat l := by
  cases l with
  | nil =>
    unfold run_lengths_struct run_lengths_nat
    rfl
  | cons h t =>
    dsimp [run_lengths_struct]
    rw [run_lengths_helper_eq]
    rw [run_lengths_nat]
    simp
    omega







/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown T_{n-1}$.
$n$ is 1-indexed here.
-/
private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

private lemma A381587_T_struct_eq (n : ℕ) : A381587_T_struct n = A381587_T n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | k + 4 =>
      unfold A381587_T_struct A381587_T
      have ih1 := ih (k + 3) (by omega)
      rw [ih1]
      dsimp
      rw [run_lengths_struct_eq]


/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum


private lemma A381587_T_pos (n : ℕ) : ∀ x ∈ A381587_T n, 1 ≤ x := by
  match n with
  | 0 => simp [A381587_T]
  | 1 => simp [A381587_T]
  | 2 => simp [A381587_T]
  | 3 => simp [A381587_T]
  | k + 4 =>
    unfold A381587_T
    simp
    intro x hx
    rcases hx with h1 | h2
    · have h_pos := run_lengths_nat_pos (A381587_T (k + 3)).reverse
      exact h_pos x h1
    · have h_ih := A381587_T_pos (k + 3)
      exact h_ih x h2


private lemma A381587_T_length_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ (A381587_T n).length := by
  match n with
  | 0 => omega
  | 1 => simp [A381587_T]
  | 2 => simp [A381587_T]
  | 3 => simp [A381587_T]
  | k + 4 =>
    unfold A381587_T
    simp
    have h_ih := A381587_T_length_pos (k + 3) (by omega)
    omega

private lemma A381358_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ A381358 n := by
  unfold A381358
  have h_pos := A381587_T_pos n
  have h_le := length_le_sum_of_pos (A381587_T n) h_pos
  have h_len := A381587_T_length_pos n hn
  omega

private lemma A381358_recurrence (k : ℕ) : A381358 (k + 4) = A381358 (k + 3) + (A381587_T (k + 3)).length := by
  unfold A381358
  rw [A381587_T]
  simp [run_lengths_nat_sum]
  omega

private lemma A381587_T_length_le_mul_two (k : ℕ) : (A381587_T (k + 4)).length ≤ 2 * (A381587_T (k + 3)).length := by
  rw [A381587_T]
  simp
  have h_le := run_lengths_nat_length_le (A381587_T (k + 3)).reverse
  simp at h_le
  omega

private lemma A381358_le_mul_two (k : ℕ) : A381358 (k + 4) ≤ 2 * A381358 (k + 3) := by
  rw [A381358_recurrence]
  unfold A381358
  have h_pos := A381587_T_pos (k + 3)
  have h_le := length_le_sum_of_pos (A381587_T (k + 3)) h_pos
  omega



private lemma A381358_le_pow_two (n : ℕ) : A381358 n ≤ 2 ^ n := by
  match n with
  | 0 => simp [A381358, A381587_T]
  | 1 => simp [A381358, A381587_T]
  | 2 => simp [A381358, A381587_T]
  | 3 => simp [A381358, A381587_T]
  | k + 4 =>
    have h_le := A381358_le_mul_two k
    have h_ih := A381358_le_pow_two (k + 3)
    have : 2 * 2 ^ (k + 3) = 2 ^ (k + 4) := by ring
    omega
termination_by n










/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/

private lemma A381587_T_suffix (n m : ℕ) (hn : 3 ≤ n) : ∃ X, A381587_T (n + m) = X ++ A381587_T n := by
  induction m with
  | zero =>
    use []
    simp
  | succ m ih =>
    rcases ih with ⟨X, hX⟩
    -- n + succ m = n + m + 1. Since 3 <= n, we have 4 <= n + m + 1.
    -- So we can write n + m + 1 = (n + m - 3) + 4.
    have h_ge : 4 ≤ n + m + 1 := by omega
    let k := n + m - 3
    have h_eq : n + m + 1 = k + 4 := by omega
    have h_eq3 : n + m = k + 3 := by omega
    have h_step : A381587_T (n + m + 1) = run_lengths_nat (A381587_T (n + m)).reverse ++ A381587_T (n + m) := by
      rw [h_eq, h_eq3]
      rfl
    use run_lengths_nat (A381587_T (n + m)).reverse ++ X
    rw [← Nat.add_assoc]
    rw [h_step, hX]
    simp


private def sum_range_nat (f : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => sum_range_nat f start m + f (start + m)


private lemma sum_range_nat_split (f : ℕ → ℕ) (start : ℕ) (k : ℕ) :
    sum_range_nat f start (k + 2) = f start + f (start + 1) + sum_range_nat f (start + 2) k := by
  induction k with
  | zero =>
    dsimp [sum_range_nat]
    omega
  | succ k ih =>
    have h_eq : start + (k + 1) + 1 = start + k + 2 := by omega
    have h_eq2 : start + 2 + k = start + k + 2 := by omega
    -- sum_range_nat f start (k + 3) = sum_range_nat f start (k + 2) + f (start + k + 2)
    -- by unfolding sum_range_nat
    -- But since k+3 = k+2+1, definitionally:
    have h_def : sum_range_nat f start (k + 3) = sum_range_nat f start (k + 2) + f (start + k + 2) := rfl
    have h_def2 : sum_range_nat f (start + 2) (k + 1) = sum_range_nat f (start + 2) k + f (start + 2 + k) := rfl
    rw [h_def, h_def2, h_eq2, ih]
    omega


private lemma sum_range_nat_mul (f : ℕ → ℕ) (start : ℕ) (k : ℕ) (a : ℕ) :
    sum_range_nat (fun j => a * f j) start k = a * sum_range_nat f start k := by
  induction k with
  | zero => simp [sum_range_nat]
  | succ k ih =>
    have h_def : sum_range_nat f start (k + 1) = sum_range_nat f start k + f (start + k) := rfl
    have h_def2 : sum_range_nat (fun j => a * f j) start (k + 1) = sum_range_nat (fun j => a * f j) start k + a * f (start + k) := rfl
    rw [h_def, h_def2, ih]
    ring


private lemma sum_range_nat_le (f g : ℕ → ℕ) (start : ℕ) (k : ℕ) (h : ∀ j, start ≤ j → f j ≤ g j) :
    sum_range_nat f start k ≤ sum_range_nat g start k := by
  induction k with
  | zero => simp [sum_range_nat]
  | succ k ih =>
    have h_def : sum_range_nat f start (k + 1) = sum_range_nat f start k + f (start + k) := rfl
    have h_def2 : sum_range_nat g start (k + 1) = sum_range_nat g start k + g (start + k) := rfl
    rw [h_def, h_def2]
    have h1 := h (start + k) (by omega)
    omega

private lemma A381358_sum_range (n m : ℕ) (hn : 3 ≤ n) :
    A381358 (n + m) = A381358 n + sum_range_nat (fun j => (A381587_T j).length) n m := by
  induction m with
  | zero => simp [sum_range_nat]
  | succ m ih =>
    have h_ge : 3 ≤ n + m := by omega
    let k := n + m - 3
    have h_eq : n + m = k + 3 := by omega
    have h_eq4 : n + m + 1 = k + 4 := by omega
    have h_rec := A381358_recurrence k
    rw [← h_eq, ← h_eq4] at h_rec
    have h_assoc : n + (m + 1) = n + m + 1 := by omega
    rw [h_assoc]
    unfold sum_range_nat
    omega

private lemma A381587_T_length_le_succ (n : ℕ) : (A381587_T n).length ≤ (A381587_T (n + 1)).length := by
  match n with
  | 0 => simp [A381587_T]
  | 1 => simp [A381587_T]
  | 2 => simp [A381587_T]
  | 3 => simp [A381587_T]
  | k + 4 =>
    have h_eq : A381587_T (k + 5) = run_lengths_nat (A381587_T (k + 4)).reverse ++ A381587_T (k + 4) := rfl
    rw [h_eq]
    simp


private lemma A381587_T_length_mono (n m : ℕ) (h : n ≤ m) : (A381587_T n).length ≤ (A381587_T m).length := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this
    rfl
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rfl
    · have h_lt : n ≤ m := by omega
      have ih_val := ih h_lt
      have h_succ := A381587_T_length_le_succ m
      omega


private lemma A381358_le_succ (n : ℕ) : A381358 n ≤ A381358 (n + 1) := by
  match n with
  | 0 => simp [A381358, A381587_T]
  | 1 => simp [A381358, A381587_T]
  | 2 => simp [A381358, A381587_T]
  | k + 3 =>
    -- n = k + 3 >= 3, so n + 1 = k + 4
    rw [A381358_recurrence k]
    omega

private lemma A381358_mono (n m : ℕ) (h : n ≤ m) : A381358 n ≤ A381358 m := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this
    rfl
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq
      rfl
    · have h_lt : n ≤ m := by omega
      have ih_val := ih h_lt
      have h_succ := A381358_le_succ m
      omega



private noncomputable def u_seq (n : ℕ) : ℝ :=
  if n = 0 then 0 else - Real.log (A381358 n)

private lemma A381587_T_R_mono (k : ℕ) :
    (run_lengths_nat (A381587_T (k + 3)).reverse).length ≤ (run_lengths_nat (A381587_T (k + 4)).reverse).length := by
  have h_eq : (A381587_T (k + 4)).reverse = (A381587_T (k + 3)).reverse ++ (run_lengths_nat (A381587_T (k + 3)).reverse).reverse := by
    change (run_lengths_nat (A381587_T (k + 3)).reverse ++ A381587_T (k + 3)).reverse = (A381587_T (k + 3)).reverse ++ (run_lengths_nat (A381587_T (k + 3)).reverse).reverse
    rw [List.reverse_append]
  rw [h_eq]
  apply run_lengths_nat_append_length_le

private lemma R_growth (n : ℕ) (hn : 5 ≤ n) :
    3 * (run_lengths_nat (A381587_T n).reverse).length ≤ 2 * (run_lengths_nat (A381587_T (n + 1)).reverse).length := by
  sorry

private lemma L_le_two_R (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T n).length ≤ 2 * (run_lengths_nat (A381587_T n).reverse).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | _ | k
    · omega
    · omega
    · omega
    · change (A381587_T 3).length ≤ 2 * (run_lengths_nat (A381587_T 3).reverse).length
      have h1 : (A381587_T 3).length = 1 := by
        rw [← A381587_T_struct_eq 3]; rfl
      have h2 : (run_lengths_nat (A381587_T 3).reverse).length = 1 := by
        rw [← run_lengths_struct_eq, ← A381587_T_struct_eq 3]; rfl
      omega
    · change (A381587_T 4).length ≤ 2 * (run_lengths_nat (A381587_T 4).reverse).length
      have h_T4 : (A381587_T 4).length = 2 := by
        rw [← A381587_T_struct_eq 4]; rfl
      have h_R4 : (run_lengths_nat (A381587_T 4).reverse).length = 2 := by
        rw [← run_lengths_struct_eq, ← A381587_T_struct_eq 4]; rfl
      omega
    · change (A381587_T 5).length ≤ 2 * (run_lengths_nat (A381587_T 5).reverse).length
      have h_T5 : (A381587_T 5).length = 4 := by
        rw [← A381587_T_struct_eq 5]; rfl
      have h_R5 : (run_lengths_nat (A381587_T 5).reverse).length = 2 := by
        rw [← run_lengths_struct_eq, ← A381587_T_struct_eq 5]; rfl
      omega
    · have h_ih := ih (k + 5) (by omega) (by omega)
      change (A381587_T (k + 5)).length ≤ 2 * (run_lengths_nat (A381587_T (k + 5)).reverse).length at h_ih
      have h_rec : A381587_T (k + 6) = run_lengths_nat (A381587_T (k + 5)).reverse ++ A381587_T (k + 5) := rfl
      have h_len : (A381587_T (k + 6)).length = (run_lengths_nat (A381587_T (k + 5)).reverse).length + (A381587_T (k + 5)).length := by
        rw [h_rec]
        simp
      have h_rg := R_growth (k + 5) (by omega)
      change 3 * (run_lengths_nat (A381587_T (k + 5)).reverse).length ≤ 2 * (run_lengths_nat (A381587_T (k + 6)).reverse).length at h_rg
      change (A381587_T (k + 6)).length ≤ 2 * (run_lengths_nat (A381587_T (k + 6)).reverse).length
      omega

private lemma L_growth (k : ℕ) : 2 * (A381587_T (k + 3)).length ≤ (A381587_T (k + 5)).length := by
  have h_rec5 : A381587_T (k + 5) = run_lengths_nat (A381587_T (k + 4)).reverse ++ A381587_T (k + 4) := rfl
  have h_rec4 : A381587_T (k + 4) = run_lengths_nat (A381587_T (k + 3)).reverse ++ A381587_T (k + 3) := rfl
  have h_len5 : (A381587_T (k + 5)).length = (run_lengths_nat (A381587_T (k + 4)).reverse).length + (run_lengths_nat (A381587_T (k + 3)).reverse).length + (A381587_T (k + 3)).length := by
    rw [h_rec5, h_rec4]
    simp
    omega
  have h_mono := A381587_T_R_mono k
  have h_le := L_le_two_R (k + 3) (by omega)
  omega

private lemma L_mul_le_growth (n j : ℕ) (hn : 3 ≤ n) (hj : 3 ≤ j) :
    (A381587_T n).length * (A381587_T j).length + (A381587_T (n + j)).length ≤ (A381587_T (n + j + 1)).length := by
  sorry

private lemma Fact1_fixed (n j : ℕ) (hn : 3 ≤ n) (hj : 3 ≤ j) :
    A381358 n * (A381587_T j).length ≤ (A381587_T (n + j)).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · omega
    · omega
    · omega
    · have h_growth := L_growth (j - 3)
      have h_mono : (A381587_T (j + 2)).length ≤ (A381587_T (3 + j)).length := by
        apply A381587_T_length_mono
        omega
      have h_eq : j - 3 + 5 = j + 2 := by omega
      have h_eq3 : j - 3 + 3 = j := by omega
      rw [h_eq3, h_eq] at h_growth
      have h_sum3 : A381358 3 = 2 := rfl
      change A381358 3 * (A381587_T j).length ≤ (A381587_T (3 + j)).length
      rw [h_sum3]
      omega
    · have h_rec := A381358_recurrence k
      have h_ih := ih (k + 3) (by omega) (by omega)
      change A381358 (k + 3) * (A381587_T j).length ≤ (A381587_T (k + 3 + j)).length at h_ih
      have h_growth := L_mul_le_growth (k + 3) j (by omega) hj
      have h_idx : k + 3 + j + 1 = k + 4 + j := by omega
      rw [h_idx] at h_growth
      have h_dist : (A381358 (k + 3) + (A381587_T (k + 3)).length) * (A381587_T j).length =
          A381358 (k + 3) * (A381587_T j).length + (A381587_T (k + 3)).length * (A381587_T j).length := by
        ring
      change A381358 (k + 4) * (A381587_T j).length ≤ (A381587_T (k + 4 + j)).length
      rw [h_rec, h_dist]
      omega
private lemma Fact2 (n : ℕ) (hn : 1 ≤ n) :
    A381358 n ≤ (A381587_T n).length + (A381587_T (n + 1)).length := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · omega
    · change A381358 1 ≤ (A381587_T 1).length + (A381587_T 2).length
      decide
    · change A381358 2 ≤ (A381587_T 2).length + (A381587_T 3).length
      decide
    · have h_T4 : (A381587_T 4).length = 2 := by
        change (run_lengths_nat [2] ++ [2]).length = 2
        unfold run_lengths_nat
        dsimp
        simp [takeWhile, drop]
        unfold run_lengths_nat
        rfl
      have h3 : A381358 3 = 2 := rfl
      have h3_len : (A381587_T 3).length = 1 := rfl
      change A381358 3 ≤ (A381587_T 3).length + (A381587_T 4).length
      omega
    · have h_rec := A381358_recurrence k
      have h_ih := ih (k + 3) (by omega) (by omega)
      change A381358 (k + 3) ≤ (A381587_T (k + 3)).length + (A381587_T (k + 4)).length at h_ih
      have h_growth := L_growth k
      change A381358 (k + 4) ≤ (A381587_T (k + 4)).length + (A381587_T (k + 5)).length
      omega

private lemma A381358_mul_le (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    A381358 n * A381358 m ≤ A381358 (n + m) := by
  by_cases hn3 : n < 3
  · interval_cases n
    · have h1 : A381358 1 = 1 := rfl
      rw [h1, one_mul]
      apply A381358_mono
      omega
    · have h2 : A381358 2 = 1 := rfl
      rw [h2, one_mul]
      apply A381358_mono
      omega
  by_cases hm3 : m < 3
  · interval_cases m
    · have h1 : A381358 1 = 1 := rfl
      rw [h1, mul_one]
      apply A381358_mono
      omega
    · have h2 : A381358 2 = 1 := rfl
      rw [h2, mul_one]
      apply A381358_mono
      omega
  have hn_ge : 3 ≤ n := by omega
  have hm_ge : 3 ≤ m := by omega
  clear hn hm hm3 hn3
  induction m, hm_ge using Nat.le_induction with
  | base =>
    have h_eq_3 : A381358 3 = 2 := rfl
    rw [h_eq_3, mul_comm]
    have h_sum := A381358_sum_range n 3 hn_ge
    have h_sum_3 : sum_range_nat (fun j => (A381587_T j).length) n 3 =
      (A381587_T n).length + (A381587_T (n + 1)).length + (A381587_T (n + 2)).length := by
      dsimp [sum_range_nat]
      omega
    rw [h_sum_3] at h_sum
    have h_fact2 := Fact2 n (by omega)
    omega
  | succ m hm ih =>
    have hm_ge_1 : 1 ≤ m := by omega
    have hm_ge_4 : 4 ≤ m + 1 := by omega
    have h_rec_m : A381358 (m + 1) = A381358 m + (A381587_T m).length := by
      let k := m - 3
      have h_eq : m + 1 = k + 4 := by omega
      have h_eq2 : m = k + 3 := by omega
      rw [h_eq, h_eq2, A381358_recurrence k]
    have h_rec_nm : A381358 (n + m + 1) = A381358 (n + m) + (A381587_T (n + m)).length := by
      let k := n + m - 3
      have h_eq : n + m + 1 = k + 4 := by omega
      have h_eq2 : n + m = k + 3 := by omega
      rw [h_eq, h_eq2, A381358_recurrence k]
    have h_nm_eq : n + (m + 1) = n + m + 1 := by omega
    rw [h_nm_eq, h_rec_m, h_rec_nm]
    rw [mul_add]
    have h_fact1 := Fact1_fixed n m hn_ge hm
    omega

private lemma u_seq_subadditive : Subadditive u_seq := by
  intro m n
  by_cases hm : m = 0
  · subst hm
    simp [u_seq]
  · by_cases hn : n = 0
    · subst hn
      simp [u_seq]
    · unfold u_seq
      have hmn : m + n ≠ 0 := by omega
      simp [hm, hn]
      have hm_pos : (A381358 m : ℝ) ≠ 0 := by
        have : 1 ≤ A381358 m := A381358_pos m (by omega)
        have h_real : (1 : ℝ) ≤ (A381358 m : ℝ) := by exact_mod_cast this
        linarith
      have hn_pos : (A381358 n : ℝ) ≠ 0 := by
        have : 1 ≤ A381358 n := A381358_pos n (by omega)
        have h_real : (1 : ℝ) ≤ (A381358 n : ℝ) := by exact_mod_cast this
        linarith
      have h1 : 0 < (A381358 m : ℝ) * (A381358 n : ℝ) := by
        have : 1 ≤ A381358 m := A381358_pos m (by omega)
        have : 1 ≤ A381358 n := A381358_pos n (by omega)
        positivity
      have h2 : ((A381358 m : ℝ) * (A381358 n : ℝ)) ≤ (A381358 (m + n) : ℝ) := by
        have h_mul := A381358_mul_le m n (by omega) (by omega)
        exact_mod_cast h_mul
      have h3 : Real.log (A381358 m) + Real.log (A381358 n) = Real.log (A381358 m * A381358 n) := by
        rw [Real.log_mul hm_pos hn_pos]
      have h4 : Real.log (A381358 m * A381358 n) ≤ Real.log (A381358 (m + n)) := Real.log_le_log h1 h2
      linarith

private lemma u_seq_bdd_below : BddBelow (Set.range (fun n : ℕ => u_seq n / n)) := by
  use - Real.log 2
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    simp [u_seq]
    have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · simp [u_seq, hn]
    rw [neg_div, neg_le_neg_iff]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (0 : ℝ) < A381358 n := by
      have : 1 ≤ A381358 n := A381358_pos n (by omega)
      exact_mod_cast this
    have h2 : (A381358 n : ℝ) ≤ 2 ^ n := by
      exact_mod_cast A381358_le_pow_two n
    have h3 := Real.log_le_log h1 h2
    rw [Real.log_pow 2 n] at h3
    rw [mul_comm] at h3
    exact h3

theorem A381358_limit_exists_draft :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  have h_sub := u_seq_subadditive
  have h_bdd := u_seq_bdd_below
  have h_lim := h_sub.tendsto_lim h_bdd
  have h_neg := Filter.Tendsto.neg h_lim
  have h_exp := Filter.Tendsto.rexp h_neg
  use Real.exp (- h_sub.lim)
  have h_eq_eq : (fun n : ℕ => Real.exp (- (u_seq n / n))) =ᶠ[Filter.atTop] (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro n hn
    have h_pos : 0 < (A381358 n : ℝ) := by
      have : 1 ≤ A381358 n := A381358_pos n hn
      have h_real : (1 : ℝ) ≤ (A381358 n : ℝ) := by exact_mod_cast this
      linarith
    rw [Real.rpow_def_of_pos h_pos]
    unfold u_seq
    have hn_ne : n ≠ 0 := by omega
    simp [hn_ne]
    ring
  exact Filter.Tendsto.congr' h_eq_eq h_exp

theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
  A381358_limit_exists_draft



