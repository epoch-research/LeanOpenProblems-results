import FormalConjectures.Util.ProblemImports
open List

namespace A381

/-- File's run-length function. -/
def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

/-- Clean run-length function with explicit current run state. -/
def rlAux : ℕ → ℕ → List ℕ → List ℕ
  | _, c, [] => [c]
  | v, c, x :: xs => if x = v then rlAux v (c+1) xs else c :: rlAux x 1 xs

def rl : List ℕ → List ℕ
  | [] => []
  | x :: xs => rlAux x 1 xs

@[simp] theorem rl_nil : rl [] = [] := rfl
@[simp] theorem rl_cons (x : ℕ) (xs : List ℕ) : rl (x :: xs) = rlAux x 1 xs := rfl
@[simp] theorem rlAux_nil (v c : ℕ) : rlAux v c [] = [c] := rfl

theorem rlAux_cons (v c x : ℕ) (xs : List ℕ) :
    rlAux v c (x :: xs) = if x = v then rlAux v (c+1) xs else c :: rlAux x 1 xs := rfl

/-- Key helper relating `rlAux` to `takeWhile`/`drop`. -/
theorem rlAux_eq (v c : ℕ) (l : List ℕ) :
    rlAux v c l = (c + (l.takeWhile (fun x => x = v)).length)
                  :: rl (l.drop (l.takeWhile (fun x => x = v)).length) := by
  induction l generalizing v c with
  | nil => simp
  | cons x xs ih =>
    rw [rlAux_cons]
    by_cases h : x = v
    · subst h
      simp only [takeWhile_cons, decide_true, if_true, length_cons, List.drop_succ_cons]
      rw [ih x (c+1)]
      congr 1
      omega
    · have hd : (decide (x = v)) = false := by simp [h]
      simp only [takeWhile_cons, hd, if_false, List.drop_zero, Nat.add_zero]
      rw [if_neg h]
      rfl

theorem run_lengths_nat_eq_rl (l : List ℕ) : run_lengths_nat l = rl l := by
  suffices H : ∀ n l, l.length = n → run_lengths_nat l = rl l from H l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    match l with
    | [] => rw [run_lengths_nat]; rfl
    | h :: t =>
      rw [run_lengths_nat]
      show ((h::t).takeWhile (fun x => x = h)).length
            :: run_lengths_nat ((h::t).drop ((h::t).takeWhile (fun x => x = h)).length)
          = rl (h :: t)
      rw [rl_cons, rlAux_eq h 1]
      have hk : ((h :: t).takeWhile (fun x => x = h)).length
              = 1 + (t.takeWhile (fun x => x = h)).length := by
        simp only [takeWhile_cons, decide_true, if_true, length_cons]; omega
      set k := ((h :: t).takeWhile (fun x => x = h)).length with hkdef
      have hkpos : 1 ≤ k := by rw [hk]; omega
      have hdrop : (h :: t).drop k = t.drop (t.takeWhile (fun x => x = h)).length := by
        rw [hk, Nat.add_comm, List.drop_succ_cons]
      have hlen : ((h :: t).drop k).length < n := by
        rw [List.length_drop, ← hl]
        simp only [List.length_cons]
        omega
      have hrec := ih ((h :: t).drop k).length hlen ((h :: t).drop k) rfl
      rw [hrec, hdrop, hk]

/-- Number of maximal runs, via adjacency. -/
def nruns : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | x :: y :: t => (if x = y then 0 else 1) + nruns (y :: t)

@[simp] theorem nruns_nil : nruns [] = 0 := rfl
@[simp] theorem nruns_single (x : ℕ) : nruns [x] = 1 := rfl
theorem nruns_cons2 (x y : ℕ) (t : List ℕ) :
    nruns (x :: y :: t) = (if x = y then 0 else 1) + nruns (y :: t) := rfl

/-- `rlAux` length equals `nruns` of `v :: l` started appropriately. -/
theorem rlAux_length (v c : ℕ) (l : List ℕ) :
    (rlAux v c l).length = nruns (v :: l) := by
  induction l generalizing v c with
  | nil => simp
  | cons x xs ih =>
    rw [rlAux_cons, nruns_cons2]
    by_cases h : x = v
    · subst h
      simp only [if_pos rfl, if_true, Nat.zero_add]
      rw [ih x (c+1)]
    · rw [if_neg h]
      have : (decide (v = x)) = false := by simp [Ne.symm h]
      simp only [List.length_cons, ih x 1]
      rw [if_neg (Ne.symm h)]
      omega

theorem nruns_eq_rl_length (l : List ℕ) : nruns l = (rl l).length := by
  cases l with
  | nil => simp
  | cons x xs => rw [rl_cons, rlAux_length]

/-- Merge formula for `nruns` under append (avoiding subtraction). -/
theorem nruns_append (X : List ℕ) (z : ℕ) (Y : List ℕ) :
    nruns (X ++ z :: Y) + (if X.getLast? = some z then 1 else 0)
      = nruns X + nruns (z :: Y) := by
  induction X with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.getLast?_singleton,
        nruns_single, Option.some.injEq]
      rw [nruns_cons2]
      split_ifs with h <;> omega
    | cons x' xs' =>
      rw [List.getLast?_cons_cons]
      rw [show (x :: x' :: xs') ++ z :: Y = x :: x' :: (xs' ++ z :: Y) from rfl, nruns_cons2,
          show x' :: (xs' ++ z :: Y) = (x' :: xs') ++ z :: Y from rfl,
          show nruns (x :: x' :: xs') = (if x = x' then 0 else 1) + nruns (x' :: xs') from
            nruns_cons2 x x' xs']
      generalize (if x = x' then 0 else 1) = A at ⊢
      generalize (if (x' :: xs').getLast? = some z then 1 else 0) = B at ih ⊢
      generalize nruns ((x' :: xs') ++ z :: Y) = P at ih ⊢
      omega

theorem nruns_reverse (l : List ℕ) : nruns l.reverse = nruns l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.reverse_cons]
    have := nruns_append xs.reverse x []
    rw [List.getLast?_reverse] at this
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [nruns_cons2]
      simp only [List.head?_cons] at this
      rw [ih] at this
      rw [nruns_single] at this
      by_cases h : x = y
      · simp only [h, if_pos rfl, if_true] at this ⊢
        omega
      · have h' : (some y = some x) = False := by simp [Ne.symm h]
        rw [if_neg h]
        simp only [h', if_false] at this
        omega

theorem nruns_le_length : ∀ l : List ℕ, nruns l ≤ l.length
  | [] => by simp
  | [_] => by simp
  | x :: y :: t => by
      rw [nruns_cons2]
      have ih := nruns_le_length (y :: t)
      simp only [List.length_cons] at *
      split_ifs <;> omega

/-- The triangle sequence (copy of file's definition). -/
def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

theorem T_succ (n : ℕ) (hn : 3 ≤ n) :
    A381587_T (n+1) = run_lengths_nat (A381587_T n).reverse ++ A381587_T n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rfl

theorem rlAux_sum (v c : ℕ) (l : List ℕ) : (rlAux v c l).sum = c + l.length := by
  induction l generalizing v c with
  | nil => simp
  | cons x xs ih =>
    rw [rlAux_cons]
    by_cases h : x = v
    · subst h; rw [if_pos rfl, ih x (c+1)]; simp; omega
    · rw [if_neg h]; simp only [List.sum_cons, ih x 1, List.length_cons]; omega

theorem rl_sum (l : List ℕ) : (rl l).sum = l.length := by
  cases l with
  | nil => simp
  | cons x xs => rw [rl_cons, rlAux_sum]; simp; omega

theorem rlAux_ne_nil (v c : ℕ) (l : List ℕ) : rlAux v c l ≠ [] := by
  induction l generalizing v c with
  | nil => simp [rlAux]
  | cons x xs ih =>
    rw [rlAux_cons]; split
    · exact ih v (c+1)
    · simp

theorem getLastD_indep (l : List ℕ) (d d' : ℕ) (h : l ≠ []) :
    l.getLastD d = l.getLastD d' := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rw [List.getLastD_cons, List.getLastD_cons]

theorem rlAux_append (v c : ℕ) (xs ys : List ℕ) :
    rlAux v c (xs ++ ys) =
      (rlAux v c xs).dropLast ++ rlAux (xs.getLastD v) ((rlAux v c xs).getLastD 0) ys := by
  induction xs generalizing v c with
  | nil => simp [rlAux]
  | cons x xs' ih =>
    by_cases h : x = v
    · subst h
      rw [List.cons_append, rlAux_cons, if_pos rfl, ih x (c+1), rlAux_cons, if_pos rfl]
      simp only [List.getLastD_cons]
    · rw [List.cons_append, rlAux_cons, if_neg h, ih x 1, rlAux_cons, if_neg h]
      have hne : rlAux x 1 xs' ≠ [] := rlAux_ne_nil x 1 xs'
      rw [List.dropLast_cons_of_ne_nil hne]
      simp only [List.getLastD_cons, List.cons_append]
      rw [getLastD_indep (rlAux x 1 xs') c 0 hne]

theorem dropLast_getLastD (l : List ℕ) (h : l ≠ []) :
    l.dropLast ++ [l.getLastD 0] = l := by
  rw [show l.getLastD 0 = l.getLast h from by
    rw [getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]; rfl]
  exact List.dropLast_concat_getLast h

theorem getLastD_reverse (l : List ℕ) (d : ℕ) : (reverse l).getLastD d = l.headD d := by
  rw [getLastD_eq_getLast?, getLast?_reverse, headD_eq_head?_getD]

theorem rlAux_succ (v c : ℕ) (l : List ℕ) :
    rlAux v (c+1) l = ((rlAux v c l).headD 0 + 1) :: (rlAux v c l).tail := by
  rw [rlAux_eq v c l, rlAux_eq v (c+1) l]
  simp only [List.headD_cons, List.tail_cons]
  congr 1; omega

/-- Run-length of a list with a prepended element. -/
theorem rl_cons_formula (a : ℕ) (l : List ℕ) :
    rl (a :: l) =
      if l = [] then [1]
      else if a = l.headD 0 then ((rl l).headD 0 + 1) :: (rl l).tail
      else 1 :: rl l := by
  cases l with
  | nil => rfl
  | cons b l'' =>
    rw [if_neg (List.cons_ne_nil b l'')]
    simp only [List.headD_cons]
    rw [show rl (b :: l'') = rlAux b 1 l'' from rl_cons b l'']
    rw [rl_cons, rlAux_cons]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, if_pos rfl, rlAux_succ]
    · rw [if_neg (Ne.symm hab), if_neg hab]

/-- Run-length of a list with an appended element. -/
theorem rl_snoc_formula (l : List ℕ) (a : ℕ) (hl : l ≠ []) :
    rl (l ++ [a]) =
      if a = l.getLastD 0 then (rl l).dropLast ++ [(rl l).getLastD 0 + 1]
      else rl l ++ [1] := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, l = x :: xs := by
    cases l with
    | nil => exact absurd rfl hl
    | cons x xs => exact ⟨x, xs, rfl⟩
  rw [List.cons_append, rl_cons, rlAux_append]
  rw [show rlAux x 1 xs = rl (x :: xs) from rfl]
  rw [show (x :: xs).getLastD 0 = xs.getLastD x from by rw [List.getLastD_cons]]
  rw [rlAux_cons]
  by_cases h : a = xs.getLastD x
  · rw [if_pos h, if_pos h, rlAux_nil]
  · rw [if_neg h, if_neg h, rlAux_nil]
    rw [show (rl (x :: xs)).getLastD 0 :: [(1:ℕ)]
          = [(rl (x :: xs)).getLastD 0] ++ [1] from rfl, ← List.append_assoc,
        dropLast_getLastD (rl (x :: xs)) (by rw [rl_cons]; exact rlAux_ne_nil x 1 xs)]

/-- Run-length commutes with reverse. -/
theorem rl_reverse (l : List ℕ) : rl (reverse l) = reverse (rl l) := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    rw [reverse_cons]
    cases l' with
    | nil => rfl
    | cons b l'' =>
      have hrev_ne : reverse (b :: l'') ≠ [] := by simp
      rw [rl_snoc_formula (reverse (b :: l'')) a hrev_ne, ih,
          getLastD_reverse, rl_cons_formula a (b :: l'')]
      rw [if_neg (List.cons_ne_nil b l'')]
      simp only [List.headD_cons]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, dropLast_reverse, getLastD_reverse, reverse_cons]
      · rw [if_neg hab, if_neg hab, reverse_cons]

/-- Continuing run-length encoding into a block that starts with the current value. -/
theorem rlAux_merge (v c : ℕ) (B' : List ℕ) :
    rlAux v c (v :: B') = (c + (rl (v :: B')).headD 0) :: (rl (v :: B')).tail := by
  rw [rlAux_cons, if_pos rfl, rl_cons, rlAux_eq v (c+1) B', rlAux_eq v 1 B']
  simp only [List.headD_cons, List.tail_cons]
  congr 1; omega

/-- Merge append: when `last A = head B`, the boundary run merges. -/
theorem rl_merge_append (A B : List ℕ) (hA : A ≠ []) (hB : B ≠ [])
    (hbnd : A.getLastD 0 = B.headD 0) :
    rl (A ++ B) =
      (rl A).dropLast ++ ((rl A).getLastD 0 + (rl B).headD 0) :: (rl B).tail := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, A = x :: xs := by
    cases A with
    | nil => exact absurd rfl hA
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨bh, B', rfl⟩ : ∃ bh B', B = bh :: B' := by
    cases B with
    | nil => exact absurd rfl hB
    | cons bh B' => exact ⟨bh, B', rfl⟩
  have hxb : xs.getLastD x = bh := by
    have := hbnd
    rw [List.getLastD_cons, List.headD_cons] at this
    exact this
  rw [List.cons_append, rl_cons, rlAux_append]
  rw [show rlAux x 1 xs = rl (x :: xs) from rfl, hxb]
  rw [rlAux_merge bh ((rl (x :: xs)).getLastD 0) B']

/-- No-merge append: when `last A ≠ head B`, the run-lengths concatenate. -/
theorem rl_no_merge_append (A B : List ℕ) (hA : A ≠ []) (hB : B ≠ [])
    (hbnd : A.getLastD 0 ≠ B.headD 0) :
    rl (A ++ B) = rl A ++ rl B := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, A = x :: xs := by
    cases A with
    | nil => exact absurd rfl hA
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨bh, B', rfl⟩ : ∃ bh B', B = bh :: B' := by
    cases B with
    | nil => exact absurd rfl hB
    | cons bh B' => exact ⟨bh, B', rfl⟩
  have hxb : xs.getLastD x ≠ bh := by
    intro h; apply hbnd; rw [List.getLastD_cons, List.headD_cons]; exact h
  rw [List.cons_append, rl_cons, rlAux_append]
  rw [show rlAux x 1 xs = rl (x :: xs) from rfl]
  rw [rlAux_cons, if_neg (Ne.symm hxb)]
  rw [show rlAux bh 1 B' = rl (bh :: B') from rfl]
  rw [List.append_cons, dropLast_getLastD (rl (x :: xs))
        (by rw [rl_cons]; exact rlAux_ne_nil x 1 xs)]

/-- Changing the first element (still distinct from the second) doesn't change run-lengths. -/
theorem rl_first_insensitive (a b : ℕ) (rest : List ℕ) (hrest : rest ≠ [])
    (ha : a ≠ rest.headD 0) (hb : b ≠ rest.headD 0) :
    rl (a :: rest) = rl (b :: rest) := by
  rw [rl_cons_formula a rest, rl_cons_formula b rest, if_neg hrest, if_neg hrest,
      if_neg ha, if_neg hb]

/-- `rl` of a list with last element replaced (still a singleton run) is unchanged. -/
theorem rl_last_insensitive (l : List ℕ) (w : ℕ) (hl : l.dropLast ≠ [])
    (h1 : (l.dropLast).getLastD 0 ≠ l.getLastD 0) (h2 : (l.dropLast).getLastD 0 ≠ w) :
    rl (l.dropLast ++ [w]) = rl l := by
  have hlne : l ≠ [] := by
    intro h; rw [h] at hl; simp at hl
  have key : rl l = rl (l.dropLast ++ [l.getLastD 0]) := by
    rw [dropLast_getLastD l hlne]
  rw [key, rl_snoc_formula l.dropLast (l.getLastD 0) hl, rl_snoc_formula l.dropLast w hl]
  rw [if_neg (show ¬ (l.getLastD 0 = l.dropLast.getLastD 0) from fun h => h1 h.symm)]
  rw [if_neg (show ¬ (w = l.dropLast.getLastD 0) from fun h => h2 h.symm)]

/-- Suffix-preservation: `rl (A ++ B)` ends with `(rl B).tail`. -/
theorem rl_suffix (A B : List ℕ) (hB : B ≠ []) :
    ∃ pre, rl (A ++ B) = pre ++ (rl B).tail := by
  cases A with
  | nil =>
    refine ⟨[(rl B).headD 0], ?_⟩
    obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
      cases B with
      | nil => exact absurd rfl hB
      | cons b B' => exact ⟨b, B', rfl⟩
    simp only [List.nil_append, rl_cons]
    rw [show rlAux b 1 B' = rl (b :: B') from rfl]
    conv_lhs => rw [show rl (b :: B') = (rl (b :: B')).headD 0 :: (rl (b :: B')).tail from by
      have : rl (b :: B') ≠ [] := by rw [rl_cons]; exact rlAux_ne_nil b 1 B'
      cases h : rl (b :: B') with
      | nil => exact absurd h this
      | cons x xs => simp]
    rfl
  | cons x xs =>
    have hA : (x :: xs) ≠ [] := List.cons_ne_nil x xs
    by_cases hbnd : (x :: xs).getLastD 0 = B.headD 0
    · rw [rl_merge_append (x :: xs) B hA hB hbnd]
      exact ⟨(rl (x :: xs)).dropLast ++ [(rl (x :: xs)).getLastD 0 + (rl B).headD 0], by
        rw [List.append_cons]⟩
    · rw [rl_no_merge_append (x :: xs) B hA hB hbnd]
      refine ⟨rl (x :: xs) ++ [(rl B).headD 0], ?_⟩
      obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
        cases B with
        | nil => exact absurd rfl hB
        | cons b B' => exact ⟨b, B', rfl⟩
      rw [List.append_assoc]
      congr 1
      rw [show rl (b :: B') = (rl (b :: B')).headD 0 :: (rl (b :: B')).tail from by
        have : rl (b :: B') ≠ [] := by rw [rl_cons]; exact rlAux_ne_nil b 1 B'
        cases h : rl (b :: B') with
        | nil => exact absurd h this
        | cons p ps => simp]
      rfl

/-- If first two elements differ, `rl l.tail = (rl l).tail`. -/
theorem rl_tail_ne (a : ℕ) (rest : List ℕ) (hrest : rest ≠ [])
    (h : a ≠ rest.headD 0) : rl rest = (rl (a :: rest)).tail := by
  rw [rl_cons_formula a rest, if_neg hrest, if_neg h, List.tail_cons]

/-- If first two elements agree, `rl l.tail = (head(rl l) - 1) :: (rl l).tail`. -/
theorem rl_tail_eq (a : ℕ) (rest : List ℕ) (hrest : rest ≠ [])
    (h : a = rest.headD 0) :
    rl rest = ((rl (a :: rest)).headD 0 - 1) :: (rl (a :: rest)).tail := by
  rw [rl_cons_formula a rest, if_neg hrest, if_pos h, List.headD_cons, List.tail_cons]
  have hrne : rl rest ≠ [] := by
    obtain ⟨b, r', rfl⟩ : ∃ b r', rest = b :: r' := by
      cases rest with
      | nil => exact absurd rfl hrest
      | cons b r' => exact ⟨b, r', rfl⟩
    rw [rl_cons]; exact rlAux_ne_nil b 1 r'
  conv_lhs => rw [show rl rest = (rl rest).headD 0 :: (rl rest).tail from by
    cases h2 : rl rest with
    | nil => exact absurd h2 hrne
    | cons p ps => simp]
  rw [Nat.add_sub_cancel]

/-- General level-1 recursion (merge form). -/
theorem genR1 (u t : List ℕ) (hu : u ≠ []) (ht : t ≠ [])
    (hbnd : u.headD 0 = t.headD 0) :
    rl (reverse u ++ t) =
      reverse ((rl u).tail) ++ ((rl u).headD 0 + (rl t).headD 0) :: (rl t).tail := by
  have hru : reverse u ≠ [] := by simp [hu]
  rw [rl_merge_append (reverse u) t hru ht
        (by rw [getLastD_reverse]; exact hbnd),
      rl_reverse, dropLast_reverse, getLastD_reverse]

theorem getLastD_append_right (pre M : List ℕ) (h : M ≠ []) :
    (pre ++ M).getLastD 0 = M.getLastD 0 := by
  rw [getLastD_eq_getLast?, getLast?_append_of_ne_nil pre h, ← getLastD_eq_getLast?]

theorem tail_getLastD (l : List ℕ) (h : 2 ≤ l.length) :
    l.tail.getLastD 0 = l.getLastD 0 := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with
    | nil => simp at h
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hr : rest ≠ [] := by
    simp only [List.length_cons] at h
    intro hc; rw [hc] at h; simp at h
  rw [List.tail_cons, List.getLastD_cons, getLastD_indep rest a 0 hr]

theorem dropLast_ne_nil (M : List ℕ) (h : 2 ≤ M.length) : M.dropLast ≠ [] := by
  intro hc
  have : M.dropLast.length = 0 := by rw [hc]; rfl
  rw [List.length_dropLast] at this; omega

theorem dropLast_getLastD_append_right (pre M : List ℕ) (h : 2 ≤ M.length) :
    (pre ++ M).dropLast.getLastD 0 = M.dropLast.getLastD 0 := by
  have hM : M ≠ [] := by rintro rfl; simp at h
  rw [dropLast_append_of_ne_nil hM, getLastD_append_right pre M.dropLast (dropLast_ne_nil M h)]

theorem tail_dropLast_getLastD (l : List ℕ) (h : 3 ≤ l.length) :
    l.tail.dropLast.getLastD 0 = l.dropLast.getLastD 0 := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with
    | nil => simp at h
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hr : rest ≠ [] := by
    simp only [List.length_cons] at h; intro hc; rw [hc] at h; simp at h
  have hrd : rest.dropLast ≠ [] := dropLast_ne_nil rest (by simp only [List.length_cons] at h; omega)
  rw [List.tail_cons, List.dropLast_cons_of_ne_nil hr, List.getLastD_cons,
      getLastD_indep rest.dropLast a 0 hrd]

/-- The triangle row and its successive run-length transforms. -/
def Tt (n : ℕ) : List ℕ := A381587_T n
def ss (n : ℕ) : List ℕ := rl (Tt n)
def ss2 (n : ℕ) : List ℕ := rl (ss n)
def ss3 (n : ℕ) : List ℕ := rl (ss2 n)

theorem ss_def (n : ℕ) : ss n = rl (Tt n) := rfl
theorem ss2_def (n : ℕ) : ss2 n = rl (ss n) := rfl
theorem ss3_def (n : ℕ) : ss3 n = rl (ss2 n) := rfl

theorem Tt_succ (n : ℕ) (hn : 3 ≤ n) : Tt (n+1) = reverse (ss n) ++ Tt n := by
  rw [Tt, T_succ n hn, run_lengths_nat_eq_rl, rl_reverse]; rfl

/-- Level-1 step: structure of `ss (n+1)`. -/
theorem step_ss (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ []) :
    ss (n+1) =
      reverse ((ss2 n).tail) ++ ((ss2 n).headD 0 + (ss n).headD 0) :: (ss n).tail := by
  rw [show ss (n+1) = rl (Tt (n+1)) from rfl, Tt_succ n hn,
      genR1 (ss n) (Tt n) hsn htn hbnd, ← ss2_def, ← ss_def]

/-- Level-2 step: structure of `ss2 (n+1)`. -/
theorem step_ss2 (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1)
    (hs2_hd : 3 ≤ (ss2 n).headD 0) (hs2_h2 : (ss2 n).tail.headD 0 = 1)
    (hs2ne : ss2 n ≠ []) (hs2tne : (ss2 n).tail ≠ []) (hstne : (ss n).tail ≠ []) :
    ss2 (n+1) =
      reverse ((ss3 n).tail) ++ 1 :: ((ss2 n).headD 0 - 1) :: (ss2 n).tail := by
  rw [show ss2 (n+1) = rl (ss (n+1)) from rfl, step_ss n hn hbnd hsn htn, hs_hd]
  -- now: rl (reverse ((ss2 n).tail) ++ ((ss2 n).headD 0 + 1) :: (ss n).tail)
  have hrevP : reverse ((ss2 n).tail) ≠ [] := by simp [hs2tne]
  have hBne : ((ss2 n).headD 0 + 1) :: (ss n).tail ≠ [] := by simp
  have hbnd2 : (reverse ((ss2 n).tail)).getLastD 0 ≠
      (((ss2 n).headD 0 + 1) :: (ss n).tail).headD 0 := by
    rw [getLastD_reverse, List.headD_cons, hs2_h2]; omega
  rw [rl_no_merge_append _ _ hrevP hBne hbnd2, rl_reverse]
  -- rl ((ss2 n).tail) = (ss3 n).tail
  have hsplit : (ss2 n).headD 0 :: (ss2 n).tail = ss2 n := by
    obtain ⟨a, l, hal⟩ : ∃ a l, ss2 n = a :: l := by
      cases h : ss2 n with
      | nil => exact absurd h hs2ne
      | cons a l => exact ⟨a, l, rfl⟩
    rw [hal]; simp
  have htailP : rl ((ss2 n).tail) = (ss3 n).tail := by
    rw [rl_tail_ne ((ss2 n).headD 0) ((ss2 n).tail) hs2tne (by rw [hs2_h2]; omega),
        hsplit, ← ss3_def]
  rw [htailP]
  -- rl (((ss2 n).headD 0 + 1) :: (ss n).tail) = 1 :: rl ((ss n).tail)
  rw [rl_cons_formula ((ss2 n).headD 0 + 1) ((ss n).tail), if_neg hstne,
      if_neg (show ¬ ((ss2 n).headD 0 + 1 = ((ss n).tail).headD 0) by rw [hs_h2]; omega)]
  -- rl ((ss n).tail) = ((ss2 n).headD 0 - 1) :: (ss2 n).tail
  have hsplits : (ss n).headD 0 :: (ss n).tail = ss n := by
    obtain ⟨a, l, hal⟩ : ∃ a l, ss n = a :: l := by
      cases h : ss n with
      | nil => exact absurd h hsn
      | cons a l => exact ⟨a, l, rfl⟩
    rw [hal]; simp
  have htails : rl ((ss n).tail) = ((ss2 n).headD 0 - 1) :: (ss2 n).tail := by
    rw [rl_tail_eq ((ss n).headD 0) ((ss n).tail) hstne (by rw [hs_hd, hs_h2]),
        hsplits, ← ss2_def]
  rw [htails]

/-- Helper: split a nonempty list as head :: tail. -/
theorem head_cons_tail (l : List ℕ) (h : l ≠ []) : l.headD 0 :: l.tail = l := by
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => exact absurd rfl h
    | cons a t => exact ⟨a, t, rfl⟩
  simp

/-- Level-3 step: structure of `ss3 (n+1)`, using the level-4 self-similarity. -/
theorem step_ss3 (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1)
    (hs2_hd : 3 ≤ (ss2 n).headD 0) (hs2_h2 : (ss2 n).tail.headD 0 = 1)
    (hs2ne : ss2 n ≠ []) (hs2tne : (ss2 n).tail ≠ []) (hstne : (ss n).tail ≠ [])
    (hs3_hd : (ss3 n).headD 0 = 1) (hs3_h2 : (ss3 n).tail.headD 0 = 3)
    (hs3tne : (ss3 n).tail ≠ [])
    (hss4 : rl (ss3 n) = ss (n-4)) :
    ss3 (n+1) = reverse ((ss (n-4)).tail) ++ 1 :: ss3 n := by
  rw [show ss3 (n+1) = rl (ss2 (n+1)) from rfl,
      step_ss2 n hn hbnd hsn htn hs_hd hs_h2 hs2_hd hs2_h2 hs2ne hs2tne hstne]
  have hrevX3 : reverse ((ss3 n).tail) ≠ [] := by simp [hs3tne]
  have hB3ne : (1 : ℕ) :: ((ss2 n).headD 0 - 1) :: (ss2 n).tail ≠ [] := by simp
  have hbnd3 : (reverse ((ss3 n).tail)).getLastD 0 ≠
      ((1 : ℕ) :: ((ss2 n).headD 0 - 1) :: (ss2 n).tail).headD 0 := by
    rw [getLastD_reverse, List.headD_cons, hs3_h2]; omega
  rw [rl_no_merge_append (reverse ((ss3 n).tail))
        ((1 : ℕ) :: ((ss2 n).headD 0 - 1) :: (ss2 n).tail) hrevX3 hB3ne hbnd3, rl_reverse]
  have htailX3 : rl ((ss3 n).tail) = (ss (n-4)).tail := by
    rw [rl_tail_ne ((ss3 n).headD 0) ((ss3 n).tail) hs3tne (by rw [hs3_hd, hs3_h2]; omega),
        head_cons_tail (ss3 n) (by intro h; rw [h] at hs3tne; simp at hs3tne), hss4]
  rw [htailX3]
  rw [rl_cons_formula 1 (((ss2 n).headD 0 - 1) :: (ss2 n).tail), if_neg (by simp),
      if_neg (show ¬ ((1:ℕ) = (((ss2 n).headD 0 - 1) :: (ss2 n).tail).headD 0) by
        rw [List.headD_cons]; omega)]
  have hfirst : rl (((ss2 n).headD 0 - 1) :: (ss2 n).tail) = ss3 n := by
    rw [rl_first_insensitive ((ss2 n).headD 0 - 1) ((ss2 n).headD 0) ((ss2 n).tail) hs2tne
          (by rw [hs2_h2]; omega) (by rw [hs2_h2]; omega),
        head_cons_tail (ss2 n) hs2ne, ← ss3_def]
  rw [hfirst]

/-- Level-4 self-similarity from the word identity `W`. -/
theorem ss4_eq (n m : ℕ) (hW : ss3 n = (Tt m).dropLast ++ [6])
    (hTm_lst : (Tt m).getLastD 0 = 2) (hTm_l2 : (Tt m).dropLast.getLastD 0 = 1)
    (hTm_len : 2 ≤ (Tt m).length) :
    rl (ss3 n) = ss m := by
  rw [hW, rl_last_insensitive (Tt m) 6 (dropLast_ne_nil (Tt m) hTm_len)
        (by rw [hTm_l2, hTm_lst]; omega) (by rw [hTm_l2]; omega)]
  rfl

/-- The word identity propagates: `W (n+1)` from the structure of `ss3 (n+1)` and `W n`. -/
theorem step_W (n : ℕ) (hn7 : 7 ≤ n)
    (hss3succ : ss3 (n+1) = reverse ((ss (n-4)).tail) ++ 1 :: ss3 n)
    (hWn : ss3 n = (Tt (n-4)).dropLast ++ [6])
    (hsn4_hd : (ss (n-4)).headD 0 = 1) (hsn4 : ss (n-4) ≠ []) (htn4 : Tt (n-4) ≠ []) :
    ss3 (n+1) = (Tt (n+1-4)).dropLast ++ [6] := by
  rw [hss3succ]
  have he : n + 1 - 4 = (n-4) + 1 := by omega
  rw [he, Tt_succ (n-4) (by omega), dropLast_append_of_ne_nil htn4, List.append_assoc, ← hWn]
  have hrev : reverse (ss (n-4)) = reverse ((ss (n-4)).tail) ++ [1] := by
    conv_lhs => rw [← head_cons_tail (ss (n-4)) hsn4]
    rw [hsn4_hd, reverse_cons]
  rw [hrev, List.append_assoc, List.singleton_append]

theorem headD_append_left (A B : List ℕ) (h : A ≠ []) : (A ++ B).headD 0 = A.headD 0 := by
  obtain ⟨a, A', rfl⟩ : ∃ a A', A = a :: A' := by
    cases A with | nil => exact absurd rfl h | cons a A' => exact ⟨a, A', rfl⟩
  rfl

theorem tail_append_left (A B : List ℕ) (h : A ≠ []) : (A ++ B).tail = A.tail ++ B := by
  obtain ⟨a, A', rfl⟩ : ∃ a A', A = a :: A' := by
    cases A with | nil => exact absurd rfl h | cons a A' => exact ⟨a, A', rfl⟩
  rfl

theorem dropLast_headD (l : List ℕ) (h : 2 ≤ l.length) : l.dropLast.headD 0 = l.headD 0 := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with | nil => simp at h | cons a rest => exact ⟨a, rest, rfl⟩
  have hr : rest ≠ [] := by
    simp only [List.length_cons] at h; intro hc; rw [hc] at h; simp at h
  rw [List.dropLast_cons_of_ne_nil hr]; rfl

theorem dropLast_tail_headD (l : List ℕ) (h : 3 ≤ l.length) :
    l.dropLast.tail.headD 0 = l.tail.headD 0 := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with | nil => simp at h | cons a rest => exact ⟨a, rest, rfl⟩
  have hr : rest ≠ [] := by
    simp only [List.length_cons] at h; intro hc; rw [hc] at h; simp at h
  rw [List.dropLast_cons_of_ne_nil hr, List.tail_cons, List.tail_cons]
  exact dropLast_headD rest (by simp only [List.length_cons] at h; omega)

/-- All boundary facts of `ss3 n` derived from the word identity. -/
theorem ss3_facts (n m : ℕ) (hW : ss3 n = (Tt m).dropLast ++ [6])
    (hT_hd : (Tt m).headD 0 = 1) (hT_h2 : (Tt m).tail.headD 0 = 3)
    (hT_l2 : (Tt m).dropLast.getLastD 0 = 1) (hT_len : 3 ≤ (Tt m).length) :
    (ss3 n).headD 0 = 1 ∧ (ss3 n).tail.headD 0 = 3 ∧
    (ss3 n).getLastD 0 = 6 ∧ (ss3 n).dropLast.getLastD 0 = 1 ∧
    (ss3 n).tail ≠ [] ∧ 3 ≤ (ss3 n).length := by
  have hdlne : (Tt m).dropLast ≠ [] := dropLast_ne_nil (Tt m) (by omega)
  have hdltailne : (Tt m).dropLast.tail ≠ [] := by
    intro hc
    have := congrArg List.length hc
    rw [List.length_tail, List.length_dropLast] at this
    simp only [List.length_nil] at this; omega
  have hlen : 3 ≤ (ss3 n).length := by
    rw [hW, List.length_append, List.length_dropLast]
    simp only [List.length_cons, List.length_nil]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, hlen⟩
  · rw [hW, headD_append_left _ _ hdlne, dropLast_headD (Tt m) (by omega), hT_hd]
  · rw [hW, tail_append_left _ _ hdlne, headD_append_left _ _ hdltailne,
        dropLast_tail_headD (Tt m) hT_len, hT_h2]
  · rw [hW, getLastD_append_right _ [6] (by simp)]; rfl
  · rw [hW, dropLast_concat, hT_l2]
  · intro hc
    have := congrArg List.length hc
    rw [List.length_tail] at this
    simp only [List.length_nil] at this; omega

theorem tail_ne_nil (l : List ℕ) (h : 2 ≤ l.length) : l.tail ≠ [] := by
  intro hc; have := congrArg List.length hc
  rw [List.length_tail] at this; simp only [List.length_nil] at this; omega

/-- `ss (n+1)` ends with `(ss n).tail`. -/
theorem ss_suffix (n : ℕ) (hn : 3 ≤ n) (htn : Tt n ≠ []) :
    ∃ pre, ss (n+1) = pre ++ (ss n).tail := by
  rw [show ss (n+1) = rl (Tt (n+1)) from rfl, Tt_succ n hn]
  obtain ⟨pre, hpre⟩ := rl_suffix (reverse (ss n)) (Tt n) htn
  exact ⟨pre, hpre⟩

theorem Tt_suffix_facts (n : ℕ) (hn : 3 ≤ n) (htn : Tt n ≠ []) (hlen : 2 ≤ (Tt n).length) :
    (Tt (n+1)).getLastD 0 = (Tt n).getLastD 0 ∧
    (Tt (n+1)).dropLast.getLastD 0 = (Tt n).dropLast.getLastD 0 := by
  rw [Tt_succ n hn]
  exact ⟨getLastD_append_right _ (Tt n) htn, dropLast_getLastD_append_right _ (Tt n) hlen⟩

theorem ss_suffix_facts (n : ℕ) (hn : 3 ≤ n) (htn : Tt n ≠ []) (hslen : 3 ≤ (ss n).length) :
    (ss (n+1)).getLastD 0 = (ss n).getLastD 0 ∧
    (ss (n+1)).dropLast.getLastD 0 = (ss n).dropLast.getLastD 0 := by
  obtain ⟨pre, hpre⟩ := ss_suffix n hn htn
  have hM : (ss n).tail ≠ [] := tail_ne_nil (ss n) (by omega)
  have htail2 : 2 ≤ (ss n).tail.length := by rw [List.length_tail]; omega
  exact ⟨by rw [hpre, getLastD_append_right pre _ hM, tail_getLastD (ss n) (by omega)],
        by rw [hpre, dropLast_getLastD_append_right pre _ htail2,
              tail_dropLast_getLastD (ss n) (by omega)]⟩

/-- `ss2 (n+1)` ends with `(ss2 n).tail`. -/
theorem ss2_suffix (n : ℕ) (hn : 3 ≤ n) (htn : Tt n ≠ [])
    (hsn : ss n ≠ []) (hstne : (ss n).tail ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1) :
    ∃ pre, ss2 (n+1) = pre ++ (ss2 n).tail := by
  obtain ⟨q, hq⟩ := ss_suffix n hn htn
  rw [show ss2 (n+1) = rl (ss (n+1)) from rfl, hq]
  obtain ⟨pre, hpre⟩ := rl_suffix q ((ss n).tail) hstne
  refine ⟨pre, ?_⟩
  rw [hpre]
  have htails : rl ((ss n).tail) = ((ss2 n).headD 0 - 1) :: (ss2 n).tail := by
    rw [rl_tail_eq ((ss n).headD 0) ((ss n).tail) hstne (by rw [hs_hd, hs_h2]),
        head_cons_tail (ss n) hsn, ← ss2_def]
  rw [htails, List.tail_cons]

theorem ss2_suffix_facts (n : ℕ) (hn : 3 ≤ n) (htn : Tt n ≠ [])
    (hsn : ss n ≠ []) (hstne : (ss n).tail ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1)
    (hs2len : 3 ≤ (ss2 n).length) :
    (ss2 (n+1)).getLastD 0 = (ss2 n).getLastD 0 ∧
    (ss2 (n+1)).dropLast.getLastD 0 = (ss2 n).dropLast.getLastD 0 := by
  obtain ⟨pre, hpre⟩ := ss2_suffix n hn htn hsn hstne hs_hd hs_h2
  have hM : (ss2 n).tail ≠ [] := tail_ne_nil (ss2 n) (by omega)
  have htail2 : 2 ≤ (ss2 n).tail.length := by rw [List.length_tail]; omega
  exact ⟨by rw [hpre, getLastD_append_right pre _ hM, tail_getLastD (ss2 n) (by omega)],
        by rw [hpre, dropLast_getLastD_append_right pre _ htail2,
              tail_dropLast_getLastD (ss2 n) (by omega)]⟩

theorem headD_reverse (l : List ℕ) : (reverse l).headD 0 = l.getLastD 0 := by
  rw [headD_eq_head?_getD, head?_reverse, ← getLastD_eq_getLast?]

theorem Tt_head_fact (n : ℕ) (hn : 3 ≤ n) (hsn : ss n ≠ []) :
    (Tt (n+1)).headD 0 = (ss n).getLastD 0 := by
  rw [Tt_succ n hn, headD_append_left _ _ (by simp [hsn]), headD_reverse]

theorem ss_head_facts (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (hs2tne : (ss2 n).tail ≠ []) (hs2len : 3 ≤ (ss2 n).length) :
    (ss (n+1)).headD 0 = (ss2 n).getLastD 0 ∧
    (ss (n+1)).tail.headD 0 = (ss2 n).dropLast.getLastD 0 := by
  rw [step_ss n hn hbnd hsn htn]
  have hA : reverse ((ss2 n).tail) ≠ [] := by simp [hs2tne]
  have hAtne : (reverse ((ss2 n).tail)).tail ≠ [] := by
    rw [tail_reverse]; simp; exact dropLast_ne_nil _ (by rw [List.length_tail]; omega)
  constructor
  · rw [headD_append_left _ _ hA, headD_reverse, tail_getLastD (ss2 n) (by omega)]
  · rw [tail_append_left _ _ hA, headD_append_left _ _ hAtne, tail_reverse, headD_reverse,
        tail_dropLast_getLastD (ss2 n) (by omega)]

theorem ss2_head_facts (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1)
    (hs2_hd : 3 ≤ (ss2 n).headD 0) (hs2_h2 : (ss2 n).tail.headD 0 = 1)
    (hs2ne : ss2 n ≠ []) (hs2tne : (ss2 n).tail ≠ []) (hstne : (ss n).tail ≠ [])
    (hs3tne : (ss3 n).tail ≠ []) (hs3len : 3 ≤ (ss3 n).length) :
    (ss2 (n+1)).headD 0 = (ss3 n).getLastD 0 ∧
    (ss2 (n+1)).tail.headD 0 = (ss3 n).dropLast.getLastD 0 := by
  rw [step_ss2 n hn hbnd hsn htn hs_hd hs_h2 hs2_hd hs2_h2 hs2ne hs2tne hstne]
  have hA : reverse ((ss3 n).tail) ≠ [] := by simp [hs3tne]
  have hAtne : (reverse ((ss3 n).tail)).tail ≠ [] := by
    rw [tail_reverse]; simp; exact dropLast_ne_nil _ (by rw [List.length_tail]; omega)
  constructor
  · rw [headD_append_left _ _ hA, headD_reverse, tail_getLastD (ss3 n) (by omega)]
  · rw [tail_append_left _ _ hA, headD_append_left _ _ hAtne, tail_reverse, headD_reverse,
        tail_dropLast_getLastD (ss3 n) (by omega)]

theorem Tt_head2_fact (n : ℕ) (hn : 3 ≤ n) (hsn : ss n ≠ []) (hslen2 : 2 ≤ (ss n).length) :
    (Tt (n+1)).tail.headD 0 = (ss n).dropLast.getLastD 0 := by
  rw [Tt_succ n hn, tail_append_left _ _ (by simp [hsn]),
      headD_append_left _ _ (by rw [tail_reverse]; simp; exact dropLast_ne_nil _ hslen2),
      tail_reverse, headD_reverse]

theorem Tt_len_succ (n : ℕ) (hn : 3 ≤ n) :
    (Tt (n+1)).length = (ss n).length + (Tt n).length := by
  rw [Tt_succ n hn, List.length_append, List.length_reverse]

theorem ss_len_succ (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (h2 : 1 ≤ (ss2 n).length) (hs : 1 ≤ (ss n).length) :
    (ss (n+1)).length = (ss2 n).length + (ss n).length - 1 := by
  rw [step_ss n hn hbnd hsn htn]
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_tail]
  omega

theorem ss2_len_succ (n : ℕ) (hn : 3 ≤ n)
    (hbnd : (ss n).headD 0 = (Tt n).headD 0) (hsn : ss n ≠ []) (htn : Tt n ≠ [])
    (hs_hd : (ss n).headD 0 = 1) (hs_h2 : (ss n).tail.headD 0 = 1)
    (hs2_hd : 3 ≤ (ss2 n).headD 0) (hs2_h2 : (ss2 n).tail.headD 0 = 1)
    (hs2ne : ss2 n ≠ []) (hs2tne : (ss2 n).tail ≠ []) (hstne : (ss n).tail ≠ [])
    (h3 : 1 ≤ (ss3 n).length) (h2 : 1 ≤ (ss2 n).length) :
    (ss2 (n+1)).length = (ss3 n).length + (ss2 n).length := by
  rw [step_ss2 n hn hbnd hsn htn hs_hd hs_h2 hs2_hd hs2_h2 hs2ne hs2tne hstne]
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_tail]
  omega

theorem ne_of_len (l : List ℕ) (h : 1 ≤ l.length) : l ≠ [] := by
  intro hc; rw [hc] at h; simp at h

/-- Weaker facts about `Tt` and `ss` (hold for indices `≥ 6`). -/
structure TF (m : ℕ) : Prop where
  T_hd  : (Tt m).headD 0 = 1
  T_h2  : (Tt m).tail.headD 0 = 3
  T_lst : (Tt m).getLastD 0 = 2
  T_l2  : (Tt m).dropLast.getLastD 0 = 1
  T_len : 4 ≤ (Tt m).length
  s_hd  : (ss m).headD 0 = 1
  s_len : 1 ≤ (ss m).length

/-- The full invariant (holds for indices `≥ 10`). -/
structure Inv (n : ℕ) : Prop where
  T_hd  : (Tt n).headD 0 = 1
  T_h2  : (Tt n).tail.headD 0 = 3
  T_lst : (Tt n).getLastD 0 = 2
  T_l2  : (Tt n).dropLast.getLastD 0 = 1
  T_len : 4 ≤ (Tt n).length
  s_hd  : (ss n).headD 0 = 1
  s_h2  : (ss n).tail.headD 0 = 1
  s_lst : (ss n).getLastD 0 = 1
  s_l2  : (ss n).dropLast.getLastD 0 = 3
  s_len : 4 ≤ (ss n).length
  s2_hd : 3 ≤ (ss2 n).headD 0
  s2_h2 : (ss2 n).tail.headD 0 = 1
  s2_lst: (ss2 n).getLastD 0 = 1
  s2_l2 : (ss2 n).dropLast.getLastD 0 = 1
  s2_len: 4 ≤ (ss2 n).length
  W     : ss3 n = (Tt (n-4)).dropLast ++ [6]

theorem TF_of_Inv {m : ℕ} (h : Inv m) : TF m :=
  ⟨h.T_hd, h.T_h2, h.T_lst, h.T_l2, h.T_len, h.s_hd, le_trans (by norm_num) h.s_len⟩

/-- The main inductive step. -/
theorem inv_step (n : ℕ) (hn : 10 ≤ n) (hI : Inv n) (hTF : TF (n-4)) : Inv (n+1) := by
  have hn3 : 3 ≤ n := by omega
  have hTlen := hI.T_len
  have hslen := hI.s_len
  have hs2len := hI.s2_len
  have hTFlen := hTF.T_len
  have htn : Tt n ≠ [] := ne_of_len _ (by omega)
  have hsn : ss n ≠ [] := ne_of_len _ (by omega)
  have hs2ne : ss2 n ≠ [] := ne_of_len _ (by omega)
  have hstne : (ss n).tail ≠ [] := tail_ne_nil _ (by omega)
  have hs2tne : (ss2 n).tail ≠ [] := tail_ne_nil _ (by omega)
  have hbnd : (ss n).headD 0 = (Tt n).headD 0 := by rw [hI.s_hd, hI.T_hd]
  have htn4 : Tt (n-4) ≠ [] := ne_of_len _ (le_trans (by norm_num) hTF.T_len)
  have hsn4 : ss (n-4) ≠ [] := ne_of_len _ hTF.s_len
  obtain ⟨hs3_hd, hs3_h2, hs3_lst, hs3_l2, hs3tne, hs3len⟩ :=
    ss3_facts n (n-4) hI.W hTF.T_hd hTF.T_h2 hTF.T_l2 (le_trans (by norm_num) hTF.T_len)
  have hss4 : rl (ss3 n) = ss (n-4) :=
    ss4_eq n (n-4) hI.W hTF.T_lst hTF.T_l2 (le_trans (by norm_num) hTF.T_len)
  have hss3succ : ss3 (n+1) = reverse ((ss (n-4)).tail) ++ 1 :: ss3 n :=
    step_ss3 n hn3 hbnd hsn htn hI.s_hd hI.s_h2 hI.s2_hd hI.s2_h2 hs2ne hs2tne hstne
      hs3_hd hs3_h2 hs3tne hss4
  have hW1 : ss3 (n+1) = (Tt (n+1-4)).dropLast ++ [6] :=
    step_W n (by omega) hss3succ hI.W hTF.s_hd hsn4 htn4
  obtain ⟨hsh1, hsh2⟩ := ss_head_facts n hn3 hbnd hsn htn hs2tne (by omega)
  obtain ⟨hssf1, hssf2⟩ := ss_suffix_facts n hn3 htn (by omega)
  obtain ⟨hs2h1, hs2h2⟩ := ss2_head_facts n hn3 hbnd hsn htn hI.s_hd hI.s_h2 hI.s2_hd hI.s2_h2
    hs2ne hs2tne hstne hs3tne hs3len
  obtain ⟨hs2sf1, hs2sf2⟩ := ss2_suffix_facts n hn3 htn hsn hstne hI.s_hd hI.s_h2 (by omega)
  obtain ⟨htsf1, htsf2⟩ := Tt_suffix_facts n hn3 htn (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW1⟩
  · rw [Tt_head_fact n hn3 hsn, hI.s_lst]
  · rw [Tt_head2_fact n hn3 hsn (by omega), hI.s_l2]
  · rw [htsf1, hI.T_lst]
  · rw [htsf2, hI.T_l2]
  · rw [Tt_len_succ n hn3]; omega
  · rw [hsh1, hI.s2_lst]
  · rw [hsh2, hI.s2_l2]
  · rw [hssf1, hI.s_lst]
  · rw [hssf2, hI.s_l2]
  · rw [ss_len_succ n hn3 hbnd hsn htn (by omega) (by omega)]; omega
  · rw [hs2h1, hs3_lst]; omega
  · rw [hs2h2, hs3_l2]
  · rw [hs2sf1, hI.s2_lst]
  · rw [hs2sf2, hI.s2_l2]
  · rw [ss2_len_succ n hn3 hbnd hsn htn hI.s_hd hI.s_h2 hI.s2_hd hI.s2_h2 hs2ne hs2tne hstne
        (by omega) (by omega)]; omega

theorem hT3 : Tt 3 = [2] := rfl
theorem hT4 : Tt 4 = [1, 2] := by
  rw [show (4:ℕ) = 3+1 from rfl, Tt_succ 3 (by norm_num), ss_def, hT3]; rfl
theorem hT5 : Tt 5 = [1, 1, 1, 2] := by
  rw [show (5:ℕ) = 4+1 from rfl, Tt_succ 4 (by norm_num), ss_def, hT4]; rfl
theorem hT6 : Tt 6 = [1, 3, 1, 1, 1, 2] := by
  rw [show (6:ℕ) = 5+1 from rfl, Tt_succ 5 (by norm_num), ss_def, hT5]; rfl
theorem hT7 : Tt 7 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (7:ℕ) = 6+1 from rfl, Tt_succ 6 (by norm_num), ss_def, hT6]; rfl
theorem hT8 : Tt 8 = [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (8:ℕ) = 7+1 from rfl, Tt_succ 7 (by norm_num), ss_def, hT7]; rfl
theorem hT9 : Tt 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (9:ℕ) = 8+1 from rfl, Tt_succ 8 (by norm_num), ss_def, hT8]; rfl
theorem hT10 : Tt 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1,
    1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show (10:ℕ) = 9+1 from rfl, Tt_succ 9 (by norm_num), ss_def, hT9]; rfl

theorem hTF6 : TF 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT6]; rfl
  · rw [hT6]; rfl
  · rw [hT6]; decide
  · rw [hT6]; decide
  · rw [hT6]; decide
  · rw [ss_def, hT6]; rfl
  · rw [ss_def, hT6]; decide
theorem hTF7 : TF 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT7]; rfl
  · rw [hT7]; rfl
  · rw [hT7]; decide
  · rw [hT7]; decide
  · rw [hT7]; decide
  · rw [ss_def, hT7]; rfl
  · rw [ss_def, hT7]; decide
theorem hTF8 : TF 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT8]; rfl
  · rw [hT8]; rfl
  · rw [hT8]; decide
  · rw [hT8]; decide
  · rw [hT8]; decide
  · rw [ss_def, hT8]; rfl
  · rw [ss_def, hT8]; decide
theorem hTF9 : TF 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT9]; rfl
  · rw [hT9]; rfl
  · rw [hT9]; decide
  · rw [hT9]; decide
  · rw [hT9]; decide
  · rw [ss_def, hT9]; rfl
  · rw [ss_def, hT9]; decide

theorem hInv10 : Inv 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT10]; rfl
  · rw [hT10]; rfl
  · rw [hT10]; decide
  · rw [hT10]; decide
  · rw [hT10]; decide
  · rw [ss_def, hT10]; rfl
  · rw [ss_def, hT10]; rfl
  · rw [ss_def, hT10]; decide
  · rw [ss_def, hT10]; decide
  · rw [ss_def, hT10]; decide
  · rw [ss2_def, ss_def, hT10]; decide
  · rw [ss2_def, ss_def, hT10]; rfl
  · rw [ss2_def, ss_def, hT10]; decide
  · rw [ss2_def, ss_def, hT10]; decide
  · rw [ss2_def, ss_def, hT10]; decide
  · show ss3 10 = (Tt (10-4)).dropLast ++ [6]
    rw [ss3_def, ss2_def, ss_def, hT10, show (10-4 : ℕ) = 6 from rfl, hT6]; rfl

theorem TF_base (m : ℕ) (h6 : 6 ≤ m) (h9 : m ≤ 9) : TF m := by
  interval_cases m
  · exact hTF6
  · exact hTF7
  · exact hTF8
  · exact hTF9

theorem inv_all : ∀ n, 10 ≤ n → Inv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 11 with h | h
    · have hn10 : n = 10 := by omega
      rw [hn10]; exact hInv10
    · have hIn1 : Inv (n-1) := ih (n-1) (by omega) (by omega)
      have hTF : TF (n-1-4) := by
        rcases Nat.lt_or_ge (n-1-4) 10 with hh | hh
        · exact TF_base (n-1-4) (by omega) (by omega)
        · exact TF_of_Inv (ih (n-1-4) (by omega) hh)
      have hstep := inv_step (n-1) (by omega) hIn1 hTF
      rwa [Nat.sub_add_cancel (by omega)] at hstep

theorem TF_all (m : ℕ) (h : 6 ≤ m) : TF m := by
  rcases Nat.lt_or_ge m 10 with hh | hh
  · exact TF_base m h (by omega)
  · exact TF_of_Inv (inv_all m hh)

theorem ss3_len_eq (n : ℕ) (hn : 10 ≤ n) : (ss3 n).length = (Tt (n-4)).length := by
  have hI := inv_all n hn
  have hge : 1 ≤ (Tt (n-4)).length := by have := (TF_all (n-4) (by omega)).T_len; omega
  rw [hI.W, List.length_append, List.length_dropLast]
  simp only [List.length_cons, List.length_nil]; omega

theorem Tt_len_le_succ (n : ℕ) : (Tt n).length ≤ (Tt (n+1)).length := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> decide
  · rw [Tt_len_succ n h]; omega

theorem Tt_len_mono : Monotone (fun n => (Tt n).length) :=
  monotone_nat_of_le_succ Tt_len_le_succ

theorem ss_len_le_Tt (k : ℕ) : (ss k).length ≤ (Tt k).length := by
  rw [ss_def, ← nruns_eq_rl_length]; exact nruns_le_length (Tt k)

theorem ss2_len_le_ss (k : ℕ) : (ss2 k).length ≤ (ss k).length := by
  rw [ss2_def, ← nruns_eq_rl_length]; exact nruns_le_length (ss k)

theorem HR1n (n : ℕ) (hn : 3 ≤ n) :
    (Tt (n+1)).length = (Tt n).length + (ss n).length := by
  rw [Tt_len_succ n hn]; ring

theorem HR2n (n : ℕ) (hn : 10 ≤ n) :
    (ss (n+1)).length = (ss n).length + (ss2 n).length - 1 := by
  have hI := inv_all n hn
  have htn : Tt n ≠ [] := ne_of_len _ (by have := hI.T_len; omega)
  have hsn : ss n ≠ [] := ne_of_len _ (by have := hI.s_len; omega)
  rw [ss_len_succ n (by omega) (by rw [hI.s_hd, hI.T_hd]) hsn htn
    (by have := hI.s2_len; omega) (by have := hI.s_len; omega)]
  omega

theorem HR3n (n : ℕ) (hn : 10 ≤ n) :
    (ss2 (n+1)).length = (ss2 n).length + (Tt (n-4)).length := by
  have hI := inv_all n hn
  have htn : Tt n ≠ [] := ne_of_len _ (by have := hI.T_len; omega)
  have hsn : ss n ≠ [] := ne_of_len _ (by have := hI.s_len; omega)
  have hs2ne : ss2 n ≠ [] := ne_of_len _ (by have := hI.s2_len; omega)
  have hstne : (ss n).tail ≠ [] := tail_ne_nil _ (by have := hI.s_len; omega)
  have hs2tne : (ss2 n).tail ≠ [] := tail_ne_nil _ (by have := hI.s2_len; omega)
  have hs3len : 1 ≤ (ss3 n).length := by rw [ss3_len_eq n hn]; have := (TF_all (n-4) (by omega)).T_len; omega
  rw [ss2_len_succ n (by omega) (by rw [hI.s_hd, hI.T_hd]) hsn htn hI.s_hd hI.s_h2 hI.s2_hd
        hI.s2_h2 hs2ne hs2tne hstne hs3len (by have := hI.s2_len; omega), ss3_len_eq n hn]
  ring

/-- Sum recurrence (HR0). -/
theorem HR0 (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T (n+1)).sum = (A381587_T n).sum + (A381587_T n).length := by
  rw [T_succ n hn, List.sum_append, run_lengths_nat_eq_rl, rl_sum, List.length_reverse]
  ring

/-- Length recurrence (HR1). -/
theorem HR1 (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T (n+1)).length = (A381587_T n).length + nruns (A381587_T n) := by
  rw [T_succ n hn, List.length_append, run_lengths_nat_eq_rl, ← nruns_eq_rl_length,
      nruns_reverse]
  ring

end A381
