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

/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

/-! ### Run-length encoding lemmas -/

private theorem length_takeWhile_le' (p : ℕ → Bool) (l : List ℕ) :
    (l.takeWhile p).length ≤ l.length :=
  Sublist.length_le (takeWhile_sublist p)

private theorem takeWhile_cons_eq_length_pos (h : ℕ) (t : List ℕ) :
    0 < ((h :: t).takeWhile (fun x => decide (x = h))).length := by
  simp [takeWhile_cons_of_pos]

private theorem drop_takeWhile_length_lt (h : ℕ) (t : List ℕ) :
    ((h :: t).drop ((h :: t).takeWhile (fun x => decide (x = h))).length).length
      < (h :: t).length := by
  rw [length_drop]
  have hpos := takeWhile_cons_eq_length_pos h t
  have hle := length_takeWhile_le' (fun x => decide (x = h)) (h :: t)
  omega

private theorem run_lengths_nat_sum (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    match l with
    | [] =>
      simp [run_lengths_nat] at hn ⊢
      exact hn
    | hd :: tl =>
      unfold run_lengths_nat
      dsimp
      let pf := (hd :: tl).takeWhile (fun x => decide (x = hd))
      let rest := (hd :: tl).drop pf.length
      change pf.length + (run_lengths_nat rest).sum = n
      have hlt : rest.length < n := by
        have := drop_takeWhile_length_lt hd tl
        simp only [rest, pf] at this ⊢
        omega
      have ih' := ih rest.length hlt rest rfl
      rw [ih']
      simp only [rest, pf, length_drop]
      have hle := length_takeWhile_le' (fun x => decide (x = hd)) (hd :: tl)
      omega

private theorem run_lengths_nat_entries_pos (l : List ℕ) : ∀ x ∈ run_lengths_nat l, 1 ≤ x := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    intro x hx
    match l with
    | [] =>
      unfold run_lengths_nat at hx
      simp at hx
    | hd :: tl =>
      unfold run_lengths_nat at hx
      dsimp at hx
      let pf := (hd :: tl).takeWhile (fun x => decide (x = hd))
      let rest := (hd :: tl).drop pf.length
      change x ∈ pf.length :: run_lengths_nat rest at hx
      have hpos := takeWhile_cons_eq_length_pos hd tl
      rw [mem_cons] at hx
      rcases hx with rfl | hx
      · exact hpos
      · have hlt : rest.length < n := by
          have := drop_takeWhile_length_lt hd tl
          simp only [rest, pf] at this ⊢
          omega
        exact ih rest.length hlt rest rfl x hx

/-- Length of `T n`. -/
private def Tlen (n : ℕ) : ℕ := (A381587_T n).length

private theorem A381358_zero : A381358 0 = 0 := rfl
private theorem A381358_one : A381358 1 = 1 := rfl
private theorem A381358_two : A381358 2 = 1 := rfl
private theorem A381358_three : A381358 3 = 2 := rfl

private theorem A381587_T_succ_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    A381587_T (n + 1) = run_lengths_nat (A381587_T n).reverse ++ A381587_T n := by
  match n with
  | 0 | 1 | 2 => omega
  | k + 3 =>
    simp only [A381587_T]

private theorem A381358_succ_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    A381358 (n + 1) = A381358 n + Tlen n := by
  rw [A381358, A381358, Tlen, A381587_T_succ_of_ge_three n hn, List.sum_append,
    run_lengths_nat_sum, List.length_reverse]
  ac_rfl

private theorem Tlen_succ_eq (n : ℕ) (hn : 3 ≤ n) :
    Tlen (n + 1) = (run_lengths_nat (A381587_T n).reverse).length + Tlen n := by
  rw [Tlen, Tlen, A381587_T_succ_of_ge_three n hn, List.length_append]

private theorem A381358_pos (n : ℕ) (hn : 1 ≤ n) : 0 < A381358 n := by
  match n with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
    have : 3 ≤ k + 3 := by omega
    rw [show k + 4 = (k + 3) + 1 from rfl, A381358_succ_of_ge_three (k + 3) this]
    have hpos : 0 < A381358 (k + 3) := A381358_pos (k + 3) (by omega)
    omega

private theorem A381358_mono (n : ℕ) (hn : 2 ≤ n) : A381358 n ≤ A381358 (n + 1) := by
  match n with
  | 0 | 1 => omega
  | 2 => decide
  | k + 3 =>
    have h3 : 3 ≤ k + 3 := by omega
    rw [A381358_succ_of_ge_three (k + 3) h3]
    omega

private theorem A381358_le_of_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    A381358 m ≤ A381358 n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hk2 : 2 ≤ k := by omega
    exact ih.trans (A381358_mono k hk2)

private theorem Tlen_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Tlen n := by
  match n with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
    have : 3 ≤ k + 3 := by omega
    rw [show k + 4 = (k + 3) + 1 from rfl, Tlen_succ_eq (k + 3) this]
    have ih : 0 < Tlen (k + 3) := Tlen_pos (k + 3) (by omega)
    omega

private theorem entries_pos : ∀ (n : ℕ) (x : ℕ), x ∈ A381587_T n → 1 ≤ x
  | 0, x, hx => by simp [A381587_T] at hx
  | 1, x, hx => by simp [A381587_T] at hx; omega
  | 2, x, hx => by simp [A381587_T] at hx; omega
  | 3, x, hx => by simp [A381587_T] at hx; omega
  | k + 4, x, hx => by
    simp only [A381587_T] at hx
    rw [mem_append] at hx
    rcases hx with hx | hx
    · exact run_lengths_nat_entries_pos _ x hx
    · exact entries_pos (k + 3) x hx

private theorem Tlen_le_sum (n : ℕ) : Tlen n ≤ A381358 n := by
  simpa [Tlen, A381358] using
    List.length_le_sum_of_one_le (A381587_T n) (fun x hx => entries_pos n x hx)

/- ### Auxiliary sequences -/

private def U (n : ℕ) : List ℕ := (A381587_T n).reverse

private theorem U_succ_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    U (n + 1) = U n ++ (run_lengths_nat (U n)).reverse := by
  simp only [U, A381587_T_succ_of_ge_three n hn, reverse_append]

private def numRuns (l : List ℕ) : ℕ := (run_lengths_nat l).length

private def cseq (n : ℕ) : ℕ := numRuns (A381587_T n)

private theorem T_one : A381587_T 1 = [1] := rfl
private theorem T_two : A381587_T 2 = [1] := rfl
private theorem T_three : A381587_T 3 = [2] := rfl
private theorem T_four : A381587_T 4 = [1, 2] := by simp [A381587_T, run_lengths_nat]
private theorem T_five : A381587_T 5 = [1, 1, 1, 2] := by simp [A381587_T, run_lengths_nat]
private theorem T_six : A381587_T 6 = [1, 3, 1, 1, 1, 2] := by simp [A381587_T, run_lengths_nat]

private theorem T_seven : A381587_T 7 = [1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show 7 = 6 + 1 from rfl, A381587_T_succ_of_ge_three 6 (by omega), T_six]
  simp [run_lengths_nat]

private theorem T_eight : A381587_T 8 =
    [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show 8 = 7 + 1 from rfl, A381587_T_succ_of_ge_three 7 (by omega), T_seven]
  simp [run_lengths_nat]

private theorem T_nine : A381587_T 9 =
    [1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show 9 = 8 + 1 from rfl, A381587_T_succ_of_ge_three 8 (by omega), T_eight]
  simp [run_lengths_nat]

private theorem T_ten : A381587_T 10 =
    [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1,
     3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show 10 = 9 + 1 from rfl, A381587_T_succ_of_ge_three 9 (by omega), T_nine]
  simp [run_lengths_nat]

private theorem T_eleven : A381587_T 11 =
    [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3,
     1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1,
     1, 3, 1, 1, 1, 3, 1, 1, 1, 2] := by
  rw [show 11 = 10 + 1 from rfl, A381587_T_succ_of_ge_three 10 (by omega), T_ten]
  simp [run_lengths_nat]

private theorem Tlen_mono (n : ℕ) (hn : 1 ≤ n) : Tlen n ≤ Tlen (n + 1) := by
  match n with
  | 0 => omega
  | 1 => simp [Tlen, T_one, T_two]
  | 2 =>
    simp [Tlen, T_two, T_three]
  | k + 3 =>
    have h3 : 3 ≤ k + 3 := by omega
    rw [Tlen_succ_eq (k + 3) h3]
    exact Nat.le_add_left _ _

private theorem Tlen_le_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : Tlen m ≤ Tlen n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    exact ih.trans (Tlen_mono k (by omega))

private theorem T_ne_nil (n : ℕ) (hn : 1 ≤ n) : A381587_T n ≠ [] :=
  length_pos_iff.mp (by simpa [Tlen] using Tlen_pos n hn)

private theorem T_getLast?_eq_two : ∀ n : ℕ, 3 ≤ n → (A381587_T n).getLast? = some 2
  | 3, _ => by simp [T_three]
  | k + 4, hn => by
    have h3 : 3 ≤ k + 3 := by omega
    have hne : A381587_T (k + 3) ≠ [] := T_ne_nil (k + 3) (by omega)
    rw [show (k + 4) = (k + 3) + 1 from rfl, A381587_T_succ_of_ge_three (k + 3) h3]
    simp [getLast?_append, T_getLast?_eq_two (k + 3) h3]

private theorem T_suffix_1112 (n : ℕ) (hn : 5 ≤ n) :
    (A381587_T n).drop ((A381587_T n).length - 4) = [1, 1, 1, 2] := by
  induction n, hn using Nat.le_induction with
  | base => simp [T_five]
  | succ k hk ih =>
    have h3 : 3 ≤ k := by omega
    have hklen : 4 ≤ (A381587_T k).length := by
      have hle : Tlen 5 ≤ Tlen k := Tlen_le_of_le (by omega) hk
      simpa [Tlen, T_five] using hle
    rw [A381587_T_succ_of_ge_three k h3]
    set rle := run_lengths_nat (A381587_T k).reverse
    have hlen : (rle ++ A381587_T k).length = rle.length + (A381587_T k).length :=
      length_append
    rw [hlen]
    have hsum :
        rle.length + (A381587_T k).length - 4
          = rle.length + ((A381587_T k).length - 4) := by omega
    rw [hsum]
    have hdrop := drop_append (l₁ := rle) (l₂ := A381587_T k)
      (i := rle.length + ((A381587_T k).length - 4))
    rw [hdrop]
    have hge : rle.length ≤ rle.length + ((A381587_T k).length - 4) := Nat.le_add_right _ _
    rw [drop_eq_nil_of_le hge]
    simp only [nil_append]
    have : rle.length + ((A381587_T k).length - 4) - rle.length
        = (A381587_T k).length - 4 := by omega
    rw [this, ih]

private theorem run_lengths_nat_eq_nil_iff (l : List ℕ) :
    run_lengths_nat l = [] ↔ l = [] := by
  constructor
  · intro h
    have := congrArg List.sum (congrArg id h)
    -- use run_lengths_nat_sum
    have hs := run_lengths_nat_sum l
    simp [h] at hs
    exact (List.length_eq_zero_iff).mp hs.symm
  · rintro rfl
    simp [run_lengths_nat]

private theorem run_lengths_nat_head_of_cons_ne (a b : ℕ) (t : List ℕ) (hne : a ≠ b) :
    (run_lengths_nat (a :: b :: t)).head? = some 1 := by
  have hb : ¬ (b = a) := hne.symm
  unfold run_lengths_nat
  simp [takeWhile_cons_of_pos, takeWhile_cons_of_neg (p := fun x => decide (x = a)) (a := b)
    (l := t) (h := by simp [hb])]

private theorem T_reverse_take4 (n : ℕ) (hn : 5 ≤ n) :
    (A381587_T n).reverse.take 4 = [2, 1, 1, 1] := by
  rw [take_reverse, T_suffix_1112 n hn]
  simp

private theorem T_head?_of_ge_four (n : ℕ) (hn : 4 ≤ n) :
    (A381587_T n).head? = some 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [T_four]
  | succ k hk ih =>
    have h3 : 3 ≤ k := by omega
    rw [A381587_T_succ_of_ge_three k h3]
    have hk5 : 5 ≤ k ∨ k = 4 := by omega
    have hheadR : (run_lengths_nat (A381587_T k).reverse).head? = some 1 := by
      rcases hk5 with hk5 | rfl
      · have htk := T_reverse_take4 k hk5
        have hlen : 4 ≤ (A381587_T k).reverse.length := by
          have : Tlen 5 ≤ Tlen k := Tlen_le_of_le (by omega) hk5
          simpa [Tlen, T_five, length_reverse] using this
        have hcons : ∃ t, (A381587_T k).reverse = 2 :: 1 :: t := by
          match hr : (A381587_T k).reverse with
          | [] =>
            simp [hr] at hlen
          | [_] =>
            simp [hr] at hlen
          | [_, _] =>
            simp [hr] at hlen
          | [_, _, _] =>
            simp [hr] at hlen
          | a :: b :: c :: d :: rest =>
            simp [hr] at htk
            rcases htk with ⟨rfl, rfl, _⟩
            exact ⟨c :: d :: rest, rfl⟩
        rcases hcons with ⟨t, ht⟩
        rw [ht]
        exact run_lengths_nat_head_of_cons_ne 2 1 t (by decide)
      · -- k = 4, T_4 = [1,2], reverse = [2,1]
        have : (A381587_T 4).reverse = [2, 1] := by simp [T_four]
        rw [this]
        exact run_lengths_nat_head_of_cons_ne 2 1 [] (by decide)
    match hR : run_lengths_nat (A381587_T k).reverse with
    | [] =>
      have : A381587_T k = [] := (reverse_eq_nil_iff).mp ((run_lengths_nat_eq_nil_iff _).mp hR)
      exact (T_ne_nil k (by omega) this).elim
    | a :: t =>
      simp [hR] at hheadR
      simp [hheadR]

open Filter Topology

private theorem T_suffix_31112 (n : ℕ) (hn : 6 ≤ n) :
    (A381587_T n).drop ((A381587_T n).length - 5) = [3, 1, 1, 1, 2] := by
  induction n, hn using Nat.le_induction with
  | base => simp [T_six]
  | succ k hk ih =>
    have h3 : 3 ≤ k := by omega
    have hklen : 5 ≤ (A381587_T k).length := by
      have hle : Tlen 6 ≤ Tlen k := Tlen_le_of_le (by omega) hk
      have : 6 ≤ (A381587_T k).length := by simpa [Tlen, T_six] using hle
      omega
    rw [A381587_T_succ_of_ge_three k h3]
    set rle := run_lengths_nat (A381587_T k).reverse
    have hlen : (rle ++ A381587_T k).length = rle.length + (A381587_T k).length :=
      length_append
    rw [hlen]
    have hsum :
        rle.length + (A381587_T k).length - 5
          = rle.length + ((A381587_T k).length - 5) := by omega
    rw [hsum, drop_append]
    have hge : rle.length ≤ rle.length + ((A381587_T k).length - 5) := Nat.le_add_right _ _
    rw [drop_eq_nil_of_le hge, nil_append]
    have : rle.length + ((A381587_T k).length - 5) - rle.length
        = (A381587_T k).length - 5 := by omega
    rw [this, ih]

private theorem T_reverse_take5 (n : ℕ) (hn : 6 ≤ n) :
    (A381587_T n).reverse.take 5 = [2, 1, 1, 1, 3] := by
  rw [take_reverse, T_suffix_31112 n hn]
  simp

private theorem run_lengths_nat_start_1_3 (rest : List ℕ) :
    (run_lengths_nat (2 :: 1 :: 1 :: 1 :: 3 :: rest)).take 2 = [1, 3] := by
  unfold run_lengths_nat
  -- first run is [2] length 1; remainder is 1,1,1,3,...
  simp [takeWhile_cons_of_pos, takeWhile_cons_of_neg (p := fun x => decide (x = 2))
    (a := 1) (h := by decide)]
  -- now unfold the remaining RLE of [1,1,1,3,...]
  unfold run_lengths_nat
  simp [takeWhile_cons_of_pos]

private theorem T_prefix_13 (n : ℕ) (hn : 6 ≤ n) :
    (A381587_T n).take 2 = [1, 3] := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => omega
  | 6 => simp [T_six]
  | k + 7 =>
    have h6 : 6 ≤ k + 6 := by omega
    have h3 : 3 ≤ k + 6 := by omega
    rw [show k + 7 = (k + 6) + 1 from rfl, A381587_T_succ_of_ge_three (k + 6) h3]
    have hrev := T_reverse_take5 (k + 6) h6
    have hlen : 5 ≤ (A381587_T (k + 6)).reverse.length := by
      have hle : Tlen 6 ≤ Tlen (k + 6) := Tlen_le_of_le (by omega) h6
      have : 6 ≤ (A381587_T (k + 6)).length := by simpa [Tlen, T_six] using hle
      simpa [length_reverse] using (show 5 ≤ (A381587_T (k + 6)).length by omega)
    have hcons : ∃ rest, (A381587_T (k + 6)).reverse = 2 :: 1 :: 1 :: 1 :: 3 :: rest := by
      match hr : (A381587_T (k + 6)).reverse with
      | a :: b :: c :: d :: e :: rest =>
        simp [hr] at hrev
        rcases hrev with ⟨rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨rest, rfl⟩
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] =>
        simp [hr] at hlen
    rcases hcons with ⟨rest, hrest⟩
    rw [hrest]
    have htk := run_lengths_nat_start_1_3 rest
    have hlenR : 2 ≤ (run_lengths_nat (2 :: 1 :: 1 :: 1 :: 3 :: rest)).length := by
      have h1 := congrArg List.length htk
      simp [length_take] at h1
      omega
    rw [take_append_of_le_length hlenR, htk]

/-- Number of adjacent unequal pairs. Then `numRuns l = numChanges l + 1` for nonempty `l`. -/
private def numChanges : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a = b then 0 else 1) + numChanges (b :: t)

private theorem numChanges_nil : numChanges [] = 0 := rfl
private theorem numChanges_singleton (x : ℕ) : numChanges [x] = 0 := rfl
private theorem numChanges_cons_cons (a b : ℕ) (t : List ℕ) :
    numChanges (a :: b :: t) = (if a = b then 0 else 1) + numChanges (b :: t) := rfl

private theorem numRuns_cons_cons (a b : ℕ) (t : List ℕ) :
    numRuns (a :: b :: t) = numRuns (b :: t) + if a = b then 0 else 1 := by
  unfold numRuns
  by_cases hab : a = b
  · subst hab
    unfold run_lengths_nat
    simp [takeWhile_cons_of_pos]
  · unfold run_lengths_nat
    have hb : ¬ (b = a) := Ne.symm hab
    simp [takeWhile_cons_of_pos, takeWhile_cons_of_neg (p := fun x => decide (x = a))
      (a := b) (h := by simp [hb]), hab]
    -- LHS after simp is length (RLE (b::t)); goal wants 1 + length (RLE (rest of b::t))
    conv_lhs => unfold run_lengths_nat
    simp [takeWhile_cons_of_pos]

private theorem numRuns_eq_numChanges : ∀ l : List ℕ, l ≠ [] → numRuns l = numChanges l + 1
  | [], hl => (hl rfl).elim
  | [x], _ => by simp [numRuns, numChanges, run_lengths_nat]
  | a :: b :: t, _ => by
    rw [numRuns_cons_cons, numChanges_cons_cons, numRuns_eq_numChanges (b :: t) (by simp)]
    omega

private theorem numChanges_append_merge (l₁ l₂ : List ℕ) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hm : l₁.getLast h₁ = l₂.head h₂) :
    numChanges (l₁ ++ l₂) = numChanges l₁ + numChanges l₂ := by
  -- induction on l₁
  match l₁ with
  | [] => exact (h₁ rfl).elim
  | [x] =>
    -- [x] ++ l₂, x = head l₂, so no new change at the junction
    match l₂ with
    | [] => exact (h₂ rfl).elim
    | y :: ys =>
      simp [getLast] at hm
      subst hm
      simp [numChanges_cons_cons, numChanges_singleton]
  | a :: b :: t =>
    have hne : (b :: t) ≠ [] := by simp
    have hm' : (b :: t).getLast hne = l₂.head h₂ := by
      simpa [getLast_cons] using hm
    have ih := numChanges_append_merge (b :: t) l₂ hne h₂ hm'
    simp only [cons_append, numChanges_cons_cons]
    have hconv : numChanges (b :: (t ++ l₂)) = numChanges (b :: t ++ l₂) := rfl
    rw [hconv, ih]
    ac_rfl

private theorem numRuns_append_merge (l₁ l₂ : List ℕ) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hm : l₁.getLast h₁ = l₂.head h₂) :
    numRuns (l₁ ++ l₂) + 1 = numRuns l₁ + numRuns l₂ := by
  have h12 : l₁ ++ l₂ ≠ [] := by simp [h₁]
  rw [numRuns_eq_numChanges _ h12, numRuns_eq_numChanges _ h₁, numRuns_eq_numChanges _ h₂,
    numChanges_append_merge l₁ l₂ h₁ h₂ hm]
  omega

private def dseq (n : ℕ) : ℕ := numRuns (run_lengths_nat (A381587_T n))

private theorem T_first_run_length_one (n : ℕ) (hn : 6 ≤ n) :
    (run_lengths_nat (A381587_T n)).head? = some 1 := by
  have htk := T_prefix_13 n hn
  have hlen : 2 ≤ (A381587_T n).length := by
    have : Tlen 6 ≤ Tlen n := Tlen_le_of_le (by omega) hn
    have : 6 ≤ (A381587_T n).length := by simpa [Tlen, T_six] using this
    omega
  match hT : A381587_T n with
  | [] | [_] =>
    simp [hT] at hlen
  | a :: b :: t =>
    simp [hT] at htk
    rcases htk with ⟨rfl, rfl⟩
    exact run_lengths_nat_head_of_cons_ne 1 3 t (by decide)

private theorem numChanges_concat_singleton : ∀ (l : List ℕ) (x : ℕ),
    numChanges (l ++ [x]) =
      numChanges l + if hl : l = [] then 0 else if l.getLast hl = x then 0 else 1
  | [], x => by simp [numChanges]
  | [a], x => by
    simp [numChanges_cons_cons, numChanges_singleton]
  | a :: b :: t, x => by
    have ih := numChanges_concat_singleton (b :: t) x
    simp [numChanges_cons_cons, cons_append]
    have hne : b :: t ≠ [] := by simp
    simp [getLast_cons hne] at ih ⊢
    omega

private theorem numChanges_reverse : ∀ l : List ℕ, numChanges l.reverse = numChanges l
  | [] => by simp [numChanges]
  | [x] => by simp [numChanges]
  | a :: b :: t => by
    have ih := numChanges_reverse (b :: t)
    rw [reverse_cons, numChanges_concat_singleton, ih]
    have hne : (b :: t).reverse ≠ [] := by simp
    simp [getLast_reverse]
    -- last of reverse (b::t) is head of (b::t) = b
    have : (b :: t).reverse.getLast hne = b := by
      rw [getLast_reverse]
      simp
    simp [this, numChanges_cons_cons]
    split_ifs <;> omega

private theorem numRuns_reverse (l : List ℕ) : numRuns l.reverse = numRuns l := by
  by_cases h : l = []
  · subst h; simp [numRuns, run_lengths_nat]
  · have hr : l.reverse ≠ [] := by simp [h]
    rw [numRuns_eq_numChanges _ hr, numRuns_eq_numChanges _ h, numChanges_reverse]

private theorem firstRunLen_cons (h : ℕ) (t : List ℕ) :
    ((h :: t).takeWhile (fun x => decide (x = h))).length
      = 1 + (t.takeWhile (fun x => decide (x = h))).length := by
  simp [takeWhile_cons_of_pos]; ac_rfl

private theorem takeWhile_append_drop_eq (p : ℕ → Bool) (l : List ℕ) :
    l.takeWhile p ++ l.drop (l.takeWhile p).length = l := by
  have heq : l.takeWhile p = l.take (l.takeWhile p).length :=
    (prefix_iff_eq_take).mp (takeWhile_prefix p)
  conv => lhs; lhs; rw [heq]
  exact take_append_drop _ _

/- ### RLE structure: first run, append, reverse -/

private theorem run_lengths_nat_nil : run_lengths_nat [] = [] := by
  unfold run_lengths_nat; rfl

private theorem run_lengths_nat_singleton (x : ℕ) : run_lengths_nat [x] = [1] := by
  simp [run_lengths_nat]

private theorem takeWhile_eq_of_all (v : ℕ) (l : List ℕ) (hall : ∀ x ∈ l, x = v) :
    l.takeWhile (fun x => decide (x = v)) = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a = v := hall a (mem_cons_self)
    rw [ha, takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp)]
    refine congrArg (cons v) (ih ?_)
    intro x hx
    exact hall x (mem_cons_of_mem _ hx)

private theorem takeWhile_cons_all (v : ℕ) (l : List ℕ) (hall : ∀ x ∈ v :: l, x = v) :
    (v :: l).takeWhile (fun x => decide (x = v)) = v :: l :=
  takeWhile_eq_of_all v (v :: l) hall

private theorem run_lengths_nat_all_eq (v : ℕ) (l : List ℕ) (hall : ∀ x ∈ l, x = v) :
    run_lengths_nat (v :: l) = [l.length + 1] := by
  unfold run_lengths_nat
  dsimp
  have htk : (v :: l).takeWhile (fun x => decide (x = v)) = v :: l :=
    takeWhile_eq_of_all v (v :: l) (by
      intro x hx
      rw [mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact hall x hx)
  simp [htk]
  unfold run_lengths_nat
  rfl

private theorem takeWhile_append_of_last_ne (l₁ l₂ : List ℕ) (v : ℕ)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hne : l₁.getLast h₁ ≠ l₂.head h₂) :
    (l₁ ++ l₂).takeWhile (fun x => decide (x = v))
      = l₁.takeWhile (fun x => decide (x = v)) := by
  induction l₁ with
  | nil => exact (h₁ rfl).elim
  | cons a t ih =>
    by_cases ha : a = v
    · rw [ha, cons_append,
        takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp),
        takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp)]
      cases t with
      | nil =>
        simp only [getLast] at hne
        cases l₂ with
        | nil => exact (h₂ rfl).elim
        | cons b s =>
          have hb : b ≠ v := by
            intro hbv
            have : a = (b :: s).head h₂ := by simp [head, ha, hbv]
            exact hne this
          rw [nil_append,
            takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [hb]),
            takeWhile_nil]
      | cons a' t' =>
        have h₁' : a' :: t' ≠ [] := by simp
        have hne' : (a' :: t').getLast h₁' ≠ l₂.head h₂ := by
          simpa [getLast_cons] using hne
        exact congrArg (cons v) (ih (by simp) hne')
    · rw [cons_append,
        takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [ha]),
        takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [ha])]

private theorem drop_append_takeWhile_of_last_ne (l₁ l₂ : List ℕ)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (hne : l₁.getLast h₁ ≠ l₂.head h₂) :
    let v := l₁.head h₁
    (l₁ ++ l₂).drop ((l₁ ++ l₂).takeWhile (fun x => decide (x = v))).length
      = l₁.drop (l₁.takeWhile (fun x => decide (x = v))).length ++ l₂ := by
  intro v
  have hv : l₁.head h₁ = v := rfl
  rw [takeWhile_append_of_last_ne l₁ l₂ v h₁ h₂ hne]
  have hle : (l₁.takeWhile (fun x => decide (x = v))).length ≤ l₁.length :=
    length_takeWhile_le' (fun x => decide (x = v)) l₁
  rw [drop_append_of_le_length hle]

private theorem drop_takeWhile_eq_dropWhile (p : ℕ → Bool) (l : List ℕ) :
    l.drop (l.takeWhile p).length = l.dropWhile p := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : p a = true
    · rw [takeWhile_cons_of_pos ha, dropWhile_cons_of_pos ha, length_cons, drop_succ_cons, ih]
    · rw [takeWhile_cons_of_neg (by simpa using ha), dropWhile_cons_of_neg (by simpa using ha)]
      simp

private theorem head_dropWhile_not (p : ℕ → Bool) (l : List ℕ) (h : l.dropWhile p ≠ []) :
    p ((l.dropWhile p).head h) = false := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    by_cases ha : p a = true
    · have h' : t.dropWhile p ≠ [] := by
        rwa [dropWhile_cons_of_pos ha] at h
      have : (a :: t).dropWhile p = t.dropWhile p := dropWhile_cons_of_pos ha
      simpa [this] using ih h'
    · have : (a :: t).dropWhile p = a :: t := dropWhile_cons_of_neg (by simpa using ha)
      simpa [this] using ha

private theorem drop_takeWhile_eq_nil_iff (p : ℕ → Bool) (l : List ℕ) :
    l.drop (l.takeWhile p).length = [] ↔ l.takeWhile p = l := by
  constructor
  · intro h
    have hlen : (l.takeWhile p).length = l.length := by
      have := congrArg List.length h
      simp [length_drop] at this
      have hle := length_takeWhile_le' p l
      omega
    have hpre : l.takeWhile p = l.take (l.takeWhile p).length :=
      (prefix_iff_eq_take).mp (takeWhile_prefix p)
    rw [hpre, hlen, take_length]
  · intro h
    rw [h, drop_length]

private theorem takeWhile_mem_eq (v : ℕ) (l : List ℕ)
    (x : ℕ) (hx : x ∈ l.takeWhile (fun y => decide (y = v))) : x = v := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    by_cases ha : a = v
    · rw [takeWhile_cons_of_pos (p := fun y => decide (y = v)) (h := by simp [ha])] at hx
      rw [mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ih hx
    · rw [takeWhile_cons_of_neg (p := fun y => decide (y = v)) (h := by simp [ha])] at hx
      simp at hx

private theorem Tlen_succ (n : ℕ) (hn : 3 ≤ n) :
    Tlen (n + 1) = cseq n + Tlen n := by
  rw [Tlen_succ_eq n hn, cseq, numRuns]
  rw [show (run_lengths_nat (A381587_T n).reverse).length
      = (run_lengths_nat (A381587_T n)).length from numRuns_reverse _]

private theorem run_lengths_nat_cons (h : ℕ) (t : List ℕ) :
    run_lengths_nat (h :: t) =
      ((h :: t).takeWhile (fun x => decide (x = h))).length ::
        run_lengths_nat ((h :: t).drop
          ((h :: t).takeWhile (fun x => decide (x = h))).length) := by
  simp [run_lengths_nat]

private theorem dropWhile_head?_not (p : ℕ → Bool) {l : List ℕ} {x : ℕ}
    (hx : (l.dropWhile p).head? = some x) : p x = false := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    by_cases ha : p a = true
    · rw [dropWhile_cons_of_pos ha] at hx
      exact ih hx
    · rw [dropWhile_cons_of_neg (by simpa using ha)] at hx
      simp at hx
      rcases hx with rfl
      simpa using ha

private theorem run_lengths_nat_of_all_eq {v : ℕ} {l : List ℕ} (hl : l ≠ [])
    (hall : ∀ x ∈ l, x = v) : run_lengths_nat l = [l.length] := by
  match l with
  | [] => exact (hl rfl).elim
  | a :: t =>
    have ha : a = v := hall a mem_cons_self
    subst ha
    simpa using run_lengths_nat_all_eq a t (fun x hx => hall x (mem_cons_of_mem _ hx))

private theorem takeWhile_append_of_head_ne (l₁ l₂ : List ℕ) (v : ℕ)
    (hne : l₂.head? ≠ some v) :
    (l₁ ++ l₂).takeWhile (fun x => decide (x = v))
      = l₁.takeWhile (fun x => decide (x = v)) := by
  induction l₁ with
  | nil =>
    match l₂ with
    | [] => simp
    | b :: s =>
      have hb : b ≠ v := fun hbv => hne (by simp [hbv])
      rw [nil_append,
        takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [hb]),
        takeWhile_nil]
  | cons a t ih =>
    by_cases ha : a = v
    · rw [ha, cons_append,
        takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp),
        takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp)]
      exact congrArg (cons v) ih
    · rw [cons_append,
        takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [ha]),
        takeWhile_cons_of_neg (p := fun x => decide (x = v)) (h := by simp [ha])]

private theorem rest_after_first_run_head_ne (a : ℕ) (t : List ℕ)
    (hrest : (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length ≠ []) :
    ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).head?
      ≠ some a := by
  intro hhd
  rw [drop_takeWhile_eq_dropWhile] at hhd
  have := dropWhile_head?_not (fun x => decide (x = a)) hhd
  simp at this

private theorem getLast?_append_of_right_ne (l₁ l₂ : List ℕ) (hl₂ : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? :=
  getLast?_append_of_ne_nil l₁ hl₂

private theorem head?_append_of_left_ne (l₁ l₂ : List ℕ) (hl₁ : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  match l₁ with
  | [] => exact (hl₁ rfl).elim
  | a :: t => simp

/-- RLE of a concatenation with no merge at the junction. -/
private theorem run_lengths_nat_append_ne :
    ∀ (l₁ l₂ : List ℕ), l₂ ≠ [] → l₁.getLast? ≠ l₂.head? →
      run_lengths_nat (l₁ ++ l₂) = run_lengths_nat l₁ ++ run_lengths_nat l₂ := by
  intro l₁
  induction hn : l₁.length using Nat.strong_induction_on generalizing l₁ with
  | h n ih =>
    intro l₂ hl₂ hne
    match l₁ with
    | [] =>
      simp [run_lengths_nat]
    | a :: t =>
      have hlen : (a :: t).length = n := hn
      have hsplit := takeWhile_append_drop_eq (fun x => decide (x = a)) (a :: t)
      have hrestlt :
          ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).length < n := by
        have := drop_takeWhile_length_lt a t
        omega
      rw [cons_append, run_lengths_nat_cons a (t ++ l₂), run_lengths_nat_cons a t]
      -- first-run prefix of `a :: t`
      have hpf_all : ∀ x ∈ (a :: t).takeWhile (fun y => decide (y = a)), x = a :=
        fun x hx => takeWhile_mem_eq a (a :: t) x hx
      by_cases hr :
          (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length = []
      · -- `a :: t` is a single run of `a`
        have hpf_eq : (a :: t).takeWhile (fun y => decide (y = a)) = a :: t := by
          have h' := hsplit
          simp only [hr, append_nil] at h'
          exact h'
        have hall : ∀ x ∈ a :: t, x = a := by
          intro x hx
          exact hpf_all x (by simpa [hpf_eq] using hx)
        have hlast : (a :: t).getLast? = some a := by
          have hne' : a :: t ≠ [] := by simp
          rw [getLast?_eq_some_getLast hne']
          exact congrArg some (hall _ (getLast_mem hne'))
        have hhead : l₂.head? ≠ some a := fun h => hne (hlast.trans h.symm)
        have htk :
            (a :: (t ++ l₂)).takeWhile (fun x => decide (x = a)) = a :: t := by
          have : a :: (t ++ l₂) = (a :: t) ++ l₂ := by simp
          rw [this, takeWhile_append_of_head_ne (a :: t) l₂ a hhead]
          exact takeWhile_eq_of_all a (a :: t) hall
        rw [htk, hpf_eq]
        have hdl : (a :: (t ++ l₂)).drop (a :: t).length = l₂ := by
          simpa using drop_left (l₁ := a :: t) (l₂ := l₂)
        rw [hdl, drop_length, run_lengths_nat_nil]
        simp [run_lengths_nat_of_all_eq (l := a :: t) (by simp) hall]
      · -- first run is a proper prefix
        have hhd := rest_after_first_run_head_ne a t hr
        have htk :
            (a :: (t ++ l₂)).takeWhile (fun x => decide (x = a)) =
              (a :: t).takeWhile (fun x => decide (x = a)) := by
          have hdecomp : a :: (t ++ l₂) =
              (a :: t).takeWhile (fun x => decide (x = a)) ++
                ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length ++ l₂) := by
            have : a :: (t ++ l₂) = (a :: t) ++ l₂ := by simp
            rw [this, ← append_assoc, hsplit]
          rw [hdecomp, takeWhile_append_of_head_ne]
          · exact takeWhile_eq_of_all a _ hpf_all
          · intro h
            have hrest_ne :
                (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length ≠ [] := hr
            have : (((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length) ++ l₂).head?
                = ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).head? :=
              head?_append_of_left_ne _ _ hrest_ne
            rw [this] at h
            exact hhd h
        rw [htk]
        have hdecomp : a :: (t ++ l₂) =
            (a :: t).takeWhile (fun x => decide (x = a)) ++
              ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length ++ l₂) := by
          have : a :: (t ++ l₂) = (a :: t) ++ l₂ := by simp
          rw [this, ← append_assoc, hsplit]
        have hdl :
            (a :: (t ++ l₂)).drop
              ((a :: t).takeWhile (fun x => decide (x = a))).length =
              (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length ++ l₂ := by
          rw [hdecomp, drop_left]
        rw [hdl]
        have hne' :
            ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).getLast?
              ≠ l₂.head? := by
          have hde : a :: t =
              (a :: t).takeWhile (fun x => decide (x = a)) ++
                (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length :=
            hsplit.symm
          have hgl := getLast?_append_of_ne_nil
            ((a :: t).takeWhile (fun x => decide (x = a))) hr
          rw [← hde] at hgl
          exact hgl ▸ hne
        have ih' :=
          ih _ hrestlt
            ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length) rfl
            l₂ hl₂ hne'
        rw [ih']
        simp

private theorem takeWhile_all_reverse (v : ℕ) (l : List ℕ) (hall : ∀ x ∈ l, x = v) :
    ∀ x ∈ l.reverse, x = v := by
  intro x hx
  exact hall x (mem_reverse.mp hx)

/-- RLE commutes with reverse. -/
private theorem run_lengths_nat_reverse :
    ∀ l : List ℕ, run_lengths_nat l.reverse = (run_lengths_nat l).reverse := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    match l with
    | [] =>
      simp [run_lengths_nat]
    | a :: t =>
      have hsplit := takeWhile_append_drop_eq (fun x => decide (x = a)) (a :: t)
      have hrestlt :
          ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).length < n := by
        have := drop_takeWhile_length_lt a t
        omega
      have hpf_all : ∀ x ∈ (a :: t).takeWhile (fun y => decide (y = a)), x = a :=
        fun x hx => takeWhile_mem_eq a (a :: t) x hx
      rw [run_lengths_nat_cons]
      by_cases hr :
          (a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length = []
      · -- single run
        have hpf_eq : (a :: t).takeWhile (fun y => decide (y = a)) = a :: t := by
          have h' := hsplit
          simp only [hr, append_nil] at h'
          exact h'
        have hall : ∀ x ∈ a :: t, x = a := fun x hx => hpf_all x (by simpa [hpf_eq] using hx)
        rw [hpf_eq, drop_length, run_lengths_nat_nil]
        have hr' : run_lengths_nat (a :: t).reverse = [(a :: t).length] := by
          have := run_lengths_nat_of_all_eq (l := (a :: t).reverse) (by simp)
            (takeWhile_all_reverse a (a :: t) hall)
          simpa [length_reverse] using this
        simpa using hr'
      · -- proper prefix
        have hhd := rest_after_first_run_head_ne a t hr
        have hpf_ne : (a :: t).takeWhile (fun x => decide (x = a)) ≠ [] := by
          intro h
          have := takeWhile_cons_eq_length_pos a t
          simp [h] at this
        have hrev_split :
            (a :: t).reverse =
              ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).reverse ++
                ((a :: t).takeWhile (fun x => decide (x = a))).reverse := by
          rw [← reverse_append, hsplit]
        have hne_j :
            ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).reverse.getLast?
              ≠ ((a :: t).takeWhile (fun x => decide (x = a))).reverse.head? := by
          rw [getLast?_reverse, head?_reverse]
          -- last of takeWhile is `a` (nonempty, all `a`); head of rest ≠ `a`
          have hlast_pf :
              ((a :: t).takeWhile (fun x => decide (x = a))).getLast? = some a := by
            have := getLast?_eq_some_getLast hpf_ne
            rw [this]
            exact congrArg some (hpf_all _ (getLast_mem hpf_ne))
          intro h
          have : ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length).head?
              = some a := by
            -- h : rest.reverse.getLast? = pf.reverse.head?
            -- after rw: rest.head? = pf.getLast?
            have h' := h
            rw [hlast_pf] at h'
            exact h'
          exact hhd this
        have hpf_rev_ne : ((a :: t).takeWhile (fun x => decide (x = a))).reverse ≠ [] := by
          simp [hpf_ne]
        rw [hrev_split, run_lengths_nat_append_ne _ _ hpf_rev_ne hne_j]
        have ih' :=
          ih _ hrestlt
            ((a :: t).drop ((a :: t).takeWhile (fun x => decide (x = a))).length) rfl
        rw [ih']
        have hrle_pf :
            run_lengths_nat ((a :: t).takeWhile (fun x => decide (x = a))).reverse =
              [((a :: t).takeWhile (fun x => decide (x = a))).length] := by
          have := run_lengths_nat_of_all_eq
            (l := ((a :: t).takeWhile (fun x => decide (x = a))).reverse)
            (by simp [hpf_ne]) (takeWhile_all_reverse a _ hpf_all)
          simpa [length_reverse] using this
        rw [hrle_pf]
        simp

/-- First-run length of a nonempty list. -/
private def firstRunLen : List ℕ → ℕ
  | [] => 0
  | h :: t => ((h :: t).takeWhile (fun x => decide (x = h))).length

private theorem firstRunLen_cons_eq (h : ℕ) (t : List ℕ) :
    firstRunLen (h :: t) = ((h :: t).takeWhile (fun x => decide (x = h))).length := rfl

private theorem run_lengths_nat_head?_cons (h : ℕ) (t : List ℕ) :
    (run_lengths_nat (h :: t)).head? = some (firstRunLen (h :: t)) := by
  rw [run_lengths_nat_cons, firstRunLen_cons_eq, head?_cons]

private theorem run_lengths_nat_head?_of_ne_nil {l : List ℕ} (hl : l ≠ []) :
    (run_lengths_nat l).head? = some (firstRunLen l) := by
  match l with
  | [] => exact (hl rfl).elim
  | h :: t => exact run_lengths_nat_head?_cons h t

private theorem firstRunLen_eq_head_rle {l : List ℕ} (hl : l ≠ []) :
    firstRunLen l =
      (run_lengths_nat l).head (fun h => hl ((run_lengths_nat_eq_nil_iff l).mp h)) := by
  have hne : run_lengths_nat l ≠ [] := fun h => hl ((run_lengths_nat_eq_nil_iff l).mp h)
  have hhd := run_lengths_nat_head?_of_ne_nil hl
  rw [← head_eq_iff_head?_eq_some hne] at hhd
  exact hhd.symm


private theorem tail_cons {α : Type*} (a : α) (t : List α) : (a :: t).tail = t := rfl

private theorem takeWhile_append_of_all_eq (v : ℕ) (l₁ l₂ : List ℕ)
    (hall : ∀ x ∈ l₁, x = v) :
    (l₁ ++ l₂).takeWhile (fun x => decide (x = v)) =
      l₁ ++ l₂.takeWhile (fun x => decide (x = v)) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    have ha : a = v := hall a mem_cons_self
    rw [ha, cons_append,
      takeWhile_cons_of_pos (p := fun x => decide (x = v)) (by simp)]
    refine congrArg (cons v) (ih ?_)
    intro x hx
    exact hall x (mem_cons_of_mem _ hx)

private theorem drop_takeWhile_append_of_all_eq (v : ℕ) (l₁ l₂ : List ℕ)
    (hall : ∀ x ∈ l₁, x = v) :
    (l₁ ++ l₂).drop ((l₁ ++ l₂).takeWhile (fun x => decide (x = v))).length =
      l₂.drop (l₂.takeWhile (fun x => decide (x = v))).length := by
  rw [takeWhile_append_of_all_eq v l₁ l₂ hall, length_append]
  exact drop_length_add_append _

private theorem run_lengths_nat_ne_nil_of_ne_nil {l : List ℕ} (hl : l ≠ []) :
    run_lengths_nat l ≠ [] :=
  fun h => hl ((run_lengths_nat_eq_nil_iff l).mp h)

private theorem getLast?_rle_isSome {l : List ℕ} (hl : l ≠ []) :
    ∃ a, (run_lengths_nat l).getLast? = some a := by
  have := run_lengths_nat_ne_nil_of_ne_nil hl
  exact (Option.isSome_iff_exists).mp (getLast?_isSome.mpr this)

/-- Merge case: last of `l₁` equals head of `l₂`. -/
private theorem run_lengths_nat_append_eq :
    ∀ (l₁ l₂ : List ℕ), l₁ ≠ [] → l₂ ≠ [] → l₁.getLast? = l₂.head? →
      ∃ a b, (run_lengths_nat l₁).getLast? = some a ∧
        (run_lengths_nat l₂).head? = some b ∧
        run_lengths_nat (l₁ ++ l₂) =
          (run_lengths_nat l₁).dropLast ++ [a + b] ++ (run_lengths_nat l₂).tail := by
  intro l₁
  induction hn : l₁.length using Nat.strong_induction_on generalizing l₁ with
  | h n ih =>
    intro l₂ hl₁ hl₂ heq
    match l₁ with
    | [] => exact (hl₁ rfl).elim
    | hd :: t =>
      have hsplit := takeWhile_append_drop_eq (fun x => decide (x = hd)) (hd :: t)
      have hrestlt :
          ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length).length < n := by
        have := drop_takeWhile_length_lt hd t
        omega
      have hpf_all : ∀ x ∈ (hd :: t).takeWhile (fun y => decide (y = hd)), x = hd :=
        fun x hx => takeWhile_mem_eq hd (hd :: t) x hx
      have hb : (run_lengths_nat l₂).head? = some (firstRunLen l₂) :=
        run_lengths_nat_head?_of_ne_nil hl₂
      by_cases hr :
          (hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length = []
      · -- `hd :: t` is a single run of `hd`, which merges with `l₂`
        have hpf_eq : (hd :: t).takeWhile (fun y => decide (y = hd)) = hd :: t := by
          have h' := hsplit
          simp only [hr, append_nil] at h'
          exact h'
        have hall : ∀ x ∈ hd :: t, x = hd := fun x hx => hpf_all x (by simpa [hpf_eq] using hx)
        have hlast : (hd :: t).getLast? = some hd := by
          have hne' : hd :: t ≠ [] := by simp
          rw [getLast?_eq_some_getLast hne']
          exact congrArg some (hall _ (getLast_mem hne'))
        have hhead : l₂.head? = some hd := by
          rw [← heq, hlast]
        have hrle1 : run_lengths_nat (hd :: t) = [(hd :: t).length] :=
          run_lengths_nat_of_all_eq (by simp) hall
        refine ⟨(hd :: t).length, firstRunLen l₂, ?_, hb, ?_⟩
        · simp [hrle1]
        · -- rle((hd::t) ++ l₂)
          have : hd :: t ++ l₂ = hd :: (t ++ l₂) := by simp
          rw [this, run_lengths_nat_cons]
          have htk :
              (hd :: (t ++ l₂)).takeWhile (fun x => decide (x = hd)) =
                hd :: t ++ l₂.takeWhile (fun x => decide (x = hd)) := by
            have h' : hd :: (t ++ l₂) = (hd :: t) ++ l₂ := by simp
            rw [h', takeWhile_append_of_all_eq hd (hd :: t) l₂ hall]
          have hdrop :
              (hd :: (t ++ l₂)).drop
                ((hd :: (t ++ l₂)).takeWhile (fun x => decide (x = hd))).length =
                l₂.drop (l₂.takeWhile (fun x => decide (x = hd))).length := by
            have h' : hd :: (t ++ l₂) = (hd :: t) ++ l₂ := by simp
            rw [h', drop_takeWhile_append_of_all_eq hd (hd :: t) l₂ hall]
          rw [hdrop, htk]
          -- rle(l₂) = firstRunLen l₂ :: rle(drop first-run of l₂)
          have hrle2 : run_lengths_nat l₂ =
              firstRunLen l₂ ::
                run_lengths_nat (l₂.drop (l₂.takeWhile (fun x => decide (x = hd))).length) := by
            match hl2 : l₂ with
            | [] => exact (hl₂ rfl).elim
            | c :: s =>
              have hc : c = hd := by
                simp [hl2] at hhead
                exact hhead
              subst hc
              simp [firstRunLen, run_lengths_nat_cons, hl2]
          -- firstRunLen l₂ = takeWhile length of l₂ starting with hd
          have hfr : firstRunLen l₂ =
              (l₂.takeWhile (fun x => decide (x = hd))).length := by
            match hl2 : l₂ with
            | [] => exact (hl₂ rfl).elim
            | c :: s =>
              have hc : c = hd := by
                simp [hl2] at hhead
                exact hhead
              subst hc
              simp [firstRunLen, hl2]
          rw [hfr, length_append]
          simp [hrle1, hrle2]
      · -- first run is a proper prefix; merge happens later
        have hhd := rest_after_first_run_head_ne hd t hr
        have htk :
            (hd :: (t ++ l₂)).takeWhile (fun x => decide (x = hd)) =
              (hd :: t).takeWhile (fun x => decide (x = hd)) := by
          have hdecomp : hd :: (t ++ l₂) =
              (hd :: t).takeWhile (fun x => decide (x = hd)) ++
                ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length ++ l₂) := by
            have : hd :: (t ++ l₂) = (hd :: t) ++ l₂ := by simp
            rw [this, ← append_assoc, hsplit]
          rw [hdecomp, takeWhile_append_of_head_ne]
          · exact takeWhile_eq_of_all hd _ hpf_all
          · intro h
            have : (((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length)
                ++ l₂).head? =
                ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length).head? :=
              head?_append_of_left_ne _ _ hr
            rw [this] at h
            exact hhd h
        have hdecomp : hd :: (t ++ l₂) =
            (hd :: t).takeWhile (fun x => decide (x = hd)) ++
              ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length ++ l₂) := by
          have : hd :: (t ++ l₂) = (hd :: t) ++ l₂ := by simp
          rw [this, ← append_assoc, hsplit]
        have hdl :
            (hd :: (t ++ l₂)).drop
              ((hd :: t).takeWhile (fun x => decide (x = hd))).length =
              (hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length ++ l₂ := by
          rw [hdecomp, drop_left]
        have hne' :
            ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length).getLast?
              = l₂.head? := by
          have hde : hd :: t =
              (hd :: t).takeWhile (fun x => decide (x = hd)) ++
                (hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length :=
            hsplit.symm
          have hgl := getLast?_append_of_ne_nil
            ((hd :: t).takeWhile (fun x => decide (x = hd))) hr
          rw [← hde] at hgl
          exact hgl ▸ heq
        have ⟨a, b, ha, hb', hmerge⟩ :=
          ih _ hrestlt
            ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length) rfl
            l₂ hr hl₂ hne'
        refine ⟨a, b, ?_, hb', ?_⟩
        · -- last of rle(hd::t) = last of rle(rest)
          rw [run_lengths_nat_cons]
          have hrest_rle_ne :
              run_lengths_nat
                ((hd :: t).drop ((hd :: t).takeWhile (fun x => decide (x = hd))).length) ≠ [] :=
            run_lengths_nat_ne_nil_of_ne_nil hr
          rw [getLast?_cons, ha]
          simp
        · have : hd :: t ++ l₂ = hd :: (t ++ l₂) := by simp
          rw [this, run_lengths_nat_cons, htk, hdl, hmerge]
          have hdlst :
              (((hd :: t).takeWhile (fun x => decide (x = hd))).length ::
                run_lengths_nat
                  ((hd :: t).drop
                    ((hd :: t).takeWhile (fun x => decide (x = hd))).length)).dropLast =
              ((hd :: t).takeWhile (fun x => decide (x = hd))).length ::
                (run_lengths_nat
                  ((hd :: t).drop
                    ((hd :: t).takeWhile (fun x => decide (x = hd))).length)).dropLast :=
            dropLast_cons_of_ne_nil (run_lengths_nat_ne_nil_of_ne_nil hr)
          rw [run_lengths_nat_cons, hdlst]
          simp [append_assoc]


private theorem first_run_len (l : List ℕ) (hl : l ≠ []) :
    (l.takeWhile (fun x => decide (x = l.head hl))).length
      = (run_lengths_nat l).head (by
          intro h; exact hl ((run_lengths_nat_eq_nil_iff l).mp h)) := by
  match l with
  | [] => exact (hl rfl).elim
  | a :: t =>
    unfold run_lengths_nat
    simp [takeWhile_cons_of_pos]

private theorem last_rle_rev_eq_first_run (l : List ℕ) (hl : l ≠ []) :
    (run_lengths_nat l.reverse).getLast? = some
      (l.takeWhile (fun x => decide (x = l.head hl))).length := by
  rw [run_lengths_nat_reverse, getLast?_reverse]
  match l with
  | [] => exact (hl rfl).elim
  | a :: t =>
    simp [run_lengths_nat_cons, takeWhile_cons_of_pos]

private theorem cseq_succ_of_ge_six (n : ℕ) (hn : 6 ≤ n) :
    cseq (n + 1) + 1 = dseq n + cseq n := by
  have h3 : 3 ≤ n := by omega
  have hT : A381587_T n ≠ [] := T_ne_nil n (by omega)
  have hR : run_lengths_nat (A381587_T n).reverse ≠ [] :=
    run_lengths_nat_ne_nil_of_ne_nil (by simp [hT])
  rw [cseq, cseq, A381587_T_succ_of_ge_three n h3]
  have hheadT : (A381587_T n).head? = some 1 := T_head?_of_ge_four n (by omega)
  have hfirst : firstRunLen (A381587_T n) = 1 := by
    have h1 := T_first_run_length_one n hn
    have h2 := run_lengths_nat_head?_of_ne_nil hT
    rw [h2] at h1
    exact Option.some.inj h1
  have hlastR : (run_lengths_nat (A381587_T n).reverse).getLast? = some 1 := by
    have h := last_rle_rev_eq_first_run (A381587_T n) hT
    have heq : ((A381587_T n).takeWhile
        (fun x => decide (x = (A381587_T n).head hT))).length =
        firstRunLen (A381587_T n) := by
      revert hT
      cases A381587_T n with
      | nil => intro hT; exact (hT rfl).elim
      | cons a t =>
        intro hT
        simp [firstRunLen, head]
    rwa [heq, hfirst] at h
  have hmerge' :
      numRuns (run_lengths_nat (A381587_T n).reverse ++ A381587_T n) + 1 =
        numRuns (run_lengths_nat (A381587_T n).reverse) + numRuns (A381587_T n) := by
    refine numRuns_append_merge _ _ hR hT ?_
    have hl := hlastR
    rw [getLast?_eq_some_getLast hR] at hl
    have hh : (A381587_T n).head hT = 1 :=
      (head_eq_iff_head?_eq_some hT).mpr hheadT
    exact Option.some.inj (hl.trans (congrArg some hh.symm))
  have hnum : numRuns (run_lengths_nat (A381587_T n).reverse) = dseq n := by
    simp only [dseq, numRuns]
    rw [run_lengths_nat_reverse, run_lengths_nat_reverse, length_reverse]
  simpa [hnum] using hmerge'

/- ### D(n) = S(n-4)+4 via the delayed word Y -/

private theorem T_getLast_eq_two (n : ℕ) (hn : 3 ≤ n) :
    (A381587_T n).getLast (T_ne_nil n (by omega)) = 2 := by
  have := T_getLast?_eq_two n hn
  rw [getLast?_eq_some_getLast (T_ne_nil n (by omega))] at this
  exact Option.some.inj this

private theorem U_head?_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    (U n).head? = some 2 := by
  simp [U, head?_reverse, T_getLast?_eq_two n hn]

private theorem U_succ (n : ℕ) (hn : 3 ≤ n) :
    U (n + 1) = U n ++ (run_lengths_nat (U n)).reverse :=
  U_succ_of_ge_three n hn

/-- Replacing an isolated leading `2` by `6` does not change the RLE. -/
private theorem rle_cons_replace_isolated (a b c : ℕ) (t : List ℕ)
    (hac : a ≠ c) (hbc : b ≠ c) :
    run_lengths_nat (a :: c :: t) = run_lengths_nat (b :: c :: t) := by
  have ha : ¬ (c = a) := hac.symm
  have hb : ¬ (c = b) := hbc.symm
  rw [run_lengths_nat_cons, run_lengths_nat_cons]
  simp [takeWhile_cons_of_pos,
    takeWhile_cons_of_neg (p := fun x => decide (x = a)) (a := c) (h := by simp [ha]),
    takeWhile_cons_of_neg (p := fun x => decide (x = b)) (a := c) (h := by simp [hb])]

/-- `Y k` is `X k` with the leading `2` replaced by `6`. -/
private def Y (k : ℕ) : List ℕ :=
  match U k with
  | [] => []
  | _ :: t => 6 :: t

private theorem Y_eq_cons_tail (k : ℕ) (hk : 3 ≤ k) :
    Y k = 6 :: (U k).tail := by
  have hne : U k ≠ [] := by
    simp [U, T_ne_nil k (by omega)]
  match h : U k with
  | [] => exact (hne h).elim
  | a :: t => simp [Y, h]

private theorem Y_four : Y 4 = [6, 1] := by
  simp [Y, U, T_four]

private theorem U_eq_two_cons (k : ℕ) (hk : 4 ≤ k) :
    ∃ t, U k = 2 :: t ∧ t.head? = some 1 := by
  have hhd := U_head?_of_ge_three k (by omega)
  have hT := T_head?_of_ge_four k hk
  -- U = reverse T, last of T is 2, first of T is 1
  -- so U = 2 :: ... and last of U = first of T = 1
  -- we need the SECOND element of U, i.e. second-to-last of T
  -- For k≥5, T ends with 1112, so U starts with 2,1,1,1
  have hne : U k ≠ [] := by simp [U, T_ne_nil k (by omega)]
  match hU : U k with
  | [] => exact (hne hU).elim
  | a :: t =>
    have ha : a = 2 := by simpa [hU] using hhd
    subst ha
    refine ⟨t, rfl, ?_⟩
    -- need t.head? = some 1
    by_cases hk5 : 5 ≤ k
    · have hsuf := T_suffix_1112 k hk5
      have : U k = (A381587_T k).reverse := rfl
      have htk : (U k).take 4 = [2, 1, 1, 1] := by
        have := T_reverse_take4 k hk5
        simpa [U] using this
      match t with
      | [] =>
        have hlen4 : 4 ≤ (U k).length := by
          have hle : Tlen 5 ≤ Tlen k := Tlen_le_of_le (by omega) hk5
          have : Tlen 5 = 4 := by simp [Tlen, T_five]
          have hUk : Tlen k = (U k).length := by simp [Tlen, U]
          omega
        simp [hU] at hlen4
      | b :: s =>
        simp [hU] at htk
        exact congrArg some htk.1
    · have : k = 4 := by omega
      subst this
      have hU4 : U 4 = [2, 1] := by simp [U, T_four]
      rw [hU4] at hU
      have : t = [1] := by
        injection hU with _ ht'; exact ht'.symm
      simp [this]

private theorem rle_Y_eq_rle_U (k : ℕ) (hk : 4 ≤ k) :
    run_lengths_nat (Y k) = run_lengths_nat (U k) := by
  obtain ⟨t, hU, ht⟩ := U_eq_two_cons k hk
  have hY : Y k = 6 :: t := by
    simp [Y, hU]
  rw [hU, hY]
  match t with
  | [] =>
    simp at ht
  | c :: s =>
    have hc : c = 1 := by simpa using ht
    subst hc
    exact (rle_cons_replace_isolated 2 6 1 s (by decide) (by decide)).symm

private theorem Y_succ (k : ℕ) (hk : 4 ≤ k) :
    Y (k + 1) = Y k ++ (run_lengths_nat (Y k)).reverse := by
  have h3 : 3 ≤ k := by omega
  have hU : U (k + 1) = U k ++ (run_lengths_nat (U k)).reverse := U_succ k h3
  obtain ⟨t, hUk, ht⟩ := U_eq_two_cons k hk
  have hYk : Y k = 6 :: t := by simp [Y, hUk]
  have hne : U (k + 1) ≠ [] := by simp [U, T_ne_nil (k + 1) (by omega)]
  -- U(k+1) starts with 2, so Y(k+1) = 6 :: tail(U(k+1))
  have hYsucc : Y (k + 1) = 6 :: (U (k + 1)).tail := Y_eq_cons_tail (k + 1) (by omega)
  rw [hYsucc, hU, hUk]
  simp only [cons_append, List.tail_cons]
  rw [hYk, ← cons_append]
  congr 1
  have := rle_Y_eq_rle_U k hk
  simp [hYk, hUk] at this
  exact congrArg List.reverse this.symm

private def R1 (n : ℕ) : List ℕ := run_lengths_nat (U n)
private def R2 (n : ℕ) : List ℕ := run_lengths_nat (R1 n)
private def R3 (n : ℕ) : List ℕ := run_lengths_nat (R2 n)
private def R4 (n : ℕ) : List ℕ := run_lengths_nat (R3 n)

private theorem dseq_eq_sum_R3 (n : ℕ) (hn : 1 ≤ n) :
    dseq n = (R3 n).sum := by
  -- D(n) = length(rle² T) = sum(rle³ T) = sum(rle³ X) = sum(R3)
  simp only [dseq, numRuns, R3, R2, R1]
  have h1 : run_lengths_nat (A381587_T n) = (run_lengths_nat (U n)).reverse := by
    simpa [U] using run_lengths_nat_reverse (U n)
  rw [h1, run_lengths_nat_reverse, length_reverse]
  exact (run_lengths_nat_sum _).symm

private theorem A381358_eq_sum_U (n : ℕ) : A381358 n = (U n).sum := by
  simp [A381358, U, sum_reverse]

private theorem Y_sum (k : ℕ) (hk : 4 ≤ k) :
    (Y k).sum = A381358 k + 4 := by
  obtain ⟨t, hU, _⟩ := U_eq_two_cons k hk
  have hY : Y k = 6 :: t := by simp [Y, hU]
  have hUsum : (U k).sum = 2 + t.sum := by simp [hU]
  have hYsum : (Y k).sum = 6 + t.sum := by simp [hY]
  rw [A381358_eq_sum_U, hUsum, hYsum]
  omega

/-- Base cases of `R3 n = Y (n-4)` computed directly. -/
private theorem R3_eq_Y_eight : R3 8 = Y 4 := by
  have hU : U 8 = [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1] := by
    simp [U, T_eight]
  have hR1 : R1 8 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 1] := by
    simp [R1, hU, run_lengths_nat]
  have hR2 : R2 8 = [1, 1, 1, 1, 1, 1, 4] := by
    simp [R2, hR1, run_lengths_nat]
  have hR3 : R3 8 = [6, 1] := by
    simp [R3, hR2, run_lengths_nat]
  rw [hR3, Y_four]

private theorem Y_five : Y 5 = [6, 1, 1, 1] := by
  simp [Y, U, T_five]

private theorem R3_eq_Y_nine : R3 9 = Y 5 := by
  have hU : U 9 =
      [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
    simp [U, T_nine]
  have hR1 : R1 9 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1] := by
    simp [R1, hU, run_lengths_nat]
  have hR2 : R2 9 = [1, 1, 1, 1, 1, 1, 3, 1, 6] := by
    simp [R2, hR1, run_lengths_nat]
  have hR3 : R3 9 = [6, 1, 1, 1] := by
    simp [R3, hR2, run_lengths_nat]
  rw [hR3, Y_five]

private theorem Y_six : Y 6 = [6, 1, 1, 1, 3, 1] := by
  simp [Y, U, T_six]

private theorem R3_eq_Y_ten : R3 10 = Y 6 := by
  have hR1 : R1 10 =
      [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 1] := by
    rw [R1, U, T_ten]; simp [run_lengths_nat]
  have hR2 : R2 10 = [1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6] := by
    simp [R2, hR1, run_lengths_nat]
  have hR3 : R3 10 = [6, 1, 1, 1, 3, 1] := by
    simp [R3, hR2, run_lengths_nat]
  rw [hR3, Y_six]

private theorem Y_seven : Y 7 = [6, 1, 1, 1, 3, 1, 1, 1, 3, 1] := by
  simp [Y, U, T_seven]

private theorem R3_eq_Y_eleven : R3 11 = Y 7 := by
  have hR1 : R1 11 =
      [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 1,
       5, 1, 3, 1, 1, 1, 1, 1, 1] := by
    rw [R1, U, T_eleven]; simp [run_lengths_nat]
  have hR2 : R2 11 = [1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6] := by
    simp [R2, hR1, run_lengths_nat]
  have hR3 : R3 11 = [6, 1, 1, 1, 3, 1, 1, 1, 3, 1] := by
    simp [R3, hR2, run_lengths_nat]
  rw [hR3, Y_seven]

private theorem T_eleven_prefix :
    (A381587_T 11).take 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5] := by
  rw [T_eleven]; simp

private theorem R1_eleven :
    R1 11 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 1, 7,
      1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by
  have hU : U 11 = (A381587_T 11).reverse := rfl
  rw [R1, hU, T_eleven]
  simp [run_lengths_nat]

private theorem R1_eleven_prefix :
    (R1 11).take 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5] := by
  rw [R1_eleven]; simp

private theorem R1_eleven_length : 10 ≤ (R1 11).length := by
  rw [R1_eleven]; simp

private theorem Tlen_eleven : 10 ≤ Tlen 11 := by
  simp [Tlen, T_eleven]

private theorem cseq_eleven : cseq 11 = 36 := by
  have h : (R1 11).length = 36 := by rw [R1_eleven]; simp
  have hc : cseq 11 = (R1 11).length := by
    simp only [cseq, numRuns, R1, U]
    simpa using (numRuns_reverse (A381587_T 11)).symm
  exact hc.trans h

private theorem dseq_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ dseq n := by
  have hT : A381587_T n ≠ [] := T_ne_nil n hn
  have hr : run_lengths_nat (A381587_T n) ≠ [] :=
    run_lengths_nat_ne_nil_of_ne_nil hT
  have : 0 < (run_lengths_nat (run_lengths_nat (A381587_T n))).length :=
    length_pos_iff.mpr (run_lengths_nat_ne_nil_of_ne_nil hr)
  simpa [dseq, numRuns] using this

private theorem cseq_mono_ge_six (n : ℕ) (hn : 6 ≤ n) : cseq n ≤ cseq (n + 1) := by
  have h := cseq_succ_of_ge_six n hn
  have hd : 1 ≤ dseq n := dseq_pos n (by omega)
  omega

private theorem cseq_le_of_le_ge_six {m n : ℕ} (hm : 6 ≤ m) (hmn : m ≤ n) :
    cseq m ≤ cseq n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    exact ih.trans (cseq_mono_ge_six k (by omega))

private theorem cseq_eq_R1_length (n : ℕ) :
    cseq n = (R1 n).length := by
  simp [cseq, numRuns, R1, U, run_lengths_nat_reverse]

private theorem U_is_prefix_succ (n : ℕ) (hn : 3 ≤ n) :
    U n <+: U (n + 1) := by
  rw [U_succ n hn]
  exact prefix_append _ _

private theorem U_is_prefix_of_le {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    U m <+: U n := by
  induction n, hmn using Nat.le_induction with
  | base => exact prefix_rfl
  | succ k hk ih =>
    have : 3 ≤ k := by omega
    exact ih.trans (U_is_prefix_succ k this)

private theorem firstRunLen_eq_takeWhile_head (l : List ℕ) (hl : l ≠ []) :
    firstRunLen l = (l.takeWhile (fun x => decide (x = l.head hl))).length := by
  match l with
  | [] => exact (hl rfl).elim
  | a :: t => rfl

private theorem R1_getLast?_eq_firstRunLen (n : ℕ) (hn : 1 ≤ n) :
    (R1 n).getLast? = some (firstRunLen (A381587_T n)) := by
  have hT := T_ne_nil n hn
  have h := last_rle_rev_eq_first_run (A381587_T n) hT
  rw [← firstRunLen_eq_takeWhile_head (A381587_T n) hT] at h
  simpa [R1, U] using h

private theorem firstRunLen_T_ge_six (n : ℕ) (hn : 6 ≤ n) :
    firstRunLen (A381587_T n) = 1 := by
  have h1 := T_first_run_length_one n hn
  have h2 := run_lengths_nat_head?_of_ne_nil (T_ne_nil n (by omega))
  rw [h2] at h1
  exact Option.some.inj h1

private theorem U_decomp_after (m n : ℕ) (hm : 3 ≤ m) (hmn : m < n) :
    ∃ rest, U n = U m ++ rest ∧ rest.head? = (R1 m).getLast? := by
  have hstep : U (m + 1) = U m ++ (R1 m).reverse := by
    simpa [R1] using U_succ m hm
  have hhd : ((R1 m).reverse).head? = (R1 m).getLast? := head?_reverse
  by_cases h : n = m + 1
  · subst h
    exact ⟨(R1 m).reverse, hstep, hhd⟩
  · have : m + 1 < n := by omega
    have hpre : U (m + 1) <+: U n := U_is_prefix_of_le (by omega) (by omega)
    obtain ⟨more, hmore⟩ := hpre
    refine ⟨(R1 m).reverse ++ more, ?_, ?_⟩
    · rw [← append_assoc, ← hstep, hmore]
    · have hRne : (R1 m).reverse ≠ [] := by
        simp [R1, U]
        exact run_lengths_nat_ne_nil_of_ne_nil (by simp [T_ne_nil m (by omega)])
      rw [head?_append_of_left_ne _ _ hRne, hhd]

private theorem take_dropLast_of_lt {α : Type*} (l : List α) {k : ℕ}
    (hk : k < l.length) : l.dropLast.take k = l.take k := by
  rw [dropLast_eq_take]
  have : k ≤ l.length - 1 := by omega
  rw [take_take, min_eq_left this]

/-- The prefix of `R1 n` (hence of `T (n+1)`) is stable for `n ≥ 11`. -/
private theorem R1_prefix_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (R1 n).take 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5] := by
  by_cases heq : n = 11
  · subst heq; exact R1_eleven_prefix
  · have hlt : 11 < n := by omega
    obtain ⟨rest, hU, hhd⟩ := U_decomp_after 11 n (by omega) hlt
    have hr : rest ≠ [] := by
      intro h
      simp [h] at hhd
      have : (R1 11).getLast? = none := hhd.symm
      have hne : R1 11 ≠ [] := by
        have : (R1 11).length = 36 := by
          simpa [cseq_eq_R1_length] using cseq_eleven
        intro h'; simp [h'] at this
      exact getLast?_eq_none_iff.mp this ▸ hne <| rfl
    have hlastU : (U 11).getLast? = some 1 := by
      simp [U, getLast?_reverse, T_head?_of_ge_four 11 (by omega)]
    have hlastR1 : (R1 11).getLast? = some 1 := by
      rw [R1_getLast?_eq_firstRunLen 11 (by omega), firstRunLen_T_ge_six 11 (by omega)]
    have hhead : rest.head? = some 1 := by
      rw [hhd, hlastR1]
    have ⟨a, b, ha, hb, hmerge⟩ :=
      run_lengths_nat_append_eq (U 11) rest
        (by simp [U, T_ne_nil 11 (by omega)]) hr (hlastU.trans hhead.symm)
    have hR1 : R1 n = (R1 11).dropLast ++ [a + b] ++ (run_lengths_nat rest).tail := by
      simpa [R1, hU] using hmerge
    have hlen36 : (R1 11).length = 36 := by
      simpa [cseq_eq_R1_length] using cseq_eleven
    have hlenDL : 10 ≤ (R1 11).dropLast.length := by
      have : (R1 11).dropLast.length = (R1 11).length - 1 := length_dropLast
      omega
    have htake : (R1 n).take 10 = (R1 11).dropLast.take 10 := by
      have hle' : 10 ≤ ((R1 11).dropLast ++ [a + b]).length := by
        simp [length_append]; omega
      rw [hR1, take_append_of_le_length hle', take_append_of_le_length hlenDL]
    have htd : (R1 11).dropLast.take 10 = (R1 11).take 10 :=
      take_dropLast_of_lt (R1 11) (by omega)
    rw [htake, htd, R1_eleven_prefix]

/-- The prefix of `T n` stabilizes for `n ≥ 11`. -/
private theorem T_prefix_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (A381587_T n).take 10 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5] := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => omega
  | 11 => exact T_eleven_prefix
  | k + 12 =>
    have hk : 11 ≤ k + 11 := by omega
    have h3 : 3 ≤ k + 11 := by omega
    rw [show k + 12 = (k + 11) + 1 from rfl, A381587_T_succ_of_ge_three (k + 11) h3]
    have hlen : 10 ≤ (run_lengths_nat (A381587_T (k + 11)).reverse).length := by
      have : cseq (k + 11) = (run_lengths_nat (A381587_T (k + 11)).reverse).length := by
        simp [cseq, numRuns, run_lengths_nat_reverse]
      have hle : cseq 11 ≤ cseq (k + 11) :=
        cseq_le_of_le_ge_six (by omega) (by omega)
      have h11 : cseq 11 = 36 := cseq_eleven
      omega
    rw [take_append_of_le_length hlen]
    simpa [R1, U] using R1_prefix_ge_eleven (k + 11) hk

private theorem U_suffix_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (U n).drop ((U n).length - 10) = [5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
  have htk := T_prefix_ge_eleven n hn
  have hlen : 10 ≤ (U n).length := by
    have : Tlen 11 ≤ Tlen n := Tlen_le_of_le (by omega) hn
    have : 10 ≤ Tlen 11 := Tlen_eleven
    have : Tlen n = (U n).length := by simp [Tlen, U]
    omega
  have hUlen : (U n).length = (A381587_T n).length := by simp [U]
  have hlenT : 10 ≤ (A381587_T n).length := by omega
  have : (U n).drop ((U n).length - 10) = ((A381587_T n).take 10).reverse := by
    simp only [U]
    rw [length_reverse, drop_reverse]
    have : (A381587_T n).length - ((A381587_T n).length - 10) = 10 := by omega
    rw [this]
  rw [this, htk]
  simp

private theorem rle_U_suffix :
    run_lengths_nat [5, 1, 1, 1, 3, 1, 3, 1, 3, 1] = [1, 3, 1, 1, 1, 1, 1, 1] := by
  simp [run_lengths_nat]

private theorem drop_append_suffix {α : Type*} (l₁ l₂ : List α) {k : ℕ}
    (hk : k ≤ l₂.length) :
    (l₁ ++ l₂).drop ((l₁ ++ l₂).length - k) = l₂.drop (l₂.length - k) := by
  rw [length_append]
  have : l₁.length + l₂.length - k = l₁.length + (l₂.length - k) := by omega
  rw [this, drop_length_add_append]

private theorem R1_ends_six_ones (n : ℕ) (hn : 11 ≤ n) :
    (R1 n).drop ((R1 n).length - 6) = [1, 1, 1, 1, 1, 1] := by
  have hsuf := U_suffix_ge_eleven n hn
  have hlenU : 10 ≤ (U n).length := by
    have : Tlen 11 ≤ Tlen n := Tlen_le_of_le (by omega) hn
    have : 10 ≤ Tlen 11 := Tlen_eleven
    have : Tlen n = (U n).length := by simp [Tlen, U]
    omega
  have hsplit0 : U n =
      (U n).take ((U n).length - 10) ++ [5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
    have := take_append_drop ((U n).length - 10) (U n)
    rw [hsuf] at this
    exact this.symm
  generalize hpre : (U n).take ((U n).length - 10) = pre
  rw [hpre] at hsplit0
  have hrleS := rle_U_suffix
  by_cases hp : pre = []
  · have : U n = [5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
      simpa [hp] using hsplit0
    simp [R1, this, hrleS]
  · by_cases hmerge : pre.getLast? = some 5
    · obtain ⟨a, b, ha, hb, hme⟩ :=
        run_lengths_nat_append_eq pre [5, 1, 1, 1, 3, 1, 3, 1, 3, 1]
          hp (by simp) (by simpa using hmerge)
      have hR1 : R1 n =
          (run_lengths_nat pre).dropLast ++ [a + b] ++ [3, 1, 1, 1, 1, 1, 1] := by
        have htail : (run_lengths_nat [5, 1, 1, 1, 3, 1, 3, 1, 3, 1]).tail =
            [3, 1, 1, 1, 1, 1, 1] := by rw [hrleS]; rfl
        unfold R1
        rw [hsplit0, hme, htail]
      rw [hR1]
      have hcat : [a + b] ++ [3, 1, 1, 1, 1, 1, 1] = [a + b, 3, 1, 1, 1, 1, 1, 1] := rfl
      rw [append_assoc, hcat]
      rw [drop_append_suffix (l₁ := (run_lengths_nat pre).dropLast)
        (l₂ := [a + b, 3, 1, 1, 1, 1, 1, 1]) (k := 6) (by simp)]
      simp
    · have hne' : pre.getLast? ≠ [5, 1, 1, 1, 3, 1, 3, 1, 3, 1].head? := by
        simpa using hmerge
      have hneapp := run_lengths_nat_append_ne pre [5, 1, 1, 1, 3, 1, 3, 1, 3, 1]
        (by simp) hne'
      have hR1 : R1 n = run_lengths_nat pre ++ [1, 3, 1, 1, 1, 1, 1, 1] := by
        unfold R1
        rw [hsplit0, hneapp, hrleS]
      rw [hR1]
      rw [drop_append_suffix (l₁ := run_lengths_nat pre)
        (l₂ := [1, 3, 1, 1, 1, 1, 1, 1]) (k := 6) (by simp)]
      simp

/- Extra RLE / list helpers for the `R3 = Y` induction -/

private theorem tail_reverse_eq_dropLast_reverse {α : Type*} (l : List α) :
    l.reverse.tail = l.dropLast.reverse := by
  have h := dropLast_reverse (l := l.reverse)
  -- h : l.dropLast = l.reverse.tail.reverse
  simpa using (congrArg List.reverse h).symm

private theorem run_lengths_nat_append3_ne
    (l₁ l₂ l₃ : List ℕ) (h₂ : l₂ ≠ []) (h₃ : l₃ ≠ [])
    (h12 : l₁.getLast? ≠ l₂.head?) (h23 : l₂.getLast? ≠ l₃.head?) :
    run_lengths_nat (l₁ ++ l₂ ++ l₃) =
      run_lengths_nat l₁ ++ run_lengths_nat l₂ ++ run_lengths_nat l₃ := by
  have hne : (l₁ ++ l₂).getLast? ≠ l₃.head? := by
    rw [getLast?_append_of_right_ne l₁ l₂ h₂]
    exact h23
  rw [run_lengths_nat_append_ne (l₁ ++ l₂) l₃ h₃ hne,
      run_lengths_nat_append_ne l₁ l₂ h₂ h12]

private theorem rle_five_one : run_lengths_nat [5, 1] = [1, 1] := by
  simp [run_lengths_nat]

private theorem rle_U_suffix16 :
    run_lengths_nat [7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] =
      [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by
  simp [run_lengths_nat]

private theorem rle_R1_suffix10 :
    run_lengths_nat [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 6] := by
  simp [run_lengths_nat]

private theorem rle_six_ones : run_lengths_nat [1, 1, 1, 1, 1, 1] = [6] := by
  simp [run_lengths_nat]

private theorem rle_five_ones : run_lengths_nat [1, 1, 1, 1, 1] = [5] := by
  simp [run_lengths_nat]

private theorem T_eleven_prefix17 :
    (A381587_T 11).take 17 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1] := by
  rw [T_eleven]; simp

private theorem R1_eleven_prefix17 :
    (R1 11).take 17 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1] := by
  rw [R1_eleven]; simp

private theorem Tlen_eleven_17 : 17 ≤ Tlen 11 := by
  simp [Tlen, T_eleven]

private theorem R1_length_ge_eleven (n : ℕ) (hn : 11 ≤ n) : 36 ≤ (R1 n).length := by
  have hle : cseq 11 ≤ cseq n := cseq_le_of_le_ge_six (by omega) hn
  have h11 : cseq 11 = 36 := cseq_eleven
  simpa [cseq_eq_R1_length] using le_trans (le_of_eq h11.symm) hle

private theorem R1_prefix_ge_eleven_17 (n : ℕ) (hn : 11 ≤ n) :
    (R1 n).take 17 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1] := by
  by_cases heq : n = 11
  · subst heq; exact R1_eleven_prefix17
  · have hlt : 11 < n := by omega
    obtain ⟨rest, hU, hhd⟩ := U_decomp_after 11 n (by omega) hlt
    have hr : rest ≠ [] := by
      intro h
      simp [h] at hhd
      have : (R1 11).getLast? = none := hhd.symm
      have hne : R1 11 ≠ [] := by
        have : 36 ≤ (R1 11).length := R1_length_ge_eleven 11 (by omega)
        intro h'; simp [h'] at this
      exact getLast?_eq_none_iff.mp this ▸ hne <| rfl
    have hlastU : (U 11).getLast? = some 1 := by
      simp [U, getLast?_reverse, T_head?_of_ge_four 11 (by omega)]
    have hlastR1 : (R1 11).getLast? = some 1 := by
      rw [R1_getLast?_eq_firstRunLen 11 (by omega), firstRunLen_T_ge_six 11 (by omega)]
    have hhead : rest.head? = some 1 := by
      rw [hhd, hlastR1]
    have ⟨a, b, ha, hb, hmerge⟩ :=
      run_lengths_nat_append_eq (U 11) rest
        (by simp [U, T_ne_nil 11 (by omega)]) hr (hlastU.trans hhead.symm)
    have hR1 : R1 n = (R1 11).dropLast ++ [a + b] ++ (run_lengths_nat rest).tail := by
      simpa [R1, hU] using hmerge
    have hlenR1 : 36 ≤ (R1 11).length := R1_length_ge_eleven 11 (by omega)
    have hlenDL : 17 ≤ (R1 11).dropLast.length := by
      have : (R1 11).dropLast.length = (R1 11).length - 1 := length_dropLast
      omega
    have htake : (R1 n).take 17 = (R1 11).dropLast.take 17 := by
      have hle' : 17 ≤ ((R1 11).dropLast ++ [a + b]).length := by
        simp [length_append]; omega
      rw [hR1, take_append_of_le_length hle', take_append_of_le_length hlenDL]
    have htd : (R1 11).dropLast.take 17 = (R1 11).take 17 :=
      take_dropLast_of_lt (R1 11) (by omega)
    rw [htake, htd, R1_eleven_prefix17]

private theorem T_prefix_ge_eleven_17 (n : ℕ) (hn : 11 ≤ n) :
    (A381587_T n).take 17 = [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1] := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => omega
  | 11 => exact T_eleven_prefix17
  | k + 12 =>
    have hk : 11 ≤ k + 11 := by omega
    have h3 : 3 ≤ k + 11 := by omega
    rw [show k + 12 = (k + 11) + 1 from rfl, A381587_T_succ_of_ge_three (k + 11) h3]
    have hlen : 17 ≤ (run_lengths_nat (A381587_T (k + 11)).reverse).length := by
      have : cseq (k + 11) = (run_lengths_nat (A381587_T (k + 11)).reverse).length := by
        simp [cseq, numRuns, run_lengths_nat_reverse]
      have hle : cseq 11 ≤ cseq (k + 11) :=
        cseq_le_of_le_ge_six (by omega) (by omega)
      have h11 : cseq 11 = 36 := cseq_eleven
      omega
    rw [take_append_of_le_length hlen]
    simpa [R1, U] using R1_prefix_ge_eleven_17 (k + 11) hk

private theorem U_len_ge_seventeen (n : ℕ) (hn : 11 ≤ n) : 17 ≤ (U n).length := by
  have : Tlen 11 ≤ Tlen n := Tlen_le_of_le (by omega) hn
  have : 17 ≤ Tlen 11 := Tlen_eleven_17
  have : Tlen n = (U n).length := by simp [Tlen, U]
  omega

private theorem U_suffix_ge_eleven_16 (n : ℕ) (hn : 11 ≤ n) :
    (U n).drop ((U n).length - 16) = [7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
  have htk := T_prefix_ge_eleven_17 n hn
  have hlen := U_len_ge_seventeen n hn
  have hUlen : (U n).length = (A381587_T n).length := by simp [U]
  have hlenT : 17 ≤ (A381587_T n).length := by omega
  have : (U n).drop ((U n).length - 16) = ((A381587_T n).take 16).reverse := by
    simp only [U]
    rw [length_reverse, drop_reverse]
    have : (A381587_T n).length - ((A381587_T n).length - 16) = 16 := by omega
    rw [this]
  have htake16 : (A381587_T n).take 16 =
      [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7] := by
    have : (A381587_T n).take 16 = ((A381587_T n).take 17).take 16 := by
      rw [take_take, min_eq_left (by omega)]
    rw [this, htk]
    simp
  rw [this, htake16]
  simp

private theorem U_suffix_ge_eleven_17 (n : ℕ) (hn : 11 ≤ n) :
    (U n).drop ((U n).length - 17) =
      [1, 7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
  have htk := T_prefix_ge_eleven_17 n hn
  have hlen := U_len_ge_seventeen n hn
  have hUlen : (U n).length = (A381587_T n).length := by simp [U]
  have hlenT : 17 ≤ (A381587_T n).length := by omega
  have : (U n).drop ((U n).length - 17) = ((A381587_T n).take 17).reverse := by
    simp only [U]
    rw [length_reverse, drop_reverse]
    have : (A381587_T n).length - ((A381587_T n).length - 17) = 17 := by omega
    rw [this]
  rw [this, htk]
  simp

private theorem R1_suffix10_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (R1 n).drop ((R1 n).length - 10) = [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by
  have hsuf := U_suffix_ge_eleven_16 n hn
  have hlen := U_len_ge_seventeen n hn
  have hsplit0 : U n =
      (U n).take ((U n).length - 16) ++
        [7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] := by
    have := take_append_drop ((U n).length - 16) (U n)
    rw [hsuf] at this
    exact this.symm
  generalize hpre : (U n).take ((U n).length - 16) = pre
  rw [hpre] at hsplit0
  -- last of pre is 1, from the 17-suffix
  have hpreLast : pre.getLast? = some 1 := by
    have h17 := U_suffix_ge_eleven_17 n hn
    have htake : (U n).take ((U n).length - 16) =
        (U n).take ((U n).length - 17) ++ [1] := by
      have hcalc : (U n).length - 16 = (U n).length - 17 + 1 := by omega
      rw [hcalc, take_add, h17]
      simp
    rw [← hpre, htake, getLast?_concat]
  have hp : pre ≠ [] := by
    intro h; simp [h] at hpreLast
  have hne : pre.getLast? ≠
      [7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1].head? := by
    rw [hpreLast]; simp
  have hrle :=
    run_lengths_nat_append_ne pre
      [7, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 1] (by simp) hne
  have hR1 : R1 n = run_lengths_nat pre ++
      [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by
    unfold R1
    rw [hsplit0, hrle, rle_U_suffix16]
  rw [hR1]
  rw [drop_append_suffix (l₁ := run_lengths_nat pre)
    (l₂ := [1, 5, 1, 3, 1, 1, 1, 1, 1, 1]) (k := 10) (by simp)]
  simp

private theorem R2_suffix4_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (R2 n).drop ((R2 n).length - 4) = [1, 1, 1, 6] := by
  have hsuf := R1_suffix10_ge_eleven n hn
  have hlenR1 : 10 ≤ (R1 n).length := by
    have : 36 ≤ (R1 n).length := R1_length_ge_eleven n hn
    omega
  have hsplit0 : R1 n =
      (R1 n).take ((R1 n).length - 10) ++ [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by
    have := take_append_drop ((R1 n).length - 10) (R1 n)
    rw [hsuf] at this
    exact this.symm
  generalize hpre : (R1 n).take ((R1 n).length - 10) = pre
  rw [hpre] at hsplit0
  have hrleS := rle_R1_suffix10
  by_cases hp : pre = []
  · have : R1 n = [1, 5, 1, 3, 1, 1, 1, 1, 1, 1] := by simpa [hp] using hsplit0
    simp [R2, this, hrleS]
  · by_cases hmerge : pre.getLast? = some 1
    · obtain ⟨a, b, ha, hb, hme⟩ :=
        run_lengths_nat_append_eq pre [1, 5, 1, 3, 1, 1, 1, 1, 1, 1]
          hp (by simp) (by simpa using hmerge)
      have hR2 : R2 n =
          (run_lengths_nat pre).dropLast ++ [a + b] ++ [1, 1, 1, 6] := by
        have htail : (run_lengths_nat [1, 5, 1, 3, 1, 1, 1, 1, 1, 1]).tail =
            [1, 1, 1, 6] := by rw [hrleS]; rfl
        unfold R2
        rw [hsplit0, hme, htail]
      rw [hR2]
      have hcat : [a + b] ++ [1, 1, 1, 6] = [a + b, 1, 1, 1, 6] := rfl
      rw [append_assoc, hcat]
      rw [drop_append_suffix (l₁ := (run_lengths_nat pre).dropLast)
        (l₂ := [a + b, 1, 1, 1, 6]) (k := 4) (by simp)]
      simp
    · have hne' : pre.getLast? ≠ [1, 5, 1, 3, 1, 1, 1, 1, 1, 1].head? := by
        simpa using hmerge
      have hneapp := run_lengths_nat_append_ne pre [1, 5, 1, 3, 1, 1, 1, 1, 1, 1]
        (by simp) hne'
      have hR2 : R2 n = run_lengths_nat pre ++ [1, 1, 1, 1, 6] := by
        unfold R2
        rw [hsplit0, hneapp, hrleS]
      rw [hR2]
      rw [drop_append_suffix (l₁ := run_lengths_nat pre)
        (l₂ := [1, 1, 1, 1, 6]) (k := 4) (by simp)]
      simp

private theorem R2_len_ge_four (n : ℕ) (hn : 11 ≤ n) : 4 ≤ (R2 n).length := by
  have hs := R2_suffix4_ge_eleven n hn
  have hlen : ((R2 n).drop ((R2 n).length - 4)).length = 4 := by
    rw [hs]; simp
  have : ((R2 n).drop ((R2 n).length - 4)).length =
      (R2 n).length - ((R2 n).length - 4) := length_drop
  omega

private theorem R2_getLast?_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    (R2 n).getLast? = some 6 := by
  have hs := R2_suffix4_ge_eleven n hn
  have hlen := R2_len_ge_four n hn
  have hlt : (R2 n).length - 4 < (R2 n).length := by omega
  have hdrop := getLast?_drop (l := R2 n) (i := (R2 n).length - 4)
  simp only [Nat.not_le.mpr hlt, ↓reduceIte] at hdrop
  rw [← hdrop, hs]
  simp

private theorem R2_ne_nil_ge_eleven (n : ℕ) (hn : 11 ≤ n) : R2 n ≠ [] := by
  intro h
  have := R2_getLast?_ge_eleven n hn
  simp [h] at this

private theorem R1_ne_nil (n : ℕ) (hn : 1 ≤ n) : R1 n ≠ [] :=
  run_lengths_nat_ne_nil_of_ne_nil (by simp [U, T_ne_nil n hn])

private theorem R1_getLast?_ge_six (n : ℕ) (hn : 6 ≤ n) :
    (R1 n).getLast? = some 1 := by
  rw [R1_getLast?_eq_firstRunLen n (by omega), firstRunLen_T_ge_six n hn]

private theorem U_getLast?_ge_four (n : ℕ) (hn : 4 ≤ n) :
    (U n).getLast? = some 1 := by
  simp [U, getLast?_reverse, T_head?_of_ge_four n hn]

private theorem R1_succ_of_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    R1 (n + 1) = (R1 n).dropLast ++ [7] ++ (R2 n).dropLast.reverse := by
  have h3 : 3 ≤ n := by omega
  have hU : U (n + 1) = U n ++ (R1 n).reverse := by
    simpa [R1] using U_succ n h3
  have hUne : U n ≠ [] := by simp [U, T_ne_nil n (by omega)]
  have hR1ne : R1 n ≠ [] := R1_ne_nil n (by omega)
  have hR1revne : (R1 n).reverse ≠ [] := by simp [hR1ne]
  have hlastU : (U n).getLast? = some 1 := U_getLast?_ge_four n (by omega)
  have hlastR1 : (R1 n).getLast? = some 1 := R1_getLast?_ge_six n (by omega)
  have hheadrev : (R1 n).reverse.head? = some 1 := by
    rwa [head?_reverse]
  have hmerge : (U n).getLast? = (R1 n).reverse.head? := by
    rw [hlastU, hheadrev]
  obtain ⟨a, b, ha, hb, hme⟩ :=
    run_lengths_nat_append_eq (U n) (R1 n).reverse hUne hR1revne hmerge
  have ha1 : a = 1 := by
    have : (R1 n).getLast? = some a := ha
    rw [hlastR1] at this
    exact Option.some.inj this.symm
  have hb6 : b = 6 := by
    have : (run_lengths_nat (R1 n).reverse).head? = some b := hb
    rw [run_lengths_nat_reverse, head?_reverse] at this
    have hR2last : (R2 n).getLast? = some 6 := R2_getLast?_ge_eleven n hn
    change (run_lengths_nat (R1 n)).getLast? = some 6 at hR2last
    rw [hR2last] at this
    exact Option.some.inj this.symm
  unfold R1
  rw [hU, hme, ha1, hb6, run_lengths_nat_reverse]
  simp [tail_reverse_eq_dropLast_reverse]
  rfl

private theorem R1_dropLast_getLast?_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    ((R1 n).dropLast).getLast? = some 1 := by
  have hs := R1_suffix10_ge_eleven n hn
  have hlen : 36 ≤ (R1 n).length := R1_length_ge_eleven n hn
  rw [getLast?_dropLast]
  have : ¬ (R1 n).length ≤ 1 := by omega
  simp only [this, ↓reduceIte]
  have : (R1 n)[(R1 n).length - 2]? =
      ((R1 n).drop ((R1 n).length - 10))[8]? := by
    rw [getElem?_drop]
    congr 1
    omega
  rw [this, hs]
  simp

private theorem R2_dropLast_getLast?_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    ((R2 n).dropLast).getLast? = some 1 := by
  have hs := R2_suffix4_ge_eleven n hn
  have hlen := R2_len_ge_four n hn
  rw [getLast?_dropLast]
  have : ¬ (R2 n).length ≤ 1 := by omega
  simp only [this, ↓reduceIte]
  have : (R2 n)[(R2 n).length - 2]? =
      ((R2 n).drop ((R2 n).length - 4))[2]? := by
    rw [getElem?_drop]
    congr 1
    omega
  rw [this, hs]
  simp

private theorem firstRunLen_ge_three_of_take (l : List ℕ)
    (h : l.take 3 = [1, 1, 1]) : 3 ≤ firstRunLen l := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | a :: b :: c :: t =>
    simp at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rw [firstRunLen_cons_eq]
    have : (1 :: 1 :: 1 :: t).takeWhile (fun x => decide (x = 1)) =
        1 :: 1 :: 1 :: t.takeWhile (fun x => decide (x = 1)) := by
      simp [takeWhile_cons_of_pos]
    rw [this]
    simp

private theorem R2_dropLast_lastRun_ge_three (n : ℕ) (hn : 11 ≤ n) :
    3 ≤ firstRunLen ((R2 n).dropLast.reverse) := by
  have hs := R2_suffix4_ge_eleven n hn
  have hlen := R2_len_ge_four n hn
  have hrev : ((R2 n).dropLast.reverse).take 3 = [1, 1, 1] := by
    -- reverse.take 3 = reverse of last 3 of dropLast = reverse of [1,1,1]
    have hlenDL : (R2 n).dropLast.length = (R2 n).length - 1 := length_dropLast
    have h3 : 3 ≤ (R2 n).dropLast.length := by omega
    rw [take_reverse]
    have hidx : (R2 n).dropLast.length - 3 = (R2 n).length - 4 := by omega
    rw [hidx]
    have : (R2 n).dropLast.drop ((R2 n).length - 4) = [1, 1, 1] := by
      rw [dropLast_eq_take]
      have : ((R2 n).take ((R2 n).length - 1)).drop ((R2 n).length - 4) =
          ((R2 n).drop ((R2 n).length - 4)).take 3 := by
        rw [drop_take]; congr 1; omega
      rw [this, hs]; simp
    rw [this]
    simp
  exact firstRunLen_ge_three_of_take _ hrev

private theorem getLast?_rle_eq_firstRunLen_reverse {l : List ℕ} (hl : l ≠ []) :
    (run_lengths_nat l).getLast? = some (firstRunLen l.reverse) := by
  rw [getLast?_eq_head?_reverse, ← run_lengths_nat_reverse]
  exact run_lengths_nat_head?_of_ne_nil (by simp [hl])

private theorem R2_dropLast_rle_getLast?_ne_one (n : ℕ) (hn : 11 ≤ n) :
    (run_lengths_nat (R2 n).dropLast).getLast? ≠ some 1 := by
  have hne : (R2 n).dropLast ≠ [] := by
    have hlen := R2_len_ge_four n hn
    have : (R2 n).dropLast.length = (R2 n).length - 1 := length_dropLast
    intro h; simp [h] at this; omega
  have h := getLast?_rle_eq_firstRunLen_reverse hne
  rw [h]
  have hge := R2_dropLast_lastRun_ge_three n hn
  intro heq
  have : firstRunLen (R2 n).dropLast.reverse = 1 := Option.some.inj heq
  omega

private theorem rle_dropLast_R1_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    run_lengths_nat (R1 n).dropLast = (R2 n).dropLast ++ [5] := by
  have hs6 := R1_ends_six_ones n hn
  have hs10 := R1_suffix10_ge_eleven n hn
  have hlen : 10 ≤ (R1 n).length := by
    have : 36 ≤ (R1 n).length := R1_length_ge_eleven n hn
    omega
  have hsplit0 : R1 n = (R1 n).take ((R1 n).length - 6) ++ [1, 1, 1, 1, 1, 1] := by
    have := take_append_drop ((R1 n).length - 6) (R1 n)
    rw [hs6] at this
    exact this.symm
  generalize hpre : (R1 n).take ((R1 n).length - 6) = pre
  rw [hpre] at hsplit0
  have hpreLast : pre.getLast? = some 3 := by
    have htake : (R1 n).take ((R1 n).length - 6) =
        (R1 n).take ((R1 n).length - 10) ++ [1, 5, 1, 3] := by
      have hcalc : (R1 n).length - 6 = (R1 n).length - 10 + 4 := by omega
      rw [hcalc, take_add, hs10]
      simp
    rw [← hpre, htake, getLast?_append_of_right_ne]
    · simp
    · simp
  have hp : pre ≠ [] := by intro h; simp [h] at hpreLast
  have hne : pre.getLast? ≠ ([1, 1, 1, 1, 1, 1] : List ℕ).head? := by
    rw [hpreLast]; simp
  have hrle := run_lengths_nat_append_ne pre [1, 1, 1, 1, 1, 1] (by simp) hne
  have hR2 : R2 n = run_lengths_nat pre ++ [6] := by
    unfold R2
    rw [hsplit0, hrle, rle_six_ones]
  have hR2dl : (R2 n).dropLast = run_lengths_nat pre := by
    rw [hR2, dropLast_concat]
  have hdl : (R1 n).dropLast = pre ++ [1, 1, 1, 1, 1] := by
    have : (R1 n).dropLast = (R1 n).take ((R1 n).length - 1) := dropLast_eq_take
    have hcalc : (R1 n).length - 1 = (R1 n).length - 6 + 5 := by omega
    rw [this, hcalc, take_add, hs6, hpre]
    simp
  have hne' : pre.getLast? ≠ ([1, 1, 1, 1, 1] : List ℕ).head? := by
    rw [hpreLast]; simp
  have hrle' := run_lengths_nat_append_ne pre [1, 1, 1, 1, 1] (by simp) hne'
  rw [hdl, hrle', rle_five_ones, hR2dl]

private theorem R2_succ_of_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    R2 (n + 1) =
      (R2 n).dropLast ++ [5, 1] ++
        (run_lengths_nat (R2 n).dropLast).reverse := by
  have hR1 := R1_succ_of_ge_eleven n hn
  have hR2dlNe : (R2 n).dropLast ≠ [] := by
    have hlen := R2_len_ge_four n hn
    have : (R2 n).dropLast.length = (R2 n).length - 1 := length_dropLast
    intro h; simp [h] at this; omega
  have h12 : ((R1 n).dropLast).getLast? ≠ ([7] : List ℕ).head? := by
    rw [R1_dropLast_getLast?_ge_eleven n hn]; simp
  have h23 : ([7] : List ℕ).getLast? ≠ ((R2 n).dropLast.reverse).head? := by
    rw [head?_reverse, R2_dropLast_getLast?_ge_eleven n hn]; simp
  have happ :=
    run_lengths_nat_append3_ne (R1 n).dropLast [7] (R2 n).dropLast.reverse
      (by simp) (by simp [hR2dlNe]) h12 h23
  change run_lengths_nat (R1 (n + 1)) = _
  rw [hR1, happ, run_lengths_nat_singleton, rle_dropLast_R1_ge_eleven n hn,
      run_lengths_nat_reverse]
  simp [append_assoc]

private theorem R3_succ_of_ge_eleven (n : ℕ) (hn : 11 ≤ n) :
    R3 (n + 1) = R3 n ++ (R4 n).reverse := by
  have hR2 := R2_succ_of_ge_eleven n hn
  have hR2dlNe : (R2 n).dropLast ≠ [] := by
    have hlen := R2_len_ge_four n hn
    have : (R2 n).dropLast.length = (R2 n).length - 1 := length_dropLast
    intro h; simp [h] at this; omega
  have hA : ((R2 n).dropLast).getLast? ≠ ([5, 1] : List ℕ).head? := by
    rw [R2_dropLast_getLast?_ge_eleven n hn]; simp
  have hBC : ([5, 1] : List ℕ).getLast? ≠
      (run_lengths_nat (R2 n).dropLast).reverse.head? := by
    rw [head?_reverse]
    intro h
    exact R2_dropLast_rle_getLast?_ne_one n hn (by simpa using h.symm)
  have happ :=
    run_lengths_nat_append3_ne (R2 n).dropLast [5, 1]
      (run_lengths_nat (R2 n).dropLast).reverse
      (by simp)
      (by exact reverse_ne_nil_iff.mpr (run_lengths_nat_ne_nil_of_ne_nil hR2dlNe))
      hA hBC
  have hR3' : R3 (n + 1) =
      run_lengths_nat (R2 n).dropLast ++ [1, 1] ++
        (run_lengths_nat (run_lengths_nat (R2 n).dropLast)).reverse := by
    change run_lengths_nat (R2 (n + 1)) = _
    rw [hR2, happ, rle_five_one, run_lengths_nat_reverse]
  have hR2split : R2 n = (R2 n).dropLast ++ [6] := by
    have hne : R2 n ≠ [] := R2_ne_nil_ge_eleven n hn
    have hlast : (R2 n).getLast hne = 6 := by
      have := R2_getLast?_ge_eleven n hn
      rw [getLast?_eq_some_getLast hne] at this
      exact Option.some.inj this
    simpa [hlast] using (dropLast_append_getLast hne).symm
  have hne6 : ((R2 n).dropLast).getLast? ≠ ([6] : List ℕ).head? := by
    rw [R2_dropLast_getLast?_ge_eleven n hn]; simp
  have hR3 : R3 n = run_lengths_nat (R2 n).dropLast ++ [1] := by
    generalize hdl : (R2 n).dropLast = d
    rw [hdl] at hR2split hne6
    unfold R3
    rw [hR2split, run_lengths_nat_append_ne d [6] (by simp) hne6,
        run_lengths_nat_singleton]
  have hne1 : (run_lengths_nat (R2 n).dropLast).getLast? ≠ ([1] : List ℕ).head? := by
    simpa using R2_dropLast_rle_getLast?_ne_one n hn
  have hR4 : R4 n =
      run_lengths_nat (run_lengths_nat (R2 n).dropLast) ++ [1] := by
    unfold R4
    rw [hR3, run_lengths_nat_append_ne (run_lengths_nat (R2 n).dropLast) [1]
      (by simp) hne1, run_lengths_nat_singleton]
  have hR4rev : (R4 n).reverse =
      [1] ++ (run_lengths_nat (run_lengths_nat (R2 n).dropLast)).reverse := by
    rw [hR4]; simp
  rw [hR3', hR3, hR4rev]
  simp [append_assoc]

private theorem R3_eq_Y (n : ℕ) (hn : 8 ≤ n) : R3 n = Y (n - 4) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simpa using R3_eq_Y_eight
  | succ n hn ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega
    | 8 => simpa using R3_eq_Y_nine
    | 9 => simpa using R3_eq_Y_ten
    | 10 => simpa using R3_eq_Y_eleven
    | k + 11 =>
      have hk : 11 ≤ k + 11 := by omega
      have hsucc := R3_succ_of_ge_eleven (k + 11) hk
      have ih' : R3 (k + 11) = Y (k + 7) := by
        simpa [show (k + 11) - 4 = k + 7 from rfl] using ih
      have hY : Y (k + 8) = Y (k + 7) ++ (run_lengths_nat (Y (k + 7))).reverse :=
        Y_succ (k + 7) (by omega)
      have hR4 : R4 (k + 11) = run_lengths_nat (Y (k + 7)) := by
        simp only [R4, ih']
      rw [show (k + 11) + 1 - 4 = k + 8 from rfl]
      rw [hsucc, ih', hR4, hY]

private theorem dseq_eq_S_add_four (n : ℕ) (hn : 8 ≤ n) :
    dseq n = A381358 (n - 4) + 4 := by
  have h1 : 1 ≤ n := by omega
  have h4 : 4 ≤ n - 4 := by omega
  rw [dseq_eq_sum_R3 n h1, R3_eq_Y n hn, Y_sum (n - 4) h4]

private theorem A381358_succ_le_two (n : ℕ) (hn : 1 ≤ n) :
    A381358 (n + 1) ≤ 2 * A381358 n := by
  match n with
  | 0 => omega
  | 1 =>
    change A381358 2 ≤ 2 * A381358 1
    simp [A381358_one, A381358_two]
  | 2 =>
    change A381358 3 ≤ 2 * A381358 2
    simp [A381358_two, A381358_three]
  | k + 3 =>
    have h3 : 3 ≤ k + 3 := by omega
    rw [A381358_succ_of_ge_three (k + 3) h3]
    have : Tlen (k + 3) ≤ A381358 (k + 3) := Tlen_le_sum (k + 3)
    omega

/-- `s n ≤ 2^n`. -/
private theorem A381358_le_pow_two : ∀ n : ℕ, A381358 n ≤ 2 ^ n
  | 0 => by simp [A381358_zero]
  | 1 => by simp [A381358_one]
  | k + 2 => by
    have hle : A381358 (k + 2) ≤ 2 * A381358 (k + 1) :=
      A381358_succ_le_two (k + 1) (by omega)
    have ih : A381358 (k + 1) ≤ 2 ^ (k + 1) := A381358_le_pow_two (k + 1)
    calc
      A381358 (k + 2) ≤ 2 * A381358 (k + 1) := hle
      _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 2) := by rw [← pow_succ']

/-- Fekete for a supermultiplicative positive sequence bounded by `2^n`. -/
private theorem tendsto_nthRoot_of_supermul
    (s : ℕ → ℕ)
    (hpos : ∀ n, 1 ≤ n → 0 < s n)
    (hsm : ∀ m n, 1 ≤ m → 1 ≤ n → s m * s n ≤ s (m + n))
    (hge : ∀ n, s n ≤ 2 ^ n) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (s n : ℝ) ^ ((n : ℝ) ⁻¹)) atTop (nhds L) := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else -Real.log (s n : ℝ)
  have hsub : Subadditive u := by
    intro m n
    by_cases hm : m = 0
    · simp [u, hm]
    by_cases hn0 : n = 0
    · simp [u, hn0]
    have hm1 : 1 ≤ m := by omega
    have hn1 : 1 ≤ n := by omega
    have smpos : (0 : ℝ) < s m := by exact_mod_cast hpos m hm1
    have snpos : (0 : ℝ) < s n := by exact_mod_cast hpos n hn1
    have smnpos : (0 : ℝ) < s (m + n) := by exact_mod_cast hpos (m + n) (by omega)
    have hmul : (s m : ℝ) * s n ≤ s (m + n) := by exact_mod_cast hsm m n hm1 hn1
    simp only [u, hm, hn0, show m + n ≠ 0 by omega, ↓reduceIte]
    have : Real.log (s m : ℝ) + Real.log (s n : ℝ) ≤ Real.log (s (m + n) : ℝ) := by
      rw [← Real.log_mul (ne_of_gt smpos) (ne_of_gt snpos)]
      exact Real.log_le_log (mul_pos smpos snpos) hmul
    linarith
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨-Real.log 2, ?_⟩
    rintro y ⟨n, rfl⟩
    by_cases hn0 : n = 0
    · subst hn0
      simp [u]
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hn1 : 1 ≤ n := by omega
    have snpos : (0 : ℝ) < s n := by exact_mod_cast hpos n hn1
    have hle : (s n : ℝ) ≤ (2 : ℝ) ^ n := by
      have := hge n
      exact_mod_cast this
    have hlog : Real.log (s n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
      Real.log_le_log snpos hle
    have hlog2 : Real.log ((2 : ℝ) ^ n) = n * Real.log 2 :=
      Real.log_pow 2 n
    simp only [u, hn0, ↓reduceIte]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have : -Real.log (s n : ℝ) / (n : ℝ) ≥ -(n : ℝ) * Real.log 2 / (n : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ hnpos.le
      linarith [hlog, hlog2]
    have : -(n : ℝ) * Real.log 2 / (n : ℝ) = -Real.log 2 := by
      field_simp
    linarith
  have htend := hsub.tendsto_lim hbdd
  refine ⟨Real.exp (-hsub.lim), ?_⟩
  have hev : (fun n : ℕ => (s n : ℝ) ^ ((n : ℝ) ⁻¹))
      =ᶠ[atTop] fun n => Real.exp (-u n / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    have snpos : (0 : ℝ) < s n := by exact_mod_cast hpos n (by omega)
    simp only [u, hn0, ↓reduceIte]
    have : Real.exp (Real.log (s n : ℝ) / n) = (s n : ℝ) ^ ((n : ℝ) ⁻¹) := by
      rw [Real.rpow_def_of_pos snpos, div_eq_mul_inv, mul_comm]
    convert this.symm using 1
    congr 1
    ring
  refine Tendsto.congr' hev.symm ?_
  have hcomp : Tendsto (fun n : ℕ => -u n / (n : ℝ)) atTop (nhds (-hsub.lim)) := by
    convert htend.neg using 1
    ext n
    rw [neg_div]
  exact (Real.continuous_exp.tendsto _).comp hcomp

private theorem numRuns_le_length (l : List ℕ) : numRuns l ≤ l.length := by
  have hsum := run_lengths_nat_sum l
  have hpos := run_lengths_nat_entries_pos l
  have : (run_lengths_nat l).length ≤ (run_lengths_nat l).sum :=
    List.length_le_sum_of_one_le _ hpos
  simpa [numRuns, hsum] using this

private theorem cseq_le_Tlen (n : ℕ) : cseq n ≤ Tlen n := by
  simpa [cseq, Tlen] using numRuns_le_length (A381587_T n)

private theorem cseq_succ_eq (n : ℕ) (hn : 6 ≤ n) :
    cseq (n + 1) = cseq n + dseq n - 1 := by
  have h := cseq_succ_of_ge_six n hn
  omega

private theorem cseq_succ_of_ge_eight (n : ℕ) (hn : 8 ≤ n) :
    cseq (n + 1) = cseq n + A381358 (n - 4) + 3 := by
  have hC := cseq_succ_eq n (by omega)
  have hD := dseq_eq_S_add_four n hn
  have hpos : 1 ≤ cseq n + dseq n := by
    have : 1 ≤ dseq n := dseq_pos n (by omega)
    omega
  omega

private theorem exists_lam : ∃ r : ℝ, 1 < r ∧ r ^ 4 * (r - 1) ^ 3 = 1 := by
  let g : ℝ → ℝ := fun x => x ^ 4 * (x - 1) ^ 3 - 1
  have hgcont : Continuous g :=
    ((continuous_pow 4).mul (((continuous_id.sub continuous_const).pow 3))).sub
      continuous_const
  have hg1 : g 1 = -1 := by norm_num
  have hg2 : g 2 = 15 := by norm_num
  have hsub : Set.Icc (g 1) (g 2) ⊆ g '' Set.Icc (1 : ℝ) 2 :=
    intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hgcont.continuousOn
  have hz : (0 : ℝ) ∈ Set.Icc (g 1) (g 2) := by
    rw [hg1, hg2]; constructor <;> norm_num
  rcases hsub hz with ⟨r, hrI, hr0⟩
  have hrge : 1 ≤ r := hrI.1
  have hrne : r ≠ 1 := by
    intro h
    subst h
    change (1 : ℝ) ^ 4 * (1 - 1) ^ 3 - 1 = 0 at hr0
    norm_num at hr0
  refine ⟨r, lt_of_le_of_ne hrge hrne.symm, ?_⟩
  change r ^ 4 * (r - 1) ^ 3 - 1 = 0 at hr0
  linarith

private noncomputable def lam : ℝ := Classical.choose exists_lam

private theorem lam_gt_one : 1 < lam :=
  (Classical.choose_spec exists_lam).1

private theorem lam_spec : lam ^ 4 * (lam - 1) ^ 3 = 1 :=
  (Classical.choose_spec exists_lam).2

private theorem lam_sub_one_pos : 0 < lam - 1 :=
  sub_pos.mpr lam_gt_one

private noncomputable def phi (n : ℕ) : ℝ :=
  ((A381358 n : ℝ) + 3) +
    (1 / (lam - 1)) * (Tlen n : ℝ) +
    (1 / (lam - 1) ^ 2) * (cseq n : ℝ) +
    (lam - 1) * ((A381358 (n - 1) : ℝ) + 3) +
    (lam * (lam - 1)) * ((A381358 (n - 2) : ℝ) + 3) +
    (lam ^ 2 * (lam - 1)) * ((A381358 (n - 3) : ℝ) + 3) +
    (lam ^ 3 * (lam - 1)) * ((A381358 (n - 4) : ℝ) + 3)

private theorem phi_succ (n : ℕ) (hn : 8 ≤ n) :
    phi (n + 1) = lam * phi n := by
  have hS : (A381358 (n + 1) : ℝ) = (A381358 n : ℝ) + (Tlen n : ℝ) := by
    exact_mod_cast A381358_succ_of_ge_three n (by omega)
  have hL : (Tlen (n + 1) : ℝ) = (Tlen n : ℝ) + (cseq n : ℝ) := by
    have := Tlen_succ n (by omega)
    exact_mod_cast this.trans (add_comm _ _)
  have hC : (cseq (n + 1) : ℝ) =
      (cseq n : ℝ) + (A381358 (n - 4) : ℝ) + 3 := by
    exact_mod_cast cseq_succ_of_ge_eight n hn
  have hnm1 : n + 1 - 1 = n := by omega
  have hnm2 : n + 1 - 2 = n - 1 := by omega
  have hnm3 : n + 1 - 3 = n - 2 := by omega
  have hnm4 : n + 1 - 4 = n - 3 := by omega
  have ha : 1 / (lam - 1) * lam = 1 / (lam - 1) + 1 := by
    have : lam - 1 ≠ 0 := ne_of_gt lam_sub_one_pos
    field_simp
    ring
  have hb : 1 / (lam - 1) ^ 2 * lam = 1 / (lam - 1) + 1 / (lam - 1) ^ 2 := by
    have : lam - 1 ≠ 0 := ne_of_gt lam_sub_one_pos
    field_simp
    ring
  have hc : 1 / (lam - 1) ^ 2 = lam ^ 4 * (lam - 1) := by
    have h := lam_spec
    have : lam - 1 ≠ 0 := ne_of_gt lam_sub_one_pos
    field_simp at h ⊢
    nlinarith
  have hpos : lam - 1 ≠ 0 := ne_of_gt lam_sub_one_pos
  have hspec := lam_spec
  simp only [phi, hS, hL, hC, hnm1, hnm2, hnm3, hnm4]
  field_simp [hpos]
  ring_nf
  have hcancel : lam ^ 4 * (lam - 1) ^ 3 = 1 := hspec
  -- after field_simp, the identity reduces using lam^4 (lam-1)^3 = 1
  nlinarith [hspec, sq_nonneg (lam - 1), sq_nonneg lam]

private theorem phi_eq_pow (n : ℕ) (hn : 8 ≤ n) :
    phi n = lam ^ (n - 8) * phi 8 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [phi_succ n hn, ih]
    have : n + 1 - 8 = n - 8 + 1 := by omega
    rw [this, pow_succ, mul_assoc, mul_left_comm]

private theorem phi_eight_pos : 0 < phi 8 := by
  have hlam : 0 < lam - 1 := lam_sub_one_pos
  have hS : (0 : ℝ) ≤ (A381358 8 : ℝ) := by exact_mod_cast Nat.zero_le _
  have hL : (0 : ℝ) ≤ (Tlen 8 : ℝ) := by exact_mod_cast Nat.zero_le _
  have hC : (0 : ℝ) ≤ (cseq 8 : ℝ) := by exact_mod_cast Nat.zero_le _
  have h3 : (0 : ℝ) < 3 := by norm_num
  simp only [phi]
  nlinarith [pow_pos hlam 2, mul_pos (lt_trans zero_lt_one lam_gt_one) hlam,
    mul_pos (pow_pos (lt_trans zero_lt_one lam_gt_one) 2) hlam,
    mul_pos (pow_pos (lt_trans zero_lt_one lam_gt_one) 3) hlam,
    div_pos (by norm_num : (0 : ℝ) < 1) hlam,
    div_pos (by norm_num : (0 : ℝ) < 1) (pow_pos hlam 2)]

private theorem phi_pos (n : ℕ) (hn : 8 ≤ n) : 0 < phi n := by
  rw [phi_eq_pow n hn]
  exact mul_pos (pow_pos (lt_trans zero_lt_one lam_gt_one) _) phi_eight_pos

private theorem phi_le_mul_S (n : ℕ) (hn : 8 ≤ n) :
    phi n ≤
      (1 + 1 / (lam - 1) + 1 / (lam - 1) ^ 2 + (lam - 1) +
        lam * (lam - 1) + lam ^ 2 * (lam - 1) + lam ^ 3 * (lam - 1)) *
        ((A381358 n : ℝ) + 3) := by
  have hlam : 0 < lam - 1 := lam_sub_one_pos
  have hSmono1 : A381358 (n - 1) ≤ A381358 n :=
    A381358_le_of_le (by omega) (by omega)
  have hSmono2 : A381358 (n - 2) ≤ A381358 n :=
    A381358_le_of_le (by omega) (by omega)
  have hSmono3 : A381358 (n - 3) ≤ A381358 n :=
    A381358_le_of_le (by omega) (by omega)
  have hSmono4 : A381358 (n - 4) ≤ A381358 n :=
    A381358_le_of_le (by omega) (by omega)
  have hL : Tlen n ≤ A381358 n := Tlen_le_sum n
  have hC : cseq n ≤ A381358 n := (cseq_le_Tlen n).trans hL
  have h1 : 0 ≤ 1 / (lam - 1) := le_of_lt (div_pos (by norm_num) hlam)
  have h2 : 0 ≤ 1 / (lam - 1) ^ 2 := le_of_lt (div_pos (by norm_num) (pow_pos hlam 2))
  have h3 : 0 ≤ lam - 1 := le_of_lt hlam
  have h4 : 0 ≤ lam * (lam - 1) := mul_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) h3
  have h5 : 0 ≤ lam ^ 2 * (lam - 1) :=
    mul_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) 2) h3
  have h6 : 0 ≤ lam ^ 3 * (lam - 1) :=
    mul_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) 3) h3
  simp only [phi]
  have : (Tlen n : ℝ) ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast (hL.trans (Nat.le_add_right _ 3))
  have : (cseq n : ℝ) ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast (hC.trans (Nat.le_add_right _ 3))
  have : (A381358 (n - 1) : ℝ) + 3 ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast Nat.add_le_add_right hSmono1 3
  have : (A381358 (n - 2) : ℝ) + 3 ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast Nat.add_le_add_right hSmono2 3
  have : (A381358 (n - 3) : ℝ) + 3 ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast Nat.add_le_add_right hSmono3 3
  have : (A381358 (n - 4) : ℝ) + 3 ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast Nat.add_le_add_right hSmono4 3
  nlinarith

private theorem S_le_phi (n : ℕ) : (A381358 n : ℝ) ≤ phi n := by
  have hlam : 0 < lam - 1 := lam_sub_one_pos
  simp only [phi]
  have : 0 ≤ (1 / (lam - 1)) * (Tlen n : ℝ) :=
    mul_nonneg (le_of_lt (div_pos (by norm_num) hlam)) (by exact_mod_cast Nat.zero_le _)
  have : 0 ≤ (1 / (lam - 1) ^ 2) * (cseq n : ℝ) :=
    mul_nonneg (le_of_lt (div_pos (by norm_num) (pow_pos hlam 2))) (by exact_mod_cast Nat.zero_le _)
  have : 0 ≤ (lam - 1) * ((A381358 (n - 1) : ℝ) + 3) :=
    mul_nonneg (le_of_lt hlam) (by linarith)
  have : 0 ≤ (lam * (lam - 1)) * ((A381358 (n - 2) : ℝ) + 3) :=
    mul_nonneg (mul_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) (le_of_lt hlam)) (by linarith)
  have : 0 ≤ (lam ^ 2 * (lam - 1)) * ((A381358 (n - 3) : ℝ) + 3) :=
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) 2) (le_of_lt hlam))
      (by linarith)
  have : 0 ≤ (lam ^ 3 * (lam - 1)) * ((A381358 (n - 4) : ℝ) + 3) :=
    mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one lam_gt_one)) 3) (le_of_lt hlam))
      (by linarith)
  linarith

private theorem tendsto_inv_nat_zero :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_const_rpow_inv (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((n : ℝ) ⁻¹)) atTop (nhds 1) := by
  have hexp : (fun n : ℕ => c ^ ((n : ℝ) ⁻¹)) =
      fun n : ℕ => Real.exp (Real.log c * (n : ℝ) ⁻¹) := by
    ext n
    rw [Real.rpow_def_of_pos hc, mul_comm]
  rw [hexp]
  have h0 : Tendsto (fun n : ℕ => Real.log c * (n : ℝ) ⁻¹) atTop (nhds 0) := by
    convert (tendsto_const_nhds (x := Real.log c)).mul tendsto_inv_nat_zero
    exact (mul_zero (Real.log c)).symm
  have hcomp := (Real.continuous_exp.tendsto 0).comp h0
  have hfun :
      Real.exp ∘ (fun n : ℕ => Real.log c * (n : ℝ) ⁻¹) =
        fun n : ℕ => Real.exp (Real.log c * (n : ℝ) ⁻¹) := rfl
  rw [hfun, Real.exp_zero] at hcomp
  exact hcomp

private theorem lam_pos : 0 < lam :=
  lt_trans zero_lt_one lam_gt_one

private noncomputable def phiBound : ℝ :=
  1 + 1 / (lam - 1) + 1 / (lam - 1) ^ 2 + (lam - 1) +
    lam * (lam - 1) + lam ^ 2 * (lam - 1) + lam ^ 3 * (lam - 1)

private theorem phiBound_pos : 0 < phiBound := by
  have hlam : 0 < lam - 1 := lam_sub_one_pos
  have hlam0 : 0 < lam := lam_pos
  simp only [phiBound]
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) hlam,
    div_pos (by norm_num : (0 : ℝ) < 1) (pow_pos hlam 2),
    mul_pos hlam0 hlam,
    mul_pos (pow_pos hlam0 2) hlam,
    mul_pos (pow_pos hlam0 3) hlam]

private theorem lam_pow_nat_rpow_inv (n : ℕ) (hn : 8 ≤ n) :
    (lam ^ (n - 8)) ^ ((n : ℝ)⁻¹) = lam ^ (((n : ℝ) - 8) / n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt lam_pos), div_eq_mul_inv,
    Nat.cast_sub hn]
  simp

private theorem tendsto_lam_rpow_ratio :
    Tendsto (fun n : ℕ => lam ^ (((n : ℝ) - 8) / n)) atTop (nhds lam) := by
  have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) - 8) / n) atTop (nhds 1) := by
    have heq : (fun n : ℕ => ((n : ℝ) - 8) / n) =ᶠ[atTop]
        fun n : ℕ => (1 : ℝ) - (8 : ℝ) * (n : ℝ)⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    refine Tendsto.congr' heq.symm ?_
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (8 : ℝ))).mul tendsto_inv_nat_zero)
    norm_num
  have hlim := (tendsto_const_nhds (x := lam)).rpow hdiv (Or.inl (ne_of_gt lam_pos))
  simpa [Real.rpow_one] using hlim

private theorem S_add_three_ge (n : ℕ) (hn : 8 ≤ n) :
    (phi 8 / phiBound) * lam ^ (n - 8) ≤ (A381358 n : ℝ) + 3 := by
  have hphi : phi n ≤ phiBound * ((A381358 n : ℝ) + 3) := phi_le_mul_S n hn
  have heq := phi_eq_pow n hn
  have hmul : lam ^ (n - 8) * phi 8 ≤ phiBound * ((A381358 n : ℝ) + 3) := by
    rw [← heq]; exact hphi
  calc
    (phi 8 / phiBound) * lam ^ (n - 8)
        = (lam ^ (n - 8) * phi 8) / phiBound := by ring
    _ ≤ (phiBound * ((A381358 n : ℝ) + 3)) / phiBound :=
      div_le_div_of_nonneg_right hmul (le_of_lt phiBound_pos)
    _ = (A381358 n : ℝ) + 3 := by field_simp [ne_of_gt phiBound_pos]

private theorem S_add_three_le (n : ℕ) (hn : 8 ≤ n) :
    (A381358 n : ℝ) + 3 ≤ (phi 8 + 3) * lam ^ (n - 8) := by
  have hS : (A381358 n : ℝ) ≤ phi n := S_le_phi n
  have heq := phi_eq_pow n hn
  have hpow : (1 : ℝ) ≤ lam ^ (n - 8) := one_le_pow₀ (le_of_lt lam_gt_one)
  calc
    (A381358 n : ℝ) + 3 ≤ phi n + 3 := by linarith
    _ = lam ^ (n - 8) * phi 8 + 3 := by rw [heq]
    _ ≤ lam ^ (n - 8) * phi 8 + 3 * lam ^ (n - 8) := by
      nlinarith [phi_eight_pos]
    _ = (phi 8 + 3) * lam ^ (n - 8) := by ring

private theorem tendsto_S_add_three_rpow :
    Tendsto (fun n : ℕ => ((A381358 n : ℝ) + 3) ^ ((n : ℝ)⁻¹)) atTop (nhds lam) := by
  let c1 := phi 8 / phiBound
  let c2 := phi 8 + 3
  have hc1 : 0 < c1 := div_pos phi_eight_pos phiBound_pos
  have hc2 : 0 < c2 := by linarith [phi_eight_pos]
  have hlo : Tendsto (fun n : ℕ => c1 ^ ((n : ℝ)⁻¹) * lam ^ (((n : ℝ) - 8) / n))
      atTop (nhds lam) := by
    convert (tendsto_const_rpow_inv c1 hc1).mul tendsto_lam_rpow_ratio
    exact (one_mul lam).symm
  have hhi : Tendsto (fun n : ℕ => c2 ^ ((n : ℝ)⁻¹) * lam ^ (((n : ℝ) - 8) / n))
      atTop (nhds lam) := by
    convert (tendsto_const_rpow_inv c2 hc2).mul tendsto_lam_rpow_ratio
    exact (one_mul lam).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 8] with n hn
    have hge := S_add_three_ge n hn
    have hn0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hbase : 0 ≤ c1 * lam ^ (n - 8) :=
      mul_nonneg (le_of_lt hc1) (pow_nonneg (le_of_lt lam_pos) _)
    have := Real.rpow_le_rpow hbase hge hn0
    rwa [Real.mul_rpow (le_of_lt hc1) (pow_nonneg (le_of_lt lam_pos) _),
      lam_pow_nat_rpow_inv n hn] at this
  · filter_upwards [eventually_ge_atTop 8] with n hn
    have hle := S_add_three_le n hn
    have hn0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hS3 : 0 ≤ (A381358 n : ℝ) + 3 := by exact_mod_cast Nat.zero_le (A381358 n + 3)
    have := Real.rpow_le_rpow hS3 hle hn0
    rwa [Real.mul_rpow (le_of_lt hc2) (pow_nonneg (le_of_lt lam_pos) _),
      lam_pow_nat_rpow_inv n hn] at this

private theorem tendsto_S_div_S_add_three_rpow :
    Tendsto (fun n : ℕ =>
      ((A381358 n : ℝ) / ((A381358 n : ℝ) + 3)) ^ ((n : ℝ)⁻¹)) atTop (nhds 1) := by
  have hlo := tendsto_const_rpow_inv ((1 : ℝ) / 4) (by norm_num)
  have hhi : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hS : (1 : ℝ) ≤ A381358 n := by exact_mod_cast A381358_pos n hn
    have hden : 0 < (A381358 n : ℝ) + 3 := by linarith
    have hfrac : (1 : ℝ) / 4 ≤ (A381358 n : ℝ) / ((A381358 n : ℝ) + 3) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden]
      nlinarith
    exact Real.rpow_le_rpow (by norm_num) hfrac (inv_nonneg.mpr (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hSpos : (0 : ℝ) < A381358 n := by exact_mod_cast A381358_pos n hn
    have hden : 0 < (A381358 n : ℝ) + 3 := by linarith
    have hfrac : (A381358 n : ℝ) / ((A381358 n : ℝ) + 3) ≤ 1 :=
      (div_le_one hden).mpr (by linarith)
    have hn0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hle := Real.rpow_le_rpow (div_nonneg (le_of_lt hSpos) (le_of_lt hden)) hfrac hn0
    simpa [Real.one_rpow] using hle

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  refine ⟨lam, ?_⟩
  have heq : (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ)⁻¹)) =ᶠ[atTop]
      fun n => ((A381358 n : ℝ) + 3) ^ ((n : ℝ)⁻¹) *
        ((A381358 n : ℝ) / ((A381358 n : ℝ) + 3)) ^ ((n : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hS : 0 ≤ (A381358 n : ℝ) := by exact_mod_cast Nat.zero_le _
    have hSpos : (0 : ℝ) < A381358 n := by exact_mod_cast A381358_pos n hn
    have hsum : 0 < (A381358 n : ℝ) + 3 := by linarith
    have hfrac : 0 ≤ (A381358 n : ℝ) / ((A381358 n : ℝ) + 3) :=
      div_nonneg hS (le_of_lt hsum)
    rw [← Real.mul_rpow (le_of_lt hsum) hfrac]
    congr 1
    field_simp [ne_of_gt hsum]
  refine Tendsto.congr' heq.symm ?_
  convert tendsto_S_add_three_rpow.mul tendsto_S_div_S_add_three_rpow
  exact (mul_one lam).symm
