import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
def run_lengths_nat : List ℕ → List ℕ
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
def A381587_T : ℕ → List ℕ
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


/-
The reversed rows consist of pairs [x, 1]. Recording whether x differs from 1
reduces their evolution to a binary run derivative. A delayed identity for
three successive binary derivatives gives a seven-coordinate positive linear
recurrence. Its positive eigenvalue r satisfies r^4 * (r - 1)^3 = 1.
A positive weighted sum supplies two-sided geometric bounds; these bounds
also hold for the original row sums and hence give their root limit.
-/
namespace A381358Proof

-- Binary run derivative: a `true` emits whether it is followed by a `false`.
def deriv : List Bool → List Bool
  | [] => []
  | false :: w => deriv w
  | true :: w => (!w.headD true) :: deriv w

def H (w : List Bool) : List Bool := (deriv w).reverse

def word : ℕ → List Bool
  | 0 => [true]
  | n+1 => word n ++ H (word n)

@[simp] theorem deriv_nil : deriv [] = [] := rfl
@[simp] theorem deriv_false (w : List Bool) : deriv (false :: w) = deriv w := rfl
@[simp] theorem deriv_true (w : List Bool) :
    deriv (true :: w) = (!w.headD true) :: deriv w := rfl

@[simp] theorem H_nil : H [] = [] := rfl

@[simp] theorem H_false (w : List Bool) : H (false :: w) = H w := rfl
@[simp] theorem H_true (w : List Bool) :
    H (true :: w) = H w ++ [!w.headD true] := by simp [H]

@[simp] theorem deriv_append_true (u v : List Bool) :
    deriv (u ++ true :: v) = deriv u ++ deriv (true :: v) := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    cases x
    · simpa using ih
    · simp only [cons_append, deriv_true, ih, cons_append]
      congr 2
      cases u <;> rfl

@[simp] theorem H_append_true (u v : List Bool) :
    H (u ++ true :: v) = H (true :: v) ++ H u := by
  simp [H]

-- A boundary ending in true changes its final emitted bit when followed by false.
theorem H_append_tf (u v : List Bool) :
    H ((u ++ [true]) ++ false :: v) = H v ++ [true] ++ H u := by
  rw [append_assoc, singleton_append, H_append_true]
  simp [H_true, append_assoc]

-- Gap indicators, including the two end gaps.
def gaps : List Bool → List Bool
  | [] => [false]
  | true :: w => false :: gaps w
  | false :: w => true :: (gaps w).tail

@[simp] theorem gaps_ne_nil (w : List Bool) : gaps w ≠ [] := by
  cases w with
  | nil => simp [gaps]
  | cons b w => cases b <;> simp [gaps]

@[simp] theorem deriv_true_eq_gaps (w : List Bool) : deriv (true :: w) = gaps w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp only [deriv_true, headD_cons, Bool.not_false, deriv_false, gaps]
      rw [← ih]
      rfl
    · simp only [deriv_true, headD_cons, Bool.not_true, gaps] at *
      rw [ih]

@[simp] theorem gaps_append_true (w : List Bool) : gaps (w ++ [true]) = gaps w ++ [false] := by
  rw [← deriv_true_eq_gaps, ← cons_append, deriv_append_true]
  change deriv (true :: w) ++ [false] = gaps w ++ [false]
  rw [deriv_true_eq_gaps]

@[simp] theorem gaps_append_false (w : List Bool) :
    gaps (w ++ [false]) = (gaps w).dropLast ++ [true] := by
  induction w with
  | nil => simp [gaps]
  | cons b w ih =>
    cases b
    · simp only [cons_append, gaps, ih]
      have h := gaps_ne_nil w
      cases hg : gaps w with
      | nil => exact (h hg).elim
      | cons a l =>
        cases l <;> simp_all
    · simp only [cons_append, gaps, ih]
      simp [dropLast_cons_of_ne_nil (gaps_ne_nil w)]

@[simp] theorem gaps_reverse (w : List Bool) : gaps w.reverse = (gaps w).reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp only [reverse_cons, gaps_append_false, ih, gaps]
      rw [dropLast_reverse]
    · simp [gaps, ih]

-- Shifting the distinguished first true past reversal shifts one emitted bit.
theorem reverse_shift (v : List Bool) :
    H ((v ++ [true]).reverse) ++ [false] = deriv (true :: (v ++ [true])) := by
  simp only [reverse_append, reverse_singleton, singleton_append, H,
    deriv_true_eq_gaps, gaps_reverse, reverse_reverse, gaps_append_true]


theorem word_prefix (n : ℕ) : ∃ v, word (n+1) = true :: false :: v := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨v ++ H (word (n+1)), by rw [word, hv]; rfl⟩

theorem word_ends (n : ℕ) : ∃ v, word (n+2) = true :: (v ++ [true]) := by
  obtain ⟨v, hv⟩ := word_prefix n
  refine ⟨(false :: v) ++ H v, ?_⟩
  rw [show n+2 = (n+1)+1 by omega, word, hv]
  simp [append_assoc]

theorem H_word_ends (n : ℕ) : ∃ v, H (word (n+1)) = v ++ [true] := by
  obtain ⟨v, hv⟩ := word_prefix n
  exact ⟨H v, by simp [hv]⟩

theorem H_step {w : List Bool} (hw : ∃ u, w = u ++ [true])
    (hh : ∃ v, H w = false :: v) :
    H (w ++ H w) = H (H w) ++ true :: (H w).tail := by
  obtain ⟨u, rfl⟩ := hw
  obtain ⟨v, hv⟩ := hh
  have hu : H u = v := by
    simpa using hv
  rw [hv, H_append_tf]
  simp [hu]

theorem HH_step {w : List Bool} (hw : ∃ u, w = u ++ [true])
    (hh : ∃ v, H w = false :: false :: v) :
    H (H (w ++ H w)) = H (H w) ++ [true] ++ H (H (H w)) := by
  obtain ⟨v, hv⟩ := hh
  rw [H_step hw ⟨false :: v, hv⟩, H_append_true]
  simp [hv, append_assoc]

theorem binary_structure (n : ℕ) :
    (∃ v, H (word (n+6)) = false :: false :: v) ∧
    (∃ v, H (H (word (n+6))) = false :: false :: v) ∧
    H (H (H (word (n+6)))) = (word (n+2)).tail.reverse := by
  induction n with
  | zero => exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩
  | succ n ih =>
    rcases ih with ⟨⟨v, hv⟩, ⟨u, hu⟩, hr⟩
    obtain ⟨t, ht⟩ := word_ends (n+4)
    have hw : ∃ t, word (n+6) = t ++ [true] :=
      ⟨true :: t, by simpa [cons_append] using ht⟩
    have h1 := H_step hw ⟨false :: v, hv⟩
    have h2 := HH_step hw ⟨v, hv⟩
    change (∃ v, H (word (n+6) ++ H (word (n+6))) = false :: false :: v) ∧
      (∃ v, H (H (word (n+6) ++ H (word (n+6)))) = false :: false :: v) ∧
      H (H (H (word (n+6) ++ H (word (n+6))))) = (word (n+3)).tail.reverse
    refine ⟨⟨u ++ true :: (H (word (n+6))).tail, ?_⟩,
      ⟨u ++ [true] ++ H (H (H (word (n+6)))), ?_⟩, ?_⟩
    · rw [h1, hu]; rfl
    · rw [h2, hu]; rfl
    · rw [h2, append_assoc, singleton_append, H_append_true, hr]
      obtain ⟨s, hs⟩ := word_ends n
      rw [hs]
      simp only [tail_cons, reverse_append, reverse_singleton, singleton_append,
        H_true, headD_cons, Bool.not_true]
      rw [← H_true]
      -- The last bit closes the derivative of the earlier word.
      have he := reverse_shift s
      simp only [reverse_append, reverse_singleton, singleton_append] at he
      rw [he]
      rw [show n+3 = (n+2)+1 by omega, word, hs]
      simp [H, append_assoc]


-- Relating the binary model to the natural-number rows.
def pairs (w : List ℕ) : List ℕ := w.flatMap (fun x => [x, 1])

@[simp] theorem pairs_nil : pairs [] = [] := rfl
@[simp] theorem pairs_cons (x : ℕ) (w : List ℕ) :
    pairs (x :: w) = x :: 1 :: pairs w := rfl
@[simp] theorem pairs_append (u v : List ℕ) : pairs (u ++ v) = pairs u ++ pairs v := by
  simp [pairs]
@[simp] theorem length_pairs (w : List ℕ) : (pairs w).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons x w ih => simp [ih]; omega

-- Emit the (odd) lengths of the intervening strings of ones.
def gapN (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | x :: w => if x = 1 then gapN (k+2) w else k :: gapN 1 w

def scanN (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | x :: w => if x = 1 then scanN (k+2) w else k :: 1 :: scanN 1 w

theorem runs_block (k a b : ℕ) (w : List ℕ) (hab : b ≠ a) :
    run_lengths_nat (replicate (k+1) a ++ b :: w) =
      (k+1) :: run_lengths_nat (b :: w) := by
  have ht : (replicate k a ++ b :: w).takeWhile (fun x => decide (x = a)) =
      replicate k a := by
    rw [takeWhile_append_of_pos (by simp)]
    simp [takeWhile_cons_of_neg, hab]
  rw [replicate_succ, cons_append, run_lengths_nat]
  simp [takeWhile_cons_of_pos, ht]

theorem runs_replicate (k a : ℕ) : run_lengths_nat (replicate (k+1) a) = [k+1] := by
  rw [replicate_succ, run_lengths_nat]
  simp [run_lengths_nat]

theorem runs_pair_aux (w : List ℕ) (k : ℕ) :
    run_lengths_nat (replicate (k+1) 1 ++ pairs w) = scanN (k+1) w := by
  induction w generalizing k with
  | nil => simp [scanN, runs_replicate]
  | cons x w ih =>
    by_cases hx : x = 1
    · subst x
      have he : replicate (k+1) 1 ++ pairs (1 :: w) =
          replicate ((k+2)+1) 1 ++ pairs w := by
        simp only [pairs_cons]
        rw [show (k+2)+1 = (k+1)+2 by omega, replicate_add (k+1) 2 1]
        simp only [replicate_succ, replicate_zero, append_assoc]
        rfl
      rw [he, ih]
      simp [scanN]
    · rw [pairs_cons, runs_block k 1 x _ hx]
      have he : run_lengths_nat (x :: 1 :: pairs w) = 1 :: run_lengths_nat (1 :: pairs w) := by
        simpa using runs_block 0 x 1 (pairs w) (Ne.symm hx)
      rw [he]
      simpa [scanN, hx] using congrArg (fun z => (k+1) :: 1 :: z) (ih 0)

theorem scanN_gapN (w : List ℕ) (k : ℕ) :
    1 :: scanN k w = (gapN k w).flatMap (fun x => [1, x]) := by
  induction w generalizing k with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : x = 1
    · simp [scanN, gapN, hx, ih]
    · simp [scanN, gapN, hx, ← ih]

theorem runs_pairs {a : ℕ} (ha : a ≠ 1) (w : List ℕ) :
    (run_lengths_nat (pairs (a :: w))).reverse = pairs (gapN 1 w).reverse := by
  have he : run_lengths_nat (a :: 1 :: pairs w) = 1 :: run_lengths_nat (1 :: pairs w) := by
    simpa using runs_block 0 a 1 (pairs w) (Ne.symm ha)
  rw [pairs_cons, he]
  have hr := runs_pair_aux w 0
  simp only [zero_add, replicate_one, singleton_append] at hr
  rw [hr, scanN_gapN]
  simp [pairs, reverse_flatMap, Function.comp_def]

def mark (x : ℕ) : Bool := decide (x ≠ 1)

def flags (b : Bool) : List Bool → List Bool
  | [] => [b]
  | false :: w => flags true w
  | true :: w => b :: flags false w

theorem flags_eq (w : List Bool) (b : Bool) :
    flags b w = (b || !w.headD true) :: deriv w := by
  induction w generalizing b with
  | nil => simp [flags]
  | cons a w ih =>
    cases a <;> simp [flags, ih]

theorem gapN_mark (w : List ℕ) {k : ℕ} (hk : 0 < k) :
    (gapN k w).map mark = flags (mark k) (w.map mark) := by
  induction w generalizing k with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : x = 1
    · have hmark : mark (k+2) = true := by simp [mark]
      simp only [gapN, if_pos hx, map_cons]
      rw [ih (by omega), hmark]
      simp [hx, mark, flags]
    · simp only [gapN, if_neg hx, map_cons]
      rw [ih (by decide : 0 < 1)]
      simp [mark, hx, flags]

theorem gapN_one_mark (w : List ℕ) :
    (gapN 1 w).map mark = deriv (true :: w.map mark) := by
  rw [gapN_mark w (by decide), flags_eq]
  simp [mark]

def numWord : ℕ → List ℕ
  | 0 => [2]
  | n+1 => numWord n ++ (gapN 1 (numWord n).tail).reverse

theorem numWord_prefix (n : ℕ) : ∃ v, numWord n = 2 :: v := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    exact ⟨v ++ (gapN 1 (numWord n).tail).reverse, by rw [numWord, hv]; rfl⟩

theorem numWord_mark (n : ℕ) : (numWord n).map mark = word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨v, hv⟩ := numWord_prefix n
    rw [numWord, map_append, map_reverse, ih, word]
    congr 1
    rw [hv, tail_cons, gapN_one_mark]
    simp only [hv, map_cons] at ih
    rw [← ih]
    rfl

theorem triangle_pairs (n : ℕ) : (A381587_T (n+4)).reverse = pairs (numWord n) := by
  induction n with
  | zero => norm_num [A381587_T, run_lengths_nat, pairs, numWord]
  | succ n ih =>
    rw [show n+1+4 = (n+1)+4 by omega, A381587_T]
    rw [show n+1+3 = n+4 by omega, reverse_append, ih]
    obtain ⟨v, hv⟩ := numWord_prefix n
    rw [numWord, pairs_append, hv, tail_cons, runs_pairs (by decide : 2 ≠ 1)]

theorem triangle_length (n : ℕ) : (A381587_T (n+4)).length = 2 * (word n).length := by
  have he := congrArg List.length (triangle_pairs n)
  have hm := congrArg List.length (numWord_mark n)
  simpa only [length_reverse, length_pairs, ← hm, length_map] using he


theorem runs_sum (w : List ℕ) : (run_lengths_nat w).sum = w.length := by
  induction w using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 x w pref rest ih =>
    dsimp [rest, pref] at ih
    rw [run_lengths_nat]
    simp only [sum_cons, ih, length_drop]
    exact Nat.add_sub_of_le (takeWhile_sublist _).length_le

theorem runs_length_le (w : List ℕ) : (run_lengths_nat w).length ≤ w.length := by
  induction w using run_lengths_nat.induct with
  | case1 => simp [run_lengths_nat]
  | case2 x w pref rest ih =>
    dsimp [rest, pref] at ih
    rw [run_lengths_nat]
    simp only [length_cons]
    have hp : 0 < ((x :: w).takeWhile (fun a => decide (a = x))).length := by simp
    have hle := (takeWhile_sublist (l := x :: w) (fun a => decide (a = x))).length_le
    simp only [length_drop, length_cons] at ih hle
    omega

theorem row_sum_step (n : ℕ) :
    A381358 (n+5) = A381358 (n+4) + 2 * (word n).length := by
  have ht : A381587_T (n+5) =
      run_lengths_nat (A381587_T (n+4)).reverse ++ A381587_T (n+4) := by
    rw [show n+5 = (n+1)+4 by omega, A381587_T]
  simp only [A381358, ht, List.sum_append, runs_sum, length_reverse, triangle_length]
  omega

theorem row_sum_ge_length (n : ℕ) :
    (A381587_T (n+4)).length ≤ A381358 (n+4) := by
  induction n with
  | zero => norm_num [A381358, A381587_T, run_lengths_nat]
  | succ n ih =>
    have ht : A381587_T (n+1+4) =
        run_lengths_nat (A381587_T (n+4)).reverse ++ A381587_T (n+4) := by
      rw [A381587_T]
    simp only [A381358, ht, length_append, List.sum_append, runs_sum, length_reverse] at *
    have := runs_length_le (A381587_T (n+4)).reverse
    simp only [length_reverse] at this
    omega

-- The seven positive coordinates of the length recurrence.
def a (n : ℕ) : ℝ := (word n).length
def b (n : ℕ) : ℝ := (H (word n)).length
def c (n : ℕ) : ℝ := (H (H (word n))).length

theorem a_step (n : ℕ) : a (n+1) = a n + b n := by simp [a, b, word]

theorem b_step (n : ℕ) : b (n+7) = b (n+6) + c (n+6) := by
  rcases binary_structure n with ⟨⟨v, hv⟩, _, _⟩
  obtain ⟨t, ht⟩ := word_ends (n+4)
  have hw : ∃ t, word (n+6) = t ++ [true] :=
    ⟨true :: t, by simpa [cons_append] using ht⟩
  have he := congrArg List.length (H_step hw ⟨false :: v, hv⟩)
  simp only [hv, length_append, length_cons, tail_cons] at he
  unfold b c
  rw [show n+7 = (n+6)+1 by omega, word, hv, he]
  simp only [length_cons]
  push_cast
  ring

theorem c_step (n : ℕ) : c (n+7) = c (n+6) + a (n+2) := by
  rcases binary_structure n with ⟨hh, _, hr⟩
  obtain ⟨t, ht⟩ := word_ends (n+4)
  have hw : ∃ t, word (n+6) = t ++ [true] :=
    ⟨true :: t, by simpa [cons_append] using ht⟩
  have he := congrArg List.length (HH_step hw hh)
  rw [hr] at he
  obtain ⟨v, hv⟩ := word_ends n
  simp only [length_append, length_singleton, length_reverse, hv, tail_cons] at he
  unfold c a
  rw [show n+7 = (n+6)+1 by omega, word, he, hv]
  simp
  ring

theorem deriv_length_le (w : List Bool) : (deriv w).length ≤ w.length := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp_all <;> omega

theorem a_nonneg (n : ℕ) : 0 ≤ a n := Nat.cast_nonneg _
theorem b_nonneg (n : ℕ) : 0 ≤ b n := Nat.cast_nonneg _
theorem c_nonneg (n : ℕ) : 0 ≤ c n := Nat.cast_nonneg _

theorem a_pos (n : ℕ) : 0 < a n := by
  cases n with
  | zero => norm_num [a, word]
  | succ n => obtain ⟨v, hv⟩ := word_prefix n; simp [a, hv]; positivity

theorem a_mono : Monotone a := by
  apply monotone_nat_of_le_succ
  intro n
  rw [a_step]
  exact le_add_of_nonneg_right (b_nonneg n)

theorem b_le_a (n : ℕ) : b n ≤ a n := by
  unfold b a
  exact_mod_cast (show (H (word n)).length ≤ (word n).length by
    simpa [H] using deriv_length_le (word n))

theorem c_le_a (n : ℕ) : c n ≤ a n := by
  have he : c n ≤ b n := by
    unfold c b
    exact_mod_cast (show (H (H (word n))).length ≤ (H (word n)).length by
      simpa [H] using deriv_length_le (H (word n)))
  exact he.trans (b_le_a n)


-- A positive left eigenvector turns the seven-coordinate recurrence into
-- an exactly geometric sequence.
def mass (r : ℝ) (n : ℕ) : ℝ :=
  r^3 * a (n+2) + r^2 * a (n+3) + r * a (n+4) + a (n+5) +
  r^4 * (r-1)^2 * a (n+6) + r^4 * (r-1) * b (n+6) + r^4 * c (n+6)

def weights (r : ℝ) : ℝ :=
  r^3 + r^2 + r + 1 + r^4 * (r-1)^2 + r^4 * (r-1) + r^4

theorem exists_rate : ∃ r : ℝ, 1 < r ∧ r^4 * (r-1)^3 = 1 := by
  have hc : ContinuousOn (fun x : ℝ => x^4 * (x-1)^3) (Set.Icc 1 2) := by fun_prop
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hc
    (by norm_num : (1 : ℝ) ∈ Set.Icc ((1 : ℝ)^4 * (1-1)^3) ((2 : ℝ)^4 * (2-1)^3))
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, he⟩
  intro hh
  subst r
  norm_num at he

theorem mass_step {r : ℝ} (hr : r^4 * (r-1)^3 = 1) (n : ℕ) :
    mass r (n+1) = r * mass r n := by
  unfold mass
  simp only [show n+1+2 = n+3 by omega, show n+1+3 = n+4 by omega,
    show n+1+4 = n+5 by omega, show n+1+5 = n+6 by omega,
    show n+1+6 = n+7 by omega]
  rw [b_step, c_step, show n+7 = (n+6)+1 by omega, a_step (n+6)]
  linear_combination -a (n+6) * hr

theorem mass_eq {r : ℝ} (hr : r^4 * (r-1)^3 = 1) (n : ℕ) :
    mass r n = mass r 0 * r^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [mass_step hr, ih, pow_succ]; ring

theorem mass_pos {r : ℝ} (hr : 1 < r) (n : ℕ) : 0 < mass r n := by
  have h0 : 0 < r := by linarith
  have hd : 0 < r-1 := by linarith
  have := a_pos (n+2)
  have := a_nonneg (n+3)
  have := a_nonneg (n+4)
  have := a_nonneg (n+5)
  have := a_nonneg (n+6)
  have := b_nonneg (n+6)
  have := c_nonneg (n+6)
  unfold mass
  positivity

theorem weights_pos {r : ℝ} (hr : 1 < r) : 0 < weights r := by
  have h0 : 0 < r := by linarith
  have hd : 0 < r-1 := by linarith
  unfold weights
  positivity

theorem mass_upper {r : ℝ} (hr : 1 < r) (n : ℕ) :
    mass r n ≤ weights r * a (n+6) := by
  have h0 : 0 ≤ r := by linarith
  have hd : 0 ≤ r-1 := by linarith
  calc
    mass r n ≤ r^3 * a (n+6) + r^2 * a (n+6) + r * a (n+6) + a (n+6) +
        r^4 * (r-1)^2 * a (n+6) + r^4 * (r-1) * a (n+6) + r^4 * a (n+6) := by
      unfold mass
      gcongr
      · exact a_mono (by omega)
      · exact a_mono (by omega)
      · exact a_mono (by omega)
      · exact a_mono (by omega)
      · exact b_le_a _
      · exact c_le_a _
    _ = weights r * a (n+6) := by unfold weights; ring

theorem mass_lower {r : ℝ} (hr : 1 < r) (n : ℕ) :
    r^4 * (r-1)^2 * a (n+6) ≤ mass r n := by
  have h0 : 0 ≤ r := by linarith
  have hd : 0 ≤ r-1 := by linarith
  have h2 : 0 ≤ r^3 * a (n+2) := mul_nonneg (by positivity) (a_nonneg _)
  have h3 : 0 ≤ r^2 * a (n+3) := mul_nonneg (by positivity) (a_nonneg _)
  have h4 : 0 ≤ r * a (n+4) := mul_nonneg h0 (a_nonneg _)
  have h5 := a_nonneg (n+5)
  have hb : 0 ≤ r^4 * (r-1) * b (n+6) := mul_nonneg (by positivity) (b_nonneg _)
  have hc : 0 ≤ r^4 * c (n+6) := mul_nonneg (by positivity) (c_nonneg _)
  unfold mass
  linarith

theorem length_geometric_bounds {r : ℝ} (hr : 1 < r) (he : r^4 * (r-1)^3 = 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ n, C * r^n ≤ a (n+6) ∧ a (n+6) ≤ D * r^n := by
  have hw := weights_pos hr
  have hm := mass_pos hr 0
  have h0 : 0 < r := by linarith
  have hd : 0 < r-1 := by linarith
  have hp : 0 < r^4 * (r-1)^2 := by positivity
  refine ⟨mass r 0 / weights r, mass r 0 / (r^4 * (r-1)^2),
    div_pos hm hw, div_pos hm hp, fun n => ⟨?_, ?_⟩⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hw, ← mass_eq he]
    simpa [mul_comm] using mass_upper hr n
  · rw [div_mul_eq_mul_div, le_div_iff₀ hp, ← mass_eq he]
    simpa [mul_comm] using mass_lower hr n

theorem sum_geometric_bounds {r : ℝ} (hr : 1 < r) (he : r^4 * (r-1)^3 = 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ n, C * r^n ≤ (A381358 (n+10) : ℝ) ∧ (A381358 (n+10) : ℝ) ≤ D * r^n := by
  obtain ⟨C, D, hC, hD, hb⟩ := length_geometric_bounds hr he
  have h0 : 0 < r := by linarith
  have hd : 0 < r-1 := by linarith
  let U : ℝ := (A381358 10 : ℝ) + 2*D/(r-1)
  have hU : 0 < U := by dsimp [U]; positivity
  have hU0 : (A381358 10 : ℝ) ≤ U := by
    exact le_add_of_nonneg_right (by positivity)
  have hUd : 2*D ≤ U*(r-1) := by
    dsimp [U]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hd)]
    exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hd.le)
  refine ⟨C, U, hC, hU, fun n => ⟨?_, ?_⟩⟩
  · have hg : 2 * a (n+6) ≤ (A381358 (n+10) : ℝ) := by
      have ht := row_sum_ge_length (n+6)
      rw [triangle_length] at ht
      unfold a
      exact_mod_cast (by simpa [Nat.add_assoc] using ht :
        2 * (word (n+6)).length ≤ A381358 (n+10))
    have ha := a_nonneg (n+6)
    linarith [(hb n).1]
  · induction n with
    | zero => simpa using hU0
    | succ n ih =>
      have hs : (A381358 (n+1+10) : ℝ) = (A381358 (n+10) : ℝ) + 2*a (n+6) := by
        have hs := row_sum_step (n+6)
        unfold a
        exact_mod_cast (by simpa [Nat.add_assoc] using hs :
          A381358 (n+1+10) = A381358 (n+10) + 2 * (word (n+6)).length)
      rw [hs]
      calc
        (A381358 (n+10) : ℝ) + 2*a (n+6) ≤ U*r^n + 2*(D*r^n) := by
          gcongr
          exact (hb n).2
        _ ≤ U * r^(n+1) := by
          rw [pow_succ]
          have hh := mul_le_mul_of_nonneg_right hUd (pow_nonneg h0.le n)
          nlinarith


open Filter Topology in
theorem geometric_root_limit {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (k : ℕ) :
    Tendsto (fun n : ℕ => (C * r^n) ^ ((n+k : ℕ) : ℝ)⁻¹) atTop (𝓝 r) := by
  have hi : Tendsto (fun n : ℕ => ((n+k : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat k).2
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hq : Tendsto (fun n : ℕ => (n : ℝ) * ((n+k : ℕ) : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Nat.cast_add, ← div_eq_mul_inv] using tendsto_natCast_div_add_atTop (k : ℝ)
  have h₁ := (tendsto_const_nhds (x := C)).rpow hi (Or.inl (ne_of_gt hC))
  have h₂ := (tendsto_const_nhds (x := r)).rpow hq (Or.inl (ne_of_gt hr))
  have ht := h₁.mul h₂
  simpa only [Real.rpow_zero, Real.rpow_one, one_mul,
    Real.rpow_natCast_mul hr.le, ← Real.mul_rpow hC.le (pow_nonneg hr.le _)] using ht

open Filter Topology in
theorem root_limit : ∃ r : ℝ,
    Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 r) := by
  obtain ⟨r, hr, he⟩ := exists_rate
  obtain ⟨C, D, hC, hD, hb⟩ := sum_geometric_bounds hr he
  have h0 : 0 < r := by linarith
  refine ⟨r, (tendsto_add_atTop_iff_nat 10).1 ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (geometric_root_limit hC h0 10) (geometric_root_limit hD h0 10)
  · exact Filter.Eventually.of_forall fun n =>
      Real.rpow_le_rpow (by positivity) (hb n).1 (by positivity)
  · exact Filter.Eventually.of_forall fun n =>
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hb n).2 (by positivity)

end A381358Proof

/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by
  exact A381358Proof.root_limit

theorem A381358_limit_exists.disproof : ¬ (type_of% @A381358_limit_exists) := sorry
