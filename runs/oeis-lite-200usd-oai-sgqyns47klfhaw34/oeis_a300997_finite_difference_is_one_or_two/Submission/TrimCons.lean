import FormalConjectures.Util.ProblemImports
open List Nat

def trim (l : List ℕ) : List ℕ := (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

lemma dropWhile_append_of_neg {α} (p : α → Bool) (xs : List α) {a : α} (ha : p a = false) :
    (xs ++ [a]).dropWhile p = xs.dropWhile p ++ [a] := by
  induction xs with
  | nil => simp [ha]
  | cons b xs ih =>
      by_cases hb : p b = true
      · simp [List.dropWhile, hb, ih]
      · have hb' : p b = false := by cases h : p b <;> simp_all
        simp [List.dropWhile, hb']

lemma trim_cons_ne_zero {a : ℕ} (l : List ℕ) (ha : a ≠ 0) : trim (a::l) = a :: trim l := by
  unfold trim
  simp [List.reverse_cons]
  rw [dropWhile_append_of_neg]
  simp [ha]
