import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def trim (l : List ℕ) : List ℕ := (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
def rawStep (config : List ℕ) : List ℕ :=
  List.zipWith Nat.add (config.map half_ceil ++ [0]) (0 :: config.map half_floor)
def step (config : List ℕ) : List ℕ := trim (rawStep config)
def tailSum (l : List ℕ) (i : ℕ) : ℕ := (l.drop i).sum

lemma tailSum_append_zero (l : List ℕ) (i : ℕ) : tailSum (l ++ [0]) i = tailSum l i := by
  induction l generalizing i with
  | nil => cases i <;> simp [tailSum]
  | cons a l ih => cases i <;> simp [tailSum, ih]

lemma trim_append_zero (l : List ℕ) : trim (l ++ [0]) = trim l := by
  simp [trim]

lemma trim_append_ne_zero (l : List ℕ) {x : ℕ} (hx : x ≠ 0) : trim (l ++ [x]) = l ++ [x] := by
  simp [trim, List.reverse_append, hx]

lemma tailSum_trim (l : List ℕ) (i : ℕ) : tailSum (trim l) i = tailSum l i := by
  induction l using List.reverseRecOn generalizing i with
  | nil => simp [tailSum, trim]
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · subst x
        rw [trim_append_zero, ih, tailSum_append_zero]
      · rw [trim_append_ne_zero xs hx]

lemma rawStep_nil : rawStep [] = [] := by simp [rawStep]
lemma rawStep_cons (a : ℕ) (l : List ℕ) :
    rawStep (a::l) = (half_ceil a) :: (List.zipWith Nat.add (l.map half_ceil ++ [0]) (half_floor a :: l.map half_floor)) := by
  simp [rawStep]

lemma raw_tail_step (l : List ℕ) (i : ℕ) :
    tailSum (rawStep l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  induction l generalizing i with
  | nil => cases i <;> simp [rawStep, tailSum]
  | cons a l ih =>
      cases i with
      | zero =>
          simp [rawStep, tailSum, half_ceil, half_floor]
          -- need sum of zipWith equals floor a + sum l
          sorry
      | succ i =>
          -- after dropping first raw cell, the tail raw recurrence should recurse with carry half_floor a
          sorry

lemma tail_step (l : List ℕ) (i : ℕ) :
    tailSum (step l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  simp [step, tailSum_trim, raw_tail_step]
