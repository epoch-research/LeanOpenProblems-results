import FormalConjectures.Util.ProblemImports
open List Nat Function Set

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2
def trim (l : List ℕ) : List ℕ := (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
def step (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim next_config_long

def tailSum (l : List ℕ) (i : ℕ) : ℕ := (l.drop i).sum

lemma tailSum_nil (i) : tailSum [] i = 0 := by simp [tailSum]
lemma tailSum_cons_zero (a l) : tailSum (a::l) 0 = a + tailSum l 0 := by simp [tailSum]
lemma tailSum_cons_succ (a l i) : tailSum (a::l) (i+1) = tailSum l i := by simp [tailSum]

lemma sum_trim (l : List ℕ) : (trim l).sum = l.sum := by
  unfold trim
  -- trailing zeros removed
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
      by_cases hx : x = 0
      · subst x
        simp [ih]
      · simp [List.reverse_append, hx]

lemma tailSum_trim_succ? (l : List ℕ) (i) : tailSum (trim l) (i+1) = tailSum l (i+1) := by
  -- false? trimming can affect drop beyond length only zeros, so true
  sorry

lemma tail_step (l : List ℕ) (i : ℕ) :
    tailSum (step l) (i+1) = (tailSum l i + tailSum l (i+1))/2 := by
  induction l generalizing i with
  | nil =>
      cases i <;> simp [step, tailSum, trim, half_ceil, half_floor]
  | cons a l ih =>
      cases i with
      | zero =>
          simp [step, tailSum, half_ceil, half_floor]
          sorry
      | succ i =>
          simp [step, tailSum, half_ceil, half_floor]
          sorry
