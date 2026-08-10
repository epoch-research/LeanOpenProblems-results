import FormalConjectures.Util.ProblemImports

def check_range_bin_aux (f : ℕ → Bool) (start len : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if len == 0 then true
    else if len == 1 then f start
    else
      let half := len / 2
      check_range_bin_aux f start half fuel && check_range_bin_aux f (start + half) (len - half) fuel

def check_range_bin (f : ℕ → Bool) (start len : ℕ) : Bool :=
  check_range_bin_aux f start len len

theorem check_range_bin_aux_iff (f : ℕ → Bool) (fuel : ℕ) (start len : ℕ) (h_fuel : len ≤ fuel) :
    check_range_bin_aux f start len fuel = true ↔ ∀ i, start ≤ i ∧ i < start + len → f i = true := by
  induction fuel generalizing start len with
  | zero =>
    have : len = 0 := by omega
    subst this
    simp [check_range_bin_aux]
  | succ fuel ih =>
    simp only [check_range_bin_aux]
    by_cases h0 : len = 0
    · subst h0
      simp
    · by_cases h1 : len = 1
      · subst h1
        simp
        constructor
        · intro h i hi1 hi2
          have : i = start := by omega
          subst this
          exact h
        · intro h
          exact h start (by omega) (by omega)
      · have h_gt1 : len ≥ 2 := by omega
        have h_cond0 : (len == 0) = false := by simp [h0]
        have h_cond1 : (len == 1) = false := by simp [h1]
        simp [h_cond0, h_cond1]
        have h_half1 : len / 2 ≤ fuel := by omega
        have h_half2 : len - len / 2 ≤ fuel := by omega
        rw [ih start (len / 2) h_half1, ih (start + len / 2) (len - len / 2) h_half2]
        constructor
        · intro ⟨h_left, h_right⟩ i hi1 hi2
          by_cases h_split : i < start + len / 2
          · exact h_left i hi1 h_split
          · have : start + len / 2 ≤ i := by omega
            have : i < start + len / 2 + (len - len / 2) := by omega
            exact h_right i (by omega) (by omega)
        · intro h
          constructor
          · intro i hi1 hi2
            exact h i hi1 (by omega)
          · intro i hi1 hi2
            exact h i (by omega) (by omega)

theorem check_range_bin_iff (f : ℕ → Bool) (start len : ℕ) :
    check_range_bin f start len = true ↔ ∀ i, start ≤ i ∧ i < start + len → f i = true := by
  apply check_range_bin_aux_iff f len start len (by rfl)

