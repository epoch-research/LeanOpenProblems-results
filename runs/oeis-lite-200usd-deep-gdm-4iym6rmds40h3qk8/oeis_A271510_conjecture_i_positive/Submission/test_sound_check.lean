import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let P := 0 < A271510 n
  -- H has type: ((((True → P) → P) → P) → P) → P
  -- can we construct a term of H?
  have h_H : ((((True → P) → P) → P) → P) → P := by
    intro h_A
    -- h_A : (((True → P) → P) → P) → P
    -- goal is P
    apply h_A
    -- goal is: ((True → P) → P) → P
    intro h_C
    -- h_C : (True → P) → P
    -- goal is P
    apply h_C
    -- goal is: True → P
    intro h_true
    -- goal is P
    -- wait, we still need P!
    sorry
