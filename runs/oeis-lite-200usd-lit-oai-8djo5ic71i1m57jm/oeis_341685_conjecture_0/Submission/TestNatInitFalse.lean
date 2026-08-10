import FormalConjectures.Util.ProblemImports

example : ¬ (0 ∣ (1:ℕ)) := by decide
example : ¬ (2 ∣ (1:ℕ)) := by decide

-- try all custom lemmas on suspect parameters
example : (0 ∣ (0:ℕ) - 1) ↔ (0 ∣ (1:ℕ) ∨ (0:ℕ) ≤ 1) := Nat.dvd_sub_iff_right' (by decide : (0:ℕ) ∣ 0)
example : (0 ∣ (1:ℕ) - 0) ↔ (0 ∣ (0:ℕ) ∨ (1:ℕ) ≤ 0) := Nat.dvd_sub_iff_left' (by decide : (0:ℕ) ∣ 0)

-- can this imply false?
example : False := by
  have h := (Nat.dvd_sub_iff_right' (a:=0) (b:=0) (c:=1) (by decide : (0:ℕ) ∣ 0)).2 (Or.inr (by norm_num))
  norm_num at h
