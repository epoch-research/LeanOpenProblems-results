import FormalConjectures.Util.ProblemImports

open Real

lemma floor_val_nine_real : Int.toNat (Int.floor (((3 / 2 : ℝ) ^ (9 : ℝ)) : ℝ)) = 38 := by
  have h_eq : ((3 / 2 : ℝ) ^ (9 : ℝ)) = (3 / 2 : ℝ) ^ (9 : ℕ) := by
    exact rpow_natCast (3 / 2) 9
  have h_floor : Int.floor (((3 / 2 : ℝ) ^ (9 : ℝ)) : ℝ) = 38 := by
    rw [h_eq]
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
    · norm_num
  rw [h_floor]
  rfl
