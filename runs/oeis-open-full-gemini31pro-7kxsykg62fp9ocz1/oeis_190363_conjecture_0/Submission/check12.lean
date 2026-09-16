import Submission.Spec

lemma a_144 : a 144 = 484 := by
  dsimp [a]
  have h_floor : Int.floor ((144 : ℝ) * Real.sqrt (5/4)) = 160 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (144 : ℝ) = Real.sqrt 20736 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 144)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (20736 : ℝ) * (5/4) = 25920)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (144 : ℝ) = Real.sqrt 20736 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 144)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (20736 : ℝ) * (5/4) = 25920)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

lemma a_157 : a 157 = 528 := by
  dsimp [a]
  have h_floor : Int.floor ((157 : ℝ) * Real.sqrt (5/4)) = 175 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (157 : ℝ) = Real.sqrt 24649 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 157)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (24649 : ℝ) * (5/4) = 123245/4)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (157 : ℝ) = Real.sqrt 24649 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 157)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (24649 : ℝ) * (5/4) = 123245/4)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl

lemma a_161 : a 161 = 542 := by
  dsimp [a]
  have h_floor : Int.floor ((161 : ℝ) * Real.sqrt (5/4)) = 180 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h1 : (161 : ℝ) = Real.sqrt 25921 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 161)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (25921 : ℝ) * (5/4) = 129605/4)]
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    · push_cast
      have h1 : (161 : ℝ) = Real.sqrt 25921 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 161)]
        congr
        norm_num
      rw [h1, ← Real.sqrt_mul (by norm_num), (by norm_num : (25921 : ℝ) * (5/4) = 129605/4)]
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
  rw [h_floor]
  rfl
