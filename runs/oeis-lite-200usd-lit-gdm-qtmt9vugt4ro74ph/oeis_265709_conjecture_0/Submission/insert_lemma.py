import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

old_ref = """lemma sum_two_pow_lt_two (b : ℕ) :
  (∑ j ∈ range (b + 1), ((1 : ℚ) / ((2^(j+1) : ℚ) - 1))) < 2 := by
  rw [Finset.sum_range_succ']
  have h_zero : ((1 : ℚ) / ((2^(0+1) : ℚ) - 1)) = 1 := by
    norm_num
  rw [h_zero]
  have h_le := sum_le_geom b
  have h_lt := geom_sum_half_lt_one b
  linarith"""

new_ref = """lemma sum_two_pow_lt_two (b : ℕ) :
  (∑ j ∈ range (b + 1), ((1 : ℚ) / ((2^(j+1) : ℚ) - 1))) < 2 := by
  rw [Finset.sum_range_succ']
  have h_zero : ((1 : ℚ) / ((2^(0+1) : ℚ) - 1)) = 1 := by
    norm_num
  rw [h_zero]
  have h_le := sum_le_geom b
  have h_lt := geom_sum_half_lt_one b
  linarith

lemma sum_two_pow_lt_eleven_six (b : ℕ) (hb : b ≥ 1) :
  (∑ j ∈ range (b + 1), ((1 : ℚ) / ((2^(j+1) : ℚ) - 1))) < 11 / 6 := by
  rw [Finset.sum_range_succ']
  have h_zero : ((1 : ℚ) / ((2^(0+1) : ℚ) - 1)) = 1 := by norm_num
  rw [h_zero]
  rw [Finset.sum_range_succ']
  have h_one : ((1 : ℚ) / ((2^(0+2) : ℚ) - 1)) = 1 / 3 := by norm_num
  rw [h_one]
  have h_le_geom : (∑ j ∈ range (b - 1), ((1 : ℚ) / ((2^(j+3) : ℚ) - 1))) ≤ (∑ j ∈ range (b - 1), (1 / 2 : ℚ)^(j+2)) := by
    apply sum_le_sum
    intro j hj
    have := term_le_geom_le (j+1)
    exact this
  have h_geom_sum : (∑ j ∈ range (b - 1), (1 / 2 : ℚ)^(j+2)) < 1 / 2 := by
    have h_split : (∑ j ∈ range (b - 1), (1 / 2 : ℚ)^(j+2)) = 1 / 2 * (∑ j ∈ range (b - 1), (1 / 2 : ℚ)^(j+1)) := by
      rw [← mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    rw [h_split]
    have h_lt := geom_sum_half_lt_one (b - 1)
    nlinarith
  linarith"""

if old_ref in content:
    content = content.replace(old_ref, new_ref)
    print("Inserted sum_two_pow_lt_eleven_six!")
else:
    print("Could not find sum_two_pow_lt_two!")

with open(path, 'w') as f:
    f.write(content)
