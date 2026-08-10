import os

path = "/workspace/leanproject/Submission/Spec.lean"
with open(path, 'r') as f:
    content = f.read()

# Let's clean up any previous sum_two_pow_lt_eleven_six definition first
import re
content = re.sub(r"lemma sum_two_pow_lt_eleven_six.*?\n\s*linarith\b", "", content, flags=re.DOTALL)

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
  have h_b_eq : b = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
  rw [h_b_eq]
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
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have h_eq : (1 / 2 : ℚ)^(j+2) = 1 / 2 * (1 / 2 : ℚ)^(j+1) := by ring
      exact h_eq
    rw [h_split]
    have h_lt := geom_sum_half_lt_one (b - 1)
    nlinarith
  linarith"""

# Replace in content
if old_ref in content:
    content = content.replace(old_ref, new_ref)
    print("Replaced with correct sum_two_pow_lt_eleven_six!")
else:
    # If the lemma is already there but needs updating, we can just replace the whole file part.
    # Let's search for old sum_two_pow_lt_eleven_six and replace.
    print("sum_two_pow_lt_two already modified? Let's check.")

with open(path, 'w') as f:
    f.write(content)
