import Submission.Development

/-!
A finite denominator exclusion for Erdős 68. This does not prove irrationality.
The endpoints are adjacent fractions; the proof uses their determinant, not
any unverified continued-fraction computation.
-/

namespace Erdos68Development

lemma sum_farey_bounds :
    (3872110933106098 / 3089042502434645 : ℝ) < (∑' k : ℕ, term k) ∧
      (∑' k : ℕ, term k) < 49679453951081027 / 39632631245285943 := by
  have h := partial_sum_error 29
  have hlo : (3872110933106098 / 3089042502434645 : ℝ) <
      ∑ k ∈ Finset.range 29, term k := by
    norm_num [Finset.sum_range_succ, term, Nat.factorial]
  have hhi : (∑ k ∈ Finset.range 29, term k) + (3 / 2 : ℝ) * term 29 <
      49679453951081027 / 39632631245285943 := by
    norm_num [Finset.sum_range_succ, term, Nat.factorial]
  constructor <;> linarith [h.1, h.2]

/-- A rational strictly between two determinant-one fractions has denominator
at least the sum of the endpoint denominators. -/
lemma denominator_ge_of_farey_bounds (q : ℚ) (a b c d : ℤ)
    (hb : 0 < b) (hd : 0 < d) (hdet : b * c - a * d = 1)
    (hlo : (a : ℝ) / b < (q : ℝ))
    (hhi : (q : ℝ) < (c : ℝ) / d) : b + d ≤ (q.den : ℤ) := by
  have hqden : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Rat.cast_def] at hlo hhi
  have hloR := (div_lt_div_iff₀ hbR hqden).mp hlo
  have hhiR := (div_lt_div_iff₀ hqden hdR).mp hhi
  have hloZ : a * (q.den : ℤ) < q.num * b := by exact_mod_cast hloR
  have hhiZ : q.num * d < c * (q.den : ℤ) := by exact_mod_cast hhiR
  have hleft : 1 ≤ b * q.num - a * (q.den : ℤ) := by nlinarith
  have hright : 1 ≤ c * (q.den : ℤ) - d * q.num := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hleft hd.le
  have h2 := mul_le_mul_of_nonneg_left hright hb.le
  have hid : d * (b * q.num - a * (q.den : ℤ)) +
      b * (c * (q.den : ℤ) - d * q.num) = q.den := by
    calc
      _ = (b * c - a * d) * (q.den : ℤ) := by ring
      _ = q.den := by rw [hdet, one_mul]
  nlinarith

/-- A finite necessary condition for rationality, not a proof of irrationality. -/
theorem rational_denominator_large (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    42721673747720588 ≤ q.den := by
  obtain ⟨hlo, hhi⟩ := sum_farey_bounds
  rw [hq] at hlo hhi
  have h := denominator_ge_of_farey_bounds q
    3872110933106098 3089042502434645
    49679453951081027 39632631245285943
    (by norm_num) (by norm_num) (by norm_num) hlo hhi
  norm_num at h
  exact_mod_cast h

end Erdos68Development

#print axioms Erdos68Development.sum_farey_bounds
#print axioms Erdos68Development.rational_denominator_large
