import Submission.GreedyBatchProfileConditions

/-! The real future profiles dominate all ideal mixed-rank updates with
250 relative rounding/error margins. -/
namespace Erdos773.GreedyBatchFutureProfiles
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileLower
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma normalized_gap (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    500*(1/(m:ℝ)^4)≤((1-1/(m:ℝ)^2)*A m-3*a m)*(step m t*t^2) := by
  convert step_gap m t hm ht using 1 <;> ring

lemma normalized_square (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    (step m t/t)^2≤1/(m:ℝ)^4 := by
  have hs := (step_pos m t (by omega)).le
  have ht0 : 0≤t := by linarith only [ht]
  have hh := div_le_self hs ht
  exact (pow_le_pow_left₀ (div_nonneg hs ht0) hh 2).trans (step_squared m t hm)

/-- The direct rank-four-to-two promotion is retained. -/
theorem two (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f2 m d t*(1-(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+
      2*probability m d t*f3 m d t+3*(probability m d t)^2*f4 d+
      250*f2 m d t/(m:ℝ)^4≤f2 m (nextD m d t) (t+step m t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hA : 3≤A m := hB.trans hBA
  have hA0 : 0≤A m := by linarith only [hA]
  have hi := ideal_two (A m) (B m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (step m t/t)
    ((step m t/t)^2) (1/(m:ℝ)^4) hA hBA (div_nonneg hs ht.le) (by positivity)
    (normalized_square m t (by have := h.large; omega) h.t_one) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d*t^2 by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_two t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤A m*d by positivity)
  calc
    _ ≤ A m*d*(t^2+2*t*step m t-3*a m*t^4*step m t-25*t^2*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f3,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      convert hl using 1 <;> dsimp [f2,nextD] <;> ring

/-- The leading rank-four-to-three promotion is retained. -/
theorem three (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f3 m d t*(1-2*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+
      3*probability m d t*f4 d+250*f3 m d t/(m:ℝ)^4≤f3 m (nextD m d t) (t+step m t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hB0 : 0≤B m := by linarith only [hB]
  have hi := ideal_three (A m) (B m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (step m t/t)
    (1/(m:ℝ)^4) hB (div_nonneg hs ht.le) (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d^2*t by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_three t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤B m*d^2 by positivity)
  have he : (Real.exp (-a m*delta t (step m t)))^2=Real.exp (-2*a m*delta t (step m t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ B m*d^2*(t+step m t-6*a m*t^3*step m t-22*t*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f3,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      dsimp [f3,nextD]
      rw [mul_pow,he]
      convert hl using 1 <;> ring

theorem four (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    f4 d*(1-3*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+250*f4 d/(m:ℝ)^4≤f4 (nextD m d t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hi := ideal_four (A m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (1/(m:ℝ)^4)
    (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤d^3 by positivity)
  have hl := mul_le_mul_of_nonneg_left
    (rank_four t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤d^3 by positivity)
  have he : (Real.exp (-a m*delta t (step m t)))^3=Real.exp (-3*a m*delta t (step m t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ d^3*(1-9*a m*t^2*step m t-12*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,f4,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      dsimp [f4,nextD]
      rw [mul_pow,he]
      convert hl using 1 <;> ring

theorem shared (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    fb m d*(1-2*(1-1/(m:ℝ)^2)*probability m d t*f2 m d t)+250*fb m d/(m:ℝ)^4≤fb m (nextD m d t) := by
  have hm := h.m_pos
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  obtain ⟨hB,hBA,hA4,ha,ha1,hg⟩ := coefficients m h.large
  have hi := ideal_shared (A m) (a m) (1/(m:ℝ)^2) (step m t*t^2) (1/(m:ℝ)^4)
    ha (by positivity) (by positivity) (normalized_gap m t h.large h.t_one)
  have hi' := mul_le_mul_of_nonneg_left hi (show 0≤fb m d by dsimp [fb]; positivity)
  have hl := mul_le_mul_of_nonneg_left
    (GreedyBatchProfileLower.shared t (step m t) (1/(m:ℝ)^4) (a m) ht.le hs
      (step_le_time m t (by have := h.large; omega) h.t_one)
      (step_squared_time m t (by have := h.large; omega) h.t_one) ha ha1)
    (show 0≤fb m d by dsimp [fb]; positivity)
  calc
    _ ≤ fb m d*(1-3*a m*t^2*step m t-4*(1/(m:ℝ)^4)) := by
      convert hi' using 1 <;> dsimp [f2,fb,probability] <;> field_simp <;> ring
    _ ≤ _ := by
      convert hl using 1 <;> dsimp [fb,nextD] <;> ring

#print axioms two
#print axioms three
#print axioms four
#print axioms shared
end
end Erdos773.GreedyBatchFutureProfiles
