import Submission.GreedyBatchProfileFits

/-! Load and exponential-growth estimates for the continuation reward.
The leading load coefficient is retained to within O(m^-2). -/
namespace Erdos773.GreedyBatchRateGeometry
open GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchProfileConditions
open GreedyBatchReward
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def growth (m : ℕ) (t : ℝ) : ℝ := a m*GreedyBatchProfileLower.delta t (step m t)

lemma precise_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    load (caps m d t C P) (probability m d t)≤
      A m*step m t*t^2+B m*t*(step m t)^2+(step m t)^3+
      probability m d t+(probability m d t)^2+(probability m d t)^3 := by
  have hp := (probability_pos m d t C P h).le
  obtain ⟨hf2,hf3,hf4,hfB⟩ := profile_positive m d t C P h
  have h2 := mul_le_mul_of_nonneg_right (ceil_bounds (f2 m d t) hf2.le).2 hp
  have h3 := mul_le_mul_of_nonneg_right (ceil_bounds (f3 m d t) hf3.le).2 (sq_nonneg (probability m d t))
  have h4 := mul_le_mul_of_nonneg_right (ceil_bounds (f4 d) hf4.le).2 (pow_nonneg hp 3)
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have he2 : f2 m d t*probability m d t=A m*step m t*t^2 := by
    calc
      _ = A m*(probability m d t*d)*t^2 := by unfold f2; ring
      _ = _ := by rw [hpd]
  have he3 : f3 m d t*(probability m d t)^2=B m*t*(step m t)^2 := by
    calc
      _ = B m*t*(probability m d t*d)^2 := by unfold f3; ring
      _ = _ := by rw [hpd]
  have he4 : f4 d*(probability m d t)^3=(step m t)^3 := by
    calc
      _ = (probability m d t*d)^3 := by unfold f4; ring
      _ = _ := by rw [hpd]
  dsimp [load,caps]
  nlinarith only [h2,h3,h4,he2,he3,he4]

lemma coarse_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    load (caps m d t C P) (probability m d t)≤10*step m t*t^2 ∧
    probability m d t+load (caps m d t C P) (probability m d t)≤20*step m t*t^2 ∧
    load (caps m d t C P) (probability m d t)≤10/(m:ℝ)^2 ∧
    probability m d t+load (caps m d t C P) (probability m d t)≤1 := by
  have hm := h.m_pos
  have ht : 0≤t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hh := step_le_time m t (by have := h.large; omega) h.t_one
  have hw := weighted_bounds m d t C P h
  have h21 := mul_le_mul_of_nonneg_left hh (show 0≤step m t*t by positivity)
  have h31 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hh 2) hs
  have hw2 := hw.graph
  have hw3 := hw.three_two
  have hw4 := hw.four_three
  have hz : load (caps m d t C P) (probability m d t)≤10*step m t*t^2 := by
    dsimp [load]
    nlinarith only [hw2,hw3,hw4,h21,h31]
  have hx0 : 0≤step m t*t^2 := by positivity
  have hpt := probability_le_step m d t C P h
  have htx := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h.t_one) hs
  have hx : probability m d t+load (caps m d t C P) (probability m d t)≤20*step m t*t^2 := by
    nlinarith only [hz,hpt,htx,hx0]
  have hsx := (step_weighted m t (by have := h.large; omega) h.t_one).1
  have hz' : load (caps m d t C P) (probability m d t)≤10/(m:ℝ)^2 := by
    ring_nf at hz hsx ⊢
    linarith only [hz,hsx]
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have h20 : (20:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by nlinarith only [hmR])
  refine ⟨hz,hx,hz',?_⟩
  ring_nf at hx hsx h20 ⊢
  linarith only [hx,hsx,h20]

lemma growth_bounds (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    0≤growth m t ∧ 3*a m*step m t*t^2≤growth m t ∧ growth m t≤7*step m t*t^2 := by
  have ht0 : 0≤t := by linarith only [ht]
  have hs := (step_pos m t (by omega)).le
  have hst := step_le_time m t (by omega) ht
  obtain ⟨hB,hBA,hA4,ha,ha1,hgap⟩ := coefficients m hm
  have hD0 := GreedyBatchProfileLower.delta_nonneg t (step m t) ht0 hs
  have hDlo : 3*t^2*step m t≤GreedyBatchProfileLower.delta t (step m t) := by
    have h1 := mul_nonneg ht0 (sq_nonneg (step m t))
    have h2 := pow_nonneg hs 3
    dsimp [GreedyBatchProfileLower.delta]
    nlinarith only [h1,h2]
  have hDup := (GreedyBatchProfileLower.delta_error t (step m t) ((step m t)^2*t) ht0 hs hst le_rfl).1
  have ht2 := mul_le_mul_of_nonneg_left hst (show 0≤step m t*t by positivity)
  have h1 := mul_le_mul_of_nonneg_left hDlo ha
  have h2 := mul_le_mul_of_nonneg_right ha1 hD0
  dsimp [growth]
  exact ⟨mul_nonneg ha hD0,by nlinarith only [h1],by nlinarith only [h2,hDup,ht2]⟩

lemma growth_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    growth m t*(probability m d t+load (caps m d t C P) (probability m d t))≤
      140*step m t*t^2/(m:ℝ)^2 := by
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have hz0 : 0≤load (caps m d t C P) (probability m d t) := by unfold load; positivity
  have hu := (growth_bounds m t h.large h.t_one).2.2
  have hz := (coarse_load m d t C P h).2.1
  have hh := mul_le_mul hu hz (add_nonneg hp hz0) (show 0≤7*step m t*t^2 by positivity)
  have hsx := (step_weighted m t (by have := h.large; omega) h.t_one).1
  have hx := mul_le_mul_of_nonneg_right hsx (show 0≤step m t*t^2 by positivity)
  ring_nf at hh hx ⊢
  nlinarith only [hh,hx]

lemma small_terms (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    B m*t*(step m t)^2≤4*step m t*t^2/(m:ℝ)^2 ∧
    (step m t)^3≤step m t*t^2/(m:ℝ)^2 ∧
    probability m d t≤step m t*t^2/(m:ℝ)^2 := by
  have hm := h.m_pos
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have ht : 0≤t := by have := h.t_one; linarith
  have ht2 := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h.t_one) hs
  have hratio := div_le_div_of_nonneg_right ht2 (sq_nonneg (m:ℝ))
  have hst := (step_weighted m t (by have := h.large; omega) h.t_one).2.1
  have hst' := mul_le_mul_of_nonneg_left hst hs
  have hcoef := (coefficients m h.large).2.1.trans (coefficients m h.large).2.2.1
  have hB := mul_le_mul_of_nonneg_right hcoef (show 0≤t*(step m t)^2 by positivity)
  have hs1 := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs2 : (step m t)^2≤step m t := by nlinarith only [hs,hs1]
  have hss := mul_le_mul_of_nonneg_left (hs2.trans (step_bound m t (by have := h.large; omega))) hs
  have hd2 := h.power_le_d 2 (by decide)
  have hpd := probability_mul m d t (ne_of_gt h.d_pos)
  have hdp := mul_le_mul_of_nonneg_left hd2 hp
  have hpstep : probability m d t≤step m t/(m:ℝ)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [hpd] at hdp
    exact hdp
  ring_nf at hratio hst' hB hss hpstep ⊢
  exact ⟨by nlinarith only [hratio,hst',hB],by nlinarith only [hss,hratio],by linarith only [hpstep,hratio]⟩

/-- The continuation multiplier differs from the inverse degree scale by
at most 10000*h*t^2/m^2 in a single batch. -/
theorem bracket_lower (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    -10000*step m t*t^2/(m:ℝ)^2≤growth m t-
      (probability m d t+load (caps m d t C P) (probability m d t))*(1+growth m t) := by
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hp := (probability_pos m d t C P h).le
  have hp1 := probability_le_one m d t C P h
  have hp2 : (probability m d t)^2≤probability m d t := by nlinarith only [hp,hp1]
  have hp3 : (probability m d t)^3≤probability m d t := by
    have hh := mul_le_mul_of_nonneg_right hp2 hp
    nlinarith only [hh,hp2]
  have hz := precise_load m d t C P h
  have hu := (growth_bounds m t h.large h.t_one).2.1
  have hprod := growth_load m d t C P h
  obtain ⟨hB,hcube,hround⟩ := small_terms m d t C P h
  have hgap : (A m-3*a m)*(step m t*t^2)=9000*step m t*t^2/(m:ℝ)^2 := by
    unfold A a
    ring
  have hnonneg : 0≤step m t*t^2/(m:ℝ)^2 := by positivity
  ring_nf at hz hu hprod hB hcube hround hgap hnonneg ⊢
  nlinarith only [hz,hu,hprod,hB,hcube,hround,hgap,hp2,hp3,hnonneg]

#print axioms precise_load
#print axioms coarse_load
#print axioms growth_bounds
#print axioms growth_load
#print axioms small_terms
#print axioms bracket_lower
end
end Erdos773.GreedyBatchRateGeometry
