import Submission.GreedyBatchScaledStep

/-! Elementary lower bounds for the proposed exponential mixed-degree
profiles. Only exp(x)>=1+x and polynomial estimates are used. -/
namespace Erdos773.GreedyBatchProfileLower
set_option maxHeartbeats 2500000
noncomputable section

def delta (t h : ℝ) : ℝ := (t+h)^3-t^3

lemma delta_nonneg (t h : ℝ) (ht : 0≤t) (hh : 0≤h) : 0≤delta t h := by
  dsimp [delta]
  exact sub_nonneg.mpr (pow_le_pow_left₀ ht (by linarith only [hh]) 3)

lemma delta_error (t h κ : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ) :
    delta t h≤3*t^2*h+4*κ ∧
    delta t h*(t+h)≤3*t^3*h+11*t*κ ∧
    delta t h*(t+h)^2≤3*t^4*h+25*t^2*κ := by
  have h2 := mul_le_mul_of_nonneg_right hht hh
  have h3 := mul_le_mul_of_nonneg_right hht (sq_nonneg h)
  have hd : delta t h≤3*t^2*h+4*t*h^2 := by dsimp [delta]; nlinarith only [h3]
  have hs : (t+h)^2≤t^2+3*t*h := by nlinarith only [h2]
  refine ⟨by nlinarith only [hd,hκ],?_,?_⟩
  · have he := mul_le_mul_of_nonneg_right hd (add_nonneg ht hh)
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0:ℝ)≤4*t by positivity)
    have hκ' := mul_le_mul_of_nonneg_left hκ (show (0:ℝ)≤11*t by positivity)
    nlinarith only [he,h3',hκ']
  · have he := mul_le_mul hd hs (sq_nonneg (t+h)) (by positivity)
    have h3' := mul_le_mul_of_nonneg_left h3 (show (0:ℝ)≤12*t^2 by positivity)
    have hκ' := mul_le_mul_of_nonneg_left hκ (show (0:ℝ)≤25*t^2 by positivity)
    nlinarith only [he,h3',hκ']

lemma rank_two (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    t^2+2*t*h-3*a*t^4*h-25*t^2*κ≤Real.exp (-a*delta t h)*(t+h)^2 := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-a*delta t h)) (sq_nonneg (t+h))
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).2.2 ha
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤25*t^2*κ by positivity)
  nlinarith only [he,hd,hc,sq_nonneg h]

lemma rank_three (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    t+h-6*a*t^3*h-22*t*κ≤Real.exp (-2*a*delta t h)*(t+h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2*a*delta t h)) (add_nonneg ht hh)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).2.1 (show (0:ℝ)≤2*a by positivity)
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤22*t*κ by positivity)
  nlinarith only [he,hd,hc]

lemma rank_four (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    1-9*a*t^2*h-12*κ≤Real.exp (-3*a*delta t h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := Real.add_one_le_exp (-3*a*delta t h)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).1 (show (0:ℝ)≤3*a by positivity)
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤12*κ by positivity)
  nlinarith only [he,hd,hc]

lemma shared (t h κ a : ℝ) (ht : 0≤t) (hh : 0≤h) (hht : h≤t) (hκ : h^2*t≤κ)
    (ha : 0≤a) (ha1 : a≤1) :
    1-3*a*t^2*h-4*κ≤Real.exp (-a*delta t h) := by
  have hκ0 := (mul_nonneg (sq_nonneg h) ht).trans hκ
  have he := Real.add_one_le_exp (-a*delta t h)
  have hd := mul_le_mul_of_nonneg_left (delta_error t h κ ht hh hht hκ).1 ha
  have hc := mul_le_mul_of_nonneg_right ha1 (show (0:ℝ)≤4*κ by positivity)
  nlinarith only [he,hd,hc]

/-- Normalized ideal updates are absorbed with considerable coefficient slack.
The three-mark and shared profiles retain every positive creation term. -/
lemma ideal_two (A B a η x y z κ : ℝ) (hA : 3≤A) (hBA : B≤A) (hy : 0≤y) (hκ : 0≤κ)
    (hz : z≤κ) (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    A*(1-(1-η)*A*x)+2*B*y+3*z+250*A*κ≤A*(1+2*y-3*a*x-25*κ) := by
  have hA0 : 0≤A := by linarith only [hA]
  have hh := mul_le_mul_of_nonneg_left hgap hA0
  have hab := mul_le_mul_of_nonneg_right hBA hy
  have hk := mul_le_mul_of_nonneg_right hA hκ
  have hAk := mul_nonneg hA0 hκ
  nlinarith only [hh,hab,hk,hz,hAk]

lemma ideal_three (A B a η x y κ : ℝ) (hB : 3≤B) (hy : 0≤y) (hκ : 0≤κ)
    (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    B*(1-2*(1-η)*A*x)+3*y+250*B*κ≤B*(1+y-6*a*x-22*κ) := by
  have hB0 : 0≤B := by linarith only [hB]
  have hh := mul_le_mul_of_nonneg_left hgap hB0
  have hby := mul_le_mul_of_nonneg_right hB hy
  have hBk := mul_nonneg hB0 hκ
  nlinarith only [hh,hby,hBk]

lemma ideal_four (A a η x κ : ℝ) (hκ : 0≤κ) (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    1-3*(1-η)*A*x+250*κ≤1-9*a*x-12*κ := by
  nlinarith only [hκ,hgap]

lemma ideal_shared (A a η x κ : ℝ) (ha : 0≤a) (hx : 0≤x) (hκ : 0≤κ)
    (hgap : 500*κ≤((1-η)*A-3*a)*x) :
    1-2*(1-η)*A*x+250*κ≤1-3*a*x-4*κ := by
  have hh := mul_nonneg ha hx
  nlinarith only [hh,hκ,hgap]

#print axioms delta_error
#print axioms rank_two
#print axioms rank_three
#print axioms rank_four
#print axioms shared
#print axioms ideal_two
#print axioms ideal_three
#print axioms ideal_four
#print axioms ideal_shared
end
end Erdos773.GreedyBatchProfileLower
