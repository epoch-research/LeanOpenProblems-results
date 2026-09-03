import Submission.GreedyBatchProfileLower

/-! Coarse deterministic rounding estimates for one mixed-rank batch. -/
namespace Erdos773.GreedyBatchCeilingErrors
set_option maxHeartbeats 2500000
noncomputable section

/-- Old survival plus the 100n*kappa margin costs at most 202F*kappa
beyond the ideal loss. The deficit retains its sign and its p factor. -/
theorem old_upper (n F D F2 k e p η κ : ℝ)
    (hn0 : 0≤n) (hF : 0≤F) (hD : 0≤D) (hk : 0≤k) (he : 0≤e) (hp : 0≤p)
    (hη : 0≤η) (hη1 : η≤1) (hκ : 0≤κ)
    (hn : n≤F+1) (hn2 : n≤2*F) (hround : 1≤F*κ) (hF2 : F2≤D)
    (hload : k*D*p≤1) (hdef : p*e≤κ/2) :
    n*(1-(1-η)*p*(k*D-e))+100*n*κ≤F*(1-(1-η)*p*k*F2)+202*F*κ := by
  have heta0 : 0≤1-η := sub_nonneg.mpr hη1
  have hc0 : 0≤(1-η)*p*k*D := by positivity
  have hc1 : (1-η)*p*k*D≤1 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-η≤1 by linarith only [hη])
      (show 0≤k*D*p by positivity)
    nlinarith only [hh,hload]
  have hr0 : 0≤1-(1-η)*p*k*D := by linarith only [hc1]
  have hnr := mul_le_mul_of_nonneg_right hn hr0
  have hc := mul_le_mul_of_nonneg_left hF2 (show 0≤F*((1-η)*p*k) by positivity)
  have he0 : 0≤p*e := mul_nonneg hp he
  have he1 : (1-η)*(p*e)≤κ/2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-η≤1 by linarith only [hη]) he0
    linarith only [hh,hdef]
  have hne := mul_le_mul_of_nonneg_left he1 hn0
  have hnκ := mul_le_mul_of_nonneg_right hn2 hκ
  nlinarith only [hnr,hc0,hc,hne,hnκ,hround]

/-- A ceiling in the source degree and a residual margin cost at most
three target-profile margins when the scalar witness weight is tiny. -/
lemma promotion_upper (D F E S w κ : ℝ) (hw : 0≤w) (hκ : 0≤κ)
    (hD : D≤F+1) (hE : E≤2*S) (hsmall : w≤S*κ) :
    w*D+E*κ≤w*F+3*S*κ := by
  have h1 := mul_le_mul_of_nonneg_left hD hw
  have h2 := mul_le_mul_of_nonneg_right hE hκ
  nlinarith only [h1,h2,hsmall]

#print axioms old_upper
#print axioms promotion_upper
end
end Erdos773.GreedyBatchCeilingErrors
