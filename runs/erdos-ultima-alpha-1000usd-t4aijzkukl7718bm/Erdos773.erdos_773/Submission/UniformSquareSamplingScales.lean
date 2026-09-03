import FormalConjecturesUtil

/-! Elementary scale bounds for uniform square-root sampling. -/
namespace Erdos773.UniformSquareSamplingScales
set_option maxHeartbeats 2000000
noncomputable section

def momentOrder (X : ℝ) : ℕ := ⌈X^(1/100:ℝ)⌉₊

lemma momentOrder_bounds {X : ℝ} (hX : 1 ≤ X) :
    X^(1/100:ℝ) ≤ (momentOrder X:ℝ) ∧ (momentOrder X:ℝ) ≤ 2*X^(1/100:ℝ) := by
  have hR : 1 ≤ X^(1/100:ℝ) := Real.one_le_rpow hX (by norm_num)
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (by positivity : 0 ≤ X^(1/100:ℝ))).le.trans (by linarith)⟩

lemma overlap_budget {X L : ℝ} (hX : 1 ≤ X) (hL : 0 ≤ L)
    (hsmall : 16000*L ≤ X^(1/100:ℝ)) :
    3*(momentOrder X:ℝ)^2*L^2 ≤ X/12000 := by
  have hR : 0 ≤ X^(1/100:ℝ) := Real.rpow_nonneg (by linarith) _
  have hq := (momentOrder_bounds hX).2
  have hs := mul_le_mul hq hsmall (by positivity : 0 ≤ 16000*L) (by positivity : 0 ≤ 2*X^(1/100:ℝ))
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ (momentOrder X:ℝ)*(16000*L)) hs 2
  have hfour : (X^(1/100:ℝ))^4 ≤ X := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ X)]
    exact (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ)*4 ≤ 1)).trans_eq (Real.rpow_one X)
  nlinarith only [hs2,hfour]

lemma tail_decay {X : ℝ} {q : ℕ} (hX : 0<X) (hq : 16000*Real.log X ≤ (q:ℝ)) :
    (3999/4000:ℝ)^q ≤ 1/X^4 := by
  have hb : (3999/4000:ℝ) ≤ Real.exp (-(1/4000:ℝ)) := by
    have hh := Real.add_one_le_exp (-(1/4000:ℝ))
    linarith only [hh]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3999/4000) hb q
  rw [← Real.exp_nat_mul] at hp
  have hexp : (q:ℝ)*(-(1/4000:ℝ)) ≤ -(4*Real.log X) := by linarith only [hq]
  have he : Real.exp (-(4*Real.log X)) = 1/X^4 := by
    rw [Real.exp_neg]
    have hh : Real.exp (4*Real.log X)=X^4 := by
      simpa only [Real.exp_log hX] using Real.exp_nat_mul (Real.log X) 4
    rw [hh,one_div]
  exact (hp.trans (Real.exp_le_exp.mpr hexp)).trans_eq he

lemma moment_ratio {X L : ℝ} (hX : 1 ≤ X) (hL : 0<L)
    (hsmall : 16000*L ≤ X^(1/100:ℝ)) :
    (((1/L)^3*((333/1000:ℝ)*X*L)+(3*momentOrder X:ℕ)*momentOrder X)/
      ((1999/6000:ℝ)*X/L^2)) ≤ 3999/4000 := by
  have hb := overlap_budget hX hL.le hsmall
  have hX0 : 0<X := by linarith
  apply (div_le_iff₀ (by positivity : 0<(1999/6000:ℝ)*X/L^2)).mpr
  have he : ((1/L)^3*((333/1000:ℝ)*X*L)+(3*momentOrder X:ℕ)*momentOrder X)*L^2 =
      (333/1000:ℝ)*X+3*(momentOrder X:ℝ)^2*L^2 := by
    push_cast
    field_simp
  have ht : ((3999/4000:ℝ)*((1999/6000:ℝ)*X/L^2))*L^2 =
      (3999/4000:ℝ)*(1999/6000:ℝ)*X := by field_simp
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL)).mp
  rw [he,ht]
  nlinarith only [hb,hX0]

/-- The total high-moment penalty is O(X^-2), smaller than the progression
    deletion cost. -/
lemma sampling_loss {X : ℝ} (hX : 1 ≤ X) (hL : 0<Real.log X)
    (hsmall : 16000*Real.log X ≤ X^(1/100:ℝ)) :
    (1/Real.log X)^3*(24*X*Real.log X)+X^2*
      ((((1/Real.log X)^3*((333/1000:ℝ)*X*Real.log X)+
        (3*momentOrder X:ℕ)*momentOrder X)/((1999/6000:ℝ)*X/(Real.log X)^2))^momentOrder X) ≤
      25*X/(Real.log X)^2 := by
  have hX0 : 0<X := by linarith
  have hratio := moment_ratio hX hL hsmall
  have hnon : 0 ≤ ((1/Real.log X)^3*((333/1000:ℝ)*X*Real.log X)+
      (3*momentOrder X:ℕ)*momentOrder X)/((1999/6000:ℝ)*X/(Real.log X)^2) := by positivity
  have hp := (pow_le_pow_left₀ hnon hratio (momentOrder X)).trans
    (tail_decay hX0 (hsmall.trans (momentOrder_bounds hX).1))
  have htail := mul_le_mul_of_nonneg_left hp (sq_nonneg X)
  have he : X^2*(1/X^4)=1/X^2 := by field_simp
  rw [he] at htail
  have hlog := Real.log_le_sub_one_of_pos hX0
  have hlogX : Real.log X ≤ X := by linarith only [hlog]
  have hs := pow_le_pow_left₀ hL.le hlogX 2
  have hX3 : X^2 ≤ X^3 := by nlinarith only [hX,mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hX)]
  have hlast : 1/X^2 ≤ X/(Real.log X)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hX0) (sq_pos_of_pos hL)).mpr
    nlinarith only [hs,hX3]
  have hap : (1/Real.log X)^3*(24*X*Real.log X)=24*X/(Real.log X)^2 := by field_simp
  rw [hap]
  have he25 : 25*X/(Real.log X)^2=24*X/(Real.log X)^2+X/(Real.log X)^2 := by ring
  rw [he25]
  exact add_le_add le_rfl (htail.trans hlast)

#print axioms momentOrder_bounds
#print axioms overlap_budget
#print axioms tail_decay
#print axioms moment_ratio
#print axioms sampling_loss
end
end Erdos773.UniformSquareSamplingScales
