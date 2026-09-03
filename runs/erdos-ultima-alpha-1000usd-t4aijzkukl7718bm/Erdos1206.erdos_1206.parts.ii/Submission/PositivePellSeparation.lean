import FormalConjecturesUtil

/-! A modular doubling principle for positive-norm Pell equations. -/
namespace Erdos1206.PositivePellSeparation

theorem pell_residue_doubling {D m x y x' y' r : ℤ}
    (hD : 0 < D) (hm : 0 < m)
    (hx : 0 < x) (hx' : 0 < x') (hy : 0 < y) (hyy' : y < y')
    (he : x^2-D*y^2 = m) (he' : x'^2-D*y'^2 = m)
    (hr : m ∣ x-r*y) (hr' : m ∣ x'-r*y')
    (hrD : m ∣ r^2-D) : 2*y ≤ y' := by
  let v := x*y'-x'*y
  let u := x*x'-D*y*y'
  have hy' : 0 < y' := lt_trans hy hyy'
  have hv : 0 < v := by
    have hid : (x*y')^2-(x'*y)^2 = m*(y'^2-y^2) := by
      linear_combination y'^2*he-y^2*he'
    have hys : y^2 < y'^2 := (sq_lt_sq₀ hy.le hy'.le).mpr hyy'
    have hmul : 0 < m*(y'^2-y^2) := mul_pos hm (sub_pos.mpr hys)
    have hxp : 0 ≤ x*y' := mul_nonneg hx.le hy'.le
    have hxp' : 0 ≤ x'*y := mul_nonneg hx'.le hy.le
    have hlt : (x'*y)^2 < (x*y')^2 := by linarith
    exact sub_pos.mpr ((sq_lt_sq₀ hxp' hxp).mp hlt)
  have hud : m ∣ u := by
    obtain ⟨s,hs⟩ := hr
    obtain ⟨t,ht⟩ := hr'
    obtain ⟨q,hq⟩ := hrD
    refine ⟨q*y*y'+r*y*t+r*y'*s+m*s*t, ?_⟩
    dsimp [u]
    have hxid : x=r*y+m*s := by linarith
    have hxid' : x'=r*y'+m*t := by linarith
    have hDid : D=r^2-m*q := by linarith
    rw [hxid,hxid',hDid]
    ring
  have hu : 0 < u := by
    have hbound : D*y^2 < x^2 := by linarith
    have hbound' : D*y'^2 < x'^2 := by linarith
    have hprod : (D*y*y')^2 < (x*x')^2 := by
      have h1 := mul_lt_mul_of_pos_right hbound (show 0 < x'^2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hbound'.le (show 0 ≤ D*y^2 by positivity)
      nlinarith only [h1,h2]
    have hnonneg : 0 ≤ D*y*y' := by positivity
    have hnonneg' : 0 ≤ x*x' := by positivity
    exact sub_pos.mpr ((sq_lt_sq₀ hnonneg hnonneg').mp hprod)
  have hid : u^2-D*v^2=m^2 := by
    dsimp [u,v]
    linear_combination (x'^2-D*y'^2)*he+m*he'
  have hmu : m < u := by
    have hpos : 0 < D*v^2 := by positivity
    have hs : m^2 < u^2 := by linarith
    exact (sq_lt_sq₀ hm.le hu.le).mp hs
  have hu2 : 2*m ≤ u := by
    obtain ⟨q,hq⟩ := hud
    have hq2 : 2 ≤ q := by
      by_contra hh
      have hle : m*q ≤ m := by nlinarith
      omega
    nlinarith
  have hlin : m*y'=u*y+v*x := by
    dsimp [u,v]
    linear_combination -y'*he
  have hmul : m*(2*y) ≤ m*y' := by
    have h1 := mul_le_mul_of_nonneg_right hu2 hy.le
    have h2 : 0 ≤ v*x := mul_nonneg hv.le hx.le
    nlinarith only [hlin,h1,h2]
  exact (mul_le_mul_iff_right₀ hm).mp hmul

#print axioms pell_residue_doubling
end Erdos1206.PositivePellSeparation
