import Submission.LocalCubeDifferences

/-! Local rational points for either sign of the initial coordinates. These
auxiliary results do not settle the positive-density Sidon conjecture. -/

namespace Erdos1206.RationalCurveLocal
open Erdos1206.LocalCubeDifferences Filter
open scoped Topology Classical
set_option maxHeartbeats 1000000

def scaledUpper (D a b h v : ℚ) : ℚ :=
  a*(a-b)+(a*(a-2*b)*h-D)*v+(D*b-a*b*h^2)*v^2

lemma scaled_upper_eq {D a b c d : ℚ} (hd : d≠0) :
    d^2*scaledUpper D a b (c-d) d⁻¹=sumUpperNum D a b c d := by
  simp only [scaledUpper,sumUpperNum]
  field_simp
  ring

/-- A local result allowing negative initial coordinates, provided the curve
also has an unbounded set of positive rational points. -/
theorem near_below_of_unbounded {D a b ε : ℚ} (hD : 0<D) (ha : a≠0)
    (hbase : a^3-b^3=D) (hε : 0<ε)
    (hunbounded : ∀ M : ℚ, ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=D) :
    ∃ x y : ℚ, b-ε<y ∧ y<b ∧ a-ε<x ∧ x<a ∧ x^3-y^3=D := by
  have hab : b<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith)
  choose c d hnd hd hc he using (fun n : ℕ => hunbounded n)
  have hdlim : Tendsto d atTop atTop := tendsto_atTop_mono
    (fun n => (hnd n).le) tendsto_natCast_atTop_atTop
  have hvlim : Tendsto (fun n => (d n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hdlim
  have hhlim := gap_tendsto_zero hD hd he hdlim
  have hpairlim := hhlim.prodMk_nhds hvlim
  have hScont : Continuous (fun p : ℚ×ℚ => scaledDen a b p.1 p.2) := by
    unfold scaledDen
    fun_prop
  have hPcont : Continuous (fun p : ℚ×ℚ => scaledLower D a b p.1 p.2) := by
    unfold scaledLower
    fun_prop
  have hQcont : Continuous (fun p : ℚ×ℚ => scaledUpper D a b p.1 p.2) := by
    unfold scaledUpper
    fun_prop
  have hGcont : Continuous (fun p : ℚ×ℚ => scaledGap a b p.1 p.2) := by
    unfold scaledGap
    fun_prop
  let S : ℕ → ℚ := fun n => scaledDen a b (c n-d n) (d n)⁻¹
  let P : ℕ → ℚ := fun n => scaledLower D a b (c n-d n) (d n)⁻¹
  let Q : ℕ → ℚ := fun n => scaledUpper D a b (c n-d n) (d n)⁻¹
  let G : ℕ → ℚ := fun n => scaledGap a b (c n-d n) (d n)⁻¹
  have hS : Tendsto S atTop (𝓝 (a-b)) := by
    simpa only [S,scaledDen,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hScont.continuousAt.tendsto.comp hpairlim
  have hP : Tendsto P atTop (𝓝 (b*(a-b))) := by
    simpa only [P,scaledLower,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hPcont.continuousAt.tendsto.comp hpairlim
  have hQ : Tendsto Q atTop (𝓝 (a*(a-b))) := by
    simpa only [Q,scaledUpper,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hQcont.continuousAt.tendsto.comp hpairlim
  have hG : Tendsto G atTop (𝓝 (a^2*(a-b))) := by
    simpa only [G,scaledGap,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hGcont.continuousAt.tendsto.comp hpairlim
  have hR : Tendsto (fun n => P n/S n) atTop (𝓝 b) := by
    simpa only [mul_div_cancel_right₀ _ (sub_pos.mpr hab).ne'] using
      hP.div hS (sub_pos.mpr hab).ne'
  have hU : Tendsto (fun n => Q n/S n) atTop (𝓝 a) := by
    simpa only [mul_div_cancel_right₀ _ (sub_pos.mpr hab).ne'] using
      hQ.div hS (sub_pos.mpr hab).ne'
  have hSe := hS.eventually (eventually_gt_nhds (sub_pos.mpr hab))
  have hGe := hG.eventually (eventually_gt_nhds (mul_pos (sq_pos_of_ne_zero ha) (sub_pos.mpr hab)))
  have hRe := hR.eventually (eventually_gt_nhds (show b-ε<b by linarith))
  have hUe := hU.eventually (eventually_gt_nhds (show a-ε<a by linarith))
  obtain ⟨n,hSn,hGn,hRn,hUn⟩ := (hSe.and (hGe.and (hRe.and hUe))).exists
  let X := sumLowerNum D a b (c n) (d n)
  let Y := sumUpperNum D a b (c n) (d n)
  let T := sumDen a b (c n) (d n)
  have hST : (d n)^2*S n=T := scaled_den_eq (hd n).ne'
  have hPX : (d n)^2*P n=X := scaled_lower_eq (hd n).ne'
  have hQY : (d n)^2*Q n=Y := scaled_upper_eq (hd n).ne'
  have hT : 0<T := by rw [← hST]; exact mul_pos (sq_pos_of_pos (hd n)) hSn
  have hXT : X/T=P n/S n := by
    rw [← hST,← hPX]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 (hd n).ne')
  have hYT : Y/T=Q n/S n := by
    rw [← hST,← hQY]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 (hd n).ne')
  have hbelow : X/T<b := by
    have hgap := scaled_gap_eq a b (c n-d n) (d n)⁻¹
    rw [hbase] at hgap
    change b*S n-P n=(d n)⁻¹*G n at hgap
    have hpos : 0<(d n)⁻¹*G n := mul_pos (inv_pos.mpr (hd n)) hGn
    rw [hXT]
    exact (div_lt_iff₀ hSn).mpr (by linarith)
  have hXY : Y^3-X^3=D*T^3 := sum_chord_identity hbase (he n)
  have heq : (Y/T)^3-(X/T)^3=D := by
    rw [div_pow,div_pow,← sub_div]
    exact (div_eq_iff (pow_ne_zero 3 hT.ne')).mpr hXY
  have hupper : Y/T<a := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by
    have hp := (Odd.strictMono_pow (by decide : Odd 3)) hbelow
    linarith)
  exact ⟨Y/T,X/T,by rwa [hXT],hbelow,by rwa [hYT],hupper,heq⟩

/-- A sum of two distinct positive cubes is also a difference of positive
rational cubes, by the tangent construction. -/
lemma positive_difference_of_sum {a b : ℚ} (ha : 0<a) (hab : a<b) :
    ∃ u v : ℚ, 0<v ∧ v<u ∧ u^3-v^3=a^3+b^3 := by
  have hb : 0<b := ha.trans hab
  let T := b^3-a^3
  have hT : 0<T := sub_pos.mpr ((Odd.strictMono_pow (by decide : Odd 3)) hab)
  let u := b*(b^3+2*a^3)/T
  let v := a*(2*b^3+a^3)/T
  have hu : 0<u := by dsimp [u]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have he : u^3-v^3=a^3+b^3 := by
    dsimp [u,v]
    rw [div_pow,div_pow,← sub_div]
    apply (div_eq_iff (pow_ne_zero 3 hT.ne')).mpr
    dsimp [T]
    ring
  have huv : v<u := (Odd.pow_lt_pow (by decide : Odd 3)).mp (by
    have hs : 0<a^3+b^3 := by positivity
    linarith)
  exact ⟨u,v,hv,huv,he⟩

lemma sum_unbounded {a b : ℚ} (ha : 0<a) (hab : a<b) (M : ℚ) :
    ∃ x y : ℚ, M<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=a^3+b^3 := by
  obtain ⟨u,v,hv,huv,he⟩ := positive_difference_of_sum ha hab
  simpa only [he] using UnboundedCubeDifferences.unbounded_rational_difference hv huv M

#print axioms near_below_of_unbounded
#print axioms sum_unbounded
end Erdos1206.RationalCurveLocal
