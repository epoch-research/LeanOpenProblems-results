import Submission.UnboundedCubeDifferences

/-! Rational representations close to a prescribed pair. These statements
have no bounds on the denominators of their witnesses. -/

namespace Erdos1206.LocalCubeDifferences
open Filter
open scoped Topology Classical
set_option maxHeartbeats 1000000

/-- The other chord orientation, useful near a prescribed positive pair. -/
def sumLowerNum (D a b c d : ℚ) : ℚ := b*d*(a*d-b*c)+D*(a-c)
def sumUpperNum (D a b c d : ℚ) : ℚ := a*c*(a*d-b*c)+D*(b-d)
def sumDen (a b c d : ℚ) : ℚ := a*c^2-b*d^2-a^2*c+b^2*d

lemma sum_chord_identity {D a b c d : ℚ}
    (h₁ : a^3-b^3=D) (h₂ : c^3-d^3=D) :
    (sumUpperNum D a b c d)^3-(sumLowerNum D a b c d)^3=
      D*(sumDen a b c d)^3 := by
  simp only [sumUpperNum,sumLowerNum,sumDen]
  linear_combination (a*c^2-b*d^2-D)^3*h₁-(a^2*c-b^2*d-D)^3*h₂

lemma gap_tendsto_zero {D : ℚ} (hD : 0<D) {c d : ℕ → ℚ}
    (hd : ∀ n, 0<d n) (he : ∀ n, (c n)^3-(d n)^3=D)
    (hlim : Tendsto d atTop atTop) :
    Tendsto (fun n => c n-d n) atTop (𝓝 0) := by
  have hv := tendsto_inv_atTop_zero.comp hlim
  have hdc (n : ℕ) : d n<c n :=
    (Odd.pow_lt_pow (by decide : Odd 3)).mp (by linarith [he n])
  have hupper (n : ℕ) : c n-d n≤D*(d n)⁻¹^2 := by
    have hgap : 0<c n-d n := sub_pos.mpr (hdc n)
    have hdn : 0<d n := hd n
    have hc : 0<c n := (hd n).trans (hdc n)
    have hf : (c n-d n)*((c n)^2+c n*d n+(d n)^2)=D := by
      linear_combination he n
    have hrest : 0≤(c n-d n)*((c n)^2+c n*d n) := by positivity
    have hmul : (c n-d n)*(d n)^2≤D := by nlinarith
    have hh := (le_div_iff₀ (pow_pos (hd n) 2)).mpr hmul
    simpa [div_eq_mul_inv,inv_pow] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => D*(d n)⁻¹^2) atTop (𝓝 0) from by
      simpa using tendsto_const_nhds.mul (hv.pow 2))
    (fun n => (sub_pos.mpr (hdc n)).le) hupper

def scaledDen (a b h v : ℚ) : ℚ :=
  (a-b)+(-a^2+2*a*h+b^2)*v+(-a^2*h+a*h^2)*v^2

def scaledLower (D a b h v : ℚ) : ℚ :=
  b*(a-b)+(-D-b^2*h)*v+(D*a-D*h)*v^2

def scaledGap (a b h v : ℚ) : ℚ :=
  a^2*(a-b)+(2*a*b+b^2)*h+
    (-a*(a^3-b^3)+(a^3-a^2*b-b^3)*h+a*b*h^2)*v

lemma scaled_den_eq {a b c d : ℚ} (hd : d≠0) :
    d^2*scaledDen a b (c-d) d⁻¹=sumDen a b c d := by
  simp only [scaledDen,sumDen]
  field_simp
  ring

lemma scaled_lower_eq {D a b c d : ℚ} (hd : d≠0) :
    d^2*scaledLower D a b (c-d) d⁻¹=sumLowerNum D a b c d := by
  simp only [scaledLower,sumLowerNum]
  field_simp
  ring

lemma scaled_gap_eq (a b h v : ℚ) :
    b*scaledDen a b h v-scaledLower (a^3-b^3) a b h v=v*scaledGap a b h v := by
  simp only [scaledDen,scaledLower,scaledGap]
  ring

/-- A positive rational pair has other representations approaching it from
below in the lower coordinate. -/
theorem near_pair_below {a b ε : ℚ} (hb : 0<b) (hab : b<a) (hε : 0<ε) :
    ∃ x y : ℚ, 0<y ∧ b-ε<y ∧ y<b ∧ 0<x ∧ x^3-y^3=a^3-b^3 := by
  have ha := hb.trans hab
  let D := a^3-b^3
  have hD : 0<D := sub_pos.mpr ((Odd.strictMono_pow (by decide : Odd 3)) hab)
  have hex (n : ℕ) : ∃ x y : ℚ, (n : ℚ)<y ∧ 0<y ∧ 0<x ∧ x^3-y^3=D :=
    UnboundedCubeDifferences.unbounded_rational_difference hb hab n
  choose c d hnd hd hc he using hex
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
  have hGcont : Continuous (fun p : ℚ×ℚ => scaledGap a b p.1 p.2) := by
    unfold scaledGap
    fun_prop
  let S : ℕ → ℚ := fun n => scaledDen a b (c n-d n) (d n)⁻¹
  let P : ℕ → ℚ := fun n => scaledLower D a b (c n-d n) (d n)⁻¹
  let G : ℕ → ℚ := fun n => scaledGap a b (c n-d n) (d n)⁻¹
  have hS : Tendsto S atTop (𝓝 (a-b)) := by
    simpa only [S,scaledDen,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hScont.continuousAt.tendsto.comp hpairlim
  have hP : Tendsto P atTop (𝓝 (b*(a-b))) := by
    simpa only [P,scaledLower,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hPcont.continuousAt.tendsto.comp hpairlim
  have hG : Tendsto G atTop (𝓝 (a^2*(a-b))) := by
    simpa only [G,scaledGap,mul_zero,zero_mul,zero_pow (by decide : 2≠0),add_zero]
      using hGcont.continuousAt.tendsto.comp hpairlim
  have hR : Tendsto (fun n => P n/S n) atTop (𝓝 b) := by
    simpa only [mul_div_cancel_right₀ _ (sub_pos.mpr hab).ne'] using
      hP.div hS (sub_pos.mpr hab).ne'
  have hSe := hS.eventually (eventually_gt_nhds (sub_pos.mpr hab))
  have hPe := hP.eventually (eventually_gt_nhds (mul_pos hb (sub_pos.mpr hab)))
  have hGe := hG.eventually (eventually_gt_nhds (mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hab)))
  have hRe := hR.eventually (eventually_gt_nhds (show b-ε<b by linarith))
  obtain ⟨n,hSn,hPn,hGn,hRn⟩ := (hSe.and (hPe.and (hGe.and hRe))).exists
  let X := sumLowerNum D a b (c n) (d n)
  let Y := sumUpperNum D a b (c n) (d n)
  let T := sumDen a b (c n) (d n)
  have hST : (d n)^2*S n=T := scaled_den_eq (hd n).ne'
  have hPX : (d n)^2*P n=X := scaled_lower_eq (hd n).ne'
  have hT : 0<T := by rw [← hST]; exact mul_pos (sq_pos_of_pos (hd n)) hSn
  have hX : 0<X := by rw [← hPX]; exact mul_pos (sq_pos_of_pos (hd n)) hPn
  have hXT : X/T=P n/S n := by
    rw [← hST,← hPX]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 (hd n).ne')
  have hbelow : X/T<b := by
    have hgap := scaled_gap_eq a b (c n-d n) (d n)⁻¹
    change b*S n-P n=(d n)⁻¹*G n at hgap
    have hpos : 0<(d n)⁻¹*G n := mul_pos (inv_pos.mpr (hd n)) hGn
    rw [hXT]
    exact (div_lt_iff₀ hSn).mpr (by linarith)
  have hXY : Y^3-X^3=D*T^3 := sum_chord_identity (D := D) rfl (he n)
  have hY : 0<Y := by
    apply (Odd.pow_pos_iff (by decide : Odd 3)).mp
    nlinarith [pow_pos hX 3,mul_pos hD (pow_pos hT 3)]
  refine ⟨Y/T,X/T,div_pos hX hT,by rwa [hXT],hbelow,div_pos hY hT,?_⟩
  rw [div_pow,div_pow,← sub_div]
  exact (div_eq_iff (pow_ne_zero 3 hT.ne')).mpr hXY

#print axioms near_pair_below

/-- Every two positive rational roots occur in the second and fourth positions
of some strict positive rational cubic collision. -/
theorem second_fourth_pair {b d : ℚ} (hb : 0<b) (hbd : b<d) :
    ∃ a c : ℚ, 0<a ∧ a<b ∧ b<c ∧ c<d ∧ a^3+d^3=b^3+c^3 := by
  obtain ⟨c,a,ha,hnear,hab,hc,he⟩ := near_pair_below hb hbd (sub_pos.mpr hbd)
  have hD : 0<d^3-b^3 := sub_pos.mpr ((Odd.strictMono_pow (by decide : Odd 3)) hbd)
  have hs := UnboundedCubeDifferences.strict_increment hD he rfl ha hab
  refine ⟨a,c,ha,hab,?_,hs.2.1,?_⟩ <;> linarith

#print axioms second_fourth_pair
end Erdos1206.LocalCubeDifferences
