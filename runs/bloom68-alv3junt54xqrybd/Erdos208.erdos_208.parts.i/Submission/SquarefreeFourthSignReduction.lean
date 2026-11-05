import Submission.SquarefreeFourthSignAlgebra
import Submission.SquarefreeFourthSignGeometry

/-! Integer reduction and the asymmetric unit-minor case. -/
namespace SquarefreeFourthSign

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

lemma small_weight_of_cofactor_bounds (x C L E M C₀ : ℝ)
    (hE : 0 < E) (hlow : M*E ≤ L) (hhigh : L < x*C)
    (hcoef : 4*x*C < 3*E*C₀) : 4*M < 3*C₀ := by
  have hh : (4*M)*E < (3*C₀)*E := by nlinarith only [hlow,hhigh,hcoef]
  exact (mul_lt_mul_iff_left₀ hE).mp (by simpa only [mul_comm] using hh)

/-- Once both integer minors are one, divisibility and the geometric bound
force `b=a+c` and `a≥c`. -/
lemma unit_gap_reduction (a b c u v h : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hA : b*u-a*v = 1) (hB : c*v-b*h = 1)
    (hD : 0 ≤ a*(a+b)-c*(b+c))
    (hsmall : 4*a*(a+b)*(a+b+c) < 3*(a+b)*(a+c)*(b+c)) :
    b = a+c ∧ c ≤ a := by
  have ht : 0 < a+b+c := by omega
  have hac : c ≤ a := by
    have hprod : 0 ≤ (a-c)*(a+b+c) := by nlinarith only [hD]
    by_contra hn
    have hneg := mul_neg_of_neg_of_pos (show a-c < 0 by omega) ht
    omega
  have hrel : a+c = b*(c*u-a*h) := by
    have hid := minor_gap_relation a b c u v h
    rw [hA,hB] at hid
    nlinarith only [hid]
  have hk : 1 ≤ c*u-a*h := by
    by_contra hh
    have hnon := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b by omega)
      (show c*u-a*h ≤ 0 by omega)
    nlinarith only [hrel,hnon,ha,hc]
  have hbcase : b = a+c ∨ 2*b ≤ a+c := by
    by_cases heq : c*u-a*h = 1
    · left
      rw [heq] at hrel
      linarith
    · right
      have hk2 : 2 ≤ c*u-a*h := by omega
      have hm := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ b by omega)
      nlinarith only [hm,hrel]
  rcases hbcase with heq | hhalf
  · exact ⟨heq,hac⟩
  · have hp₁ : 0 ≤ (a-c)*(7*(a+c)+4*b) := mul_nonneg (by omega) (by positivity)
    have hp₂ : 0 ≤ (a+c)*(a+c-2*b) := mul_nonneg (by positivity) (by omega)
    have hbound : 3*(a+c)*(b+c) ≤ 4*a*(a+b+c) := by nlinarith only [hp₁,hp₂]
    have hm := mul_le_mul_of_nonneg_left hbound (show 0 ≤ a+b by omega)
    nlinarith only [hm,hsmall]

/-- The residue `δv ≡ -2 (mod b)` supplies the integer lower bound needed
in the asymmetric unit-minor case. Written as a multiple, not a real congruence. -/
lemma asymmetric_residue (a b c u v : ℤ)
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hac : c < a) (hv : 1 ≤ v)
    (hb : b = a+c) (hA : b*u-a*v = 1) :
    3 ≤ b ∧ b-2 ≤ (a-c)*v := by
  have hb3 : 3 ≤ b := by omega
  have hδv : 0 < (a-c)*v := mul_pos (by omega) (by omega)
  have hid : (a-c)*v+2 = b*(2*u-v) := by
    rw [hb] at hA ⊢
    nlinarith only [hA]
  have hk : 1 ≤ 2*u-v := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b by omega)
      (show 2*u-v ≤ 0 by omega)
    nlinarith only [hm,hid,hδv]
  have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ b by omega)
  exact ⟨hb3, by nlinarith only [hm,hid]⟩

/-- All analytic inequalities in the asymmetric unit-minor case, with the
integer information isolated in `hb3` and `hres`. The two hypotheses are
exactly the supplied mixed and three-point identities with their error bounds. -/
theorem asymmetric_unit_impossible (x a b c v : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hc : 0 < c) (hv : 0 < v)
    (hb3 : 3 ≤ b) (hb : b = a+c) (hac : c < a)
    (hres : b-2 ≤ (a-c)*v)
    (hmixed :
      (2*b*a*(a+b))*e3 x (x+a) (x+a+b) (x+2*b) +
        (2*b*(a-c))*x^2*e2 (x+a) (x+a+b) (x+2*b) <
      x*(2*b*c*(a+b)*e2 x (x+a+b) (x+2*b) +
        a*b*(a+b)*e2 x (x+a) (x+a+b)))
    (htriple : a*v*(a+b)*e2 x (x+a) (x+a+b) -
        ((x+a)+(x+a+b))*x^2 < x*(a+b)*(x+(x+a+b))) : False := by
  let y := x+a
  let z := x+a+b
  let w := x+2*b
  let E := e3 x y z w
  let S₀ := e2 x y z
  let S₁ := e2 x z w
  let S₂ := e2 y z w
  let C := 2*b*c*(a+b)*S₁ + a*b*(a+b)*S₀
  let C₀ := b*(a+b)*(b+c)
  let U := 2*b*a*(a+b)
  let δ := a-c
  have hb0 : 0 < b := by linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hy : 0 < y := by dsimp [y]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hxy : x < y := by dsimp [y]; linarith
  have hyz : y < z := by dsimp [y,z]; linarith
  have hzw : z < w := by dsimp [z,w]; linarith
  have hE : 0 < E := e3_pos x y z w hx hy hz hw
  have hS₀ : 0 < S₀ := e2_pos x y z hx hy hz
  have hS₁ : 0 < S₁ := e2_pos x z w hx hz hw
  have hS₂ : 0 < S₂ := e2_pos y z w hy hz hw
  have hC : 0 < C := by dsimp [C]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  change U*E+(2*b*δ)*x^2*S₂ < x*C at hmixed
  change a*v*(a+b)*S₀-(y+z)*x^2 < x*(a+b)*(x+z) at htriple
  have hbase : U*E < x*C := by
    have hnon : 0 ≤ (2*b*δ)*x^2*S₂ := by positivity
    linarith
  have hE₀ := e3_lower_omitted_right x y z w hx hxy hyz hzw
  have hE₁ := e3_lower_omitted_middle x y z w hx hxy hyz hzw
  change (3*w+x)*S₀ < 3*E at hE₀
  change (3*y+x)*S₁ < 3*E at hE₁
  by_cases hsmall : x ≤ 2*b
  · have hax : x ≤ 4*a := by linarith
    have hS₁bound : 3*x*S₁ < 2*E := by
      have hm := mul_le_mul_of_nonneg_right (show 9*x/2 ≤ 3*y+x by dsimp [y]; linarith) hS₁.le
      nlinarith only [hE₁,hm]
    have hS₀bound : 2*x*S₀ < E := by
      have hm := mul_le_mul_of_nonneg_right (show 6*x ≤ 3*w+x by dsimp [w]; linarith) hS₀.le
      nlinarith only [hE₀,hm]
    have hm₁ := mul_lt_mul_of_pos_left (show x*S₁ < (2/3)*E by linarith)
      (show 0 < 2*b*c*(a+b) by positivity)
    have hm₀ := mul_lt_mul_of_pos_left (show x*S₀ < E/2 by linarith)
      (show 0 < a*b*(a+b) by positivity)
    have hCup : x*C < E*b*(a+b)*((4/3)*c+a/2) := by
      dsimp [C]
      nlinarith only [hm₁,hm₀]
    have hcoeff : (4/3)*c+a/2 < 2*a := by linarith
    have hCup' := mul_lt_mul_of_pos_left hcoeff (show 0 < E*b*(a+b) by positivity)
    have hright : E*b*(a+b)*(2*a) = U*E := by dsimp [U]; ring
    rw [hright] at hCup'
    linarith
  · have hxlarge : 2*b < x := lt_of_not_ge hsmall
    have hV₁ : v3 x z w = 2*b*c*(a+b) := by dsimp [v3,z,w]; rw [hb]; ring
    have hV₀ : v3 x y z = a*b*(a+b) := by dsimp [v3,y,z]; ring
    have hweight := cofactor_weight_lower x y z w hx hxy hyz hzw
    rw [hV₁,hV₀] at hweight
    have hC₀eq : 2*b*c*(a+b)+a*b*(a+b) = C₀ := by dsimp [C₀]; rw [hb]; ring
    rw [hC₀eq] at hweight
    change 4*x*C < 3*E*C₀ at hweight
    have hUratio : 2*C₀ ≤ 3*U := by
      have hp : 0 ≤ 4*b*(a+b)*(a-c) := by positivity
      have hid : 3*U-2*C₀ = 4*b*(a+b)*(a-c) := by dsimp [C₀,U]; rw [hb]; ring
      linarith only [hp,hid]
    have hmul := mul_le_mul_of_nonneg_left hUratio hE.le
    have hbasefrac : 8*x*C < 9*U*E := by nlinarith only [hweight,hmul]
    have herror : 18*b*δ*x^2*S₂ < x*C := by nlinarith only [hmixed,hbasefrac]
    have hS₂lower : 3*y^2 ≤ S₂ := e2_lower y z w hy.le hyz.le (hyz.trans hzw).le
    have hS₀upper : S₀ ≤ 3*w^2 := e2_upper x y z w hx.le hy.le hz.le
      (hxy.trans (hyz.trans hzw)).le (hyz.trans hzw).le hzw.le
    have hS₁upper : S₁ ≤ 3*w^2 := e2_upper x z w w hx.le hz.le hw.le
      (hxy.trans (hyz.trans hzw)).le hzw.le le_rfl
    have hCupper : C ≤ 3*w^2*C₀ := by
      have hm₀ := mul_le_mul_of_nonneg_left hS₀upper (show 0 ≤ a*b*(a+b) by positivity)
      have hm₁ := mul_le_mul_of_nonneg_left hS₁upper (show 0 ≤ 2*b*c*(a+b) by positivity)
      dsimp [C]
      nlinarith only [hm₀,hm₁,hC₀eq]
    have hEleft := mul_le_mul_of_nonneg_left hS₂lower (show 0 ≤ 18*b*δ*x^2 by positivity)
    have hEright := mul_le_mul_of_nonneg_left hCupper hx.le
    have hmid : (18*b*δ*x*y^2)*(3*x) < (w^2*C₀)*(3*x) := by
      nlinarith only [hEleft,herror,hEright]
    have hmid' : 18*b*δ*x*y^2 < w^2*C₀ :=
      (mul_lt_mul_iff_left₀ (show 0 < 3*x by positivity)).mp (by simpa only [mul_comm] using hmid)
    have hC₀bound : C₀ ≤ (9/4)*b^3 := by
      have hp := sq_nonneg (a-c)
      have hprod : 4*(a+b)*(b+c) ≤ 9*b^2 := by rw [hb]; nlinarith only [hp]
      have hm := mul_le_mul_of_nonneg_left hprod hb0.le
      dsimp [C₀]
      nlinarith only [hm]
    have hwratio : 5*w < 8*y := by dsimp [w,y]; linarith
    have hwsq : w^2 < (64/25)*y^2 := by
      have hm := mul_pos (show 0 < 8*y-5*w by linarith) (show 0 < 8*y+5*w by positivity)
      nlinarith only [hm]
    have hmC := mul_le_mul_of_nonneg_left hC₀bound (sq_nonneg w)
    have hmw := mul_lt_mul_of_pos_right hwsq (show 0 < (9/4)*b^3 by positivity)
    have huppermul : (18*δ*x)*(b*y^2) < ((144/25)*b^2)*(b*y^2) := by
      nlinarith only [hmid',hmC,hmw]
    have hupper : δ*x < (8/25)*b^2 := by
      have hh : 18*δ*x < (144/25)*b^2 :=
        (mul_lt_mul_iff_left₀ (show 0 < b*y^2 by positivity)).mp huppermul
      linarith
    -- Opposite inequality from the exact three-point identity and the residue.
    have hS₀strict : 3*x^2 < S₀ := e2_strict_lower x y z hx hxy hyz
    have habx : a+b < x := by linarith
    have hyzbound : y+z < (7/2)*x := by dsimp [y,z]; linarith
    have hxzbound : x+z < 3*x := by dsimp [z]; linarith
    have hmT₀ := mul_lt_mul_of_pos_left hS₀strict (show 0 < a*v*(a+b) by positivity)
    have hmT₁ := mul_lt_mul_of_pos_right hyzbound (sq_pos_of_pos hx)
    have hprod : (a+b)*(x+z) < x*(3*x) := by gcongr
    have hmT₂ := mul_lt_mul_of_pos_left hprod hx
    have hTbound : (3*a*v*(a+b))*x^2 < ((13/2)*x)*x^2 := by
      nlinarith only [hmT₀,htriple,hmT₁,hmT₂]
    have hTbound' : 3*a*v*(a+b) < (13/2)*x :=
      (mul_lt_mul_iff_left₀ (sq_pos_of_pos hx)).mp (by simpa only [mul_comm] using hTbound)
    have haprod : (3/4)*b^2 ≤ a*(a+b) := by
      have hp := mul_nonneg (show 0 ≤ 2*a-b by linarith) (show 0 ≤ 2*a+3*b by positivity)
      nlinarith only [hp]
    have hmav := mul_le_mul_of_nonneg_right haprod hv.le
    have hvx : (9/26)*v*b^2 < x := by nlinarith only [hmav,hTbound']
    have hmδ := mul_lt_mul_of_pos_left hvx hδ
    have hres' : 1 ≤ δ*v := by dsimp [δ]; linarith
    have hmres := mul_le_mul_of_nonneg_right hres' (show 0 ≤ (9/26)*b^2 by positivity)
    have hlower : (9/26)*b^2 < δ*x := by nlinarith only [hmδ,hmres]
    nlinarith only [hlower,hupper,sq_pos_of_pos hb0]

end SquarefreeFourthSign
