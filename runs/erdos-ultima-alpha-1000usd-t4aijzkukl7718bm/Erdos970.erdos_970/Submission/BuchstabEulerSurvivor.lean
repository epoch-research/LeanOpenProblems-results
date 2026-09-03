import Submission.BuchstabEulerUniformMain
import Submission.BuchstabSmoothGrowth

/-! Charging the actual smooth error costs against the quantitative Euler
main bound. The resulting estimate is explicit in the recursion depth.
It does not remove that depth cost or prove the quadratic endpoint. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 2400000

lemma eulerCoordinate_plus_one_le_log (C B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B) (k : ℕ) :
    eulerCoordinate C k+1 ≤ (1+(B+1)/log 2)*log (nthPrime k : ℝ) := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hlp : log 2 ≤ log (nthPrime k : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast (nthPrime_prime k).two_le)
  have hh := mul_le_mul_of_nonneg_left hlp (show 0 ≤ (B+1)/log 2 by positivity)
  rw [div_mul_cancel₀ _ hl2.ne'] at hh
  have hcoord := (abs_le.mp (hB k)).2
  nlinarith only [hh,hcoord]

lemma smooth_shape_le_prime_log_square (k : ℕ) (D : ℝ) (hpD : (nthPrime k : ℝ) ≤ D) :
    smoothLevelShape k D ≤ D/log (nthPrime k : ℝ)^2 := by
  have hp1 : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  have hp0 : (0 : ℝ) < nthPrime k := by linarith
  have hD0 : 0 < D := hp0.trans_le hpD
  have hlp : 0 < log (nthPrime k : ℝ) := log_pos hp1
  have hs : 1 ≤ log D/log (nthPrime k : ℝ) := by
    apply (le_div_iff₀ hlp).mpr
    simpa only [one_mul] using log_le_log hp0 hpD
  have hh := smooth_shape_exp_le k (log D/log (nthPrime k : ℝ)) hs
  rw [div_mul_cancel₀ _ hlp.ne',exp_log hD0] at hh
  exact hh

/-- Once the geometric main-profile tail is at most 1/T, the fully charged
interval length is bounded by a fixed constant times R^n*p_k^2. -/
theorem euler_main_survivor_depth_bound (C B H : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B) (hH : 0 ≤ H)
    (hB : ∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B)
    (hmain : ∀ n k : ℕ, ∀ s : ℝ, 2 ≤ s →
      prefixDensity primeMarginal k*((s-2-(24000+2*H)*(19/20 : ℝ)^n)/s) ≤
        referenceLower n k (exp (s*eulerCoordinate C k+(2*(n : ℝ)+2)*B))) :
    ∃ A > (0 : ℝ), ∀ n k : ℕ,
      (24000+2*H)*(19/20 : ℝ)^n ≤ 1/eulerCoordinate C k →
      (jacobsthalFunction k : ℝ) ≤ A*(3600*exp (2*B))^n*(nthPrime k : ℝ)^2 := by
  let F : ℝ := 1+(B+1)/log 2
  let J : ℝ := 2*C*F^2
  let a : ℝ := 60*smoothLeafConstant 1
  let A : ℝ := (J*a+1)*exp (2+4*B)
  have hF : 0 < F := by dsimp [F]; have := log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have ha : 0 < a := by dsimp [a]; have := smoothLeafConstant_pos 1; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,fun n k hn => ?_⟩
  let T := eulerCoordinate C k
  let L := log (nthPrime k : ℝ)
  let s : ℝ := 2+2/T
  let D : ℝ := exp (s*T+(2*(n : ℝ)+2)*B)
  have hT : 0 < T := eulerCoordinate_pos C hC k
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hp1 : (1 : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_prime k).one_le
  have hL : 0 < L := log_pos (by exact_mod_cast (nthPrime_prime k).one_lt)
  have hs2 : 2 ≤ s := by dsimp [s]; exact le_add_of_nonneg_right (by positivity)
  have hs : 0 < s := by linarith
  have hsT : s*T=2*T+2 := by dsimp [s]; field_simp <;> ring
  have hD : 0 < D := exp_pos _
  have hb : 2*B ≤ (2*(n : ℝ)+2)*B := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    nlinarith only [hB0,hn0]
  have hkeep : primeKeep nthPrime k D := eulerCoordinate_square_guard C B _ s hC hB hb hs2 k
  have hpD : (nthPrime k : ℝ) ≤ D := by
    have hh : (nthPrime k : ℝ)^2 ≤ D := hkeep
    nlinarith only [hh,hp1]
  have hD1 : 1 ≤ D := hp1.trans hpD
  have hden := nthPrime_prefix_density_pos k
  have hTl := eulerCoordinate_plus_one_le_log C B hB0 hB k
  change T+1 ≤ F*L at hTl
  have hprod : C*T*(s*T) ≤ J*L^2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ T+1) hTl 2
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2*C)
    have hCT := mul_pos hC hT
    rw [hsT]
    dsimp [J]
    nlinarith only [hmul,hCT,hC]
  have hid : prefixDensity primeMarginal k*(1/T/s)=1/(C*T*(s*T)) := by
    dsimp [T,eulerCoordinate]
    field_simp [hC.ne',hden.ne',hs.ne']
    <;> ring
  have hlow : 1/(J*L^2) ≤ referenceLower n k D := by
    apply le_trans _ (hmain n k s hs2)
    have hrec := one_div_le_one_div_of_le (show 0 < C*T*(s*T) by positivity) hprod
    rw [← hid] at hrec
    apply hrec.trans
    apply mul_le_mul_of_nonneg_left _ hden.le
    apply div_le_div_of_nonneg_right _ hs.le
    change 1/T ≤ s-2-(24000+2*H)*(19/20 : ℝ)^n
    change (24000+2*H)*(19/20 : ℝ)^n ≤ 1/T at hn
    dsimp only [s]
    rw [show 2/T=2*(1/T) by ring]
    linarith only [hn]
  let E : ℝ := a*3600^n*D/L^2
  have hcostAll (j : ℕ) (hj : j ≤ k) :
      lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n) j D ≤ E := by
    apply (smooth_cost_uniform_prefix n k j hj D hpD).trans
    have hh := mul_le_mul_of_nonneg_left (smooth_shape_le_prime_log_square k D hpD)
      (smoothRefinementConstant_pos n).le
    convert hh using 1
    dsimp only [E,a,smoothRefinementConstant,L]
    ring
  let X : ℝ := J*a*3600^n*D
  let m : ℕ := ⌊X⌋₊+1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXm : X < (m : ℝ) := by simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hcost : E < (m : ℝ)*(1/(J*L^2)) := by
    have hh := mul_lt_mul_of_pos_right hXm (show 0 < 1/(J*L^2) by positivity)
    have he : X*(1/(J*L^2))=E := by dsimp [X,E]; field_simp
    rwa [he] at hh
  have hpos : E < (m : ℝ)*referenceLower n k D :=
    hcost.trans_le (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg m))
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_depth_sharp_cost n k m D hD.le hkeep E hcostAll hpos)
  have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp only [m]
    push_cast
    exact add_le_add (Nat.floor_le hX) le_rfl
  have hunit : 1 ≤ (3600 : ℝ)^n*D := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD1
  have hlen : (jacobsthalFunction k : ℝ) ≤ (J*a+1)*3600^n*D := by
    dsimp only [X] at hmupper
    nlinarith only [hjR,hmupper,hunit]
  have hcoord := (abs_le.mp (hB k)).2
  change T-L ≤ B at hcoord
  have hDbound : D ≤ exp (2+4*B)*(exp (2*B))^n*(nthPrime k : ℝ)^2 := by
    have hlog : s*T+(2*(n : ℝ)+2)*B ≤ 2*L+(2+4*B)+(n : ℝ)*(2*B) := by
      rw [hsT]
      nlinarith only [hcoord]
    have hh := exp_le_exp.mpr hlog
    have hexp : exp (2*L)=(nthPrime k : ℝ)^2 := by
      simpa only [L,Nat.cast_ofNat,exp_log hp0] using exp_nat_mul L 2
    have he : exp (2*L+(2+4*B)+(n : ℝ)*(2*B)) =
        exp (2+4*B)*(exp (2*B))^n*(nthPrime k : ℝ)^2 := by
      rw [exp_add,exp_add,exp_nat_mul,hexp]
      ring
    rwa [he] at hh
  have hh := hlen.trans (mul_le_mul_of_nonneg_left hDbound (show 0 ≤ (J*a+1)*3600^n by positivity))
  dsimp only [A]
  rw [mul_pow]
  convert hh using 1 <;> ring

#print axioms euler_main_survivor_depth_bound
end Erdos970.RecursiveSieve.Buchstab
