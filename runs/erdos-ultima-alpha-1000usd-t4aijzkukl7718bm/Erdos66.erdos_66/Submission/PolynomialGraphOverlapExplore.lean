import Submission.PolynomialGraphSubsetExplore

/-! Uniform vanishing overlap with polynomial graphs under a logarithmic
representation envelope. This is not an obstruction to arbitrary sets. -/
namespace Erdos66PolynomialGraphOverlap
open Filter AdditiveCombinatorics Polynomial Erdos66PolynomialGraphSubset
open scoped Classical Topology
set_option maxHeartbeats 2400000

lemma log_graph_scale_bound (H : ℕ) (hH : 0<H) :
    Real.log (2*(H:ℝ)^4+2)≤3+8*Real.sqrt (H:ℝ) := by
  have hH1 : (1:ℝ)≤H := by exact_mod_cast hH
  have hH0 : (0:ℝ)<H := by exact_mod_cast hH
  have hp : (1:ℝ)≤(H:ℝ)^4 := one_le_pow₀ hH1
  have ht : 2*(H:ℝ)^4+2≤4*(H:ℝ)^4 := by linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2*(H:ℝ)^4+2) ht
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
  have h4 : Real.log (4:ℝ)≤3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4) using 1 <;> norm_num
  have hsmall := Real.log_le_rpow_div (le_of_lt hH0) (show (0:ℝ)<1/2 by norm_num)
  rw [←Real.sqrt_eq_rpow] at hsmall
  norm_num at hsmall hl
  nlinarith

/-- The permitted fraction tends to zero uniformly over all polynomials,
even when their coefficients and degrees depend on the modulus. -/
theorem eventually_small_polynomial_overlap_of_envelope (A : Set ℕ) (K C : ℝ)
    (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n : ℕ, (sumRep A n:ℝ)≤K+C*Real.log ((n:ℝ)+2))
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Polynomial (ZMod ((n+1)^2)),
      ((retainedInputs P A).card:ℝ)<δ*((n+1:ℕ):ℝ)^2 := by
  let D := 4*K+12*C+4
  let E := 32*C
  have hD : 0≤D := by dsimp [D]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hδ2 : 0<δ^2 := sq_pos_of_pos hδ
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((D+E)/δ^2+1))
  have hk1 : (1:ℝ)<k := (le_max_left _ _).trans_lt hk
  have hkb : (D+E)/δ^2+1<(k:ℝ) := (le_max_right _ _).trans_lt hk
  refine eventually_atTop.mpr ⟨k^2,fun n hn P ↦ ?_⟩
  let H := n+1
  let x := Real.sqrt (H:ℝ)
  have hH : 0<H := by dsimp [H]; omega
  have hH0 : (0:ℝ)<H := by exact_mod_cast hH
  have hx0 : 0≤x := Real.sqrt_nonneg _
  have hxx : x^2=(H:ℝ) := Real.sq_sqrt (by positivity)
  have hxk : (k:ℝ)≤x := by
    have hh : (k:ℝ)^2≤(H:ℝ) := by exact_mod_cast (show k^2≤H by dsimp [H]; omega)
    nlinarith
  have hx1 : (1:ℝ)≤x := by linarith
  have hxpos : 0<x := by linarith
  have hxb : D+E+δ^2<δ^2*x := by
    have hh : (D+E)/δ^2+1<x := hkb.trans_le hxk
    have hmul := mul_lt_mul_of_pos_right hh hδ2
    rw [add_mul,div_mul_cancel₀ _ hδ2.ne'] at hmul
    nlinarith
  by_contra hbad
  have hm : δ*(H:ℝ)^2≤((retainedInputs P A).card:ℝ) := le_of_not_gt hbad
  have hm2 : (δ*(H:ℝ)^2)^2≤((retainedInputs P A).card:ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) hm 2
  have hbound := retainedInputs_log_envelope P A K C hK hC hu
  have hprod : (δ^2*(H:ℝ))*(H:ℝ)^3≤
      (4*(K+C*Real.log (2*(H:ℝ)^4+2)+1))*(H:ℝ)^3 := by
    calc
      (δ^2*(H:ℝ))*(H:ℝ)^3=(δ*(H:ℝ)^2)^2 := by ring
      _ ≤ ((retainedInputs P A).card:ℝ)^2 := hm2
      _ ≤ 4*(H:ℝ)^3*(K+C*Real.log (2*(H:ℝ)^4+2)+1) := hbound
      _ = _ := by ring
  have hlin := le_of_mul_le_mul_right hprod (show (0:ℝ)<(H:ℝ)^3 by positivity)
  have hlog := log_graph_scale_bound H hH
  have hlow : δ^2*x^2≤D+E*x := by
    rw [hxx]
    dsimp [D,E]
    have hh := mul_le_mul_of_nonneg_left hlog hC
    change Real.log (2*(H:ℝ)^4+2)≤3+8*x at hlog
    nlinarith
  have hmul := mul_lt_mul_of_pos_right hxb hxpos
  have hDmul := mul_le_mul_of_nonneg_left hx1 hD
  have hδmul : 0≤δ^2*x := by positivity
  nlinarith

/-- Necessary for every finite normalized representation limit, including zero. -/
theorem eventually_small_polynomial_overlap {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Polynomial (ZMod ((n+1)^2)),
      ((retainedInputs P A).card:ℝ)<δ*((n+1:ℕ):ℝ)^2 := by
  obtain ⟨K,C,hK,hC,hu⟩ := Erdos66Counting.global_log_upper_bound h
  exact eventually_small_polynomial_overlap_of_envelope A K C hK hC.le hu δ hδ

end Erdos66PolynomialGraphOverlap
