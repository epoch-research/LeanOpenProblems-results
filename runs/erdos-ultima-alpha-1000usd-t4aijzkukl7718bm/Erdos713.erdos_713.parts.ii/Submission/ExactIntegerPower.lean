import FormalConjecturesUtil

/-! Integer values cannot agree exactly with a positive strictly subquadratic,
superlinear real power at all sufficiently large integers. This says nothing
by itself about an equivalent asymptotic or graph extremality. -/
open Filter Set
open scoped Topology
namespace Erdos713ExactIntegerPower
set_option maxHeartbeats 1000000

/-- Two applications of the mean value theorem, to the power increment and
then to its derivative. No differentiation of an asymptotic is used. -/
lemma second_difference (α x : ℝ) (hx : 0 < x) :
    ∃ z ∈ Ioo x (x+2),
      (x+2)^α - 2*(x+1)^α + x^α = α*(α-1)*z^(α-2) := by
  let D : ℝ → ℝ := fun y => (y+1)^α-y^α
  let D' : ℝ → ℝ := fun y => α*(y+1)^(α-1)-α*y^(α-1)
  have hd (y : ℝ) (hy : 0 < y) : HasDerivAt D (D' y) y := by
    have h1 := ((hasDerivAt_id y).add_const 1).rpow_const
      (Or.inl (by linarith : y+1 ≠ 0)) (p := α)
    have h0 := Real.hasDerivAt_rpow_const (Or.inl hy.ne') (p := α)
    simpa only [D, D', one_mul, mul_one] using h1.sub h0
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope D D' (by linarith : x < x+1)
    (fun y hy => (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy => hd y (by linarith [hy.1]))
  have hypos : 0 < y := by linarith [hy.1]
  have hp (z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun z : ℝ => z^(α-1)) ((α-1)*z^((α-1)-1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  obtain ⟨z,hz,he'⟩ := exists_hasDerivAt_eq_slope
    (fun z : ℝ => z^(α-1)) (fun z => (α-1)*z^((α-1)-1))
    (by linarith : y < y+1)
    (fun z hz => (hp z (by linarith [hz.1])).continuousAt.continuousWithinAt)
    (fun z hz => hp z (by linarith [hz.1]))
  refine ⟨z, ⟨by linarith [hy.1,hz.1], by linarith [hy.2,hz.2]⟩, ?_⟩
  have hsub : (α-1)-1 = α-2 := by ring
  have hadd : x+1+1 = x+2 := by ring
  simp only [D, D', add_sub_cancel_left, div_one, hadd] at he
  simp only [add_sub_cancel_left, div_one, hsub] at he'
  linear_combination -he - α*he'

/-- Exact agreement on a tail, unlike asymptotic equivalence, is incompatible
with an integer sequence when the exponent lies strictly between one and two. -/
theorem no_exact_integer_power_tail {f : ℕ → ℤ} {α c : ℝ}
    (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c) :
    ¬ (∀ᶠ n : ℕ in atTop, (f n : ℝ) = c*(n : ℝ)^α) := by
  intro hf
  have hlim : Tendsto (fun n : ℕ => c*(α*(α-1))*(n : ℝ)^(α-2)) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (show 0 < 2-α by linarith)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub, mul_zero] using hpow.const_mul (c*(α*(α-1)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hf
  obtain ⟨n,hn,hsmall⟩ := ((eventually_ge_atTop (max N 1)).and
    (hlim.eventually_lt_const (show (0 : ℝ) < 1 by norm_num))).exists
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast ((le_max_right _ _).trans hn : 1 ≤ n)
  obtain ⟨z,hz,he⟩ := second_difference α (n : ℝ) hnpos
  have hzp : 0 < z := lt_trans hnpos hz.1
  have hpow : z^(α-2) ≤ (n : ℝ)^(α-2) :=
    Real.rpow_le_rpow_of_nonpos hnpos hz.1.le (by linarith)
  let Z : ℤ := f (n+2)-2*f (n+1)+f n
  have hZ : (Z : ℝ) = c*(α*(α-1))*z^(α-2) := by
    dsimp [Z]
    push_cast
    rw [hN (n+2) (by omega), hN (n+1) (by omega), hN n hnN]
    push_cast
    nlinarith [congrArg (fun t : ℝ => c*t) he]
  have hcoef : 0 < c*(α*(α-1)) :=
    mul_pos hc (mul_pos (by linarith) (by linarith))
  have hZpos : (0 : ℝ) < Z := by rw [hZ]; positivity
  have hZlt : (Z : ℝ) < 1 := by
    rw [hZ]
    exact (mul_le_mul_of_nonneg_left hpow hcoef.le).trans_lt hsmall
  have hi : (0 : ℤ) < Z := by exact_mod_cast hZpos
  have hi' : Z < 1 := by exact_mod_cast hZlt
  omega

#print axioms second_difference
#print axioms no_exact_integer_power_tail
end Erdos713ExactIntegerPower
