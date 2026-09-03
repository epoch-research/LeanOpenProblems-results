import Submission.QuarticUnitLastCount
import Submission.APPrimeProductsSharp

/-! Primitive quartic peaks at every divisor-scale constant below log(2)/2.
These bounds remain subpolynomial and do not settle the fixed-power conjecture. -/
namespace Erdos322Research.QuarticUnitLastSharpPeaks
noncomputable section
open Finset Filter QuarticUnitLastCount APPrimeProducts
open scoped Classical Topology
set_option Elab.async false
set_option maxHeartbeats 0

private lemma logarithmic_height_bound (A : ℝ) (r n : ℕ) (hA : 1 ≤ A)
    (hr : 0 < r) (hlog : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hheight : Real.log (n : ℝ) ≤ A*r*Real.log (r : ℝ)) :
    Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)) ≤ A*r := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  apply (div_le_iff₀ hLpos).mpr
  by_cases hsmall : Real.log (n : ℝ) ≤ r
  · have hscale : (r : ℝ) ≤ A*r := by nlinarith
    have hprod : A*r ≤ (A*r)*Real.log (Real.log (n : ℝ)) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ A) hrp.le]
    exact hsmall.trans (hscale.trans hprod)
  · have hrl : Real.log (r : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log hrp (le_of_not_ge hsmall)
    exact hheight.trans (mul_le_mul_of_nonneg_left hrl (by positivity))

/-- The fixed fourth coordinate is one, so all representations counted here
are primitive. The prime-product exponent can be arbitrarily close to one. -/
theorem exp_log_div_loglog_peaks (c : ℝ) (hc : 0 < c) (hclim : c < Real.log 2/2) :
    {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      count n}.Infinite := by
  have hratio : 2 < Real.log 2/c := (lt_div_iff₀ hc).mpr (by nlinarith)
  obtain ⟨A,hA2,hAlim⟩ := exists_between hratio
  have hcA : c*A < Real.log 2 := by
    have hh := (lt_div_iff₀ hc).mp hAlim
    nlinarith
  obtain ⟨α,hα,hαA⟩ := exists_between (show (1 : ℝ) < A/2 by linarith)
  have hδ : 0 < A-2*α := by linarith
  have hε : 0 < Real.log 2-c*A := by linarith
  have hlogr : ∀ᶠ r : ℕ in atTop, 1 ≤ Real.log (r : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hδr : ∀ᶠ r : ℕ in atTop, Real.log 3/(A-2*α) ≤ (r : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hεr : ∀ᶠ r : ℕ in atTop, Real.log 4/(Real.log 2-c*A) < (r : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hlogr.and (hδr.and hεr))
  have ht : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  apply Set.infinite_of_forall_exists_gt
  intro b
  let T := max N (b+1)
  let D := (range T).sup count
  obtain ⟨S,hRS,hS,hp,hB⟩ := APPrimeProductsSharp.exists_prime_set_small_product
    (1 : ZMod 3) isUnit_one α hα (max R (4*D+1))
  have hsplit : ∀ p ∈ S, p.Prime ∧ 3 ∣ p-1 := by
    intro p hpS
    have hh := hp p hpS
    refine ⟨hh.1,?_⟩
    have he : p ≡ 1 [MOD 3] := (ZMod.natCast_eq_natCast_iff _ _ 3).mp hh.2
    have hsub := Nat.ModEq.sub_right hh.1.one_lt.le (by omega : 1 ≤ 1) he
    exact Nat.modEq_zero_iff_dvd.mp (by simpa using hsub)
  let r := S.card
  let M := ∏ p ∈ S,p
  let n := 2*M^2+1
  have hr : 0 < r := hS
  have hrR : R ≤ r := (le_max_left _ _).trans hRS
  have hrD : 4*D+1 ≤ r := (le_max_right _ _).trans hRS
  obtain ⟨hlogr,hδr,hεr⟩ := hR r hrR
  have hδr' : Real.log 3 ≤ (A-2*α)*(r : ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hδr
    nlinarith
  have hεr' : Real.log 4 < (Real.log 2-c*A)*(r : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp hεr
    nlinarith
  have hM : 0 < M := prod_pos fun p hpS ↦ (hsplit p hpS).1.pos
  have hn : 0 < n := by dsimp [n]; omega
  have hcount : 2^r ≤ 4*count n := prime_product_count S hsplit
  have hnT : T ≤ n := by
    by_contra hh
    have hnmem : n ∈ range T := mem_range.mpr (by omega)
    have hbd : count n ≤ D := le_sup hnmem
    have htwr : r < 2^r := Nat.lt_two_pow_self
    omega
  have hlog : 1 ≤ Real.log (Real.log (n : ℝ)) := hN n ((le_max_left _ _).trans hnT)
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogM : Real.log (M : ℝ) ≤ (α*r)*Real.log (r : ℝ) := by
    have hh := Real.log_le_log hMp hB
    change Real.log (M : ℝ) ≤ Real.log ((r : ℝ)^(α*r)) at hh
    rwa [Real.log_rpow hrp] at hh
  have hnM : n ≤ 3*M^2 := by
    have hM2 : 1 ≤ M^2 := one_le_pow₀ (by omega)
    dsimp [n]
    omega
  have hheight : Real.log (n : ℝ) ≤ A*r*Real.log (r : ℝ) := by
    have hh : Real.log (n : ℝ) ≤ Real.log 3+2*Real.log (M : ℝ) := by
      have hh := Real.log_le_log hnp (show (n : ℝ) ≤ 3*(M : ℝ)^2 by exact_mod_cast hnM)
      simpa only [Real.log_mul (by norm_num : (3 : ℝ)≠0) (pow_ne_zero 2 hMp.ne'),
        Real.log_pow,Nat.cast_ofNat] using hh
    have hδprod : (A-2*α)*(r : ℝ) ≤ (A-2*α)*r*Real.log (r : ℝ) := by
      exact le_mul_of_one_le_right (mul_nonneg hδ.le hrp.le) hlogr
    nlinarith
  have hbound := logarithmic_height_bound A r n (by linarith) hr hlog hheight
  have hfour : 4*Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      4*(count n : ℝ) := by
    calc
      _ ≤ 4*Real.exp (c*(A*r)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound hc.le)
      _ = Real.exp (Real.log 4+c*(A*r)) := by
        rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ < Real.exp ((r : ℝ)*Real.log 2) := by
        apply Real.exp_lt_exp.mpr
        nlinarith
      _ = (2 : ℝ)^r := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ 4*(count n : ℝ) := by exact_mod_cast hcount
  refine ⟨n,?_,?_⟩
  · change Real.exp _ < (count n : ℝ)
    linarith
  · have hbT : b+1 ≤ T := le_max_right _ _
    omega

/-- The primitive bound implies the same lower bound for the full quartic count. -/
theorem full_count_exp_log_div_loglog_peaks (c : ℝ) (hc : 0 < c)
    (hclim : c < Real.log 2/2) :
    {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      Erdos322.representationCount 4 n}.Infinite := by
  apply (exp_log_div_loglog_peaks c hc hclim).mono
  intro n hn
  exact lt_of_lt_of_le hn (show (count n : ℝ) ≤ Erdos322.representationCount 4 n from
    by exact_mod_cast count_le_full n)

end
end Erdos322Research.QuarticUnitLastSharpPeaks
