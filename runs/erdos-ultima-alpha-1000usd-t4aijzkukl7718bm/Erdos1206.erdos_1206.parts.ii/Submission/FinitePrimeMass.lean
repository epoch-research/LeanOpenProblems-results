import Submission.PrimeLogMomentNearOne

/-! Truncating smoothed prime mass to an actual finite prime prefix, with a
logarithmic-moment bound at the same cutoff. -/
namespace Erdos1206.FinitePrimeMass
open Finset Filter RealQuadraticEulerMass PrimeLogMomentNearOne QuadraticPrimeMassNearOne
open scoped Topology Classical

noncomputable def primePrefix (y : ℝ) : Finset Nat.Primes :=
  Finset.subtype Nat.Prime (Nat.primesBelow (⌊y⌋₊+1))

lemma mem_primePrefix {y : ℝ} (hy : 0 ≤ y) (p : Nat.Primes) :
    p ∈ primePrefix y ↔ (p:ℝ) ≤ y := by
  rw [primePrefix,Finset.mem_subtype]
  simp only [Nat.mem_primesBelow,p.prop,and_true,Nat.lt_add_one_iff,Nat.le_floor_iff hy]

lemma primePower_le_inverse {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    primePower s p ≤ 1/(p:ℝ) := by
  calc
    _ ≤ (p:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ p by exact_mod_cast p.prop.one_le) (by linarith)
    _ = _ := by rw [Real.rpow_neg_one,one_div]

lemma truncate_weightedMass {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    {s y : ℝ} (hs : 1 < s) (hy : 1 < y) :
    weightedMass χ s ≤
      (∑ p ∈ primePrefix y, (1-(χ (p:ZMod N):ℝ))/(p:ℝ))+
        (2/Real.log y)*primeMoment s := by
  let f : Nat.Primes → ℝ := fun p =>
    if p ∈ primePrefix y then (1-(χ (p:ZMod N):ℝ))/(p:ℝ) else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := primePrefix y)
    (fun p hp => if_neg hp)
  have hsum : (∑' p, f p)=∑ p ∈ primePrefix y, (1-(χ (p:ZMod N):ℝ))/(p:ℝ) := by
    rw [tsum_eq_sum (s := primePrefix y) (fun p hp => if_neg hp)]
    exact sum_congr rfl (fun p hp => if_pos hp)
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hh := Summable.tsum_le_tsum (f := fun p : Nat.Primes =>
      (1-(χ (p:ZMod N):ℝ))*primePower s p)
    (g := fun p => f p+(2/Real.log y)*(Real.log (p:ℝ)*primePower s p))
    (fun p => ?_) (summable_weightedMass χ hχ hs)
    (hf.add ((summable_primeMoment hs).mul_left _))
  · rw [hf.tsum_add ((summable_primeMoment hs).mul_left _),tsum_mul_left,hsum] at hh
    exact hh
  · have hcoef := integer_abs_le_one (hχ p)
    have hcoef0 : 0 ≤ 1-(χ (p:ZMod N):ℝ) := by
      have := le_abs_self (χ (p:ZMod N):ℝ); linarith
    have hcoef2 : 1-(χ (p:ZMod N):ℝ) ≤ 2 := by
      have := neg_abs_le (χ (p:ZMod N):ℝ); linarith
    have hp0 : (0:ℝ) < p := by exact_mod_cast p.prop.pos
    have hplog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast p.prop.one_le)
    by_cases hmem : p ∈ primePrefix y
    · dsimp only [f]
      rw [if_pos hmem]
      have hb := mul_le_mul_of_nonneg_left (primePower_le_inverse hs p) hcoef0
      have hn : 0 ≤ (2/Real.log y)*(Real.log (p:ℝ)*primePower s p) :=
        mul_nonneg (by positivity) (mul_nonneg hplog (primePower_pos s p).le)
      simpa only [mul_one_div] using hb.trans (le_add_of_nonneg_right hn)
    · dsimp only [f]
      rw [if_neg hmem,zero_add]
      have hpy : y < (p:ℝ) := lt_of_not_ge (fun hh => hmem ((mem_primePrefix (zero_lt_one.trans hy).le p).mpr hh))
      have hlp : Real.log y ≤ Real.log (p:ℝ) := Real.log_le_log (zero_lt_one.trans hy) hpy.le
      have hc : 1-(χ (p:ZMod N):ℝ) ≤ (2/Real.log y)*Real.log (p:ℝ) := by
        have hm := mul_le_mul_of_nonneg_left hlp (show 0 ≤ 2/Real.log y by positivity)
        have he : (2/Real.log y)*Real.log y=2 := by field_simp
        rw [he] at hm
        exact hcoef2.trans hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (primePower_pos s p).le

lemma inverse_le_exp_primePower {s y : ℝ} (hs : 1 < s) (hy : 1 < y)
    (hscale : (s-1)*Real.log y ≤ 1) (p : Nat.Primes) (hp : p ∈ primePrefix y) :
    1/(p:ℝ) ≤ Real.exp 1*primePower s p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast p.prop.pos
  have hpY := (mem_primePrefix (zero_lt_one.trans hy).le p).mp hp
  have hlog : Real.log (p:ℝ) ≤ Real.log y := Real.log_le_log hp0 hpY
  have hm := mul_le_mul_of_nonneg_left hlog (sub_pos.mpr hs).le
  calc
    _ = Real.exp (-Real.log (p:ℝ)) := by rw [Real.exp_neg,Real.exp_log hp0,one_div]
    _ ≤ Real.exp (1+Real.log (p:ℝ)*(-s)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add,primePower,Real.rpow_def_of_pos hp0]

lemma prefix_log_moment {s y : ℝ} (hs : 1 < s) (hy : 1 < y)
    (hscale : (s-1)*Real.log y ≤ 1) :
    (∑ p ∈ primePrefix y, Real.log (p:ℝ)/(p:ℝ)) ≤ Real.exp 1*primeMoment s := by
  calc
    _ ≤ ∑ p ∈ primePrefix y, Real.exp 1*(Real.log (p:ℝ)*primePower s p) := by
      apply sum_le_sum
      intro p hp
      have hh := mul_le_mul_of_nonneg_left (inverse_le_exp_primePower hs hy hscale p hp)
        (Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast p.prop.one_le))
      simpa only [mul_one_div,mul_left_comm] using hh
    _ = Real.exp 1*∑ p ∈ primePrefix y, Real.log (p:ℝ)*primePower s p := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum _ (fun p _ => mul_nonneg
        (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (primePower_pos s p).le)
        (summable_primeMoment hs)) (Real.exp_pos _).le

noncomputable def cutoff (s : ℝ) : ℝ := Real.exp (1/(s-1))

lemma cutoff_gt_one {s : ℝ} (hs : 1 < s) : 1 < cutoff s := by
  exact Real.one_lt_exp_iff.mpr (one_div_pos.mpr (sub_pos.mpr hs))

lemma log_cutoff (s : ℝ) : Real.log (cutoff s)=1/(s-1) := Real.log_exp _

/-- Near s=1 the finite prefix has the expected logarithmic mass lower bound,
and its logarithmic first moment is controlled at the same cutoff. -/
theorem eventually_prefix_bounds {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℤ N) (hnc : complexChar χ ≠ 1)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1) :
    ∃ C D : ℝ, 0 < D ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      Real.log (1/(s-1))-C ≤ ∑ p ∈ primePrefix (cutoff s), (1-(χ (p:ZMod N):ℝ))/(p:ℝ) ∧
      (∑ p ∈ primePrefix (cutoff s), Real.log (p:ℝ)/(p:ℝ)) ≤ D/(s-1) := by
  obtain ⟨C,hC⟩ := eventually_weightedMass_lower χ hnc hχ
  obtain ⟨B,hB,hbound⟩ := eventually_primeMoment_bound
  refine ⟨C+2*B,Real.exp 1*B,by positivity,?_⟩
  filter_upwards [hC,hbound,self_mem_nhdsWithin] with s hc hb hs
  have hsp : 0 < s-1 := sub_pos.mpr hs
  have hcut := cutoff_gt_one hs
  have hscale : (s-1)*Real.log (cutoff s)=1 := by rw [log_cutoff]; field_simp
  have ht := truncate_weightedMass χ hχ hs hcut
  rw [log_cutoff] at ht
  have he : (2/(1/(s-1)))*primeMoment s=2*((s-1)*primeMoment s) := by
    simp only [one_div,div_inv_eq_mul]
    ring
  rw [he] at ht
  have hm := prefix_log_moment hs hcut hscale.le
  constructor
  · linarith
  · apply (le_div_iff₀ hsp).mpr
    have hm' := mul_le_mul_of_nonneg_right hm hsp.le
    have hb' := mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le
    nlinarith only [hm',hb']

#print axioms truncate_weightedMass
#print axioms prefix_log_moment
#print axioms eventually_prefix_bounds
end Erdos1206.FinitePrimeMass
