import Submission.BuchstabContinuousMain
import Submission.BuchstabSmoothGrowth

/-! Unrestricted growth bounds at every exponent strictly above two, from
actual fixed-depth positive main terms and fully charged smooth source costs.
This does not assert the quadratic endpoint. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1000000

lemma eventual_prime_growth_above_two (s : ℝ) (hs : 2 < s) : ∃ C > (0 : ℝ), ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    (jacobsthalFunction k : ℝ) ≤ C*(nthPrime k : ℝ)^s/log (nthPrime k : ℝ) := by
  obtain ⟨n,N₀,hN₀⟩ := exists_referenceLower_positive_above_two s hs
  let γ : ℝ := (s-2)/(4*s)
  have hs0 : 0 < s := by linarith
  have hγ : 0 < γ := div_pos (sub_pos.mpr hs) (by positivity)
  let A := smoothRefinementConstant n
  have hA : 0 < A := smoothRefinementConstant_pos n
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp eventually_eulerMass_initial_le_nine_fifths_log
  refine ⟨2*A/γ+1,by positivity,max N₀ N₁,fun k hk => ?_⟩
  let p := nthPrime k
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hkP : k ≤ p := nthPrime_strictMono.id_le k
  have hNp : max N₀ N₁ ≤ p := hk.trans hkP
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hEuler := (eulerMass_strict_prefix_le p hp).trans (hN₁ p ((le_max_right _ _).trans hNp))
  let D : ℝ := exp (s*log (p : ℝ))
  have hD : 0 < D := exp_pos _
  have hpow : D = (p : ℝ)^s := by rw [rpow_def_of_pos hp0]; dsimp only [D]; congr 1; ring
  have hpD : (p : ℝ) ≤ D := by
    calc
      _ = exp (log (p : ℝ)) := (exp_log hp0).symm
      _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hlp,hs])
  have hmain := hN₀ k ((le_max_left _ _).trans hNp)
  have hEpos := eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hmainlog : γ/(2*log (p : ℝ)) ≤ referenceLower n k D := by
    apply le_trans _ hmain
    rw [nthPrime_prefix_density]
    have hE : eulerMass p.primesBelow ≤ 2*log (p : ℝ) := by linarith only [hEuler,hlp]
    have hi := one_div_le_one_div_of_le hEpos hE
    have hm := mul_le_mul_of_nonneg_left hi hγ.le
    convert hm using 1 <;> dsimp only [γ] <;> ring
  let E : ℝ := A*D/log (p : ℝ)^2
  have hcostAll (j : ℕ) (hj : j ≤ k) :
      lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n) j D ≤ E := by
    apply (smooth_cost_uniform_prefix n k j hj D hpD).trans
    have hh := mul_le_mul_of_nonneg_left (smooth_shape_exp_le k s (by linarith)) hA.le
    convert hh using 1
    dsimp only [E,A,D,p]
    ring
  let X : ℝ := (2*A/γ)*D/log (p : ℝ)
  let m : ℕ := ⌊X⌋₊+1
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hXm : X < (m : ℝ) := by simpa only [m,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one X
  have hcost : E < (m : ℝ)*(γ/(2*log (p : ℝ))) := by
    have hm := mul_lt_mul_of_pos_right hXm (div_pos hγ (by positivity : 0 < 2*log (p : ℝ)))
    have heq : X*(γ/(2*log (p : ℝ)))=E := by dsimp only [E,X]; field_simp
    rwa [heq] at hm
  have hpos : E < (m : ℝ)*referenceLower n k D := hcost.trans_le
    (mul_le_mul_of_nonneg_left hmainlog (Nat.cast_nonneg m))
  have hj := (jacobsthalFunction_le_iff k m).mpr
    (isJacobsthalBound_of_depth_sharp_cost n k m D hD.le (primeKeep_exp k _ hs.le) E hcostAll hpos)
  have hjR : (jacobsthalFunction k : ℝ) ≤ m := by exact_mod_cast hj
  have hmupper : (m : ℝ) ≤ X+1 := by
    dsimp only [m]
    push_cast
    exact add_le_add (Nat.floor_le hX) le_rfl
  have hlogp : log (p : ℝ) ≤ D := (log_le_sub_one_of_pos hp0).trans (by linarith only [hpD])
  have hunit : 1 ≤ D/log (p : ℝ) := (le_div_iff₀ hlp).mpr (by simpa using hlogp)
  have ht : (jacobsthalFunction k : ℝ) ≤ (2*A/γ+1)*D/log (p : ℝ) := by
    dsimp only [X] at hmupper
    have heq : (2*A/γ+1)*D/log (p : ℝ) = (2*A/γ)*D/log (p : ℝ)+D/log (p : ℝ) := by ring
    rw [heq]
    linarith only [hjR,hmupper,hunit]
  rwa [hpow] at ht


/-- A uniform bound for every fixed exponent greater than two, retaining the
logarithmic saving from the smooth source cost. -/
theorem exists_growth_above_two (s : ℝ) (hs : 2 < s) : ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
    (jacobsthalFunction k : ℝ) ≤ C*(k : ℝ)^s*log ((k : ℝ)+2)^(s-1) := by
  obtain ⟨A,hA,N,hN⟩ := (eventual_prime_growth_above_two s hs)
  let C : ℝ := 2*A*(160 : ℝ)^s
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨C',hC',hbound⟩ := absorb_finitely_many_bounds
    (fun k => (k : ℝ)^s*log ((k : ℝ)+2)^(s-1)) (by
      intro k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hl : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
      positivity) C hC N (by
    intro k hk hkN
    let t := log ((k : ℝ)+2)
    let p := nthPrime k
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 < t := log_pos (by linarith)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (nthPrime_prime k).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (nthPrime_prime k).two_le
    have hlp : 0 < log (p : ℝ) := log_pos (by linarith)
    have hkp : (k : ℝ) ≤ p := by exact_mod_cast nthPrime_strictMono.id_le k
    have htlog : t ≤ 2*log (p : ℝ) := by
      have hh := log_le_log (by positivity : 0 < (k : ℝ)+2) (show (k : ℝ)+2 ≤ 2*p by linarith)
      rw [log_mul (by norm_num) hp0.ne'] at hh
      have hl2 := log_le_log (by norm_num : (0 : ℝ) < 2) hp2
      linarith only [hh,hl2]
    have hinv : 1/log (p : ℝ) ≤ 2/t := by
      apply (div_le_div_iff₀ hlp ht).mpr
      linarith only [htlog]
    have hpbound : (p : ℝ) ≤ 160*(k : ℝ)*t := by
      have hh := PrimeCountingLower.nth_prime_mul_log k
      change (p : ℝ) ≤ 80*((k : ℝ)+1)*t at hh
      nlinarith only [hh,hk1,ht]
    have hpow := rpow_le_rpow hp0.le hpbound (by linarith : (0 : ℝ) ≤ s)
    have hu := mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hinv
      (by positivity : 0 ≤ 1/log (p : ℝ)) (by positivity)
    have hj := hN k hkN
    have hh : (jacobsthalFunction k : ℝ) ≤ A*(160*(k : ℝ)*t)^s*(2/t) := by
      apply hj.trans
      simpa only [mul_one_div] using hu
    rw [mul_rpow (by positivity : (0 : ℝ) ≤ 160*k) ht.le,
      mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hk0.le] at hh
    have he : t^s/t = t^(s-1) := by
      simpa only [rpow_one] using (rpow_sub ht s 1).symm
    change (jacobsthalFunction k : ℝ) ≤ C*((k : ℝ)^s*t^(s-1))
    rw [← he]
    dsimp only [C]
    convert hh using 1
    ring)
  exact ⟨C',hC',fun k hk => by simpa only [mul_assoc] using hbound k hk⟩

lemma eventually_log_pow_le_power (r δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, log ((k : ℝ)+2)^r ≤ (3 : ℝ)^δ*(k : ℝ)^δ := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hh := ht.eventually ((isLittleO_log_rpow_rpow_atTop r hδ).def (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh,eventually_ge_atTop 1] with k hk hk1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hbase : 0 ≤ (k : ℝ)+2 := by positivity
  have hlog : 0 ≤ log ((k : ℝ)+2) := log_nonneg (by linarith)
  have hb : log ((k : ℝ)+2)^r ≤ ((k : ℝ)+2)^δ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg hlog r),
      abs_of_nonneg (rpow_nonneg hbase δ),one_mul] using hk
  have hp := rpow_le_rpow hbase (show (k : ℝ)+2 ≤ 3*k by linarith) hδ.le
  rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg k)] at hp
  exact hb.trans hp

/-- An unconditional uniform bound at every exponent 2+epsilon. The implied
constant depends on epsilon; this theorem does NOT give the quadratic endpoint. -/
theorem exists_near_quadratic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C*(k : ℝ)^(2+ε) := by
  let s : ℝ := 2+ε/2
  let δ : ℝ := ε/2
  have hs : 2 < s := by dsimp [s]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A,hA,hbound⟩ := exists_growth_above_two s hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_log_pow_le_power (s-1) δ hδ)
  let C : ℝ := A*(3 : ℝ)^δ
  have hC : 0 < C := by dsimp [C]; positivity
  apply absorb_finitely_many_bounds (fun k => (k : ℝ)^(2+ε))
    (fun k hk => rpow_pos_of_pos (by exact_mod_cast hk) _) C hC N
  intro k hk hkN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left (hN k hkN)
    (show 0 ≤ A*(k : ℝ)^s by positivity)
  have hj := (hbound k hk).trans hh
  have he : A*(k : ℝ)^s*((3 : ℝ)^δ*(k : ℝ)^δ) = C*(k : ℝ)^(2+ε) := by
    dsimp only [C]
    rw [show 2+ε=s+δ by dsimp [s,δ]; ring,rpow_add hk0 s δ]
    ring
  rwa [he] at hj

#print axioms eventual_prime_growth_above_two
#print axioms exists_growth_above_two
#print axioms exists_near_quadratic_bound
end Erdos970.RecursiveSieve.Buchstab
