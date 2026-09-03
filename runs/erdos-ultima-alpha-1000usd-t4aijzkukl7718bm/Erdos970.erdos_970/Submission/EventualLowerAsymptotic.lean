import Submission.LowerAsymptotic

/-! The constructive lower bound holds eventually for every fixed multiple
of k log k. This is not a disproof of a quadratic upper bound. -/
namespace Erdos970.ConstructiveCover
open Finset Real Filter
set_option maxHeartbeats 2000000

/-- A covering at length A*t^2, with a prime budget whose leading bound is
independent of A. The threshold still depends on A and its fixed prime tail. -/
theorem eventually_square_cover_budget (A : ℕ) (hA1 : 1 < A) :
    ∀ᶠ t : ℕ in atTop, ∃ j : ℕ, ¬IsJacobsthalBound j (A*t^2) ∧
      (j : ℝ)*log (t : ℝ) ≤ (log 4+2)*(t : ℝ)^2 := by
  let B : ℝ := Real.log 4 + 1
  let E : ℝ := B + 1
  have hB : 0 < B := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [B]
    linarith
  have hE : 0 < E := by dsimp [E]; linarith
  have hAR : 1 < (A : ℝ) := by exact_mod_cast hA1
  have hApos : 0 < A := by omega
  have hARpos : 0 < (A : ℝ) := by positivity
  obtain ⟨S, hS, hden⟩ := exists_prime_tail_density A A
  let H := 2 ^ (S.sup id + 1).primesBelow.card
  let D := A * S.card + H * A + 1
  have ht : Filter.Tendsto (fun t : ℕ => (t : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have ht2 : Filter.Tendsto (fun t : ℕ => ((t ^ 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_pow, pow_two, Nat.cast_mul] using ht.atTop_mul_atTop₀ ht
  have htA : Filter.Tendsto (fun t : ℕ => ((A * t ^ 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa only [Nat.cast_mul] using ht2.const_mul_atTop hARpos
  have hcheb1 : ∀ᶠ t : ℕ in Filter.atTop,
      ((t ^ 2).primeCounting : ℝ) ≤ B * (t ^ 2 : ℕ) / Real.log (t ^ 2 : ℕ) := by
    simpa only [Nat.floor_natCast] using ht2.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hchebA : ∀ᶠ t : ℕ in Filter.atTop,
      ((A * t ^ 2).primeCounting : ℝ) ≤ B * (A * t ^ 2 : ℕ) / Real.log (A * t ^ 2 : ℕ) := by
    simpa only [Nat.floor_natCast] using htA.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hsmall : ∀ᶠ t : ℕ in Filter.atTop, (D : ℝ) * Real.log t ≤ t := by
    have hh := ((Real.isLittleO_log_id_atTop.const_mul_left (D : ℝ)).comp_tendsto ht).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh] with t hh
    have hh' : |(D : ℝ) * Real.log t| ≤ t := by simpa using hh
    exact (le_abs_self _).trans hh'
  have hlarge : ∀ᶠ t : ℕ in Filter.atTop, E ≤ Real.log (t : ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually (Filter.eventually_ge_atTop E)
  filter_upwards [hcheb1,hchebA,hsmall,hlarge,Filter.eventually_ge_atTop A]
    with t ht1 htA' htsmall htlarge htge
  have htpos : 0 < t := by omega
  have htR : 1 < (t : ℝ) := by exact_mod_cast (show 1 < t by omega)
  have htRpos : 0 < (t : ℝ) := by positivity
  have hLpos : 0 < Real.log (t : ℝ) := Real.log_pos htR
  have hAX : A ≤ t ^ 2 := by nlinarith
  obtain ⟨k, hbad, hbudget⟩ := exists_cover_budget A (t ^ 2) S hApos hAX hS hden
  have hsqrt : (A * t ^ 2).sqrt ≤ A * t := by
    have hh : A * t ^ 2 ≤ (A * t) ^ 2 := by nlinarith [sq_nonneg (t : ℤ)]
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hh
  have hbudget' : A * k ≤ A * ((t ^ 2).primeCounting + S.card) + (A * t ^ 2).primeCounting +
      H * (A * t) + 1 := by
    exact hbudget.trans (by dsimp only [H]; gcongr)
  have hbudgetR : (A : ℝ) * k ≤ A * (((t ^ 2).primeCounting : ℝ) + S.card) +
      ((A * t ^ 2).primeCounting : ℝ) + H * (A * (t : ℝ)) + 1 := by
    exact_mod_cast hbudget'
  have hlog2 : Real.log ((t ^ 2 : ℕ) : ℝ) = 2 * Real.log (t : ℝ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogA : 2 * Real.log (t : ℝ) ≤ Real.log ((A * t ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hh := Real.log_nonneg hAR.le
    norm_num
    linarith
  have hlogApos : 0 < Real.log ((A * t ^ 2 : ℕ) : ℝ) := by linarith
  have hp1 : 2 * ((t ^ 2).primeCounting : ℝ) * Real.log (t : ℝ) ≤ B * (t : ℝ) ^ 2 := by
    rw [hlog2] at ht1
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * Real.log (t : ℝ))).mp ht1
    push_cast at hh
    nlinarith
  have hpA : 2 * ((A * t ^ 2).primeCounting : ℝ) * Real.log (t : ℝ) ≤
      B * A * (t : ℝ) ^ 2 := by
    have hh := (le_div_iff₀ hlogApos).mp htA'
    have hh' := mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (A * t ^ 2).primeCounting)
    push_cast at hh hh'
    nlinarith only [hh, hh']
  have hD : ((D : ℕ) : ℝ) = A * (S.card : ℝ) + (H : ℝ) * A + 1 := by
    dsimp [D]
    push_cast
    rfl
  have herr : ((A : ℝ) * S.card + H * (A * (t : ℝ)) + 1) * Real.log (t : ℝ) ≤
      (t : ℝ) ^ 2 := by
    have hcoeff : (A : ℝ) * S.card + H * (A * (t : ℝ)) + 1 ≤ D * (t : ℝ) := by
      rw [hD]
      have hh := mul_nonneg (by positivity : 0 ≤ (A : ℝ) * S.card + 1) (sub_nonneg.mpr htR.le)
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoeff hLpos.le
    have hh' := mul_le_mul_of_nonneg_right htsmall htRpos.le
    nlinarith
  have hkl : (k : ℝ) * Real.log (t : ℝ) ≤ E * (t : ℝ) ^ 2 := by
    have hb := mul_le_mul_of_nonneg_right hbudgetR hLpos.le
    have hp1' := mul_le_mul_of_nonneg_left hp1 hARpos.le
    have hma : (A : ℝ) * ((k : ℝ) * Real.log (t : ℝ)) ≤ A * (E * (t : ℝ) ^ 2) := by
      dsimp only [E]
      nlinarith [mul_nonneg (sub_nonneg.mpr hAR.le) (sq_nonneg (t : ℝ))]
    exact (mul_le_mul_iff_right₀ hARpos).mp hma
  refine ⟨k,hbad,?_⟩
  dsimp only [E,B] at hkl
  convert hkl using 1 <;> ring

/-- Interpolation of the square-parameter construction. The threshold depends
on M; no superquadratic lower bound is asserted. -/
theorem eventually_any_mul_log_lt_jacobsthalFunction (M : ℝ) (hM : 0 < M) :
    ∀ᶠ k : ℕ in atTop, M*(k : ℝ)*log (k : ℝ) < jacobsthalFunction k := by
  let E : ℝ := log 4+2
  have hE : 0 < E := by
    have hh := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [E]
    linarith
  obtain ⟨A,hA⟩ := exists_nat_gt (128*E*M+2)
  have hA1 : 1 < A := by
    have : (1 : ℝ) < A := by nlinarith only [hA,mul_pos hE hM]
    exact_mod_cast this
  have hA0 : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_square_cover_budget A hA1)
  have hlog := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (128*E))
  filter_upwards [hlog,eventually_ge_atTop (max 2 (T^2))] with k hlog hk
  change 128*E ≤ log (k : ℝ) at hlog
  have hk2 : 2 ≤ k := (le_max_left _ _).trans hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hL : 0 < log (k : ℝ) := log_pos (by exact_mod_cast hk2)
  let X : ℝ := (k : ℝ)*log (k : ℝ)/(16*E)
  let n : ℕ := ⌊X⌋₊
  let t : ℕ := n.sqrt
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hXk : 8*(k : ℝ) ≤ X := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*E)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog hk0.le
    nlinarith only [hh]
  have hfloor : (n : ℝ) ≤ X := Nat.floor_le hX0
  have hfloor' : X < (n : ℝ)+1 := Nat.lt_floor_add_one X
  have hn : 0 < n := by
    by_contra hn
    have hz : n=0 := by omega
    rw [hz,Nat.cast_zero] at hfloor'
    linarith only [hfloor',hXk,hk1]
  have ht : 0 < t := Nat.sqrt_pos.mpr hn
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htlo : (t : ℝ)^2 ≤ n := by
    have hh := Nat.sqrt_le n
    change t*t ≤ n at hh
    have hh' : t^2 ≤ n := by simpa only [pow_two] using hh
    exact_mod_cast hh'
  have hthi : (n : ℝ) < ((t : ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have hlow : X < 8*(t : ℝ)^2 := by
    nlinarith only [hfloor',hthi,ht1,sq_nonneg ((t : ℝ)-1)]
  have hktR : (k : ℝ) ≤ (t : ℝ)^2 := by linarith only [hXk,hlow]
  have hkt : k ≤ t^2 := by exact_mod_cast hktR
  have hTt : T ≤ t := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp
    (((le_max_right _ _).trans hk).trans hkt)
  obtain ⟨j,hbad,hbudget⟩ := hT t hTt
  have hupper : E*(t : ℝ)^2 ≤ (k : ℝ)*log (k : ℝ)/16 := by
    have hh := mul_le_mul_of_nonneg_left (htlo.trans hfloor) hE.le
    apply hh.trans_eq
    dsimp only [X]
    field_simp
  have hlogt : log (k : ℝ) ≤ 2*log (t : ℝ) := by
    have hh := log_le_log hk0 hktR
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hjk : j ≤ k := by
    have hh := mul_le_mul_of_nonneg_left hlogt (Nat.cast_nonneg j)
    have hb : (j : ℝ)*log (t : ℝ) ≤ E*(t : ℝ)^2 := hbudget
    have hjR : (j : ℝ)*log (k : ℝ) ≤ (k : ℝ)*log (k : ℝ) := by
      nlinarith only [hh,hb,hupper,mul_pos hk0 hL]
    exact_mod_cast (mul_le_mul_iff_left₀ hL).mp hjR
  have hj : A*t^2 < jacobsthalFunction j := by
    apply lt_of_not_ge
    intro hh
    exact hbad ((jacobsthalFunction_le_iff _ _).mp hh)
  have hjR : (A : ℝ)*(t : ℝ)^2 < jacobsthalFunction k := by
    exact_mod_cast hj.trans_le (jacobsthalFunction_strictMono.monotone hjk)
  have hlow' : (k : ℝ)*log (k : ℝ) < 128*E*(t : ℝ)^2 := by
    dsimp only [X] at hlow
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < 16*E)).mp hlow
    nlinarith only [hh]
  have h1 := mul_lt_mul_of_pos_left hlow' hM
  have h2 := mul_lt_mul_of_pos_right hA (by positivity : (0 : ℝ) < (t : ℝ)^2)
  nlinarith only [h1,h2,hjR]

/-- The lower ratio diverges, not merely along an unspecified subsequence. -/
theorem jacobsthal_mul_log_ratio_tendsto_atTop :
    Tendsto (fun k : ℕ => (jacobsthalFunction k : ℝ)/((k : ℝ)*log (k : ℝ)))
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let M : ℝ := max (b+1) 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  filter_upwards [eventually_any_mul_log_lt_jacobsthalFunction M hM,eventually_ge_atTop 2]
    with k hk hk2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl : 0 < log (k : ℝ) := log_pos (by exact_mod_cast hk2)
  have hb : b ≤ M := le_trans (by linarith : b ≤ b+1) (le_max_left _ _)
  apply hb.trans
  apply (le_div_iff₀ (mul_pos hk0 hl)).mpr
  nlinarith only [hk]

#print axioms jacobsthal_mul_log_ratio_tendsto_atTop
#print axioms eventually_square_cover_budget
#print axioms eventually_any_mul_log_lt_jacobsthalFunction
end Erdos970.ConstructiveCover
