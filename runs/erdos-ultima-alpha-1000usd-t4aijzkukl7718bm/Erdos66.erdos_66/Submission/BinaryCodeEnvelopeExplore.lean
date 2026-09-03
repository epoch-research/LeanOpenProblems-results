import Submission.BinaryLinearCodePeakExplore

/-! Quantitative restrictions on affine binary codes contained in a set with a
logarithmic representation envelope. These do not settle Erdős 66. -/
namespace Erdos66BinaryCodeEnvelope
open Module Filter AdditiveCombinatorics Erdos66BinaryZeroSpan
  Erdos66BinaryLinearCodePeak Erdos66Counting Erdos66DigitLoopPeak
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma log_target_bound {n t : ℕ} (ht : t<2^(n+1)) :
    Real.log ((t:ℝ)+2)≤(n:ℝ)+2 := by
  have hpow : 2≤2^(n+1) := by
    have hh := Nat.one_le_pow n 2 (by norm_num)
    rw [pow_succ]
    omega
  have ht' : t+2≤2^(n+2) := by
    rw [show n+2=(n+1)+1 by omega,pow_succ]
    omega
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(t:ℝ)+2)
    (show (t:ℝ)+2≤(2:ℝ)^(n+2) by exact_mod_cast ht')
  rw [Real.log_pow] at hl
  have hlog : Real.log (2:ℝ)≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  calc
    Real.log ((t:ℝ)+2)≤((n+2:ℕ):ℝ)*Real.log 2 := hl
    _ ≤ ((n+2:ℕ):ℝ)*1 := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (n:ℝ)+2 := by push_cast; ring

/-- The excess of code dimension over one third of its length has an
exponentially small permitted range under a logarithmic upper envelope. -/
theorem affine_code_dimension_bound {A : Set ℕ} {K C : ℝ} (hC : 0≤C)
    (hu : ∀ t : ℕ, (sumRep A t:ℝ)≤K+C*Real.log ((t:ℝ)+2))
    {n : ℕ} (b : Fin n → F) (V : Submodule F (Fin n → F))
    (hVA : affineCodeSet b V⊆A) :
    (2:ℝ)^(finrank F V-n/3)≤K+C*((n:ℝ)+2) := by
  obtain ⟨t,ht,hr⟩ := exists_affine_code_peak b V
  have hh : (2:ℝ)^(finrank F V-n/3)≤(sumRep A t:ℝ) := by
    exact_mod_cast hr.trans (Erdos66Explore.sumRep_mono hVA t)
  exact hh.trans ((hu t).trans (by
    have := mul_le_mul_of_nonneg_left (log_target_bound ht) hC
    linarith))

lemma half_rate_rank_bound {n d : ℕ} (hd : n≤2*d) : n/6≤d-n/3 := by
  omega

/-- At every sufficiently large length, no affine code of rate at least
one half can lie inside a set satisfying a logarithmic upper envelope. -/
theorem eventually_no_half_rate_affine_code_of_envelope {A : Set ℕ} {K C : ℝ}
    (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ t : ℕ, (sumRep A t:ℝ)≤K+C*Real.log ((t:ℝ)+2)) :
    ∀ᶠ n : ℕ in atTop, ∀ (b : Fin n → F) (V : Submodule F (Fin n → F)),
      n≤2*finrank F V → ¬ affineCodeSet b V⊆A := by
  obtain ⟨k₀,hk₀⟩ := exists_nat_gt (max 4 (K+13*C+1))
  refine eventually_atTop.mpr ⟨6*k₀,fun n hn b V hV hVA ↦ ?_⟩
  let k := n/6
  have hk₀k : k₀≤k := by dsimp [k]; omega
  have hk4 : 4≤k := by
    have hh := (le_max_left _ _).trans_lt hk₀
    have hh' : 4≤k₀ := by exact_mod_cast hh.le
    omega
  have hk1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hkn : n+2≤6*k+7 := by dsimp [k]; omega
  have hkbound : K+13*C+1<(k:ℝ) :=
    ((le_max_right _ _).trans_lt hk₀).trans_le (by exact_mod_cast hk₀k)
  have hd := half_rate_rank_bound hV
  have hrep := affine_code_dimension_bound hC hu b V hVA
  have hsq : (k:ℝ)^2≤K+C*((n:ℝ)+2) := by
    have h₁ : (k:ℝ)^2≤(2:ℝ)^k := by exact_mod_cast square_le_two_pow k hk4
    have h₂ : (2:ℝ)^k≤(2:ℝ)^(finrank F V-n/3) :=
      pow_le_pow_right₀ (by norm_num) hd
    exact (h₁.trans h₂).trans hrep
  have hkn' : (n:ℝ)+2≤6*(k:ℝ)+7 := by exact_mod_cast hkn
  have hsq' : (k:ℝ)^2≤K+C*(6*(k:ℝ)+7) :=
    hsq.trans (by nlinarith [mul_le_mul_of_nonneg_left hkn' hC])
  have hmul := mul_lt_mul_of_pos_right hkbound (show (0:ℝ)<k by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hk1 hK
  have h₂ := mul_le_mul_of_nonneg_left hk1 hC
  nlinarith

/-- A necessary condition for any finite logarithmic limit (including zero). -/
theorem eventually_no_half_rate_affine_code {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ n : ℕ in atTop, ∀ (b : Fin n → F) (V : Submodule F (Fin n → F)),
      n≤2*finrank F V → ¬ affineCodeSet b V⊆A := by
  obtain ⟨K,C,hK,hC,hu⟩ := global_log_upper_bound h
  exact eventually_no_half_rate_affine_code_of_envelope hK hC.le hu

end Erdos66BinaryCodeEnvelope
