import Submission.QuadraticPhasePeaksExplore

/-! An explicit Liouville quadratic-phase candidate has unbounded normalized
representation peaks. This only tests one construction mechanism. -/
namespace Erdos66LiouvilleQuadraticPhase
open Filter AdditiveCombinatorics Erdos66QuadraticPhaseResonance Erdos66QuadraticPhasePeaks
open scoped Topology Classical
set_option maxHeartbeats 1800000

noncomputable def phaseParameter : ℝ := (liouvilleNumber 2)^2

def denominator (k : ℕ) : ℕ := 2^((k+2).factorial)
def phaseDenominator (k : ℕ) : ℕ := (denominator k)^2

lemma phaseParameter_transcendental : Transcendental ℤ phaseParameter := by
  have ht := (transcendental_liouvilleNumber (by norm_num : 2 ≤ (2:ℕ))).pow
    (by norm_num : 0 < (2:ℕ))
  simpa only [Nat.cast_ofNat,phaseParameter] using ht

lemma phaseDenominator_ge_sixteen (k : ℕ) : 16 ≤ phaseDenominator k := by
  have hfour : 4 ≤ denominator k := by
    change 2^2 ≤ 2^((k+2).factorial)
    exact Nat.pow_le_pow_right (by norm_num)
      ((by omega : 2 ≤ k+2).trans (Nat.self_le_factorial _))
  dsimp [phaseDenominator]
  nlinarith

lemma denominator_ge_two (k : ℕ) : 2 ≤ denominator k := by
  exact le_self_pow₀ (by norm_num : 1 ≤ (2:ℕ)) (Nat.factorial_ne_zero _)

lemma denominator_atTop : Tendsto denominator atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℕ)))
  intro k
  exact Nat.pow_le_pow_right (by norm_num) ((by omega : k ≤ k+2).trans (Nat.self_le_factorial _))

lemma phaseDenominator_atTop : Tendsto phaseDenominator atTop atTop :=
  (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp denominator_atTop

lemma partialSum_coprime (k : ℕ) :
    ∃ b : ℕ, LiouvilleNumber.partialSum 2 (k+2) = (b:ℝ)/(denominator k:ℝ) ∧
      b.Coprime (denominator k) := by
  obtain ⟨b,hb⟩ := LiouvilleNumber.partialSum_eq_rat (by norm_num : 0 < (2:ℕ)) (k+1)
  norm_num only [Nat.cast_ofNat] at hb
  let d := (k+2).factorial-(k+1).factorial
  have hd : 0 < d := by
    dsimp [d]
    apply Nat.sub_pos_of_lt
    rw [Nat.factorial_succ (k+1)]
    nlinarith [Nat.factorial_pos (k+1)]
  let c := b*2^d+1
  refine ⟨c,?_,?_⟩
  · rw [LiouvilleNumber.partialSum_succ 2 (k+1),hb]
    have hdadd : d+(k+1).factorial=(k+2).factorial := by
      dsimp [d]
      apply Nat.sub_add_cancel
      rw [Nat.factorial_succ (k+1)]
      nlinarith [Nat.factorial_pos (k+1)]
    have hpow : (2:ℝ)^((k+2).factorial)=(2:ℝ)^d*(2:ℝ)^((k+1).factorial) := by
      rw [← pow_add,hdadd]
    dsimp [c,denominator]
    push_cast
    rw [hpow]
    field_simp
  · have heven : 2 ∣ b*2^d := dvd_mul_of_dvd_right
      (dvd_pow_self (2:ℕ) (Nat.ne_of_gt hd)) b
    have hodd : Odd c := by
      obtain ⟨z,hz⟩ := heven
      refine ⟨z,?_⟩
      dsimp [c]
      omega
    exact hodd.coprime_two_right.pow_right _

lemma liouville_two_bounds : 0 ≤ liouvilleNumber 2 ∧ liouvilleNumber 2 < 2 := by
  have hrem0 := LiouvilleNumber.remainder_pos (by norm_num : (1:ℝ)<2) 0
  have hremlt := LiouvilleNumber.remainder_lt 0 (by norm_num : (2:ℝ)≤2)
  have hsplit := LiouvilleNumber.partialSum_add_remainder (by norm_num : (1:ℝ)<2) 0
  norm_num [LiouvilleNumber.partialSum] at hsplit
  norm_num at hremlt
  constructor <;> linarith

lemma partialSum_bounds (k : ℕ) :
    0 ≤ LiouvilleNumber.partialSum 2 k ∧
      LiouvilleNumber.partialSum 2 k ≤ liouvilleNumber 2 := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
  · have hsplit := LiouvilleNumber.partialSum_add_remainder (by norm_num : (1:ℝ)<2) k
    have hrem := LiouvilleNumber.remainder_pos (by norm_num : (1:ℝ)<2) k
    linarith

lemma square_partial_error (k : ℕ) :
    |phaseParameter-(LiouvilleNumber.partialSum 2 (k+2))^2| <
      4/(denominator k:ℝ)^(k+2) := by
  have hb := liouville_two_bounds
  have hs := partialSum_bounds (k+2)
  have hr := LiouvilleNumber.remainder_pos (by norm_num : (1:ℝ)<2) (k+2)
  have hsplit := LiouvilleNumber.partialSum_add_remainder (by norm_num : (1:ℝ)<2) (k+2)
  have hsq : (LiouvilleNumber.partialSum 2 (k+2))^2 ≤ (liouvilleNumber 2)^2 :=
    pow_le_pow_left₀ hs.1 hs.2 2
  have hprod := mul_le_mul_of_nonneg_right
    (show liouvilleNumber 2+LiouvilleNumber.partialSum 2 (k+2) ≤ 4 by linarith) hr.le
  have hbound : |phaseParameter-(LiouvilleNumber.partialSum 2 (k+2))^2| ≤
      4*LiouvilleNumber.remainder 2 (k+2) := by
    rw [phaseParameter,abs_of_nonneg (sub_nonneg.mpr hsq)]
    nlinarith [hsplit]
  have hremlt := LiouvilleNumber.remainder_lt (k+2) (by norm_num : (2:ℝ)≤2)
  have hrem : LiouvilleNumber.remainder 2 (k+2) < 1/(denominator k:ℝ)^(k+2) := by
    simpa only [denominator,Nat.cast_pow,Nat.cast_ofNat] using hremlt
  apply hbound.trans_lt
  simpa only [mul_one_div] using (mul_lt_mul_of_pos_left hrem (by norm_num : (0:ℝ)<4))

lemma approximation_budget (k : ℕ) (hk : 6 ≤ k) :
    4/(denominator k:ℝ)^(k+2) ≤ 1/(phaseDenominator k:ℝ)^3 := by
  have hd : (2:ℝ) ≤ denominator k := by exact_mod_cast denominator_ge_two k
  have hd0 : (0:ℝ) < denominator k := by linarith
  have hpow : (denominator k:ℝ)^8 ≤ (denominator k:ℝ)^(k+2) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hsq : 4 ≤ (denominator k:ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsq (pow_nonneg hd0.le 6)
  have he : (denominator k:ℝ)^2*(denominator k:ℝ)^6 = (denominator k:ℝ)^8 := by ring
  rw [he] at hprod
  have hb : 4*(denominator k:ℝ)^6 ≤ (denominator k:ℝ)^(k+2) := hprod.trans hpow
  dsimp [phaseDenominator]
  push_cast
  rw [← pow_mul]
  norm_num only [Nat.reduceMul]
  exact (div_le_div_iff₀ (pow_pos hd0 _) (pow_pos hd0 _)).mpr (by simpa only [one_mul] using hb)

lemma explicit_approximations (k : ℕ) (hk : 6 ≤ k) :
    ∃ a : ℕ, ∃ u : (ZMod (phaseDenominator k))ˣ,
      (a:ZMod (phaseDenominator k))*(u:ZMod (phaseDenominator k))^2=1 ∧
      |phaseParameter-(a:ℝ)/(phaseDenominator k:ℝ)| ≤ 1/(phaseDenominator k:ℝ)^3 := by
  obtain ⟨b,hb,hcop⟩ := partialSum_coprime k
  let v : (ZMod (phaseDenominator k))ˣ := ZMod.unitOfCoprime b (hcop.pow_right 2)
  have hv : (v:ZMod (phaseDenominator k))=(b:ZMod (phaseDenominator k)) :=
    ZMod.coe_unitOfCoprime b _
  refine ⟨b^2,v⁻¹,?_,?_⟩
  · push_cast
    rw [← hv,← mul_pow,Units.mul_inv,one_pow]
  · have hh := (square_partial_error k).le.trans (approximation_budget k hk)
    rw [hb,div_pow] at hh
    simpa only [phaseDenominator,Nat.cast_pow] using hh

lemma frequently_explicit_approximations :
    ∃ᶠ p : ℕ in atTop, ∃ a : ℕ, ∃ u : (ZMod p)ˣ,
      (a:ZMod p)*(u:ZMod p)^2=1 ∧ |phaseParameter-(a:ℝ)/p| ≤ 1/(p:ℝ)^3 := by
  apply phaseDenominator_atTop.frequently
  exact ((eventually_ge_atTop 6).mono fun k hk ↦ explicit_approximations k hk).frequently

theorem explicit_denominator_peaks :
    Tendsto (fun k ↦
      (sumRep (phaseSet phaseParameter logWindow) (phaseDenominator k):ℝ) /
        Real.log (phaseDenominator k)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hbase := (resonanceSize_log_atTop.comp phaseDenominator_atTop).eventually_ge_atTop B
  filter_upwards [hbase,eventually_ge_atTop 6] with k hB hk
  obtain ⟨a,u,hu,ha⟩ := explicit_approximations k hk
  have hp := phaseDenominator_ge_sixteen k
  have hpeak := cubic_approximation_peak phaseParameter logWindow (phaseDenominator k) a
    hp u hu ha logWindow_lower
  have hlog : 0 ≤ Real.log (phaseDenominator k:ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ phaseDenominator k by omega))
  exact hB.trans (div_le_div_of_nonneg_right (by exact_mod_cast hpeak) hlog)

/-- One explicit parameter with polynomially large resonant peaks. -/
theorem explicit_quadratic_phase_unbounded_peaks :
    ∀ B : ℝ, ∃ᶠ p : ℕ in atTop,
      B < (sumRep (phaseSet phaseParameter logWindow) p:ℝ)/Real.log p :=
  unbounded_peaks_of_approximations phaseParameter logWindow logWindow_lower
    frequently_explicit_approximations

theorem explicit_quadratic_phase_no_finite_limit (c : ℝ) :
    ¬ Tendsto (fun p ↦ (sumRep (phaseSet phaseParameter logWindow) p:ℝ)/Real.log p)
      atTop (𝓝 c) :=
  no_finite_limit_of_approximations phaseParameter logWindow logWindow_lower
    frequently_explicit_approximations c

end Erdos66LiouvilleQuadraticPhase
