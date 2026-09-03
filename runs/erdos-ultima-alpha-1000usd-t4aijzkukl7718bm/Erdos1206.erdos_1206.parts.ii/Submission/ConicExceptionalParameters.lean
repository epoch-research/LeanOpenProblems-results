import Submission.ConicSieveSchedule
import Submission.DyadicBoxReciprocal

/-! Reciprocal summability of the explicit conic parameters that survive
all geometrically scheduled mixed-prime bounds. -/
namespace Erdos1206.ConicExceptionalParameters
open Finset Filter ConicSieveSchedule GeometricConicSource ConicSievePrimeEstimates
open SquarefreeConicFamily SquarefreeConicCharacterScore ConicPrimeCharacterScore
open scoped Topology Classical

lemma log_z (L : ℝ) (j : ℕ) : Real.log (z L j:ℝ)=(m L j:ℝ)*Real.log 2 := by
  simp only [z,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]

lemma level_moment {L T : ℝ} (hLT : T ≤ L*Real.log 2) (j : ℕ) :
    T*Real.log (primeCutoff j) ≤ Real.log (z L j:ℝ) := by
  rw [log_z]
  have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (L*Real.exp ((3/2:ℝ)^j)))
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_right hLT (Real.exp_pos ((3/2:ℝ)^j)).le
  simp only [primeCutoff,Real.log_exp]
  dsimp only [m]
  nlinarith only [hh,hm]

lemma log_z_scale {L : ℝ} (hL : 1 ≤ L*Real.log 2) (j : ℕ) :
    (3/2:ℝ)^j ≤ Real.log (z L j:ℝ) := by
  have hh := level_moment hL j
  simp only [one_mul,primeCutoff,Real.log_exp] at hh
  have he := Real.add_one_le_exp ((3/2:ℝ)^j)
  linarith

lemma z_gt_one {L : ℝ} (hL : 0 < L) (j : ℕ) : 1 < z L j := by
  have hh := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) (m_pos hL j)
  simpa only [pow_zero,z] using hh

lemma level_below_box {L : ℝ} {j t : ℕ} (ht : r L j ≤ t) :
    (z L j:ℝ)^16 ≤ ((2^(t+1):ℕ):ℝ) := by
  have hh : (z L j)^16 ≤ 2^(t+1) := by
    rw [z,←pow_mul]
    apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    dsimp only [r] at ht
    omega
  exact_mod_cast hh

lemma error_bound {N Z A : ℝ} (hZ : 1 ≤ Z) (hN : Z^16 ≤ N) (hlog : A ≤ Real.log Z) :
    2*N*Z^6+Z^8 ≤ 3*N^2*Real.exp (-10*A) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hN0 : 0 < N := (pow_pos hZ0 16).trans_le hN
  have h₁ : 2*N*Z^6 ≤ 2*N^2/Z^10 := by
    apply (le_div_iff₀ (pow_pos hZ0 10)).mpr
    calc
      _ = 2*N*Z^16 := by ring
      _ ≤ 2*N*N := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by ring
  have h₂ : Z^8 ≤ N^2/Z^10 := by
    apply (le_div_iff₀ (pow_pos hZ0 10)).mpr
    calc
      _ = Z^18 := by ring
      _ ≤ Z^32 := pow_le_pow_right₀ hZ (by decide)
      _ = (Z^16)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hN 2
  have he : Real.exp (-10*Real.log Z)=1/Z^10 := by
    have hlog10 : Real.log (Z^10)=10*Real.log Z := by simp
    rw [show -10*Real.log Z=-(10*Real.log Z) by ring,←hlog10,
      Real.exp_neg,Real.exp_log (pow_pos hZ0 10),one_div]
  have hinv : 1/Z^10 ≤ Real.exp (-10*A) := by
    rw [←he]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 2*N^2/Z^10+N^2/Z^10 := add_le_add h₁ h₂
    _ = 3*N^2*(1/Z^10) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

noncomputable def exceptional (k : ℕ → ℕ) : Set (ℕ × ℕ) :=
  {x | 0 < x.2 ∧ ∀ j, mixedMass (P j) χ ψ (F 0 x.1 x.2) (F 1 x.1 x.2)
    (F 2 x.1 x.2) (F 3 x.1 x.2) ≤ k j}

lemma exceptional_subset_small (k : ℕ → ℕ) (j N : ℕ) :
    (DyadicBoxReciprocal.box N).filter (· ∈ exceptional k) ⊆
      smallParameters (primeCutoff j) N (k j) := by
  intro x hx
  obtain ⟨hxN,hxu,hxm⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hxN,hxu,hxm j⟩

lemma dyadic_count {E T L : ℝ} (hL : 0 < L) (hLT : T ≤ L*Real.log 2)
    (hL1 : 1 ≤ L*Real.log 2) (k : ℕ → ℕ) (j : ℕ)
    (hcount : ∀ N z k : ℕ, 1 < z → T*Real.log (primeCutoff j) ≤ Real.log z →
      ((smallParameters (primeCutoff j) N k).card:ℝ) ≤
        (8:ℝ)^k*(2*(N:ℝ)^2*Real.exp (E-(7/4)*Real.log (Real.log (primeCutoff j)))+
          2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8))
    (t : ℕ) (ht : r L j ≤ t) :
    (((DyadicBoxReciprocal.box (2^(t+1))).filter (· ∈ exceptional k)).card:ℝ) ≤
      ((2^(t+1):ℕ):ℝ)^2*cost E k j := by
  have hc := hcount (2^(t+1)) (z L j) (k j) (z_gt_one hL j) (level_moment hLT j)
  rw [log_log_primeCutoff] at hc
  have he := error_bound (show (1:ℝ) ≤ (z L j:ℝ) by exact_mod_cast (z_gt_one hL j).le)
    (level_below_box ht) (log_z_scale hL1 j)
  have hcard : (((DyadicBoxReciprocal.box (2^(t+1))).filter (· ∈ exceptional k)).card:ℝ) ≤
      ((smallParameters (primeCutoff j) (2^(t+1)) (k j)).card:ℝ) := by
    exact_mod_cast card_le_card (exceptional_subset_small k j (2^(t+1)))
  have hm := mul_le_mul_of_nonneg_left (add_le_add_left he
    (2*((2^(t+1):ℕ):ℝ)^2*Real.exp (E-(7/4)*(3/2:ℝ)^j))) (show 0 ≤ (8:ℝ)^(k j) by positivity)
  have hpow : (8:ℝ)^(k j)=Real.exp ((k j:ℝ)*Real.log 8) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 8)]
  rw [hpow] at hc hm
  dsimp only [cost]
  nlinarith only [hcard,hc,hm]

/-- The exceptional parameters have a summable reciprocal quadratic height.
The threshold is any sequence negligible relative to (3/2)^j. -/
theorem exceptional_reciprocal_summable (k : ℕ → ℕ)
    (hk : Tendsto (fun j => (k j:ℝ)/(3/2:ℝ)^j) atTop (𝓝 0)) :
    Summable (DyadicBoxReciprocal.weight (exceptional k)) := by
  obtain ⟨E,T,hT,hbound⟩ := eventually_small_parameters_count
  let L : ℝ := (T+1)/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := div_pos (by linarith) hlog2
  have hLeq : L*Real.log 2=T+1 := by dsimp only [L]; field_simp
  have hLT : T ≤ L*Real.log 2 := by rw [hLeq]; linarith
  have hL1 : 1 ≤ L*Real.log 2 := by rw [hLeq]; linarith
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (primeCutoff_tendsto.eventually hbound)
  have hr : Tendsto (fun j => r L (j+J)) atTop atTop :=
    (r_tendsto hL).comp (tendsto_add_atTop_nat J)
  have hs := (summable_band_cost hL E k hk).comp_injective
    (fun a b (h : a+J=b+J) => Nat.add_right_cancel h)
  apply DyadicBoxReciprocal.summable_of_dyadic_bands (exceptional k)
    (fun j => r L (j+J)) (fun j => cost E k (j+J)) hr
  · simpa only [Function.comp_apply,Nat.add_right_comm _ 1 J] using hs
  · intro j t ht _
    exact dyadic_count hL hLT hL1 k (j+J) (hJ _ (by omega)) t ht

#print axioms level_moment
#print axioms error_bound
#print axioms dyadic_count
#print axioms exceptional_reciprocal_summable
end Erdos1206.ConicExceptionalParameters
