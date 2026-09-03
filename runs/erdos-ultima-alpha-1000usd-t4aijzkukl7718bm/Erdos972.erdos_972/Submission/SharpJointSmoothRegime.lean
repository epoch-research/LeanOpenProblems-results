import Submission.JointSmoothL1
import Submission.FullSmoothL1Obstruction
import Submission.ChebyshevLower

/-! The exact joint-parameter regime for normalized one-variable L1
approximation. This does not prove a signed prime-pair estimate. -/
namespace Erdos972SharpJointSmoothRegime
open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972JointSmoothL1 Erdos972FullSmoothL1Obstruction
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972ChebyshevPNT Erdos972ChebyshevLower
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma exp_deficit_lower {t x a : ℝ} (ht : 0 < t) (hx : 0 ≤ x) (ha : a ≤ t*x) :
    (1-Real.exp (-a/2))/2*x ≤ |(1-Real.exp (-t*x))/t-x| := by
  let E := Real.exp (-(t*x)/2)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE : E ≤ Real.exp (-a/2) := Real.exp_le_exp.mpr (by linarith)
  have hlin : 1-E ≤ t*x/2 := by
    have hh := Real.add_one_le_exp (-(t*x)/2)
    dsimp [E]
    linarith
  have heq : Real.exp (-t*x) = E^2 := by
    dsimp [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hlin (show 0 ≤ 1+E by positivity)
  have hb : (1-Real.exp (-t*x))/t ≤ x*(1+Real.exp (-a/2))/2 := by
    apply (div_le_iff₀ ht).mpr
    rw [heq]
    have hc := mul_le_mul_of_nonneg_left hE (mul_nonneg ht.le hx)
    nlinarith only [hm, hc]
  have hab := neg_le_abs ((1-Real.exp (-t*x))/t-x)
  linarith only [hb, hab]

lemma prime_error_lower {t a : ℝ} (ht : 0 < t) {p : ℕ} (hp : p.Prime)
    (ha : a ≤ t*Real.log p) :
    (1-Real.exp (-a/2))/2*Real.log p ≤ |smoothMangoldt t p-Λ p| := by
  have he : expDivisorSum t p = 1-Real.exp (-t*Real.log p) := by
    simpa using expDivisorSum_prime_pow t hp (by decide : 0 < 1)
  rw [smoothMangoldt, expDivisorSum_at_zero, one_apply, if_neg hp.ne_one,
    sub_zero, he, vonMangoldt_apply_prime hp]
  exact exp_deficit_lower ht (Real.log_natCast_nonneg p) ha

lemma block_log_lower {N p : ℕ} (hN : 4 ≤ N) (hp : p ∈ Ioc (N/2) N) :
    (1+Real.log N)/4 ≤ Real.log p := by
  have hp0 : 0 < p := by have := (mem_Ioc.mp hp).1; omega
  have hNp : N < 2*p := by have := (mem_Ioc.mp hp).1; omega
  have hNpR : (N : ℝ) ≤ 2*p-1 := by
    have hh : (N : ℝ)+1 ≤ 2*p := by exact_mod_cast hNp
    linarith
  have hsq : (N : ℝ) ≤ (p : ℝ)^2 := by nlinarith [sq_nonneg ((p : ℝ)-1)]
  have hlog := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hsq
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogN : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<4) (Nat.cast_le.mpr hN)
    have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    rw [h4] at hh
    linarith [Real.log_two_gt_d9]
  linarith

lemma eventually_prime_block_mass :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)/4 ≤
      ∑ p ∈ (Ioc (N/2) N).filter Nat.Prime, Real.log p := by
  have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_theta_interval_lower (a := (1/2 : ℝ)) (b := 1) (by norm_num) (by norm_num))
  filter_upwards [hh] with N hN
  have he : Chebyshev.theta (N/2 : ℕ) = Chebyshev.theta ((N : ℝ)/2) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
    rw [show ⌊(N : ℝ)/2⌋₊ = N/2 by simpa using Nat.floor_div_natCast (N : ℝ) 2]
  rw [← theta_sub_eq_sum (Nat.div_le_self N 2), he]
  norm_num only [one_mul, show (1 : ℝ)-1/2 = 1/2 by norm_num,
    show (1/2 : ℝ)/2 = 1/4 by norm_num] at hN
  simpa only [one_div_mul_eq_div] using hN

noncomputable def deficit (ε : ℝ) : ℝ := (1-Real.exp (-ε/8))/8

lemma deficit_pos {ε : ℝ} (hε : 0 < ε) : 0 < deficit ε := by
  unfold deficit
  apply div_pos _ (by norm_num)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

/-- A parameter separated from the small regime forces a positive actual
L1 error, using only the contribution of large prime inputs. -/
lemma normalized_error_lower {N : ℕ} (hN : 4 ≤ N) {t ε : ℝ} (ht : 0 < t)
    (hε : 0 < ε) (hz : ε ≤ t*(1+Real.log N))
    (hblock : (N : ℝ)/4 ≤ ∑ p ∈ (Ioc (N/2) N).filter Nat.Prime, Real.log p) :
    deficit ε ≤ smoothL1Error t N/(N : ℝ) := by
  classical
  have hδ : 0 ≤ (1-Real.exp (-ε/8))/2 := by
    have hh := (deficit_pos hε).le
    unfold deficit at hh
    linarith
  have hterm (p : ℕ) (hp : p ∈ (Ioc (N/2) N).filter Nat.Prime) :
      (1-Real.exp (-ε/8))/2*Real.log p ≤ |smoothMangoldt t p-Λ p| := by
    have hlog := block_log_lower hN (mem_filter.mp hp).1
    have hmul := mul_le_mul_of_nonneg_left hlog ht.le
    have ha : ε/4 ≤ t*Real.log p := by nlinarith only [hz, hmul]
    have hh := prime_error_lower ht (mem_filter.mp hp).2 ha
    have he : -(ε/4)/2 = -ε/8 := by ring
    simpa only [he] using hh
  have hsub : (Ioc (N/2) N).filter Nat.Prime ⊆ Ioc 0 N := by
    intro p hp
    have hh := mem_Ioc.mp (mem_filter.mp hp).1
    exact mem_Ioc.mpr ⟨by omega, hh.2⟩
  have he : deficit ε*N ≤ smoothL1Error t N := by
    calc
      _ = ((1-Real.exp (-ε/8))/2)*((N : ℝ)/4) := by unfold deficit; ring
      _ ≤ ((1-Real.exp (-ε/8))/2)*
          (∑ p ∈ (Ioc (N/2) N).filter Nat.Prime, Real.log p) :=
        mul_le_mul_of_nonneg_left hblock hδ
      _ = ∑ p ∈ (Ioc (N/2) N).filter Nat.Prime,
          ((1-Real.exp (-ε/8))/2)*Real.log p := mul_sum _ _ _
      _ ≤ ∑ p ∈ (Ioc (N/2) N).filter Nat.Prime, |smoothMangoldt t p-Λ p| :=
        sum_le_sum hterm
      _ ≤ smoothL1Error t N := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  exact (le_div_iff₀ (Nat.cast_pos.mpr (show 0 < N by omega))).mpr he

/-- The small joint regime is necessary, not merely sufficient. -/
theorem small_parameter_of_l1 (t : ℕ → ℝ)
    (ht : ∀ᶠ N in atTop, 0 < t N)
    (herr : Tendsto (fun N : ℕ => smoothL1Error (t N) N/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => t N*(1+Real.log N)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [ht] with N ht
    have hh : 0 ≤ t N*(1+Real.log N) := by positivity [Real.log_natCast_nonneg N]
    linarith
  · intro ε hε
    have he := (tendsto_order.mp herr).2 (deficit ε) (deficit_pos hε)
    filter_upwards [ht, he, eventually_prime_block_mass, eventually_ge_atTop (4 : ℕ)]
      with N ht he hblock hN
    by_contra hh
    have hlo := normalized_error_lower hN ht hε (le_of_not_gt hh) hblock
    linarith

/-- Exact characterization for eventually positive smoothing parameters. -/
theorem joint_l1_iff (t : ℕ → ℝ) (ht : ∀ᶠ N in atTop, 0 < t N) :
    Tendsto (fun N : ℕ => smoothL1Error (t N) N/(N : ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun N => t N*(1+Real.log N)) atTop (𝓝 0) := by
  constructor
  · exact small_parameter_of_l1 t ht
  · intro hh
    exact joint_l1_tendsto t ht hh

/-- Any L1-approximating parameter sequence has ineffective absolute
cutoff damping at D<=N. This is not an estimate for the actual signed tail. -/
theorem damping_of_l1 (t : ℕ → ℝ) (D : ℕ → ℕ)
    (ht : ∀ᶠ N in atTop, 0 < t N) (hD : ∀ᶠ N in atTop, D N ≤ N)
    (herr : Tendsto (fun N : ℕ => smoothL1Error (t N) N/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.exp (-(t N)*Real.log (D N))) atTop (𝓝 1) :=
  joint_l1_regime_damping t D ht hD (small_parameter_of_l1 t ht herr)

/-- The necessity statement also holds along arbitrary diverging cutoffs;
no all-cutoff hypothesis is smuggled into a selected-scale application. -/
theorem small_parameter_of_l1_along {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) (t : ι → ℝ) (hN : Tendsto N l atTop)
    (ht : ∀ᶠ i in l, 0 < t i)
    (herr : Tendsto (fun i => smoothL1Error (t i) (N i)/(N i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => t i*(1+Real.log (N i))) l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [ht] with i ht
    have hh : 0 ≤ t i*(1+Real.log (N i)) := by positivity [Real.log_natCast_nonneg (N i)]
    linarith
  · intro ε hε
    have he := (tendsto_order.mp herr).2 (deficit ε) (deficit_pos hε)
    filter_upwards [ht, he, hN.eventually eventually_prime_block_mass,
      hN.eventually (eventually_ge_atTop (4 : ℕ))] with i ht he hblock hi
    by_contra hh
    have hlo := normalized_error_lower hi ht hε (le_of_not_gt hh) hblock
    linarith

/-- Exact joint characterization, including subsequences of irrational good scales. -/
theorem joint_l1_iff_along {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) (t : ι → ℝ) (hN : Tendsto N l atTop)
    (ht : ∀ᶠ i in l, 0 < t i) :
    Tendsto (fun i => smoothL1Error (t i) (N i)/(N i : ℝ)) l (𝓝 0) ↔
      Tendsto (fun i => t i*(1+Real.log (N i))) l (𝓝 0) := by
  constructor
  · exact small_parameter_of_l1_along N t hN ht
  · intro hs
    have he := (Real.continuous_exp.tendsto (14*0)).comp (hs.const_mul 14)
    simp only [mul_zero, Function.comp_def, Real.exp_zero] at he
    have hb := ((he.sub_const 1).add hs).const_mul 7
    simp only [sub_self, zero_add, mul_zero] at hb
    apply squeeze_zero' (Eventually.of_forall (fun i => by
      exact div_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) (Nat.cast_nonneg _))) _ hb
    filter_upwards [ht, hN.eventually (eventually_ge_atTop (1 : ℕ))] with i ht hi
    apply (div_le_iff₀ (Nat.cast_pos.mpr hi)).mpr
    exact (joint_l1_bound hi ht).trans_eq (by ring)

/-- Absolute-cutoff damping remains nonvanishing along any L1-approximating
sequence of diverging scales. This concerns the factor only, not the signed tail. -/
theorem damping_of_l1_along {ι : Type*} {l : Filter ι}
    (N D : ι → ℕ) (t : ι → ℝ) (hN : Tendsto N l atTop)
    (ht : ∀ᶠ i in l, 0 < t i) (hD : ∀ᶠ i in l, D i ≤ N i)
    (herr : Tendsto (fun i => smoothL1Error (t i) (N i)/(N i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => Real.exp (-(t i)*Real.log (D i))) l (𝓝 1) := by
  have hs := small_parameter_of_l1_along N t hN ht herr
  have hz : Tendsto (fun i => t i*Real.log (D i)) l (𝓝 0) := by
    apply squeeze_zero' _ _ hs
    · filter_upwards [ht] with i ht
      exact mul_nonneg ht.le (Real.log_natCast_nonneg _)
    · filter_upwards [ht, hD] with i ht hd
      have hlog : Real.log (D i) ≤ 1+Real.log (N i) := by
        by_cases hd0 : D i = 0
        · simp only [hd0, Nat.cast_zero, Real.log_zero]
          positivity [Real.log_natCast_nonneg (N i)]
        · have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0))
            (Nat.cast_le.mpr hd)
          linarith
      exact mul_le_mul_of_nonneg_left hlog ht.le
  have he := (Real.continuous_exp.tendsto (-0)).comp hz.neg
  simpa only [Function.comp_def, neg_zero, Real.exp_zero, neg_mul] using he

theorem l1_damping_incompatible {ι : Type*} {l : Filter ι} [NeBot l]
    (N D : ι → ℕ) (t : ι → ℝ) (hN : Tendsto N l atTop)
    (ht : ∀ᶠ i in l, 0 < t i) (hD : ∀ᶠ i in l, D i ≤ N i) :
    ¬ (Tendsto (fun i => smoothL1Error (t i) (N i)/(N i : ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => Real.exp (-(t i)*Real.log (D i))) l (𝓝 0)) := by
  rintro ⟨herr, hdamp⟩
  have hh := tendsto_nhds_unique (damping_of_l1_along N D t hN ht hD herr) hdamp
  norm_num at hh

#print axioms normalized_error_lower
#print axioms small_parameter_of_l1
#print axioms joint_l1_iff
#print axioms damping_of_l1
#print axioms small_parameter_of_l1_along
#print axioms joint_l1_iff_along
#print axioms damping_of_l1_along
#print axioms l1_damping_incompatible
end Erdos972SharpJointSmoothRegime
