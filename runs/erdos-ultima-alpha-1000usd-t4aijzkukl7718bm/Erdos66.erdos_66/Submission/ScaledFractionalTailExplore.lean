import Submission.FractionalFourthPowerExplore
import Submission.FiniteRepBernoulliExplore

/-! Probability profiles with any prescribed positive logarithmic
convolution coefficient, and finite Bernoulli mean bounds uniform in cutoff. -/
namespace Erdos66ScaledFractionalTail
open Erdos66Fractional Erdos66FractionalFourthPower Erdos66FiniteRepBernoulli
open Filter AdditiveCombinatorics
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def tailConv (s q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (q+1), profile (k+s)*profile (q-k+s)

lemma tailConv_zero (q : ℕ) : tailConv 0 q=(harmonic (q+1):ℝ) := by
  simpa only [tailConv,Nat.add_zero,sumConv,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    using profile_convolution q

lemma tailConv_step (s q : ℕ) :
    tailConv s (q+2)=tailConv (s+1) q+2*profile s*profile (q+s+2) := by
  unfold tailConv
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  have he : (∑ k∈Finset.range (q+1), profile (k+1+s)*profile (q+2-(k+1)+s)) =
      ∑ k∈Finset.range (q+1), profile (k+(s+1))*profile (q-k+(s+1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hh := Finset.mem_range.mp hk
    rw [show k+1+s=k+(s+1) by omega,show q+2-(k+1)+s=q-k+(s+1) by omega]
  rw [he]
  simp only [Nat.zero_add,Nat.sub_zero,Nat.sub_self]
  rw [show q+2+s=q+s+2 by omega]
  ring

lemma tailConv_bounds (s q : ℕ) :
    (harmonic (q+1):ℝ)-2*s ≤ tailConv s q ∧ tailConv s q ≤ (harmonic (q+1):ℝ) := by
  constructor
  · induction s generalizing q with
    | zero => simp [tailConv_zero]
    | succ s ih =>
      have hh := ih (q+2)
      have hs := tailConv_step s q
      have hH : (harmonic (q+1):ℝ) ≤ harmonic (q+2+1) := by
        rw [harmonic_succ (q+2), harmonic_succ (q+1)]
        push_cast
        rw [add_assoc]
        exact le_add_of_nonneg_right (by positivity)
      have hp : profile s*profile (q+s+2) ≤ 1 :=
        (mul_le_mul (profile_le_one s) (profile_le_one _) (profile_nonneg _) (by norm_num)).trans_eq (by ring)
      push_cast
      linarith
  · rw [←tailConv_zero q]
    apply Finset.sum_le_sum
    intro k hk
    simp only [Nat.add_zero]
    exact mul_le_mul (profile_antitone (by omega)) (profile_antitone (by omega))
      (profile_nonneg _) (profile_nonneg _)

lemma exists_scaled_probability_profile (c : ℝ) (hc : 0<c) :
    ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n ∧ p n ≤ 1) ∧
      Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c) := by
  let s := Real.sqrt c
  have hs : 0<s := Real.sqrt_pos.mpr hc
  have hlim := summable_profile_fourth.tendsto_atTop_zero.mul_const (s^4)
  simp only [zero_mul] at hlim
  obtain ⟨S,hS⟩ := (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1)).exists
  have hscale : s*profile S ≤ 1 := by
    by_contra hh
    have hh' : 1<s*profile S := lt_of_not_ge hh
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hh'.le 4
    have he : (s*profile S)^4=profile S^4*s^4 := by ring
    rw [he] at hp
    norm_num at hp
    linarith
  let p : ℕ → ℝ := fun n ↦ s*profile (n+S)
  have hp (n : ℕ) : 0 ≤ p n ∧ p n ≤ 1 := by
    refine ⟨mul_nonneg hs.le (profile_nonneg _),?_⟩
    exact (mul_le_mul_of_nonneg_left (profile_antitone (by omega : S≤n+S)) hs.le).trans hscale
  have he (n : ℕ) : sumConv p p n=c*tailConv S n := by
    dsimp only [sumConv,tailConv,p]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hs2 : s*s=c := Real.mul_self_sqrt hc.le
    rw [← hs2]
    ring
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := harmonic_shift_log_ratio.const_mul c
  simp only [mul_one] at hu
  have hl := hu.sub (hlog.const_div_atTop (2*S*c))
  simp only [sub_zero] at hl
  refine ⟨p,hp,tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hh := mul_le_mul_of_nonneg_left (tailConv_bounds S n).1 hc.le
    rw [he,←mul_div_assoc,←sub_div]
    apply div_le_div_of_nonneg_right _ hln.le
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hln : 0≤Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
    rw [he,←mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tailConv_bounds S n).2 hc.le) hln

lemma finite_mean_bounds (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (L n : ℕ) (hn : n≤L) :
    sumConv p p n ≤ repMean L n (fun i ↦ p i.val) ∧
      repMean L n (fun i ↦ p i.val) ≤ sumConv p p n+1 := by
  have he : (∑ a∈pairs L n, p a.1.val*p a.2.val)=sumConv p p n := by
    rw [pairs_sum_range L n (fun i j ↦ p i*p j),sumConv,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [if_pos (by omega)]
  rw [mean_decomposition,he]
  obtain ⟨hlo,hhi⟩ := diagCorrection_bounds L n (fun i ↦ p i.val) (fun i ↦ hp i.val)
  constructor <;> linarith

lemma uniform_mean_approximation (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1) (c : ℝ)
    (ht : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ L, n≤L →
      |repMean L n (fun i ↦ p i.val)/Real.log n-c| < ε := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n ↦ sumConv p p n/Real.log n-c) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const c
  have hbase := (tendsto_zero_iff_abs_tendsto_zero _).mp hzero
  have htot := hbase.add (hlog.const_div_atTop 1)
  simp only [zero_add] at htot
  have hgood := htot.eventually_lt_const hε
  filter_upwards [hgood,eventually_ge_atTop 2] with n hn hn2
  intro L hL
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  obtain ⟨hlo,hhi⟩ := finite_mean_bounds p hp L n hL
  have hb : |repMean L n (fun i ↦ p i.val)/Real.log n-sumConv p p n/Real.log n| ≤
      1/Real.log n := by
    rw [←sub_div,abs_div,abs_of_pos hln,abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact div_le_div_of_nonneg_right (by linarith) hln.le
  have ha := abs_add_le (repMean L n (fun i ↦ p i.val)/Real.log n-sumConv p p n/Real.log n)
    (sumConv p p n/Real.log n-c)
  have he : repMean L n (fun i ↦ p i.val)/Real.log n-sumConv p p n/Real.log n+
      (sumConv p p n/Real.log n-c)=repMean L n (fun i ↦ p i.val)/Real.log n-c := by ring
  rw [he] at ha
  simp only [Function.comp_apply] at hn
  linarith

end Erdos66ScaledFractionalTail
