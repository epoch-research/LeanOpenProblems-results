import Submission.ShrinkingRotationTubeExplore
import Submission.SquareAnnulusMassExplore

/-! Monotone single-window rotation sets cannot witness Erdős 66.
The conclusion concerns only this restricted class of natural sets. -/
namespace Erdos66MonotoneRotationTube
open Filter AdditiveCombinatorics Erdos66Counting Erdos66ShrinkingRotationTube
  Erdos66RotationFloorPerturbation Erdos66RotationMassLogBound
  Erdos66SquareAnnulusMass
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma floor_window_ge_one (x θ : ℝ) (h : Int.fract x<θ) :
    (1 : ℝ) ≤ ((⌊x⌋-⌊x-θ⌋ : ℤ) : ℝ) := by
  have hreal : x-θ < (⌊x⌋ : ℝ) := by
    have := Int.self_sub_fract x
    linarith
  have hi : ⌊x-θ⌋ < ⌊x⌋ := Int.floor_lt.mpr hreal
  exact_mod_cast (show (1 : ℤ) ≤ ⌊x⌋-⌊x-θ⌋ by omega)

lemma count_eq_sum (A : Set ℕ) (N : ℕ) :
    (count A N : ℝ)=∑ k∈Finset.range N, if k∈A then (1 : ℝ) else 0 := by
  simp [count,cutoff]

/-- Uniformly widening a closed window by 1/K avoids any endpoint issue.
The coarse bound here is deliberately linear in its expected mass. -/
lemma tube_count_window_upper (p : ℕ → ℝ) (hp : Antitone p)
    (hp0 : ∀ k, 0 ≤ p k) (L K : ℕ) (hK : 0<K) :
    (count (tube (Real.sqrt 2) p) (L+K) : ℝ) ≤
      count (tube (Real.sqrt 2) p) L+51*(K : ℝ)*p L+81 := by
  let θ := p L+1/(K : ℝ)
  have hKr : (0 : ℝ)<K := by exact_mod_cast hK
  have hθ : 0<θ := by
    dsimp [θ]
    exact add_pos_of_nonneg_of_pos (hp0 L) (by positivity)
  have hsum : (∑ k∈Finset.range K,
      if L+k∈tube (Real.sqrt 2) p then (1 : ℝ) else 0) ≤
      rotationSum (Real.sqrt 2) ((L : ℝ)*Real.sqrt 2) θ K := by
    apply Finset.sum_le_sum
    intro k hk
    have he : (L : ℝ)*Real.sqrt 2+(k : ℝ)*Real.sqrt 2=
        ((L+k : ℕ) : ℝ)*Real.sqrt 2 := by push_cast; ring
    rw [he]
    split_ifs with hm
    · apply floor_window_ge_one
      change Int.fract (((L+k : ℕ) : ℝ)*Real.sqrt 2) ≤ p (L+k) at hm
      have hple := hp (show L ≤ L+k by omega)
      dsimp [θ]
      have hinv : (0 : ℝ)<1/(K : ℝ) := by positivity
      linarith
    · have hh := Int.floor_le_floor (show
        ((L+k : ℕ) : ℝ)*Real.sqrt 2-θ ≤ ((L+k : ℕ) : ℝ)*Real.sqrt 2 by linarith)
      exact_mod_cast sub_nonneg.mpr hh
  have hrot := rotation_mass_log_bound (Real.sqrt 2) K (by simp) K le_rfl
    ((L : ℝ)*Real.sqrt 2) θ hθ.le
  have hlog := Real.log_le_sub_one_of_pos (show 0<(K : ℝ)*θ+1 by positivity)
  have hmass : (K : ℝ)*θ=(K : ℝ)*p L+1 := by
    dsimp [θ]
    field_simp
  rw [count_eq_sum,count_eq_sum,Finset.sum_range_add]
  have hh := (abs_le.mp hrot).2
  rw [hmass] at hh hlog
  linarith

lemma log_square_div_index_zero :
    Tendsto (fun q : ℕ ↦ Real.log (2*(q : ℝ)^2+2)/(q : ℝ)) atTop (𝓝 0) := by
  have hbase := Erdos66Counting.log_two_mul_add_two_div_nat_limit
  have hbound : ∀ᶠ q : ℕ in atTop,
      0 ≤ Real.log (2*(q : ℝ)^2+2)/(q : ℝ) ∧
      Real.log (2*(q : ℝ)^2+2)/(q : ℝ) ≤
        2*(Real.log (2*(q : ℝ)+2)/(q : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqr : (1 : ℝ)≤q := by exact_mod_cast hq
    have hq0 : (0 : ℝ)<q := by linarith
    have hl := Real.log_le_log (show 0<2*(q : ℝ)^2+2 by positivity)
      (show 2*(q : ℝ)^2+2 ≤ (2*(q : ℝ)+2)^2 by nlinarith)
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    refine ⟨div_nonneg (Real.log_nonneg (by nlinarith)) hq0.le,?_⟩
    calc
      _ ≤ (2*Real.log (2*(q : ℝ)+2))/(q : ℝ) := div_le_div_of_nonneg_right hl hq0.le
      _ = _ := by ring
  apply squeeze_zero' (hbound.mono (fun _ h ↦ h.1)) (hbound.mono (fun _ h ↦ h.2))
  simpa using hbase.const_mul 2

lemma global_cap_eventually_le_index (K C : ℝ) :
    ∀ᶠ q : ℕ in atTop, K+C*Real.log (2*(q : ℝ)^2+2) ≤ (q : ℝ) := by
  have hh := (tendsto_const_div_atTop_nhds_zero_nat K).add
    (log_square_div_index_zero.const_mul C)
  simp only [mul_zero,add_zero] at hh
  have he := hh.eventually_le_const (show (0 : ℝ)<1 by norm_num)
  filter_upwards [he,eventually_ge_atTop 1] with q hq hq1
  have hqr : (0 : ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hdiv : (K+C*Real.log (2*(q : ℝ)^2+2))/(q : ℝ)≤1 := by
    simpa only [add_div,mul_div_assoc] using hq
  exact (div_le_one hqr).mp hdiv

/-- The class is restricted to a single interval in one fixed irrational
rotation. No hypothesis of this form is imposed by the original conjecture. -/
theorem monotone_tube_no_nonzero_limit (p : ℕ → ℝ)
    (hp : Antitone p) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (c : ℝ) (hc : c≠0) :
    ¬ Tendsto (fun n ↦ (sumRep (tube (Real.sqrt 2) p) n : ℝ)/Real.log n)
      atTop (𝓝 c) := by
  intro ht
  obtain ⟨K,C,hK,hC,hcap⟩ := global_log_upper_bound ht
  obtain ⟨T,hT,hspike⟩ := exists_uniform_spike_threshold
  have hm := witness_square_annulus_gt_linear hc ht (408*T+1000)
  have htwice : Tendsto (fun q : ℕ ↦ 2*q) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro q
    change q ≤ 2*q
    omega
  have hm' := htwice.eventually hm
  obtain ⟨q,hqcap,hqmass,hq1⟩ :=
    ((global_cap_eventually_le_index K C).and (hm'.and (eventually_ge_atTop 1))).exists
  have hqR : (1 : ℝ)≤q := by exact_mod_cast hq1
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hmass : ((q^2 : ℕ) : ℝ)*p (2*q^2) ≤ 2*T+4*(q : ℝ) := by
    by_cases hh : 2*T ≤ ((q^2 : ℕ) : ℝ)*p (2*q^2)
    · have hθ : 0<p (2*q^2) := by
        have hq0 : (0 : ℝ)<((q^2 : ℕ) : ℝ) := by exact_mod_cast (show 0<q^2 by omega)
        nlinarith
      obtain ⟨n,hnlo,hnhi,hnrep⟩ := hspike p (q^2) hq2 (p (2*q^2)) hθ
        (hp1 _) (fun k hk ↦ hp hk) hh
      have hlog : Real.log ((n : ℝ)+2) ≤ Real.log (2*(q : ℝ)^2+2) := by
        apply Real.log_le_log (by positivity)
        have hnR : (n : ℝ)<2*(q : ℝ)^2 := by exact_mod_cast hnhi
        linarith
      have hmul := mul_le_mul_of_nonneg_left hlog hC.le
      have hupper := hcap n
      linarith
    · linarith
  have hwindow := tube_count_window_upper p hp hp0 (4*q^2) (4*q^2) (by nlinarith)
  have hmon := hp (show 2*q^2 ≤ 4*q^2 by omega)
  have hmul := mul_le_mul_of_nonneg_left hmon
    (show (0 : ℝ)≤204*((q^2 : ℕ) : ℝ) by positivity)
  have he1 : (2*q)^2=4*q^2 := by ring
  have he2 : 2*(2*q)^2=4*q^2+4*q^2 := by ring
  rw [he2,he1] at hqmass
  push_cast at hwindow hmass hmul hqmass
  nlinarith

end Erdos66MonotoneRotationTube
