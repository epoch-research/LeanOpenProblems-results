import Submission.PrescribedLogSpikesExplore
import Submission.UpperDensityOneLogLimitExplore

/-! Density-one convergence with harmonic exceptions and a global logarithmic
bound does not imply a pointwise limit. This does not disprove Erdős 66. -/
namespace Erdos66DensityOneNoLimit
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66Counting
  Erdos66PrescribedLogSpikes Erdos66UpperDensityOneLogLimit Erdos66DensityOneLogLimit
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma harmonic_union (E F : Set ℕ)
    (hE : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0))
    (hF : Summable (fun n : ℕ ↦ if n∈F then 1/((n:ℝ)+2) else 0)) :
    Summable (fun n : ℕ ↦ if n∈E∪F then 1/((n:ℝ)+2) else 0) := by
  apply (hE.add hF).of_norm_bounded
  intro n
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by split_ifs <;> positivity)]
  by_cases he : n∈E <;> by_cases hf : n∈F <;>
    simp only [Set.mem_union,he,hf,or_true,true_or,or_self,ite_true,ite_false] <;> linarith [show (0:ℝ)≤1/((n:ℝ)+2) by positivity]

lemma frequently_outside (E : Set ℕ)
    (hE : Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0)) :
    ∃ᶠ n : ℕ in atTop, n∉E := by
  by_contra hf
  have he : ∀ᶠ n : ℕ in atTop, n∈E := by simpa only [not_not] using not_frequently.mp hf
  have hs : Summable (fun n : ℕ ↦ 1/((n:ℝ)+2)) := by
    apply hE.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [he] with n hn
    exact if_pos hn
  have hn : ¬Summable (fun n : ℕ ↦ 1/((n:ℝ)+2)) := by
    have hh := Real.summable_one_div_nat_add_rpow 2 1
    have ha (n : ℕ) : |(n:ℝ)+2|=(n:ℝ)+2 := abs_of_nonneg (by positivity)
    simpa only [Real.rpow_one,ha,
      lt_self_iff_false,iff_false] using hh
  exact hn hs

lemma transfer_masked_limit (A B E : Set ℕ) (c : ℝ)
    (hl : Tendsto (fun n ↦ if n∈E then c else (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (hlo : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)+2*spikeMultiplicity n≤sumRep B n)
    (hhi : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep B n : ℝ)≤sumRep A n+2*spikeMultiplicity n+ε*logScale n) :
    Tendsto (fun n ↦ if n∈E∪Set.range center then c else (sumRep B n : ℝ)/Real.log n)
      atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hl (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlo.and (hhi (ε/8) (by positivity)))
  refine ⟨max (max N M) 2,fun n hn ↦ ?_⟩
  by_cases he : n∈E∪Set.range center
  · simpa only [if_pos he,dist_self] using hε
  · have hne : n∉E := fun h ↦ he (Or.inl h)
    have hnf : n∉Set.range center := fun h ↦ he (Or.inr h)
    have hnN : N≤n := (le_max_left N M).trans ((le_max_left _ _).trans hn)
    have hnM : M≤n := (le_max_right N M).trans ((le_max_left _ _).trans hn)
    have hn2 : 2≤n := (le_max_right _ _).trans hn
    have hlog : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hbase := hN n hnN
    rw [if_neg hne,Real.dist_eq] at hbase
    obtain ⟨hlo',hhi'⟩ := hM n hnM
    rw [spikeMultiplicity_off n hnf,Nat.cast_zero,mul_zero,add_zero] at hlo' hhi'
    have ha := (abs_lt.mp hbase)
    have hld := (div_le_div_iff_of_pos_right hlog).mpr hlo'
    have hupper : (sumRep B n : ℝ)/Real.log n ≤ (sumRep A n : ℝ)/Real.log n+ε/4 := by
      apply (div_le_iff₀ hlog).mpr
      have hl2 := logScale_le_double hn2
      have heq : ((sumRep A n : ℝ)/Real.log n+ε/4)*Real.log n =
          sumRep A n+(ε/4)*Real.log n := by field_simp
      rw [heq]
      nlinarith
    rw [if_neg he,Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩

lemma spikes_prevent_limit_one (A B : Set ℕ)
    (hlo : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)+2*spikeMultiplicity n≤sumRep B n) :
    ¬Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 1) := by
  intro hl
  have hh := (hl.comp center_tendsto).eventually_lt_const (show (1:ℝ)<3/2 by norm_num)
  have hbounds := center_tendsto.eventually hlo
  have hlarge := center_tendsto.eventually (eventually_ge_atTop 2)
  obtain ⟨k,hk,hlo',hk2⟩ := (hh.and (hbounds.and hlarge)).exists
  have hlog : 0<Real.log (center k : ℝ) := Real.log_pos (by exact_mod_cast (show 1<center k by omega))
  have hlower : Real.log (center k : ℝ)≤logScale (center k) :=
    Real.log_le_log (by exact_mod_cast (show 0<center k by omega)) (by linarith)
  rw [spikeMultiplicity_at] at hlo'
  have hr := (repetitions_bounds k).1
  have hnon := Nat.cast_nonneg (α := ℝ) (sumRep A (center k))
  have hu := (div_lt_iff₀ hlog).mp hk
  nlinarith

/-- A set with harmonic-exception convergence to 1 and a global O(log n)
bound can have no finite pointwise limit whatsoever. -/
theorem exists_density_one_but_no_limit :
    ∃ (B E : Set ℕ) (K C : ℝ), 0≤K ∧ 0≤C ∧
      (∀ n : ℕ, (sumRep B n : ℝ)≤K+C*logScale n) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then (1:ℝ) else (sumRep B n : ℝ)/Real.log n) atTop (𝓝 1) ∧
      ¬∃ d : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 d) := by
  classical
  obtain ⟨A,E,K,hK,hA,hE,_,hl⟩ := exists_globally_bounded_log_limit_off_exception 1 (by norm_num)
  have hA' : ∀ n, (sumRep A n : ℝ)≤K+34*logScale n := by
    intro n
    simpa only [show (2:ℝ)*1+32=34 by norm_num,logScale] using hA n
  obtain ⟨B,_,hlo,hhi⟩ := add_controlled_spikes A K 34 hK (by norm_num) hA'
  let F := E∪Set.range center
  have hF : Summable (fun n : ℕ ↦ if n∈F then 1/((n:ℝ)+2) else 0) :=
    harmonic_union E _ hE centers_harmonic_summable
  have hlim := transfer_masked_limit A B E 1 hl hlo hhi
  let D : ℝ := 1+1/Real.log 2
  have hD : 0≤D := by dsimp [D]; positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hhi 1 (by norm_num))
  have hbound : ∀ n, (sumRep B n : ℝ)≤K+(N+2:ℕ)+(35+2*D)*logScale n := by
    intro n
    by_cases hn : N≤n
    · have hh := hN n hn
      have ha := hA' n
      have hb := spikeMultiplicity_bound n
      change (spikeMultiplicity n : ℝ)≤D*logScale n at hb
      have hnat := Nat.cast_nonneg (α := ℝ) (N+2)
      nlinarith
    · have hb : (sumRep B n : ℝ)≤(N+2:ℕ) := by
        exact_mod_cast (show sumRep B n≤N+2 from (sumRep_le_succ B n).trans (by omega))
      have hpos := mul_nonneg (show 0≤35+2*D by linarith) (logScale_pos n).le
      linarith
  refine ⟨B,F,K+(N+2:ℕ),35+2*D,by positivity,by linarith,hbound,by simpa only [F, Set.mem_union, ite_or] using hF,
    density_zero_of_harmonic_summable F (by simpa only [F, Set.mem_union, ite_or] using hF),
    by simpa only [F, Set.mem_union, ite_or] using hlim,?_⟩
  rintro ⟨d,hd⟩
  have heq : d=1 := tendsto_nhds_unique_of_frequently_eq hd hlim
    ((frequently_outside F (by simpa only [F, Set.mem_union, ite_or] using hF)).mono (fun n hn ↦ (if_neg hn).symm))
  subst d
  exact spikes_prevent_limit_one A B hlo hd

end Erdos66DensityOneNoLimit
