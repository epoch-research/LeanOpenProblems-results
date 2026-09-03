import Submission.MaximalCapWithHolesExplore
import Submission.SparseRepairExplore

/-! Fixed logarithmic caps admit inclusion-maximal sets with infinitely many
holes and near-cap peaks. Maximality therefore does not force a logarithmic
representation limit. This is not a disproof of the existential conjecture. -/
namespace Erdos66LogarithmicMaximalCap
open Filter AdditiveCombinatorics Erdos66PointwiseCapBlocking Erdos66MaximalCapWithHoles
  Erdos66Explore Erdos66ClippedRepair Erdos66SparseRepair
open scoped Classical Topology
set_option maxHeartbeats 1600000

noncomputable def logCap (c : ℝ) (n : ℕ) : ℕ := ⌊c*Real.log ((n:ℝ)+2)⌋₊+10

lemma logCap_error (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    |(logCap c n:ℝ)-c*Real.log ((n:ℝ)+2)| ≤ 10 := by
  have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have h₁ := Nat.floor_le (mul_nonneg hc hlog)
  have h₂ := Nat.lt_floor_add_one (c*Real.log ((n:ℝ)+2))
  simp only [logCap,Nat.cast_add,Nat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith

lemma logCap_top (c : ℝ) (hc : 0<c) : Tendsto (logCap c) atTop atTop := by
  have hn : Tendsto (fun n : ℕ ↦ (n:ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp hn).const_mul_atTop hc)
  exact tendsto_atTop_mono (fun n ↦ by change ⌊c*Real.log ((n:ℝ)+2)⌋₊ ≤ _; dsimp [logCap]; omega) hh

lemma logCap_ratio (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n ↦ (logCap c n:ℝ)/Real.log n) atTop (𝓝 c) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n ↦ ((logCap c n:ℝ)-c*Real.log ((n:ℝ)+2))/Real.log n)
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ abs_nonneg _)) ?_
      (hlog.const_div_atTop 10)
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    rw [abs_div,abs_of_pos hl]
    exact div_le_div_of_nonneg_right (logCap_error c hc n) hl.le
  have hh := herr.add (logScale_div_log_limit.const_mul c)
  simp only [mul_one,zero_add] at hh
  apply hh.congr
  intro n
  dsimp only [logScale]
  ring

lemma subquartic_of_log_ratio (q : ℕ → ℕ) (c : ℝ)
    (h : Tendsto (fun n ↦ (q n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ n in atTop, (q n)^4<n/12 := by
  have hp : Tendsto (fun n : ℕ ↦ (Real.log (n:ℝ))^4/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (h.pow 4).mul hp
  simp only [mul_zero] at hh
  have hq : Tendsto (fun n ↦ (q n:ℝ)^4/(n:ℝ)) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n:ℝ)≠0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1<n by omega)))
    field_simp
  filter_upwards [hq.eventually_lt_const (show (0:ℝ)<1/24 by norm_num),
    eventually_ge_atTop 48] with n hn hn48
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hh' := (div_lt_iff₀ hnpos).mp hn
  have hnat : 24*(q n)^4<n := by
    have hr : (24:ℝ)*(q n:ℝ)^4<(n:ℝ) := by linarith
    exact_mod_cast hr
  omega

lemma holes_peaks_no_limit (q : ℕ → ℕ) (c : ℝ) (hc : 0<c)
    (hq : Tendsto (fun n ↦ (q n:ℝ)/Real.log n) atTop (𝓝 c))
    (A : Set ℕ) (hholes : ∀ K : ℕ, ∃ n≥K, sumRep A n=0)
    (hpeaks : ∀ K : ℕ, ∃ n≥K, q n≤sumRep A n+1) (d : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 d) := by
  intro hd
  have hd0 : d=0 := by
    by_contra hdn
    have hdpos := limit_pos hdn hd
    obtain ⟨K,hK⟩ := eventually_atTop.mp (hd.eventually (lt_mem_nhds (show d/2<d by linarith)))
    obtain ⟨n,hn,hh⟩ := hholes K
    have hv := hK n hn
    rw [hh,Nat.cast_zero,zero_div] at hv
    linarith
  subst d
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hd.eventually_lt_const (show (0:ℝ)<c/4 by positivity)
  have hbig := hq.eventually (lt_mem_nhds (show c/2<c by linarith))
  have hone := (hlog.const_div_atTop 1).eventually_lt_const (show (0:ℝ)<c/4 by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hsmall.and (hbig.and (hone.and (eventually_ge_atTop 2))))
  obtain ⟨n,hn,hpeak⟩ := hpeaks K
  obtain ⟨hs,hb,ho,hn2⟩ := hK n hn
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hp : (q n:ℝ) ≤ (sumRep A n:ℝ)+1 := by exact_mod_cast hpeak
  have hdiv := div_le_div_of_nonneg_right hp hl.le
  rw [add_div] at hdiv
  linarith

/-- Even maximality in the full fixed logarithmic-cap class allows both
arbitrarily late holes and near-cap counts, and hence no finite limit. -/
theorem exists_maximal_log_cap_without_limit (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, (∀ n, sumRep A n≤logCap c n) ∧
      (∀ B : Set ℕ, (∀ n, sumRep B n≤logCap c n) → A⊆B → B=A) ∧
      (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
      (∀ K : ℕ, ∃ n≥K, logCap c n≤sumRep A n+1) ∧
      ∀ d : ℝ, ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 d) := by
  obtain ⟨A,hcap,hmax,hholes,hpeaks⟩ := exists_maximal_with_holes_and_peaks
    (logCap c) (logCap_top c hc) (subquartic_of_log_ratio (logCap c) c (logCap_ratio c hc.le))
  exact ⟨A,hcap,hmax,hholes,hpeaks,holes_peaks_no_limit (logCap c) c hc (logCap_ratio c hc.le) A hholes hpeaks⟩

end Erdos66LogarithmicMaximalCap
