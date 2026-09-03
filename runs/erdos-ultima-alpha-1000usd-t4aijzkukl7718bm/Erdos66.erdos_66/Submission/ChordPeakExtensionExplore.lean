import Submission.LinearRoundingPeakExplore
import Submission.LargeReflectionPatchExplore

/-! Arbitrarily late chord patches with exact prefix brackets and large
normalized representation peaks. These are bad roundings, not a disproof
of the existential Erdős conjecture. -/
namespace Erdos66ChordPeakExtension
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66Rounding Erdos66ClampedPrefixContinuation
  Erdos66CenteredCumulativeRounding Erdos66LinearRoundingPeak
  Erdos66FlatProfileWindows
open scoped Topology Classical
set_option maxHeartbeats 2400000

lemma quarter_flat_window (k : ℕ) (hk : 6≤ k)
    (hH : (harmonic (6*k^32+1):ℝ)≤ (k:ℝ)^2) :
    ∃ L : ℕ, k^32≤ L ∧ L+k^19≤ 3*k^32 ∧
      ((k^19:ℕ):ℝ)*(profile L-profile (L+k^19))≤ 1/4 ∧
      (k:ℝ)/2≤ ((k^19:ℕ):ℝ)*profile (L+k^19) := by
  obtain ⟨L,hL,hR,hosc,hmass⟩ := exists_flat_profile_window k hk hH
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hk1 : 1≤ k := by omega
  have hw : k^19≤ 2*k^20 := by
    have hh : k^19≤ k^20 := Nat.pow_le_pow_right hk1 (by norm_num)
    omega
  have hmid : L+k^19≤ L+2*k^20 := by omega
  have hpcomp := profile_antitone hmid
  have hd : 0≤ profile L-profile (L+k^19) := sub_nonneg.mpr (profile_antitone (by omega))
  have hnew : (2*k^20:ℕ)*(profile L-profile (L+k^19))≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show profile L-profile (L+k^19)≤
      profile L-profile (L+2*k^20) by linarith) (by positivity : (0:ℝ)≤ (2*k^20:ℕ))
    exact hh.trans hosc
  have hnew' : 2*(k:ℝ)*((k:ℝ)^19*(profile L-profile (L+k^19)))≤ 1 := by
    push_cast at hnew
    nlinarith [show (k:ℝ)^20=(k:ℝ)*(k:ℝ)^19 by ring]
  have hos : ((k^19:ℕ):ℝ)*(profile L-profile (L+k^19))≤ 1/4 := by
    have hk6 : (6:ℝ)≤ k := by exact_mod_cast hk
    push_cast
    have hh : 0≤ (k:ℝ)^19*(profile L-profile (L+k^19)) := mul_nonneg (by positivity) hd
    nlinarith
  have hm : (k:ℝ)/2≤ ((k^19:ℕ):ℝ)*profile (L+k^19) := by
    apply (mul_le_mul_iff_right₀ hk0).mp
    push_cast at hmass ⊢
    have hh := mul_le_mul_of_nonneg_left hpcomp (show 0≤ (k:ℝ)^20 by positivity)
    nlinarith [show (k:ℝ)^20=(k:ℝ)*(k:ℝ)^19 by ring]
  exact ⟨L,hL,hmid.trans hR,hos,hm⟩

lemma eventual_linear_peak_budget (M : ℕ) :
    ∀ᶠ k : ℕ in atTop, (M:ℝ)*(Real.log 6+32*Real.log (k:ℝ))≤ (k:ℝ)/4-1 := by
  have hdecay : Tendsto (fun k : ℕ ↦ (M:ℝ)*(Real.log 6+32*Real.log (k:ℝ))/(k:ℝ))
      atTop (𝓝 0) := by
    have h₁ := (tendsto_natCast_atTop_atTop (R:=ℝ)).const_div_atTop (Real.log 6)
    have h₂ := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul 32
    have hh := (h₁.add h₂).const_mul (M:ℝ)
    simpa only [Function.comp_def,id_eq,mul_zero,add_zero,add_div,mul_div_assoc] using hh
  filter_upwards [eventually_ge_atTop 8,
    hdecay.eventually_lt_const (show (0:ℝ)<1/8 by norm_num)] with k hk hh
  have hkr : (8:ℝ)≤ k := by exact_mod_cast hk
  have ht := (div_lt_iff₀ (by linarith : (0:ℝ)<k)).mp hh
  linarith

structure State where
  F : ℕ → ℝ
  T : ℕ
  zero : F 0=1/2
  steps : UnitSteps F
  close : ∀ n, |F n-(mass profile n+1/2)|≤ 1/4
  tail : ∀ n, T≤ n → F n=mass profile n+1/2

noncomputable def initial : State where
  F := fun n ↦ mass profile n+1/2
  T := 0
  zero := by rw [mass_zero]; norm_num
  steps := centered_steps profile (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩)
  close := by intro n; simp
  tail := by intro n hn; rfl

def Extension (s : State) (M : ℕ) (q : State × ℕ) : Prop :=
  s.T<q.1.T ∧ s.T≤ q.2 ∧ q.2<q.1.T ∧
    (∀ n≤ s.T, q.1.F n=s.F n) ∧
    (M:ℝ)≤ (sumRep (rounded q.1.F) q.2:ℝ)/Real.log q.2

/-- The new patch preserves the entire old cumulative prefix and the same
quarter-unit closeness allowance. Its peak is already fixed before the
next patch begins. -/
theorem exists_extension (s : State) (M : ℕ) : ∃ q, Extension s M q := by
  obtain ⟨k,⟨⟨hk,hkT⟩,hH⟩,hbudget⟩ :=
    ((eventually_ge_atTop 8).and (eventually_ge_atTop (s.T+2)) |>.and
      eventually_harmonic_polynomial_bound |>.and (eventual_linear_peak_budget M)).exists
  obtain ⟨L,hL,hR,hosc,hmass⟩ := quarter_flat_window k (by omega) hH
  let W := k^19
  let R := L+W
  have hW : 0<W := pow_pos (by omega) _
  have hTL : s.T+2≤ L := hkT.trans ((Nat.le_self_pow (by norm_num : 32≠0) k).trans hL)
  have hLR : L<R := by dsimp [R]; omega
  let v := chordSlope profile L R
  let g := chord profile L R
  let F' := splice s.F g L R
  have hends := chord_endpoints profile L R hLR
  have hFends : s.F L=g L ∧ s.F R=g R := by
    constructor
    · rw [s.tail L (by omega)]
      exact hends.1.symm
    · rw [s.tail R (by omega)]
      exact hends.2.symm
  have hsteps : UnitSteps F' := splice_steps s.F g s.steps
    (chord_steps profile (fun i ↦ ⟨profile_nonneg i,profile_le_one i⟩)
      profile_antitone L R hLR) L R hFends.1 hFends.2
  have hclose : ∀ n, |F' n-(mass profile n+1/2)|≤ 1/4 := by
    intro n
    by_cases hn : L≤ n ∧ n≤ R
    · dsimp only [F']
      rw [splice_inside s.F g L R n hn]
      have hh := chord_error profile profile_antitone L R n hLR hn.1 hn.2
      have he : (R:ℝ)-(L:ℝ)=(W:ℝ) := by dsimp [R]; push_cast; ring
      rw [he] at hh
      exact hh.trans hosc
    · dsimp only [F']
      rw [splice_outside s.F g L R n (by omega)]
      exact s.close n
  have hzero : F' 0=1/2 := by
    dsimp only [F']
    rw [splice_outside s.F g L R 0 (Or.inl (by omega))]
    exact s.zero
  have htail : ∀ n, R≤ n → F' n=mass profile n+1/2 := by
    intro n hn
    rcases eq_or_lt_of_le hn with he | he
    · subst n
      dsimp only [F']
      rw [splice_inside s.F g L R R ⟨hLR.le,le_rfl⟩]
      exact hends.2
    · dsimp only [F']
      rw [splice_outside s.F g L R n (Or.inr he)]
      exact s.tail n (by omega)
  have hvb := chordSlope_bounds profile profile_antitone L R hLR
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hpR : 0<profile R := by
    by_contra hh
    have hle : profile R≤ 0 := le_of_not_gt hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤ W by positivity) hle
    change (k:ℝ)/2≤ (W:ℝ)*profile R at hmass
    linarith
  have hv : 0<v := hpR.trans_le hvb.1
  have hv1 : v≤ 1 := hvb.2.trans (profile_le_one L)
  let K := ⌊v*W⌋₊
  have hKW : (K:ℝ)≤ v*W := Nat.floor_le (by positivity)
  have hKmass : (k:ℝ)/2-1<(K:ℝ) := by
    have hh := Nat.lt_floor_add_one (v*W)
    have hvm := mul_le_mul_of_nonneg_right hvb.1 (show (0:ℝ)≤ W by positivity)
    change (k:ℝ)/2≤ (W:ℝ)*profile R at hmass
    change v*W<(K:ℝ)+1 at hh
    nlinarith
  have hK : 0<K := by
    have hk8 : (8:ℝ)≤ k := by exact_mod_cast hk
    have hh : (0:ℝ)<K := by linarith
    exact_mod_cast hh
  have hline (j : ℕ) (hj : j≤ W) : F' (L+j)=(mass profile L+1/2)+v*j := by
    dsimp only [F']
    rw [splice_inside s.F g L R (L+j) (by dsimp [R]; omega)]
    dsimp [g,chord,v]
    push_cast
    ring
  obtain ⟨n,hnlo,hnhi,hnpeak⟩ := linear_segment_peak F' L W K (mass profile L+1/2) v
    hv hv1 hK hKW hline
  have hn2 : 2≤ n := by omega
  have hnr : n<2*R := hnhi
  have hnupper : n≤ 6*k^32 := by dsimp [R,W] at *; omega
  have hlog : Real.log (n:ℝ)≤ Real.log 6+32*Real.log (k:ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0<n by omega) : (0:ℝ)<n)
      (by exact_mod_cast hnupper : (n:ℝ)≤ ((6*k^32:ℕ):ℝ))
    push_cast at hh
    rw [Real.log_mul (by norm_num) (pow_pos hk0 32).ne',Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  have hpk : (k:ℝ)/4-1≤ (sumRep (rounded F') n:ℝ) := by
    have hh : (K:ℝ)≤ 2*(sumRep (rounded F') n:ℝ) := by exact_mod_cast hnpeak
    linarith
  let s' : State := {
    F := F'
    T := 2*R
    zero := hzero
    steps := hsteps
    close := hclose
    tail := fun n hn ↦ htail n (by omega) }
  refine ⟨(s',n),?_,by omega,hnr,?_,?_⟩
  · change s.T<2*R
    omega
  · intro i hi
    exact splice_outside s.F g L R i (Or.inl (by omega))
  · apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (show 1<n by omega)))).mpr
    exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg M)).trans (hbudget.trans hpk)

noncomputable def step (s : State) (M : ℕ) : State × ℕ :=
  Classical.choose (exists_extension s M)

lemma step_spec (s : State) (M : ℕ) : Extension s M (step s M) :=
  Classical.choose_spec (exists_extension s M)

end Erdos66ChordPeakExtension
