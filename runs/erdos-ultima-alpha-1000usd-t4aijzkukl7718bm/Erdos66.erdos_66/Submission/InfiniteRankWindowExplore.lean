import Submission.LogProfileLowerExplore
import Submission.RankCellWindowExplore
import Submission.ShortSupportSwapTailExplore

/-! Uniform rank-row probabilities at natural counting scale. Each sufficiently
large prescribed old point receives a nonempty nearby candidate row of total
mass one, with a universal harmonic-profile pointwise majorant. -/
namespace Erdos66InfiniteRankWindow
open Filter Erdos66Fractional Erdos66Generating Erdos66Counting Erdos66Rounding
  Erdos66NaturalScaleRankWindow Erdos66LogProfileLower Erdos66LogCellWindowBudget
  Erdos66ClampedPrefixContinuation Erdos66RankProfileGap Erdos66RankCellWindow
  Erdos66RankCellExchange Erdos66ShortSupportSwapTail Erdos66ReflectionRoundingPatch
open scoped Classical Topology
set_option maxHeartbeats 3800000

lemma density_window_profile_lower (N w i : ℕ) (hN : 1 ≤ N)
    (hlog : 0<Real.log (N : ℝ))
    (hwl : Real.sqrt N/(16*Real.sqrt (Real.log N)) ≤ w)
    (hi : N ≤ i ∧ i ≤ 4*N) :
    1 ≤ 128*(w : ℝ)*profile i := by
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.sqrt (Real.log (N : ℝ)) := by positivity
  have hwidth := (div_le_iff₀ (show 0<16*Real.sqrt (Real.log (N : ℝ)) by positivity)).mp hwl
  have hwidthsq := (sq_le_sq₀ (Real.sqrt_nonneg (N : ℝ)) (by positivity : 0 ≤ (w : ℝ)*(16*Real.sqrt (Real.log N)))).mpr hwidth
  rw [Real.sq_sqrt hn.le,mul_pow,mul_pow,Real.sq_sqrt hlog.le] at hwidthsq
  have hlo := profile_log_square_lower i
  have hmono := Real.log_le_log hn (show (N : ℝ) ≤ (i : ℝ)+1 by exact_mod_cast (show N ≤ i+1 by omega))
  have hsize : 4*((2*i+1 : ℕ) : ℝ) ≤ 36*(N : ℝ) := by
    have hi' : (i : ℝ) ≤ 4*N := by exact_mod_cast hi.2
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hprofile : Real.log (N : ℝ) ≤ 36*(N : ℝ)*(profile i)^2 :=
    (hmono.trans hlo).trans (mul_le_mul_of_nonneg_right hsize (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_right hwidthsq (show 0 ≤ 36*(profile i)^2 by positivity)
  have hcancel : 1 ≤ 9216*((w : ℝ)*profile i)^2 := by
    apply le_of_mul_le_mul_left (a := Real.log (N : ℝ)) _ hlog
    nlinarith only [hprofile,hm]
  have hp : 0 ≤ (w : ℝ)*profile i := mul_nonneg (Nat.cast_nonneg w) (profile_nonneg i)
  nlinarith only [hcancel,hp]

lemma eventually_good_density_window : ∀ᶠ N : ℕ in atTop,
    2 ≤ N ∧ 6 ≤ densityWindow N ∧ densityWindow N ≤ N ∧
      (densityWindow N : ℝ)*profile N ≤ 1/4 ∧
      ∀ i, N ≤ i → i ≤ 4*N → 1 ≤ 128*(densityWindow N : ℝ)*profile i := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_density_window,eventually_ge_atTop 2,hlog.eventually_ge_atTop 1,
    (log_power_sqrt_decay 1).eventually_le_const (show (0 : ℝ)<1/96 by norm_num)]
    with N hw hN hl hdec
  simp only [pow_one] at hdec
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsp : 0<Real.sqrt (N : ℝ) := by positivity
  have hL : 0<Real.log (N : ℝ) := by linarith
  have hsL : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log N :=
    Real.sqrt_le_iff.mpr ⟨hL.le,by nlinarith⟩
  have hh := (div_le_iff₀ hsp).mp hdec
  have h6 : (6 : ℝ) ≤ Real.sqrt N/(16*Real.sqrt (Real.log N)) := by
    apply (le_div_iff₀ (by positivity : 0<16*Real.sqrt (Real.log (N : ℝ)))).mpr
    linarith
  have h6w : 6 ≤ densityWindow N := by exact_mod_cast h6.trans hw.2.2.2.1
  exact ⟨hN,h6w,hw.2.1,hw.2.2.1,fun i hi hi' ↦
    density_window_profile_lower N (densityWindow N) i (by omega) hL hw.2.2.2.1 ⟨hi,hi'⟩⟩

 theorem exists_uniform_rank_probability_rows : ∃ N₀ : ℕ,
    ∀ (A : Set ℕ) (_hbr : ∀ L, PrefixBrackets profile A L) (d : ℕ), N₀ ≤ d → d∈A →
      ∃ (L U : ℕ) (S : Finset ℕ), S.Nonempty ∧ S ⊆ Finset.Ico L U ∧
        (∀ i∈S, i∉A) ∧
        (∀ i∈Finset.Ico L U, d ≤ 2*i ∧ i ≤ 2*d ∧ cell profile i=count A d) ∧
        (∀ i∈Finset.Ico L U, ((S.card : ℝ)⁻¹ ≤ 256*profile i)) ∧
        (S.card : ℝ)⁻¹*(U-L : ℕ) ≤ 2 := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp eventually_good_density_window
  refine ⟨2*N₀,?_⟩
  intro A hbr d hd hdA
  let N := d/2
  have hNg : N₀ ≤ N := by dsimp only [N]; omega
  obtain ⟨hN,hw6,hwN,hwm,hwp⟩ := hN₀ N hNg
  let w := densityWindow N
  have hwpos : 0<w := by dsimp only [w]; omega
  have hwle : w ≤ d := hwN.trans (Nat.div_le_self d 2)
  have hNlow : N ≤ d-w := by dsimp only [w,N] at *; omega
  have hm : (w : ℝ)*profile (d-w) ≤ 1/4 :=
    (mul_le_mul_of_nonneg_left (profile_antitone hNlow) (Nat.cast_nonneg w)).trans hwm
  obtain ⟨L,hLlo,hLhi,hLi⟩ := exists_rank_cell_window profile A profile_nonneg profile_antitone hbr
    (harmonic_brackets_unbounded A hbr) d w hdA hwle hm
  have hrow (i : ℕ) (hi : i∈Finset.Ico L (L+w)) :
      N ≤ i ∧ i ≤ 4*N ∧ d ≤ 2*i ∧ i ≤ 2*d ∧ cell profile i=count A d := by
    have hi' := Finset.mem_Ico.mp hi
    let j : Fin w := ⟨i-L,by omega⟩
    have hb := hLi j
    have he : L+j.val=i := by dsimp only [j]; omega
    rw [he] at hb
    have hNd : d=2*N ∨ d=2*N+1 := by dsimp only [N]; omega
    refine ⟨?_,?_,?_,?_,hb.2.2.2.1⟩ <;> dsimp only [w] at * <;> omega
  have hNL : N ≤ L := by
    have hh := hrow L (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
    exact hh.1
  have hOld : ((intervalPart A L (L+w)).card : ℝ) ≤ 3 := by
    have hh := antitone_window_count profile A 1 profile_antitone
      (brackets_count_discrepancy profile A hbr) L w
    have hh' := mul_le_mul_of_nonneg_left (profile_antitone hNL) (Nat.cast_nonneg w)
    linarith
  let S := (Finset.Ico L (L+w)).filter (fun i ↦ i∉A)
  have hcard : (intervalPart A L (L+w)).card+S.card=w := by
    simpa only [intervalPart,S,Nat.card_Ico,Nat.add_sub_cancel_left] using
      Finset.card_filter_add_card_filter_not (s := Finset.Ico L (L+w)) (p := fun i ↦ i∈A)
  have hcard' : ((intervalPart A L (L+w)).card : ℝ)+S.card=(w : ℝ) := by exact_mod_cast hcard
  have h6 : (6 : ℝ) ≤ w := by exact_mod_cast hw6
  have hhalf : (w : ℝ) ≤ 2*(S.card : ℝ) := by linarith
  have hSpos : (0 : ℝ)<S.card := by linarith
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
  refine ⟨L,L+w,S,hSne,Finset.filter_subset _ _,fun i hi ↦ (Finset.mem_filter.mp hi).2,
    fun i hi ↦ (hrow i hi).2.2,?_,?_⟩
  · intro i hi
    have hh := hrow i hi
    have hb := hwp i hh.1 hh.2.1
    change 1 ≤ 128*(w : ℝ)*profile i at hb
    have hc := mul_le_mul_of_nonneg_right hhalf (profile_nonneg i)
    rw [←one_div]
    apply (div_le_iff₀ hSpos).mpr
    nlinarith only [hb,hc]
  · rw [Nat.add_sub_cancel_left]
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ hSpos).mpr hhalf

end Erdos66InfiniteRankWindow
