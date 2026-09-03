import Submission.LocalizedRepairExplore
import Submission.ShiftedUpperAnnulusExplore
import Submission.ClippedRepairExplore

/-! Past accuracy alone does not guarantee a next-window extension. A finite
prefix can already force a future excess. This is a limitation of an extension
criterion, not a disproof of the existential conjecture. -/
namespace Erdos66PrefixLookahead
open Filter AdditiveCombinatorics Erdos66Explore Erdos66Counting
  Erdos66Compactness Erdos66LocalizedRepair Erdos66ShiftedUpperAnnulus
  Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma logarithmic_envelope_bound (A : Set ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ z : ℕ, (sumRep A z : ℝ)/Real.log z < C) :
    ∀ z : ℕ, (sumRep A z : ℝ) ≤ 2+C*Real.log ((z : ℝ)+2) := by
  intro z
  have hlogplus : 0 ≤ Real.log ((z : ℝ)+2) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) z
    linarith)
  by_cases hz : 2 ≤ z
  · have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
    have hh := (div_lt_iff₀ hlog).mp (hA z)
    have hcomp := Real.log_le_log (by exact_mod_cast (show 0<z by omega) : (0 : ℝ)<z)
      (show (z : ℝ) ≤ z+2 by linarith)
    have hm := mul_le_mul_of_nonneg_left hcomp hC
    linarith
  · have hh : (sumRep A z : ℝ) ≤ 2 := by
      exact_mod_cast (show sumRep A z ≤ 2 by have := sumRep_le_succ A z; omega)
    linarith [mul_nonneg hC hlogplus]

lemma cutoff_rep_eq_below (A : Set ℕ) (L z : ℕ) (hz : z<L) :
    sumRep (cutoff A L : Set ℕ) z=sumRep A z := by
  apply sumRep_congr_below
  intro a ha
  simp only [Finset.mem_coe,mem_cutoff]
  exact and_iff_right (by omega)

/-- Arbitrarily long accurate annular histories may coexist with an
arbitrarily large single future peak forced entirely by the chosen prefix.
Every other target still has a global upper bound. -/
theorem exists_accurate_prefix_with_future_peak (c ε M : ℝ)
    (hc : 0<c) (hε : 0<ε) (hM : 0 ≤ M) (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N : ℕ, N₀ ≤ N ∧ 3 ≤ N ∧ ∃ C : Finset ℕ,
      C⊆Finset.range (2*(R*N)+2) ∧
      (∀ z : ℕ, z ≠ 3*(R*N) → (sumRep (C : Set ℕ) z : ℝ)/Real.log z < c+ε) ∧
      (∀ z : ℕ, N ≤ z → z<2*(R*N)+2 →
        |(sumRep (C : Set ℕ) z : ℝ)/Real.log z-c| < ε) ∧
      M < (sumRep (C : Set ℕ) (3*(R*N)) : ℝ)/Real.log ((3*(R*N) : ℕ) : ℝ) := by
  let η := ε/4
  have hη : 0<η := by dsimp [η]; positivity
  have hC : 0 ≤ c+η := by linarith
  have hD : 0 ≤ M+1 := by linarith
  have hloglim : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨P,hP⟩ := eventually_atTop.mp ((eventually_localized_repair (M+1) η 2 (c+η)
    hD hη (by norm_num) hC).and (hloglim.eventually_ge_atTop 2))
  obtain ⟨N,hN,hNp,B,hBfin,hBsupp,hBup,hBgood⟩ :=
    exists_upper_logarithmic_annulus c η hc hη (2*R+2) (max N₀ (max P 3)) (by omega)
  have hN0 : N₀ ≤ N := by omega
  have hNP : P ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hRN : N ≤ R*N := by nlinarith
  let n := 3*(R*N)
  let L := 2*(R*N)+2
  have hnP : P ≤ n := by dsimp [n]; omega
  have hnL : L ≤ n := by dsimp [L,n]; omega
  have hln : 2 ≤ Real.log (n : ℝ) := (hP n hnP).2
  have hlnpos : 0 < Real.log (n : ℝ) := by linarith
  let m := ⌊(M+1)*Real.log (n : ℝ)⌋₊
  have hm : (m : ℝ) ≤ (M+1)*Real.log n := Nat.floor_le (by positivity)
  obtain ⟨F,hFcard,hFdis,hFsupp,hFself,hFcenter,hFcoll⟩ :=
    (hP n hnP).1 B (logarithmic_envelope_bound B (c+η) hC hBup) m hm
  let C := cutoff (B∪(F : Set ℕ)) L
  have hFsub : (F : Set ℕ)⊆(C : Set ℕ) := by
    intro a ha
    have hb := (hFsupp a ha).2
    apply mem_cutoff.mpr
    refine ⟨?_,Or.inr ha⟩
    dsimp only [n,L] at hb ⊢
    omega
  have hCsub : (C : Set ℕ)⊆B∪(F : Set ℕ) := by
    intro a ha
    exact (mem_cutoff.mp ha).2
  have hlow (z : ℕ) (hz : z<L) : sumRep (C : Set ℕ) z=sumRep (B∪(F : Set ℕ)) z :=
    cutoff_rep_eq_below (B∪(F : Set ℕ)) L z hz
  have hup (z : ℕ) (hzn : z≠n) : (sumRep (C : Set ℕ) z : ℝ)/Real.log z < c+ε := by
    by_cases hz : 2 ≤ z
    · have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
      have hmono : (sumRep (C : Set ℕ) z : ℝ) ≤ sumRep (B∪(F : Set ℕ)) z := by
        exact_mod_cast sumRep_mono hCsub z
      have hcoll := (hFcoll z hzn).2
      have hcomp : Real.log ((z : ℝ)+2) ≤ 2*Real.log z := logScale_le_double hz
      have hm := mul_le_mul_of_nonneg_left hcomp hη.le
      have hbound : (sumRep (C : Set ℕ) z : ℝ)/Real.log z ≤
          (sumRep B z : ℝ)/Real.log z+2*η := by
        apply (div_le_iff₀ hlz).mpr
        rw [add_mul,div_mul_cancel₀ _ hlz.ne']
        linarith
      have hb := hBup z
      dsimp only [η] at hbound hb
      linarith
    · have he : z=0 ∨ z=1 := by omega
      rcases he with rfl | rfl <;> norm_num only [Nat.cast_zero,Nat.cast_one,Real.log_zero,
        Real.log_one,div_zero] <;> linarith
  have hgood (z : ℕ) (hzN : N ≤ z) (hzL : z<L) :
      |(sumRep (C : Set ℕ) z : ℝ)/Real.log z-c| < ε := by
    have hzn : z≠n := by omega
    have hzR : z ≤ (2*R+2)*N := by dsimp [L] at hzL; nlinarith
    have hb := hBgood z hzN hzR
    have hmono : (sumRep B z : ℝ) ≤ sumRep (C : Set ℕ) z := by
      rw [hlow z hzL]
      exact_mod_cast sumRep_mono (Set.subset_union_left : B⊆B∪(F : Set ℕ)) z
    have hlz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1<z by omega))
    have hm := div_le_div_of_nonneg_right hmono hlz.le
    have hu := hup z hzn
    rw [abs_lt] at hb ⊢
    dsimp only [η] at hb
    constructor <;> linarith
  have hpeak : M < (sumRep (C : Set ℕ) n : ℝ)/Real.log n := by
    have hmono : (2*(m : ℝ)) ≤ sumRep (C : Set ℕ) n := by
      have hh := sumRep_mono hFsub n
      rw [hFself] at hh
      exact_mod_cast hh
    have hfloor : (M+1)*Real.log (n : ℝ) < (m : ℝ)+1 := Nat.lt_floor_add_one _
    apply (lt_div_iff₀ hlnpos).mpr
    nlinarith [mul_nonneg hM hlnpos.le]
  refine ⟨N,hN0,hN3,C,?_,hup,hgood,hpeak⟩
  intro a ha
  exact Finset.mem_range.mpr (mem_cutoff.mp ha).1

/-- Accuracy on an arbitrarily long annular history does not imply that
there is a monotone extension satisfying even the next-window upper bound.
This quantifies over specially constructed bad prefixes, not all prefixes. -/
theorem accurate_history_does_not_ensure_extension (c ε : ℝ)
    (hc : 0<c) (hε : 0<ε) (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N L : ℕ, N₀ ≤ N ∧ N ≤ L ∧ R*N ≤ L ∧ ∃ C : Finset ℕ,
      C⊆Finset.range L ∧
      (∀ z : ℕ, N ≤ z → z<L → |(sumRep (C : Set ℕ) z : ℝ)/Real.log z-c| < ε) ∧
      ∀ A : Set ℕ, (C : Set ℕ)⊆A →
        ¬ (∀ z : ℕ, L ≤ z → z<2*L → (sumRep A z : ℝ)/Real.log z ≤ c+ε) := by
  obtain ⟨N,hN0,hN3,C,hC,hupper,hgood,hpeak⟩ :=
    exists_accurate_prefix_with_future_peak c ε (c+ε) hc hε (by linarith) R N₀ hR
  have hRN : N ≤ R*N := by nlinarith
  refine ⟨N,2*(R*N)+2,hN0,by omega,by omega,C,hC,hgood,?_⟩
  intro A hCA hA
  have hlow : 2*(R*N)+2 ≤ 3*(R*N) := by omega
  have hhigh : 3*(R*N)<2*(2*(R*N)+2) := by omega
  have hlog : 0 < Real.log ((3*(R*N) : ℕ) : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1<3*(R*N) by omega))
  have hm : (sumRep (C : Set ℕ) (3*(R*N)) : ℝ) ≤ sumRep A (3*(R*N)) := by
    exact_mod_cast sumRep_mono hCA (3*(R*N))
  have hd := div_le_div_of_nonneg_right hm hlog.le
  have hh := hA (3*(R*N)) hlow hhigh
  linarith

end Erdos66PrefixLookahead
