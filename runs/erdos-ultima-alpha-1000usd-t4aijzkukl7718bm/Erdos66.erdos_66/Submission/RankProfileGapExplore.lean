import Submission.RankCellExchangeExplore
import Submission.ProfileLowerGapExplore
import Submission.FlatProfileWindowsExplore

/-! Nearby cumulative-rank assignments for the harmonic profile. -/
namespace Erdos66RankProfileGap
open Erdos66Counting Erdos66Generating Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66BracketRankMove Erdos66RankCellExchange
  Erdos66Fractional Erdos66ProfileLowerGap Erdos66FlatProfileWindows Erdos66Rounding
open scoped Classical
set_option maxHeartbeats 2200000

lemma mass_add_lower (p : ℕ → ℝ) (hp : Antitone p) (a w : ℕ) :
    mass p a+(w : ℝ)*p (a+w) ≤ mass p (a+w) := by
  have he : mass p (a+w)=mass p a+∑ i∈Finset.range w, p (a+i) := Finset.sum_range_add p a w
  rw [he]
  have hh : (∑ _i∈Finset.range w, p (a+w)) ≤ ∑ i∈Finset.range w, p (a+i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hp (by have := Finset.mem_range.mp hi; omega)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,add_comm] using add_le_add_right hh (mass p a)

/-- A unit of profile mass on a length-H interval bounds the rank-assigned
point on both sides, with the harmless factor two avoiding endpoint issues. -/
theorem rank_assignment_gap (p : ℕ → ℝ) (A : Set ℕ)
    (hp : ∀ k, 0 ≤ p k) (hanti : Antitone p) (hbr : ∀ L, PrefixBrackets p A L)
    (hunb : ∀ j, ∃ N, j<count A N) (u H : ℕ) (hH : 0<H)
    (hmass : 1<(H : ℝ)*p (u+H)) :
    u<rankPoint A hunb (cell p u)+2*H ∧ rankPoint A hunb (cell p u)<u+2*H := by
  let j := cell p u
  let d := rankPoint A hunb j
  change u < d+2*H ∧ d < u+2*H
  have hb := rankPoint_mass_bounds p A hbr hunb j
  have hlo : (j : ℝ) ≤ mass p u := cell_lower p hp u
  have hhi : mass p u<(j : ℝ)+1 := cell_upper p u
  have hright : d<u+H := by
    by_contra hn
    have hm := mass_mono hp (show u+H ≤ d by omega)
    have hs := mass_add_lower p hanti u H
    change mass p d<(j : ℝ)+1 ∧ _ at hb
    linarith
  constructor
  · by_contra hn
    have hu : d+2*H ≤ u := by omega
    have hsum : u-H+H=u := by omega
    have hs := mass_add_lower p hanti (u-H) H
    rw [hsum] at hs
    have hstep : 1<(H : ℝ)*p u := by
      have hh := mul_le_mul_of_nonneg_left (hanti (show u ≤ u+H by omega)) (Nat.cast_nonneg H)
      linarith
    have hm := mass_mono hp (show d+1 ≤ u-H by omega)
    change _ ∧ (j : ℝ) < mass p (d+1) at hb
    linarith [hb.2]
  · change d<u+2*H
    omega

lemma harmonic_brackets_unbounded (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) :
    ∀ j, ∃ N, j<count A N := by
  intro j
  let n := (j+2)^2
  refine ⟨n+1,?_⟩
  by_contra hn
  have hc : count A (n+1) ≤ j := by omega
  have hcr : (count A (n+1) : ℝ) ≤ j := by exact_mod_cast hc
  have hb := hbr (n+1) (n+1) le_rfl
  rw [mass_indicator_eq_count] at hb
  have hf := Int.lt_floor_add_one (mass profile (n+1))
  have hp : 0 ≤ mass profile (n+1) := Finset.sum_nonneg (fun i _ ↦ profile_nonneg i)
  have hl := profile_prefix_lower n
  change (n : ℝ)+1 ≤ (mass profile (n+1))^2 at hl
  have hupper : mass profile (n+1)<(j : ℝ)+1 := by linarith [hb.1]
  have hncast : (n : ℝ)=((j : ℝ)+2)^2 := by dsimp only [n]; push_cast; rfl
  rw [hncast] at hl
  have hj := Nat.cast_nonneg (α := ℝ) j
  nlinarith

lemma harmonic_rank_gap (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (N H u : ℕ) (_hN : 0<N) (hH : H ≤ N) (hu : u ≤ 12*N)
    (hlen : 2*Real.sqrt ((16*N+1 : ℕ) : ℝ)<H) :
    u<rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)+2*H ∧
      rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)<u+2*H := by
  have hHp : 0<H := by
    have hn := Real.sqrt_nonneg ((16*N+1 : ℕ) : ℝ)
    have hh : (0 : ℝ)<H := by linarith
    exact_mod_cast hh
  apply rank_assignment_gap profile A profile_nonneg profile_antitone hbr
    (harmonic_brackets_unbounded A hbr) u H hHp
  have hs := Real.sqrt_le_sqrt (show (u+H : ℝ)+1 ≤ ((16*N+1 : ℕ) : ℝ) by
    exact_mod_cast (show u+H+1 ≤ 16*N+1 by omega))
  have hsn := Real.sqrt_nonneg ((16*N+1 : ℕ) : ℝ)
  have hlen' : Real.sqrt ((u+H : ℕ)+1 : ℝ)<H := by
    push_cast
    linarith
  have hh := mul_lt_mul_of_pos_right hlen' (profile_pos (u+H))
  have hl := sqrt_mul_profile_lower (u+H)
  push_cast at hh hl
  exact hl.trans_lt hh

end Erdos66RankProfileGap
