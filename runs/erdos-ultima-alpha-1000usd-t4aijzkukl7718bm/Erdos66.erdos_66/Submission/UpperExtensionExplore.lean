import Submission.ShiftedUpperAnnulusExplore
import Submission.AnnulusExtensionExplore
import Submission.CompactnessExplore

/-! Finite prefix extensions preserving a global upper envelope.
No tail lower bound is asserted here. -/
namespace Erdos66UpperExtension
set_option maxHeartbeats 1000000
open Filter AdditiveCombinatorics Erdos66ShiftedUpperAnnulus Erdos66AnnulusExtension
  Erdos66Compactness Erdos66Explore
open scoped Topology Classical

/-- If a finite set lies below a positive logarithmic upper envelope, it has
finite supersets, unchanged below any prescribed cutoff, which approach that
envelope on arbitrarily late multiplicative annuli. -/
theorem exists_upper_extension (B : Set ℕ) (L : ℕ) (hB : B ⊆ Set.Iio L)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hupper : ∀ n : ℕ, (sumRep B n : ℝ) / Real.log n ≤ c)
    (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ A : Set ℕ, A.Finite ∧ B ⊆ A ∧
      (∀ x < L, x ∈ A ↔ x ∈ B) ∧
      (∀ n : ℕ, (sumRep A n : ℝ) / Real.log n ≤ c) ∧
      ∀ n : ℕ, N ≤ n → n ≤ R * N → |(sumRep A n : ℝ) / Real.log n - c| < ε := by
  let η : ℝ := min (ε / 8) (c / 8)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηc : η ≤ c / 8 := min_le_right _ _
  have hbase : 0 < c - 4 * η := by linarith
  have hsmall := Erdos66LogTuning.log_nat_atTop.const_div_atTop (2 * (L : ℝ))
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hsmall.eventually_lt_const hη)
  let P₀ := max P (max L 2)
  obtain ⟨N, hN, hNpos, D, hDfin, hDsupport, hDup, hDgood⟩ :=
    exists_upper_logarithmic_annulus (c - 4 * η) η hbase hη R (max N₀ P₀) hR
  let A := B ∪ D
  have hAfin : A.Finite := ((Set.finite_Iio L).subset hB).union hDfin
  have hlarge (x : ℕ) (hx : x ∈ D) : P₀ ≤ x := (le_max_right N₀ P₀).trans (hDsupport hx)
  have heq (n : ℕ) (hn : n < P₀) : sumRep A n = sumRep B n := by
    apply sumRep_congr_below
    intro x hx
    change x ∈ B ∪ D ↔ x ∈ B
    have hnot : x ∉ D := by intro hd; have hh := hlarge x hd; omega
    simp [hnot]
  have herr (n : ℕ) : |(sumRep A n : ℝ) - sumRep D n| ≤ 2 * L := by
    apply sumRep_eq_tail_error A D L n
    intro x hx
    have hnot : x ∉ B := by intro hb; have hh : x < L := hB hb; omega
    simp [A, hnot]
  have hlog (n : ℕ) (hn : P₀ ≤ n) : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by dsimp [P₀] at hn; omega)
  have herrdiv (n : ℕ) (hn : P₀ ≤ n) :
      |(sumRep A n : ℝ) / Real.log n - (sumRep D n : ℝ) / Real.log n| < η := by
    rw [← sub_div, abs_div, abs_of_pos (hlog n hn)]
    exact (div_le_div_of_nonneg_right (herr n) (hlog n hn).le).trans_lt
      (hP n (by dsimp [P₀] at hn; omega))
  refine ⟨N, by omega, hNpos, A, hAfin, Set.subset_union_left, ?_, ?_, ?_⟩
  · intro x hx
    have hnot : x ∉ D := by
      intro hd
      have hh := hlarge x hd
      dsimp [P₀] at hh
      omega
    simp [A, hnot]
  · intro n
    by_cases hn : n < P₀
    · rw [heq n hn]
      exact hupper n
    have hh := (abs_lt.mp (herrdiv n (by omega))).2
    have hd := hDup n
    linarith
  · intro n hnlo hnhi
    have hnP : P₀ ≤ n := by omega
    have hh := herrdiv n hnP
    have hd := hDgood n hnlo hnhi
    rw [abs_lt] at hh hd ⊢
    constructor <;> linarith

end Erdos66UpperExtension
