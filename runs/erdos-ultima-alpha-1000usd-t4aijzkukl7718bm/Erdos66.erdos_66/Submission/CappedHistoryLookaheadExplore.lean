import Submission.ShiftedUpperAnnulusExplore
import Submission.Explore
import Submission.CountingExplore
import Submission.CompactnessExplore

/-! A limitation of arbitrary prescribed-prefix extension. Even a strict global
upper cap and a long accurate history do not force feasibility in the next window.
This is not a negation of the existential conjecture in `Spec.lean`. -/
namespace Erdos66CappedHistoryLookahead
open Filter AdditiveCombinatorics Erdos66Explore Erdos66Counting
  Erdos66Compactness Erdos66ShiftedUpperAnnulus
open scoped Topology Classical
set_option maxHeartbeats 1000000

/-- An initial gap extends the range of representation counts already fixed by
an exact membership prefix. -/
lemma sumRep_congr_past_cutoff_of_gap (A B : Set ℕ) (L H n : ℕ)
    (hA : ∀ a ≤ H, a ∉ A) (hB : ∀ a ≤ H, a ∉ B)
    (hprefix : ∀ a < L, a ∈ A ↔ a ∈ B) (hn : n ≤ L + H) :
    sumRep A n = sumRep B n := by
  rw [sumRep_def, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hs := Finset.mem_antidiagonal.mp hp
  by_cases h₁ : p.1 < L
  · by_cases h₂ : p.2 < L
    · exact and_congr (hprefix p.1 h₁) (hprefix p.2 h₂)
    · have hh : p.1 ≤ H := by omega
      simp only [hA p.1 hh, hB p.1 hh, false_and]
  · have hh : p.2 ≤ H := by omega
    simp only [hA p.2 hh, hB p.2 hh, and_false]

/-- For every prescribed lookahead distance H, there are finite prefixes
which satisfy a strict global cap, are accurate throughout an arbitrarily
long multiplicative history, but already force a lower-bound failure at L+H.
The competitor must preserve all old membership bits, including absences. -/
theorem exists_capped_accurate_history_without_next_extension
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (R H N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N L : ℕ, N₀ ≤ N ∧ N ≤ L ∧ R * N ≤ L ∧ H < L ∧
      ∃ C : Finset ℕ, C ⊆ Finset.range L ∧
        (∀ a ≤ H, a ∉ C) ∧
        (∀ n : ℕ, (sumRep (C : Set ℕ) n : ℝ) / Real.log n < c - ε / 4) ∧
        (∀ n : ℕ, N ≤ n → n < L →
          |(sumRep (C : Set ℕ) n : ℝ) / Real.log n - c| < ε) ∧
        (∀ A : Set ℕ, (∀ a < L, a ∈ A ↔ a ∈ C) →
          (sumRep A (L + H) : ℝ) / Real.log ((L + H : ℕ) : ℝ) ≤ c - ε) := by
  have hbase : 0 < c - ε / 2 := by linarith only [hc, hεc]
  obtain ⟨N, hNP, hNpos, B, hBfin, hBsupp, hBup, hBgood⟩ :=
    exists_upper_logarithmic_annulus (c - ε / 2) (ε / 4)
      hbase (by positivity) (R + 2) (max N₀ (H + 2)) (by omega)
  have hN0 : N₀ ≤ N := by omega
  have hNH : H + 2 ≤ N := by omega
  have hBmissing : ∀ a ≤ H, a ∉ B := by
    intro a ha hab
    have hh := hBsupp hab
    change max N₀ (H + 2) ≤ a at hh
    omega
  have hex : ∃ n : ℕ, N ≤ n ∧ (sumRep B n : ℝ) / Real.log n ≤ c - ε := by
    obtain ⟨n, hn, hz⟩ := ((eventually_ge_atTop N).and
      (sumRep_eventually_zero_of_finite hBfin)).exists
    refine ⟨n, hn, ?_⟩
    rw [hz, Nat.cast_zero, zero_div]
    linarith
  let m := Nat.find hex
  have hmN : N ≤ m := (Nat.find_spec hex).1
  have hmfail : (sumRep B m : ℝ) / Real.log m ≤ c - ε := (Nat.find_spec hex).2
  have hmbig : (R + 2) * N < m := by
    by_contra hh
    have hgood := hBgood m hmN (by omega)
    have hlo := (abs_lt.mp hgood).1
    linarith
  have hmH : H ≤ m := by omega
  let L := m - H
  have hLH : L + H = m := Nat.sub_add_cancel hmH
  have hRN : R * N ≤ L := by dsimp [L]; nlinarith
  have hNL : N ≤ L := by nlinarith
  have hHL : H < L := by omega
  let C := cutoff B L
  have hCsub : (C : Set ℕ) ⊆ B := by
    intro a ha
    exact (mem_cutoff.mp ha).2
  have hprefix : ∀ a < L, a ∈ (C : Set ℕ) ↔ a ∈ B := by
    intro a ha
    change a ∈ cutoff B L ↔ a ∈ B
    simp only [mem_cutoff, and_iff_right ha]
  have hCmissing : ∀ a ≤ H, a ∉ C := by
    intro a ha hac
    exact hBmissing a ha (hCsub hac)
  have hCupper (n : ℕ) :
      (sumRep (C : Set ℕ) n : ℝ) / Real.log n < c - ε / 4 := by
    have hlog : 0 ≤ Real.log (n : ℝ) := by
      by_cases hn : n = 0
      · simp only [hn, Nat.cast_zero, Real.log_zero, le_refl]
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hmono : (sumRep (C : Set ℕ) n : ℝ) ≤ sumRep B n := by
      exact_mod_cast sumRep_mono hCsub n
    have hh := div_le_div_of_nonneg_right hmono hlog
    have hb := hBup n
    linarith
  have hCgood (n : ℕ) (hnN : N ≤ n) (hnL : n < L) :
      |(sumRep (C : Set ℕ) n : ℝ) / Real.log n - c| < ε := by
    have heq : sumRep (C : Set ℕ) n = sumRep B n := by
      apply sumRep_congr_below
      intro a ha
      exact hprefix a (by omega)
    have hnM : n < m := by omega
    have hnot := Nat.find_min hex hnM
    have hlo : c - ε < (sumRep B n : ℝ) / Real.log n := by
      exact lt_of_not_ge (fun hh ↦ hnot ⟨hnN, hh⟩)
    rw [heq, abs_lt]
    have hup := hBup n
    constructor <;> linarith
  refine ⟨N, L, hN0, hNL, hRN, hHL, C, ?_, hCmissing, hCupper, hCgood, ?_⟩
  · intro a ha
    exact Finset.mem_range.mpr (mem_cutoff.mp ha).1
  · intro A hAC
    have hAmissing : ∀ a ≤ H, a ∉ A := by
      intro a ha haa
      exact hCmissing a ha ((hAC a (by omega)).mp haa)
    have hAB : ∀ a < L, a ∈ A ↔ a ∈ B := by
      intro a ha
      exact (hAC a ha).trans (hprefix a ha)
    have heq := sumRep_congr_past_cutoff_of_gap A B L H (L + H)
      hAmissing hBmissing hAB le_rfl
    rw [heq, hLH]
    exact hmfail

/-- The failed target lies inside the next window, even when a positive
lookahead distance was prescribed before constructing the prefix. -/
theorem capped_accurate_history_does_not_ensure_next_window
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (R H N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N L : ℕ, N₀ ≤ N ∧ N ≤ L ∧ R * N ≤ L ∧ H < L ∧
      ∃ C : Finset ℕ, C ⊆ Finset.range L ∧
        (∀ n : ℕ, (sumRep (C : Set ℕ) n : ℝ) / Real.log n < c - ε / 4) ∧
        (∀ n : ℕ, N ≤ n → n < L →
          |(sumRep (C : Set ℕ) n : ℝ) / Real.log n - c| < ε) ∧
        (∀ A : Set ℕ, (∀ a < L, a ∈ A ↔ a ∈ C) →
          ¬ (∀ n : ℕ, L ≤ n → n < 2 * L →
            |(sumRep A n : ℝ) / Real.log n - c| < ε)) := by
  obtain ⟨N, L, hN0, hNL, hRN, hHL, C, hCs, hCg, hCu, hCa, hCf⟩ :=
    exists_capped_accurate_history_without_next_extension c ε hc hε hεc R H N₀ hR
  refine ⟨N, L, hN0, hNL, hRN, hHL, C, hCs, hCu, hCa, ?_⟩
  intro A hAC hgood
  have hf := hCf A hAC
  have hh := (abs_lt.mp (hgood (L + H) (by omega) (by omega))).1
  linarith

end Erdos66CappedHistoryLookahead
