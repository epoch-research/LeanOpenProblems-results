import Submission.IntervalRecursiveSieve

/-! Monotone closure of a compatible signed interval pair already enforces the
four partition inequalities. This is a structural result, not a positivity
estimate and not a transfer between different prime sequences. -/
namespace Erdos970.IntervalRescaling.IntegerHull

/-- The lower function is allowed to be negative before taking its prefix hull. -/
structure Compatible (l u : ℕ → ℝ) : Prop where
  lower_zero : l 0 = 0
  upper_zero : u 0 = 0
  upper_nonneg : ∀ n, 0 ≤ u n
  lower_increment : ∀ m n, l n ≤ l (m + n) - l m ∧ l (m + n) - l m ≤ u n
  upper_increment : ∀ m n, l n ≤ u (m + n) - u m ∧ u (m + n) - u m ≤ u n

noncomputable def lowerHull (l : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ l

noncomputable def upperHull (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  sInf (u '' Set.Ici n)

lemma le_lowerHull (l : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) : l m ≤ lowerHull l n := by
  exact Finset.le_sup' l (Finset.mem_range.mpr (by omega))

lemma lowerHull_le {l : ℕ → ℝ} {n : ℕ} {b : ℝ} (h : ∀ m ≤ n, l m ≤ b) :
    lowerHull l n ≤ b := by
  exact Finset.sup'_le _ l (fun m hm => h m (by have := Finset.mem_range.mp hm; omega))

lemma lowerHull_mono (l : ℕ → ℝ) : Monotone (lowerHull l) := by
  intro m n hmn
  exact lowerHull_le (fun s hs => le_lowerHull l (hs.trans hmn))

lemma upperSet_nonempty (u : ℕ → ℝ) (n : ℕ) : (u '' Set.Ici n).Nonempty :=
  ⟨u n, n, by simp, rfl⟩

lemma upperSet_bddBelow {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    BddBelow (u '' Set.Ici n) := by
  refine ⟨0, ?_⟩
  rintro y ⟨m, hm, rfl⟩
  exact hu m

lemma upperHull_le {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) {m n : ℕ} (hnm : n ≤ m) :
    upperHull u n ≤ u m :=
  csInf_le (upperSet_bddBelow hu n) ⟨m, hnm, rfl⟩

lemma le_upperHull {u : ℕ → ℝ} {n : ℕ} {b : ℝ}
    (h : ∀ m, n ≤ m → b ≤ u m) : b ≤ upperHull u n := by
  apply le_csInf (upperSet_nonempty u n)
  rintro y ⟨m, hm, rfl⟩
  exact h m hm

lemma upperHull_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    0 ≤ upperHull u n := le_upperHull (fun m _ => hu m)

lemma upperHull_mono {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) : Monotone (upperHull u) := by
  intro m n hmn
  exact le_upperHull (fun s hs => upperHull_le hu (hmn.trans hs))

lemma Compatible.lowerHull_nonneg {l u : ℕ → ℝ} (h : Compatible l u) (n : ℕ) :
    0 ≤ lowerHull l n := by
  simpa only [h.lower_zero] using le_lowerHull l (Nat.zero_le n)

lemma Compatible.hull_lower_add {l u : ℕ → ℝ} (h : Compatible l u) (m n : ℕ) :
    lowerHull l m + lowerHull l n ≤ lowerHull l (m + n) := by
  suffices hh : lowerHull l m ≤ lowerHull l (m + n) - lowerHull l n by linarith
  apply lowerHull_le
  intro s hs
  suffices hh : lowerHull l n ≤ lowerHull l (m + n) - l s by linarith
  apply lowerHull_le
  intro t ht
  have hi := (h.lower_increment s t).1
  have hb := le_lowerHull l (show s + t ≤ m + n by omega)
  linarith

lemma Compatible.hull_upper_add {l u : ℕ → ℝ} (h : Compatible l u) (m n : ℕ) :
    upperHull u (m + n) ≤ upperHull u m + upperHull u n := by
  suffices hh : upperHull u (m + n) - upperHull u n ≤ upperHull u m by linarith
  apply le_upperHull
  intro s hs
  suffices hh : upperHull u (m + n) - u s ≤ upperHull u n by linarith
  apply le_upperHull
  intro t ht
  have hi := (h.upper_increment s t).2
  have hb := upperHull_le h.upper_nonneg (show m + n ≤ s + t by omega)
  linarith

lemma Compatible.hull_lower_mixed {l u : ℕ → ℝ} (h : Compatible l u) (m n : ℕ) :
    lowerHull l (m + n) ≤ lowerHull l m + upperHull u n := by
  suffices hh : lowerHull l (m + n) - lowerHull l m ≤ upperHull u n by linarith
  apply le_upperHull
  intro t ht
  have hraw : lowerHull l (m + t) ≤ lowerHull l m + u t := by
    apply lowerHull_le
    intro s hs
    by_cases hts : t ≤ s
    · have hi := (h.lower_increment (s - t) t).2
      rw [Nat.sub_add_cancel hts] at hi
      have hb := le_lowerHull l (show s - t ≤ m by omega)
      linarith
    · have hi := (h.upper_increment (t - s) s).1
      rw [Nat.sub_add_cancel (show s ≤ t by omega)] at hi
      have hb := h.upper_nonneg (t - s)
      have hl := h.lowerHull_nonneg m
      linarith
  have hm := lowerHull_mono l (show m + n ≤ m + t by omega)
  linarith

lemma Compatible.hull_upper_mixed {l u : ℕ → ℝ} (h : Compatible l u) (m n : ℕ) :
    upperHull u m + lowerHull l n ≤ upperHull u (m + n) := by
  apply le_upperHull
  intro t ht
  suffices hh : lowerHull l n ≤ u t - upperHull u m by linarith
  apply lowerHull_le
  intro s hs
  have hi := (h.upper_increment (t - s) s).1
  rw [Nat.sub_add_cancel (show s ≤ t by omega)] at hi
  have hb := upperHull_le h.upper_nonneg (show m ≤ t - s by omega)
  linarith

/-- After the prefix supremum and tail infimum, ALL partition and mixed
inequalities hold, not just inequalities for a selected list of block lengths. -/
theorem Compatible.hulls {l u : ℕ → ℝ} (h : Compatible l u) :
    Compatible (lowerHull l) (upperHull u) := by
  refine ⟨?_, ?_, upperHull_nonneg h.upper_nonneg, ?_, ?_⟩
  · apply le_antisymm
    · apply lowerHull_le
      intro m hm
      have hm0 : m = 0 := by omega
      simpa only [hm0] using h.lower_zero.le
    · exact h.lowerHull_nonneg 0
  · exact le_antisymm (by simpa only [h.upper_zero] using upperHull_le h.upper_nonneg (le_refl 0))
      (upperHull_nonneg h.upper_nonneg 0)
  · intro m n
    exact ⟨by linarith [h.hull_lower_add m n], by linarith [h.hull_lower_mixed m n]⟩
  · intro m n
    exact ⟨by linarith [h.hull_upper_mixed m n], by linarith [h.hull_upper_add m n]⟩

#print axioms Compatible.hulls
end Erdos970.IntervalRescaling.IntegerHull
