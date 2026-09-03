import Submission.ContinuousIntervalOrdering

/-! Chord replacement on a unit lattice cell strengthens the real extension
without changing any natural-length value. This is not rounding a normalized
count to an integer, and it makes no uniform positivity claim. -/
namespace Erdos970.ContinuousInterval

noncomputable def chord (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  f a + (x - a) * (f (a + 1) - f a)

lemma chord_left (f : ℝ → ℝ) (a : ℝ) : chord f a a = f a := by simp [chord]
lemma chord_right (f : ℝ → ℝ) (a : ℝ) : chord f a (a + 1) = f (a + 1) := by
  simp [chord]

lemma chord_combo (f : ℝ → ℝ) (t x y a b : ℝ) (hab : a + b = 1) :
    chord f t (a * x + b * y) = a * chord f t x + b * chord f t y := by
  unfold chord
  rw [show b = 1 - a by linarith]
  ring

lemma chord_convex (f : ℝ → ℝ) (t : ℝ) : ConvexOn ℝ Set.univ (chord f t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  exact le_of_eq (chord_combo f t x y a b hab)

lemma chord_concave (f : ℝ → ℝ) (t : ℝ) : ConcaveOn ℝ Set.univ (chord f t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  exact le_of_eq (chord_combo f t x y a b hab).symm

/-- The line through adjacent endpoints lies below a convex function outside
that cell. The set need only contain the three points used. -/
lemma chord_le_outside {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (a x : ℝ) (ha : a ∈ s) (ha1 : a + 1 ∈ s) (hx : x ∈ s)
    (hout : x ≤ a ∨ a + 1 ≤ x) : chord f a x ≤ f x := by
  rcases hout with hxa | hax
  · rcases eq_or_lt_of_le hxa with rfl | hxa
    · exact le_of_eq (chord_left f x)
    · have hh := hf.secant_mono_aux1 hx ha1 hxa (show a < a + 1 by linarith)
      dsimp [chord]
      nlinarith
  · rcases eq_or_lt_of_le hax with hax | hax
    · rw [← hax, chord_right]
    · have hh := hf.secant_mono_aux1 ha hx (show a < a + 1 by linarith) hax
      dsimp [chord]
      nlinarith

lemma le_chord_outside {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    (a x : ℝ) (ha : a ∈ s) (ha1 : a + 1 ∈ s) (hx : x ∈ s)
    (hout : x ≤ a ∨ a + 1 ≤ x) : f x ≤ chord f a x := by
  have hh := chord_le_outside hf.neg a x ha ha1 hx hout
  simp only [chord, Pi.neg_apply] at hh ⊢
  linarith

noncomputable def patchLower (L : ℝ → ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  max (L x) (chord L a x)

noncomputable def patchUpper (U : ℝ → ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  min (U x) (chord U a x)

lemma nat_outside_unit (a n : ℕ) : (n : ℝ) ≤ a ∨ (a : ℝ) + 1 ≤ n := by
  by_cases hn : n ≤ a
  · exact Or.inl (by exact_mod_cast hn)
  · exact Or.inr (by exact_mod_cast (show a + 1 ≤ n by omega))

lemma patchLower_nat {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (a n : ℕ) :
    patchLower L a n = L n := by
  apply max_eq_left
  exact chord_le_outside h.lower_convex _ _ (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) (nat_outside_unit a n)

lemma patchUpper_nat {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (a n : ℕ) :
    patchUpper U a n = U n := by
  apply min_eq_left
  exact le_chord_outside h.upper_concave _ _ (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)
    (show (0 : ℝ) ≤ (a : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ n from Nat.cast_nonneg n) (nat_outside_unit a n)

lemma patch_dominates (L U : ℝ → ℝ) (a : ℕ) :
    Dominates (patchLower L a) (patchUpper U a) L U :=
  ⟨fun _ => le_max_left _ _, fun _ _ => min_le_left _ _⟩

/-- A lattice chord patch preserves every invariant needed by Jensen transfer. -/
theorem Regular.patch {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U) (a : ℕ) :
    Regular d (patchLower L a) (patchUpper U a) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hLa0 : 0 ≤ L ((a : ℝ) + 1) - L a := sub_nonneg.mpr (h.lower_mono (by linarith))
  have hLa1 : L ((a : ℝ) + 1) - L a ≤ d := by
    simpa using h.lower_lip a ((a : ℝ) + 1) (by linarith)
  have hUa : d ≤ U ((a : ℝ) + 1) - U a := by
    simpa using h.upper_growth a ((a : ℝ) + 1) ha (by linarith)
  refine ⟨h.density_nonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (h.lower_nonneg x).trans (le_max_left _ _)
  · intro x hx
    have hc := chord_le_outside h.lower_convex (a : ℝ) x
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) (Or.inl (hx.trans ha))
    rw [patchLower, max_eq_left hc, h.lower_zero x hx]
  · exact h.lower_convex.sup (chord_convex L a)
  · intro x y hxy
    apply max_le_max (h.lower_mono hxy)
    unfold chord
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hLa0]
  · intro x y hxy
    have hch : chord L a y - chord L a x ≤ d * (y - x) := by
      unfold chord
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hLa1)]
    exact (max_sub_max_le_max (L y) (chord L a y) (L x) (chord L a x)).trans
      (max_le (h.lower_lip x y hxy) hch)
  · simpa only [Nat.cast_zero, h.upper_zero] using patchUpper_nat h a 0
  · exact h.upper_concave.inf
      ((chord_concave U a).subset (Set.subset_univ _) (convex_Ici 0))
  · intro x y hx hxy
    have hch : d * (y - x) ≤ chord U a y - chord U a x := by
      unfold chord
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hUa)]
    have hh := h.upper_growth x y hx hxy
    have h1 := min_le_left (U x) (chord U a x)
    have h2 := min_le_right (U x) (chord U a x)
    dsimp only [patchUpper]
    apply le_sub_iff_add_le.mpr
    exact le_min (by linarith) (by linarith)

#print axioms Regular.patch
end Erdos970.ContinuousInterval
