import Submission.ContinuousIntervalPatched

/-! Finite chord patches implement exact linear interpolation on their selected
cells. They give the strongest convex/concave extensions of the fixed natural-
length values on those cells. This is not an asymptotic positivity theorem. -/
namespace Erdos970.ContinuousInterval

lemma le_chord_inside {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (a x : ℝ) (ha : a ∈ s) (ha1 : a + 1 ∈ s) (hx0 : a ≤ x) (hx1 : x ≤ a + 1) :
    f x ≤ chord f a x := by
  have hh := hf.2 ha ha1 (show 0 ≤ a + 1 - x by linarith)
    (show 0 ≤ x - a by linarith) (show (a + 1 - x) + (x - a) = 1 by ring)
  simp only [smul_eq_mul] at hh
  rw [show (a + 1 - x) * a + (x - a) * (a + 1) = x by ring] at hh
  unfold chord
  nlinarith

lemma chord_le_inside {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    (a x : ℝ) (ha : a ∈ s) (ha1 : a + 1 ∈ s) (hx0 : a ≤ x) (hx1 : x ≤ a + 1) :
    chord f a x ≤ f x := by
  have hh := le_chord_inside hf.neg a x ha ha1 hx0 hx1
  simp only [chord, Pi.neg_apply] at hh ⊢
  linarith

lemma chord_nat_congr {f g : ℝ → ℝ} (h : ∀ n : ℕ, f n = g n) (a : ℕ) (x : ℝ) :
    chord f a x = chord g a x := by
  have ha1 : f ((a : ℝ) + 1) = g ((a : ℝ) + 1) := by simpa using h (a + 1)
  simp only [chord, h a, ha1]

lemma chordPatches_nat {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (cells : List ℕ) (n : ℕ) :
    (chordPatches cells L U).1 n = L n ∧ (chordPatches cells L U).2 n = U n := by
  induction cells generalizing L U with
  | nil => exact ⟨rfl, rfl⟩
  | cons a cells ih =>
    simpa only [chordPatches, patchLower_nat h, patchUpper_nat h] using ih (h.patch a)

lemma chordPatches_contains_chord {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (cells : List ℕ) (a : ℕ) (ha : a ∈ cells) (x : ℝ) :
    chord L a x ≤ (chordPatches cells L U).1 x ∧
      (chordPatches cells L U).2 x ≤ chord U a x := by
  induction cells generalizing L U with
  | nil => simp at ha
  | cons b cells ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · have hh := chordPatches_dominates cells (patchLower L a) (patchUpper U a)
      constructor
      · exact (le_max_right _ _).trans (hh.1 x)
      · by_cases hx : 0 ≤ x
        · exact (hh.2 x hx).trans (min_le_right _ _)
        · -- Upper patches are minima even at negative inputs.
          have hmono : ∀ (cs : List ℕ) (A B : ℝ → ℝ),
              (chordPatches cs A B).2 x ≤ B x := by
            intro cs
            induction cs with
            | nil => intro A B; rfl
            | cons c cs ih =>
              intro A B
              exact (ih (patchLower A c) (patchUpper B c)).trans (min_le_left _ _)
          exact (hmono cells (patchLower L a) (patchUpper U a)).trans (min_le_right _ _)
    · have hh := ih (h.patch b) ha
      rw [chord_nat_congr (fun n => patchLower_nat h b n) a x,
        chord_nat_congr (fun n => patchUpper_nat h b n) a x] at hh
      exact hh

/-- Once a cell is selected, its values are exactly the linear interpolants of
its endpoints. Other selected cells neither disturb nor improve those values. -/
theorem chordPatches_eq_chord_on_cell {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (cells : List ℕ) (a : ℕ) (ha : a ∈ cells) (x : ℝ)
    (hx0 : (a : ℝ) ≤ x) (hx1 : x ≤ (a : ℝ) + 1) :
    (chordPatches cells L U).1 x = chord L a x ∧
      (chordPatches cells L U).2 x = chord U a x := by
  have hr := h.chordPatches cells
  have hn := chordPatches_nat h cells
  have hb := chordPatches_contains_chord h cells a ha x
  have hl := le_chord_inside hr.lower_convex (a : ℝ) x
    (Set.mem_univ _) (Set.mem_univ _) hx0 hx1
  have hu := chord_le_inside hr.upper_concave (a : ℝ) x
    (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)
    (show (0 : ℝ) ≤ (a : ℝ) + 1 by positivity) hx0 hx1
  rw [chord_nat_congr (fun n => (hn n).1) a x] at hl
  rw [chord_nat_congr (fun n => (hn n).2) a x] at hu
  exact ⟨le_antisymm hl hb.1, le_antisymm hb.2 hu⟩

/-- The lower interpolation is maximal among convex extensions with the same
natural values, and the upper interpolation is minimal among concave ones. -/
theorem chordPatches_optimal_on_cell {d d' : ℝ} {L U L' U' : ℝ → ℝ}
    (h : Regular d L U) (h' : Regular d' L' U')
    (hL : ∀ n : ℕ, L' n = L n) (hU : ∀ n : ℕ, U' n = U n)
    (cells : List ℕ) (a : ℕ) (ha : a ∈ cells) (x : ℝ)
    (hx0 : (a : ℝ) ≤ x) (hx1 : x ≤ (a : ℝ) + 1) :
    L' x ≤ (chordPatches cells L U).1 x ∧ (chordPatches cells L U).2 x ≤ U' x := by
  have he := chordPatches_eq_chord_on_cell h cells a ha x hx0 hx1
  rw [he.1, he.2]
  have hl := le_chord_inside h'.lower_convex (a : ℝ) x
    (Set.mem_univ _) (Set.mem_univ _) hx0 hx1
  have hu := chord_le_inside h'.upper_concave (a : ℝ) x
    (show (0 : ℝ) ≤ a from Nat.cast_nonneg a)
    (show (0 : ℝ) ≤ (a : ℝ) + 1 by positivity) hx0 hx1
  simpa only [chord_nat_congr hL a x, chord_nat_congr hU a x] using And.intro hl hu

/-- Lattice patches preserve the safe zero-at-cardinality pruning rule. -/
theorem patched_lower_at_card_zero (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    (patchedEnvelope Q cells k).1 (k : ℝ) = 0 := by
  induction k with
  | zero => simp [patchedEnvelope]
  | succ k ih =>
    have hQQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hprev := ih hQQ
    have hreg := patchedEnvelope_regular Q cells k hQQ
    have hqk := hQ k (by omega)
    have hl := hreg.lower_lip (k : ℝ) ((k : ℝ) + 1) (by linarith)
    rw [hprev] at hl
    let v : ℝ := 1 + (((k : ℝ) + 1) - 1) * Q k
    have hv : 1 ≤ v := by
      dsimp [v]
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hqk.1]
    have hu := hreg.upper_growth 0 v (by norm_num) (by linarith)
    rw [hreg.upper_zero] at hu
    have hd := mul_le_mul_of_nonneg_left hv hreg.density_nonneg
    have hnp : (patchedEnvelope Q cells k).1 ((k : ℝ) + 1) -
        (patchedEnvelope Q cells k).2 v ≤ 0 := by nlinarith
    have hnat := (chordPatches_nat (hreg.step (Q k) hqk.1 hqk.2) (cells k) (k + 1)).1
    change (chordPatches (cells k) _ _).1 ((k + 1 : ℕ) : ℝ) = 0
    rw [hnat]
    simp only [stepLower, clip, Nat.cast_add, Nat.cast_one,
      max_eq_right (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
    exact max_eq_left hnp

theorem patched_lower_zero_of_le_card (Q : ℕ → ℝ) (cells : ℕ → List ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) (x : ℝ) (hx : x ≤ k) :
    (patchedEnvelope Q cells k).1 x = 0 := by
  have h := patchedEnvelope_regular Q cells k hQ
  have hh := h.lower_mono hx
  rw [patched_lower_at_card_zero Q cells k hQ] at hh
  exact le_antisymm hh (h.lower_nonneg x)

#print axioms patched_lower_zero_of_le_card
#print axioms chordPatches_eq_chord_on_cell
#print axioms chordPatches_optimal_on_cell
end Erdos970.ContinuousInterval
