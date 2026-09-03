import Submission.IntervalHullWindow
import Submission.IntervalHullSoundness

/-!
# Stabilization of short-length upper bounds

A sound nonnegative lower bound vanishes at every length at most the number of
sieve coordinates. Consequently the closed upper update at a new modulus `p`
is unchanged at lengths `n < (k+1)*(p-1)`. This does not establish lower-bound
positivity at quadratic lengths.
-/
namespace Erdos970.IntervalRescaling.IntegerHull

lemma window_div (n p : ℕ) (hp : 2 ≤ p) :
    (n + n / (p - 1)) / p = n / (p - 1) := by
  have hp1 : 0 < p - 1 := by omega
  have hps : p - 1 + 1 = p := by omega
  have h1 := Nat.div_mul_le_self n (p - 1)
  have h2 := Nat.lt_mul_div_succ n hp1
  apply Nat.div_eq_of_lt_le <;> nlinarith

/-- If the old lower bound is zero at the end of the relevant rescaled window,
then adjoining this modulus does not change the upper bound at length `n`. -/
theorem Compatible.upperHull_eq_of_lower_zero {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) (n : ℕ)
    (hz : l (n / (p - 1)) = 0) : upperHull (rawUpper p l u) n = u n := by
  have hz' (m : ℕ) (hm : m ≤ n + n / (p - 1)) : l (m / p) = 0 := by
    apply le_antisymm _ (hl _)
    have hdiv := Nat.div_le_div_right (c := p) hm
    rw [window_div n p hp] at hdiv
    simpa only [hz] using h.lower_mono hl hdiv
  rw [h.upperHull_eq_window hl p hp n]
  apply le_antisymm
  · have hh := Finset.inf'_le (rawUpper p l u)
      (Finset.mem_Icc.mpr ⟨le_refl n, Nat.le_add_right n (n / (p - 1))⟩)
    simpa only [rawUpper, hz' n (Nat.le_add_right _ _), sub_zero] using hh
  · apply Finset.le_inf'
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    dsimp [rawUpper]
    rw [hz' m hm'.2, sub_zero]
    exact h.upper_mono hl hm'.1

/-- Assigning residue `i` to coordinate `i` covers the first `k` positions. -/
lemma count_diagonal_zero (p : ℕ → ℕ) (k m : ℕ) (hm : m ≤ k) : count p id k m = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨hxm, hxa⟩ := Finset.mem_filter.mp hx
  have hxl := Finset.mem_range.mp hxm
  exact hxa x (by omega) (Nat.ModEq.refl x)

lemma Bounds.lower_zero_under_card {p : ℕ → ℕ} {k : ℕ} {l u : ℕ → ℝ}
    (h : Bounds p k l u) (hl : ∀ n, 0 ≤ l n) (m : ℕ) (hm : m ≤ k) : l m = 0 := by
  have hh := (h m id).1
  rw [count_diagonal_zero p k m hm, Nat.cast_zero] at hh
  exact le_antisymm hh (hl m)

/-- A directly usable stabilization criterion for any sound compatible pair. -/
theorem Bounds.upper_step_eq {p : ℕ → ℕ} {k : ℕ} {l u : ℕ → ℝ}
    (h : Bounds p k l u) (hshape : Compatible l u) (hl : ∀ n, 0 ≤ l n)
    (hp : 2 ≤ p k) (n : ℕ) (hn : n < (k + 1) * (p k - 1)) :
    upperHull (rawUpper (p k) l u) n = u n := by
  apply hshape.upperHull_eq_of_lower_zero hl (p k) hp n
  apply h.lower_zero_under_card hl
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega : 0 < p k - 1)).mpr hn)

#print axioms Compatible.upperHull_eq_of_lower_zero
#print axioms Bounds.lower_zero_under_card
#print axioms Bounds.upper_step_eq
end Erdos970.IntervalRescaling.IntegerHull
