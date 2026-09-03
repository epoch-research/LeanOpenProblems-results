import Submission.ConditionalExitMeasure

/-! Terminal prefixes exclude every subsequent all-stem prefix. -/
namespace Erdos7ExclusivePrefix
open Erdos7ConditionalExitMeasure
set_option autoImplicit false

lemma firstExit_eq_none_iff {p E : ℕ} (stem : Fin p) (v : Fin E → Fin p) :
    firstExit stem E v = none ↔ ∀ i, v i = stem := by
  induction E with
  | zero => simp [firstExit]
  | succ E ih =>
    rw [Fin.forall_fin_succ]
    by_cases h : v 0 = stem
    · simpa only [firstExit, if_pos h, h, true_and, Fin.tail] using ih (Fin.tail v)
    · simp [firstExit, h]

/-- A non-stem prefix cannot meet any longer stem cylinder. -/
theorem terminal_stem_disjoint {p a b E : ℕ} (stem : Fin p)
    (ha : a ≤ E) (hb : b ≤ E) (hab : a ≤ b) (v : Fin a → Fin p)
    (hv : firstExit stem a v ≠ none) (y : Fin E → Fin p) :
    ¬ (prefixMatch ha v y ∧ prefixMatch hb (fun _ => stem) y) := by
  intro h
  apply hv
  rw [firstExit_eq_none_iff]
  intro i
  have hs := h.2 (Fin.castLE hab i)
  have he : Fin.castLE hb (Fin.castLE hab i) = Fin.castLE ha i := by rfl
  rw [he] at hs
  exact (h.1 i).symm.trans hs

/-- In particular the terminal and stem counts at one level have product0,
for arbitrary finite lists of terminal prefixes and arbitrary nonnegative
weights. No equality of terminal prefixes is assumed. -/
theorem terminal_stem_count_zero {p a E : ℕ} {J : Type*} [Fintype J]
    (stem : Fin p) (ha : a ≤ E) (v : J → Fin a → Fin p)
    (hv : ∀ j, firstExit stem a (v j) ≠ none) (w : J → ℝ)
    (y : Fin E → Fin p) :
    (∑ j, if prefixMatch ha (v j) y then w j else 0) *
      (if prefixMatch ha (fun _ => stem) y then (1 : ℝ) else 0) = 0 := by
  classical
  by_cases h : prefixMatch ha (fun _ => stem) y
  · simp only [if_pos h, mul_one]
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro ht
    exact terminal_stem_disjoint stem ha ha (Nat.le_refl _) (v j) (hv j) y ⟨ht,h⟩
  · simp [h]

#print axioms firstExit_eq_none_iff
#print axioms terminal_stem_disjoint
#print axioms terminal_stem_count_zero
end Erdos7ExclusivePrefix
