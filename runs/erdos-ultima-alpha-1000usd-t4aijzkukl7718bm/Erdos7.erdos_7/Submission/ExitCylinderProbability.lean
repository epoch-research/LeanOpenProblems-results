import Submission.ExitDepthDecomposition

/-! Exact probabilities of one prefix inside a uniform prefix cylinder. -/
namespace Erdos7ExitCylinderProbability
open scoped BigOperators
open Erdos7ConditionalExitMeasure Erdos7ExitDepthDecomposition
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma prefixMatch_trans {p k a E : ℕ} (hka : k ≤ a) (haE : a ≤ E)
    (w : Fin k → Fin p) (v : Fin a → Fin p) (y : Fin E → Fin p)
    (hwv : prefixMatch hka w v) (hvy : prefixMatch haE v y) :
    prefixMatch (hka.trans haE) w y := by
  intro i
  exact (hvy (Fin.castLE hka i)).trans (hwv i)

lemma prefixMatch_intersection {p k a E : ℕ} (hka : k ≤ a) (haE : a ≤ E)
    (w : Fin k → Fin p) (v : Fin a → Fin p) (y : Fin E → Fin p) :
    (prefixMatch (hka.trans haE) w y ∧ prefixMatch haE v y) ↔
      (prefixMatch haE v y ∧ prefixMatch hka w v) := by
  constructor
  · rintro ⟨hw,hv⟩
    refine ⟨hv, ?_⟩
    intro i
    exact (hv (Fin.castLE hka i)).symm.trans (hw i)
  · rintro ⟨hv,hw⟩
    exact ⟨prefixMatch_trans hka haE w v y hw hv,hv⟩

theorem cylinder_probability_long {p k a E : ℕ} (hp : 1 ≤ p)
    (hka : k ≤ a) (haE : a ≤ E) (w : Fin k → Fin p) (v : Fin a → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch haE v y then
      cylinderDensity (hka.trans haE) w y else 0) =
      if prefixMatch hka w v then 1/(p : ℚ)^(a-k) else 0 := by
  by_cases h : prefixMatch hka w v
  · rw [if_pos h]
    have he (y : Fin E → Fin p) :
        (if prefixMatch haE v y then cylinderDensity (hka.trans haE) w y else 0) =
          (if prefixMatch haE v y then 1 else 0)/(p : ℚ)^(E-k) := by
      by_cases hy : prefixMatch haE v y
      · have hw := prefixMatch_trans hka haE w v y h hy
        simp [hy, cylinderDensity, hw]
      · simp [hy]
    simp_rw [he]
    rw [← Finset.sum_div]
    have hc : (∑ y : Fin E → Fin p, if prefixMatch haE v y then (1 : ℚ) else 0) =
        (p : ℚ)^(E-a) := by exact_mod_cast prefix_count haE v
    rw [hc]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hx : E-k=(E-a)+(a-k) := by omega
    rw [hx,pow_add]
    field_simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : prefixMatch haE v y
    · have hw : ¬ prefixMatch (hka.trans haE) w y := by
        intro hw
        exact h ((prefixMatch_intersection hka haE w v y).mp ⟨hw,hy⟩).2
      simp [hy, cylinderDensity, hw]
    · simp [hy]

theorem cylinder_probability_short {p a k E : ℕ} (hp : 1 ≤ p)
    (hak : a ≤ k) (hkE : k ≤ E) (v : Fin a → Fin p) (w : Fin k → Fin p) :
    (∑ y : Fin E → Fin p, if prefixMatch (hak.trans hkE) v y then
      cylinderDensity hkE w y else 0) =
      if prefixMatch hak v w then 1 else 0 := by
  by_cases h : prefixMatch hak v w
  · rw [if_pos h]
    calc
      _ = ∑ y : Fin E → Fin p, cylinderDensity hkE w y := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hw : prefixMatch hkE w y
        · simp only [if_pos (prefixMatch_trans hak hkE v w y h hw)]
        · simp [cylinderDensity,hw]
      _ = 1 := cylinderDensity_mass hp hkE w
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : prefixMatch (hak.trans hkE) v y
    · have hw : ¬ prefixMatch hkE w y := by
        intro hw
        exact h ((prefixMatch_intersection hak hkE v w y).mp ⟨hy,hw⟩).2
      simp [hy,cylinderDensity,hw]
    · simp [hy]

lemma code_before {p b : ℕ} (stem exit : Fin p) (i : Fin (b+1)) (hi : i.val < b) :
    code stem exit b i=stem := by
  induction b with
  | zero => omega
  | succ b ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

lemma code_last {p : ℕ} (stem exit : Fin p) (b : ℕ) :
    code stem exit b (Fin.last b)=exit := by
  induction b with
  | zero => rfl
  | succ b ih => exact ih

lemma code_prefix_stem {p a b : ℕ} (stem exit : Fin p) (hab : a ≤ b) :
    prefixMatch (hab.trans (Nat.le_succ b)) (fun _ : Fin a => stem) (code stem exit b) := by
  intro i
  exact code_before stem exit _ (lt_of_lt_of_le i.isLt hab)

/-- In an exit layer b, every stem prefix of length at most b holds surely. -/
theorem stem_before_exit_probability {p a b E : ℕ} (hp : 1 ≤ p)
    (stem exit : Fin p) (hab : a ≤ b) (hb : b+1 ≤ E) :
    (∑ y : Fin E → Fin p, if prefixMatch (hab.trans ((Nat.le_succ b).trans hb))
      (fun _ : Fin a => stem) y then cylinderDensity hb (code stem exit b) y else 0)=1 := by
  have hh := cylinder_probability_short hp (hab.trans (Nat.le_succ b)) hb
    (fun _ : Fin a => stem) (code stem exit b)
  simpa only [if_pos (code_prefix_stem stem exit hab)] using hh

/-- After the selected exit, an all-stem prefix is impossible. -/
theorem stem_after_exit_probability {p a b E : ℕ} (hp : 1 ≤ p)
    (stem exit : Fin p) (hne : exit ≠ stem) (hba : b+1 ≤ a) (ha : a ≤ E) :
    (∑ y : Fin E → Fin p, if prefixMatch ha (fun _ : Fin a => stem) y then
      cylinderDensity (hba.trans ha) (code stem exit b) y else 0)=0 := by
  have hn : ¬ prefixMatch hba (code stem exit b) (fun _ : Fin a => stem) := by
    intro h
    have hh := h (Fin.last b)
    rw [code_last] at hh
    exact hne hh.symm
  simpa only [if_neg hn] using cylinder_probability_long hp hba ha
    (code stem exit b) (fun _ : Fin a => stem)

/-- A future prefix that agrees with the exit word has the usual uniform
suffix probability, not the larger unconditional conditional-exit mass. -/
theorem terminal_after_exit_probability {p a b E : ℕ} (hp : 1 ≤ p)
    (stem exit : Fin p) (hba : b+1 ≤ a) (ha : a ≤ E) (v : Fin a → Fin p)
    (hv : prefixMatch hba (code stem exit b) v) :
    (∑ y : Fin E → Fin p, if prefixMatch ha v y then
      cylinderDensity (hba.trans ha) (code stem exit b) y else 0)=
      1/(p : ℚ)^(a-(b+1)) := by
  simpa only [if_pos hv] using cylinder_probability_long hp hba ha (code stem exit b) v

#print axioms cylinder_probability_long
#print axioms cylinder_probability_short
#print axioms stem_before_exit_probability
#print axioms stem_after_exit_probability
#print axioms terminal_after_exit_probability
end Erdos7ExitCylinderProbability
