import Submission.ContinuousIntervalOrdering

/-! Sorting the marginals in decreasing order is optimal for this continuous
interval-envelope recursion. This rules out improvement by reordering its stages;
it is not an impossibility theorem for other sieve methods. -/
namespace Erdos970.ContinuousInterval

lemma Dominates.refl (L U : ℝ → ℝ) : Dominates L U L U :=
  ⟨fun _ => le_rfl, fun _ _ => le_rfl⟩

lemma Dominates.trans {L₁ U₁ L₂ U₂ L₃ U₃ : ℝ → ℝ}
    (h₁ : Dominates L₁ U₁ L₂ U₂) (h₂ : Dominates L₂ U₂ L₃ U₃) :
    Dominates L₁ U₁ L₃ U₃ :=
  ⟨fun x => (h₂.1 x).trans (h₁.1 x), fun x hx => (h₁.2 x hx).trans (h₂.2 x hx)⟩

def run : List ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) × (ℝ → ℝ)
  | [], L, U => (L, U)
  | q :: qs, L, U => run qs (stepLower q L U) (stepUpper q L U)

theorem Dominates.run {L U L' U' : ℝ → ℝ} (h : Dominates L U L' U')
    (qs : List ℝ) (hq : ∀ q ∈ qs, 0 ≤ q ∧ q ≤ 1) :
    Dominates (ContinuousInterval.run qs L U).1 (ContinuousInterval.run qs L U).2
      (ContinuousInterval.run qs L' U').1 (ContinuousInterval.run qs L' U').2 := by
  induction qs generalizing L U L' U' with
  | nil => exact h
  | cons q qs ih =>
    have hq' := hq q List.mem_cons_self
    exact ih (h.step q hq'.1 hq'.2) (fun p hp => hq p (List.mem_cons_of_mem q hp))

theorem orderedInsert_dominates (d q : ℝ) (qs : List ℝ) (L U : ℝ → ℝ)
    (h : Regular d L U) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hqs : ∀ p ∈ qs, 0 ≤ p ∧ p ≤ 1 / 2) :
    Dominates (run (qs.orderedInsert (fun a b : ℝ => b ≤ a) q) L U).1
      (run (qs.orderedInsert (fun a b : ℝ => b ≤ a) q) L U).2
      (run (q :: qs) L U).1 (run (q :: qs) L U).2 := by
  induction qs generalizing d L U with
  | nil => exact Dominates.refl _ _
  | cons p ps ih =>
    have hp := hqs p List.mem_cons_self
    have hps : ∀ a ∈ ps, 0 ≤ a ∧ a ≤ 1 / 2 :=
      fun a ha => hqs a (List.mem_cons_of_mem p ha)
    by_cases hpq : p ≤ q
    · rw [List.orderedInsert_cons, if_pos hpq]
      exact Dominates.refl _ _
    · rw [List.orderedInsert_cons, if_neg hpq]
      have hi := ih (d * (1 - p)) (stepLower p L U) (stepUpper p L U)
        (h.step p hp.1 (by linarith [hp.2])) hps
      have hs := (adjacent_order_dominates d p q L U h hq0
        (le_of_not_ge hpq) hp.2).run ps (fun a ha =>
          ⟨(hps a ha).1, (hps a ha).2.trans (by norm_num)⟩)
      exact hi.trans hs

/-- Among orders related by sorting, decreasing marginals produce pointwise
larger lower bounds and smaller upper bounds. In particular the natural
increasing-prime order is already optimal within this recursion. -/
theorem insertionSort_dominates (d : ℝ) (qs : List ℝ) (L U : ℝ → ℝ)
    (h : Regular d L U) (hqs : ∀ q ∈ qs, 0 ≤ q ∧ q ≤ 1 / 2) :
    Dominates (run (qs.insertionSort (fun a b : ℝ => b ≤ a)) L U).1
      (run (qs.insertionSort (fun a b : ℝ => b ≤ a)) L U).2
      (run qs L U).1 (run qs L U).2 := by
  induction qs generalizing d L U with
  | nil => exact Dominates.refl _ _
  | cons q qs ih =>
    have hq := hqs q List.mem_cons_self
    have hrest : ∀ a ∈ qs, 0 ≤ a ∧ a ≤ 1 / 2 :=
      fun a ha => hqs a (List.mem_cons_of_mem q ha)
    have hsorted : ∀ a ∈ qs.insertionSort (fun a b : ℝ => b ≤ a), 0 ≤ a ∧ a ≤ 1 / 2 :=
      fun a ha => hrest a ((List.mem_insertionSort _).mp ha)
    rw [List.insertionSort_cons]
    have hi := orderedInsert_dominates d q (qs.insertionSort (fun a b : ℝ => b ≤ a))
      L U h hq.1 hq.2 hsorted
    have hs := ih (d * (1 - q)) (stepLower q L U) (stepUpper q L U)
      (h.step q hq.1 (by linarith [hq.2])) hrest
    exact hi.trans hs

#print axioms insertionSort_dominates
end Erdos970.ContinuousInterval
