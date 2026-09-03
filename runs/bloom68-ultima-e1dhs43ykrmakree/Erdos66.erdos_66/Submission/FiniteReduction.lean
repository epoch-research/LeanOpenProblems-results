import FormalConjecturesUtil

/-!
A finite-prefix compactness reduction for the logarithmic representation problem.
This file is independent of Submission.Spec. It does not establish the necessary
finite witnesses and does not settle either theorem in that file.
-/

namespace Erdos66FiniteReduction

open Filter AdditiveCombinatorics
open scoped Topology Classical

/-- Local Boolean conditions with consistent finite satisfiability have a common model. -/
theorem exists_of_finite_prefix
    (P : ℕ → (ℕ → Bool) → Prop)
    (hlocal : ∀ n f g, (∀ k ≤ n, f k = g k) → (P n f ↔ P n g))
    (hfinite : ∀ N, ∃ f, ∀ n ≤ N, P n f) : ∃ f, ∀ n, P n f := by
  let C : ℕ → Set (ℕ → Bool) := fun n ↦ {f | P n f}
  have hclosed (n : ℕ) : IsClosed (C n) := by
    let extend : (Fin (n + 1) → Bool) → ℕ → Bool := fun p k ↦
      if h : k ≤ n then p ⟨k, Nat.lt_succ_of_le h⟩ else false
    let restrict : (ℕ → Bool) → Fin (n + 1) → Bool := fun f k ↦ f k.val
    have heq : C n = restrict ⁻¹' {p | P n (extend p)} := by
      ext f
      change P n f ↔ P n (extend (restrict f))
      apply hlocal
      intro k hk
      simp [extend, restrict, hk]
    rw [heq]
    exact (isClosed_discrete _).preimage (continuous_pi fun k ↦ continuous_apply k.val)
  have hFIP (s : Finset ℕ) : (⋂ n ∈ s, C n).Nonempty := by
    obtain ⟨f, hf⟩ := hfinite (s.sup id)
    refine ⟨f, ?_⟩
    simp only [Set.mem_iInter]
    intro n hn
    exact hf n (Finset.le_sup (f := id) hn)
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hclosed hFIP
  exact ⟨f, by simpa [C] using hf⟩

/-- An ordinary representation count only depends on the indicated finite prefix. -/
theorem sumRep_local {A B : Set ℕ} (n : ℕ)
    (h : ∀ k ≤ n, k ∈ A ↔ k ∈ B) : sumRep A n = sumRep B n := by
  rw [sumRep_def, sumRep_def]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases hp : p ∈ Finset.antidiagonal n
  · have hs := Finset.mem_antidiagonal.mp hp
    have h₁ := h p.1 (by omega)
    have h₂ := h p.2 (by omega)
    simp only [hp, true_and, h₁, h₂]
  · simp [hp]

/-- One fixed vanishing error schedule, feasible at every finite horizon, suffices.
The quantifier order is essential: the schedule cannot depend on the horizon. -/
theorem exists_limit_of_finite_schedule (c : ℝ) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hfinite : ∀ N, ∃ A : Set ℕ, ∀ n ≤ N,
      |(sumRep A n : ℝ) / Real.log n - c| ≤ e n) :
    ∃ A : Set ℕ, Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  let P : ℕ → (ℕ → Bool) → Prop := fun n f ↦
    |(sumRep {k | f k = true} n : ℝ) / Real.log n - c| ≤ e n
  have hlocal : ∀ n f g, (∀ k ≤ n, f k = g k) → (P n f ↔ P n g) := by
    intro n f g hfg
    have hr : sumRep {k | f k = true} n = sumRep {k | g k = true} n := by
      apply sumRep_local
      intro k hk
      simp only [Set.mem_setOf_eq, hfg k hk]
    simp only [P, hr]
  have hfin : ∀ N, ∃ f, ∀ n ≤ N, P n f := by
    intro N
    obtain ⟨A, hA⟩ := hfinite N
    refine ⟨fun k ↦ decide (k ∈ A), ?_⟩
    intro n hn
    simpa [P] using hA n hn
  obtain ⟨f, hf⟩ := exists_of_finite_prefix P hlocal hfin
  refine ⟨{k | f k = true}, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun n ↦ dist_nonneg)
    (Eventually.of_forall fun n ↦ ?_) he
  simpa only [Real.dist_eq] using hf n

/-- Exact finite-feasibility formulation of the conjecture. This equivalence does
not prove either side; it identifies the uniform finite witness obligation. -/
theorem logarithmic_limit_iff_finite_schedule :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∃ (c : ℝ) (e : ℕ → ℝ), c ≠ 0 ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ N, ∃ B : Finset ℕ, (∀ b ∈ B, b ≤ N) ∧
        ∀ n ≤ N, |(sumRep (B : Set ℕ) n : ℝ) / Real.log n - c| ≤ e n := by
  constructor
  · rintro ⟨A, c, hc, hlim⟩
    refine ⟨c, (fun n ↦ |(sumRep A n : ℝ) / Real.log n - c|), hc, ?_, ?_⟩
    · simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.mp hlim
    · intro N
      let B := (Finset.range (N + 1)).filter (fun k ↦ k ∈ A)
      refine ⟨B, ?_, ?_⟩
      · intro b hb
        have hb' := (Finset.mem_filter.mp hb).1
        have := Finset.mem_range.mp hb'
        omega
      · intro n hn
        have hr : sumRep (B : Set ℕ) n = sumRep A n := by
          apply sumRep_local
          intro k hk
          have hkN : k ≤ N := by omega
          simp [B, hkN]
        rw [hr]
  · rintro ⟨c, e, hc, he, hfinite⟩
    have hsets : ∀ N, ∃ A : Set ℕ, ∀ n ≤ N,
        |(sumRep A n : ℝ) / Real.log n - c| ≤ e n := by
      intro N
      obtain ⟨B, _, hB⟩ := hfinite N
      exact ⟨(B : Set ℕ), hB⟩
    obtain ⟨A, hA⟩ := exists_limit_of_finite_schedule c e he hsets
    exact ⟨A, c, hc, hA⟩

/-- The exact dual obstruction criterion. To disprove the conjecture, one must
obstruct every nonzero coefficient and every fixed vanishing error schedule.
This theorem does not establish any such obstruction. -/
theorem no_limit_iff_finite_obstructions :
    (¬ ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∀ (c : ℝ) (e : ℕ → ℝ), c ≠ 0 → Tendsto e atTop (𝓝 0) →
      ∃ N, ∀ B : Finset ℕ, (∀ b ∈ B, b ≤ N) →
        ∃ n, n ≤ N ∧ e n < |(sumRep (B : Set ℕ) n : ℝ) / Real.log n - c| := by
  rw [logarithmic_limit_iff_finite_schedule]
  push_neg
  rfl

#print axioms exists_of_finite_prefix
#print axioms sumRep_local
#print axioms exists_limit_of_finite_schedule
#print axioms logarithmic_limit_iff_finite_schedule
#print axioms no_limit_iff_finite_obstructions

end Erdos66FiniteReduction
