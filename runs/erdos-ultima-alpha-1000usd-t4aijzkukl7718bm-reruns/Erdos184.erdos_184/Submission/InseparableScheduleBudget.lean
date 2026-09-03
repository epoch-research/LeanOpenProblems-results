import FormalConjecturesUtil

/-!
A limitation of an abstract target-only incidence accounting scheme.
Uncharged vertices are explicitly required to retain their residual count.
This is not a lower bound for actual graph cycle decompositions.
-/
open scoped BigOperators Classical
namespace Erdos184.InseparableScheduleBudget

/-- The residual half-degree potential. -/
noncomputable def potential (r : ℕ) : ℝ := ∑ j ∈ Finset.range r, 1 / (2 * (j : ℝ) + 3)

lemma potential_zero : potential 0 = 0 := by simp [potential]

lemma potential_succ (r : ℕ) :
    potential (r+1) = potential r + 1 / (2 * (r : ℝ) + 3) := by
  simp [potential, Finset.sum_range_succ]

lemma potential_step {a b : ℕ} (h : a = b+1) :
    potential a = potential b + 1 / (2 * (a : ℝ) + 1) := by
  subst a
  rw [potential_succ]
  congr 2
  push_cast
  ring

variable {V : Type*} [Fintype V]

/-- A charged step spends at most one unit of potential. The cardinality
condition is the necessary degree condition from target inseparability. -/
lemma one_step (T : Finset V) (before after : V → ℕ)
    (hsel : ∀ v ∈ T, before v = after v + 1)
    (hkeep : ∀ v ∉ T, before v = after v)
    (hdegree : ∀ v ∈ T, T.card ≤ 2 * before v + 1) :
    (∑ v, potential (before v)) ≤ (∑ v, potential (after v)) + 1 := by
  have hid (v : V) : potential (before v) = potential (after v) +
      if v ∈ T then 1 / (2 * (before v : ℝ) + 1) else 0 := by
    by_cases hv : v ∈ T
    · simpa [hv] using potential_step (hsel v hv)
    · simp [hv, hkeep v hv]
  have hsum : (∑ v, potential (before v)) = (∑ v, potential (after v)) +
      ∑ v ∈ T, 1 / (2 * (before v : ℝ) + 1) := by
    simp_rw [hid]
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum]
  apply add_le_add le_rfl
  by_cases hT : T.Nonempty
  · have hpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
    calc
      (∑ v ∈ T, 1 / (2 * (before v : ℝ) + 1)) ≤ ∑ _v ∈ T, 1 / (T.card : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        apply one_div_le_one_div_of_le hpos
        exact_mod_cast hdegree v hv
      _ = 1 := by simp [ne_of_gt hpos]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]

/-- Groups may be chosen adaptively and have unequal residual degrees.
Only the stated charged-incidence schedule is being bounded. -/
lemma schedule_budget (p : ℕ) (T : ℕ → Finset V) (r : ℕ → V → ℕ)
    (hsel : ∀ i < p, ∀ v ∈ T i, r i v = r (i+1) v + 1)
    (hkeep : ∀ i < p, ∀ v ∉ T i, r i v = r (i+1) v)
    (hdegree : ∀ i < p, ∀ v ∈ T i, (T i).card ≤ 2 * r i v + 1) :
    (∑ v, potential (r 0 v)) ≤ (p : ℝ) + ∑ v, potential (r p v) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp := ih (fun i hi => hsel i (by omega))
      (fun i hi => hkeep i (by omega)) (fun i hi => hdegree i (by omega))
    have hs := one_step (T p) (r p) (r (p+1)) (hsel p (by omega))
      (hkeep p (by omega)) (hdegree p (by omega))
    push_cast
    linarith

lemma exhausted_budget (p : ℕ) (T : ℕ → Finset V) (r : ℕ → V → ℕ)
    (hsel : ∀ i < p, ∀ v ∈ T i, r i v = r (i+1) v + 1)
    (hkeep : ∀ i < p, ∀ v ∉ T i, r i v = r (i+1) v)
    (hdegree : ∀ i < p, ∀ v ∈ T i, (T i).card ≤ 2 * r i v + 1)
    (hend : ∀ v, r p v = 0) :
    (∑ v, potential (r 0 v)) ≤ (p : ℝ) := by
  simpa [hend, potential_zero] using schedule_budget p T r hsel hkeep hdegree

lemma constant_initial_budget (p d : ℕ) (T : ℕ → Finset V) (r : ℕ → V → ℕ)
    (hsel : ∀ i < p, ∀ v ∈ T i, r i v = r (i+1) v + 1)
    (hkeep : ∀ i < p, ∀ v ∉ T i, r i v = r (i+1) v)
    (hdegree : ∀ i < p, ∀ v ∈ T i, (T i).card ≤ 2 * r i v + 1)
    (hstart : ∀ v, r 0 v = d) (hend : ∀ v, r p v = 0) :
    (Fintype.card V : ℝ) * potential d ≤ (p : ℝ) := by
  simpa [hstart] using exhausted_budget p T r hsel hkeep hdegree hend

/-- Comparison with one third of the usual harmonic sum. -/
lemma harmonic_le (r : ℕ) :
    (∑ j ∈ Finset.range r, 1 / ((j : ℝ) + 1)) / 3 ≤ potential r := by
  rw [potential, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [div_div]
  apply one_div_le_one_div_of_le
  · positivity
  · have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith

lemma potential_tendsto : Filter.Tendsto potential Filter.atTop Filter.atTop := by
  have hh := Real.tendsto_sum_range_one_div_nat_succ_atTop.atTop_div_const
    (by norm_num : (0 : ℝ) < 3)
  apply Filter.tendsto_atTop_mono harmonic_le hh

/-- There is no uniform cost per vertex for schedules satisfying exactly
these incidence-accounting assumptions. This does not assert that cycles
cannot remove uncharged incidences, or rule out accounting for those gains. -/
lemma unbounded_cost_per_vertex [Nonempty V] (C : ℝ) :
    ∃ d : ℕ, ∀ (p : ℕ) (T : ℕ → Finset V) (r : ℕ → V → ℕ),
      (∀ i < p, ∀ v ∈ T i, r i v = r (i+1) v + 1) →
      (∀ i < p, ∀ v ∉ T i, r i v = r (i+1) v) →
      (∀ i < p, ∀ v ∈ T i, (T i).card ≤ 2 * r i v + 1) →
      (∀ v, r 0 v = d) → (∀ v, r p v = 0) →
      C * (Fintype.card V : ℝ) < (p : ℝ) := by
  have he : ∀ᶠ d in Filter.atTop, C < potential d :=
    potential_tendsto (Filter.eventually_gt_atTop C)
  obtain ⟨d,hd⟩ := he.exists
  refine ⟨d,?_⟩
  intro p T r hsel hkeep hdegree hstart hend
  have hbudget := constant_initial_budget p d T r hsel hkeep hdegree hstart hend
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hh := mul_lt_mul_of_pos_right hd hn
  nlinarith

end Erdos184.InseparableScheduleBudget
