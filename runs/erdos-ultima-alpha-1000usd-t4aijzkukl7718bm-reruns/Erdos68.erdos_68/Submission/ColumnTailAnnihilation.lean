import Submission.Development

/-!
Exact annihilation of an irrational factorial-power column by a finite
rational tail operator forces its retained coefficient to vanish.
This is an auxiliary obstruction, not a settlement of Erdős 68.
-/

namespace ColumnTailAnnihilation

open Finset Erdos68Development

variable {ι : Type*}

noncomputable def tailForm (s : Finset ι) (w B : ι → ℚ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, (w i : ℝ) * (x - (B i : ℝ))

lemma tailForm_eq (s : Finset ι) (w B : ι → ℚ) (x : ℝ) :
    tailForm s w B x = ((∑ i ∈ s, w i : ℚ) : ℝ) * x -
      ((∑ i ∈ s, w i * B i : ℚ) : ℝ) := by
  simp only [tailForm, mul_sub, sum_sub_distrib, Rat.cast_sum, Rat.cast_mul,
    sum_mul]

/-- The vanishing is equivalent to two rational equations. In particular,
a nonzero coefficient vector is not sufficient to retain the endpoint. -/
theorem annihilate_iff (s : Finset ι) (w B : ι → ℚ) (x : ℝ)
    (hx : Irrational x) :
    tailForm s w B x = 0 ↔
      (∑ i ∈ s, w i) = 0 ∧ (∑ i ∈ s, w i * B i) = 0 := by
  rw [tailForm_eq]
  constructor
  · intro h
    have hs : (∑ i ∈ s, w i) = 0 := by
      by_contra hs
      have hi := hx.ratCast_mul hs
      exact hi ⟨∑ i ∈ s, w i * B i, (sub_eq_zero.mp h).symm⟩
    refine ⟨hs, ?_⟩
    rw [hs, Rat.cast_zero, zero_mul, zero_sub, neg_eq_zero] at h
    exact_mod_cast h
  · rintro ⟨hs, hb⟩
    simp [hs, hb]

def columnPrefix (r N : ℕ) : ℚ :=
  ∑ k ∈ range N, 1 / ((k + 2).factorial : ℚ) ^ (r + 1)

lemma columnPrefix_cast (r N : ℕ) :
    (columnPrefix r N : ℝ) = ∑ k ∈ range N, powerTerm r k := by
  simp [columnPrefix, powerTerm]

/-- The sample indices and the rational weights are arbitrary and may have
been chosen using any additional parameter. Exact column cancellation at
these samples still forces the sum of the weights to be zero. -/
theorem column_annihilate_iff (s : Finset ι) (w : ι → ℚ)
    (N : ι → ℕ) (r : ℕ) :
    (∑ i ∈ s, (w i : ℝ) *
      ((∑' k : ℕ, powerTerm r k) - ∑ k ∈ range (N i), powerTerm r k)) = 0 ↔
      (∑ i ∈ s, w i) = 0 ∧
      (∑ i ∈ s, w i * columnPrefix r (N i)) = 0 := by
  simpa only [tailForm, columnPrefix_cast] using
    annihilate_iff s w (fun i => columnPrefix r (N i))
      (∑' k : ℕ, powerTerm r k) (irrational_sum_powerTerm r)

/-- Reusing such weights with other rational prefixes gives an expression
independent of the endpoint. Thus exact column cancellation cannot by itself
produce a linear form with a nonzero coefficient of the original sum. -/
theorem endpoint_independent_of_column_annihilation
    (s : Finset ι) (w : ι → ℚ) (N : ι → ℕ) (r : ℕ)
    (h : (∑ i ∈ s, (w i : ℝ) *
      ((∑' k : ℕ, powerTerm r k) - ∑ k ∈ range (N i), powerTerm r k)) = 0)
    (B : ι → ℚ) (x y : ℝ) : tailForm s w B x = tailForm s w B y := by
  have hs := ((column_annihilate_iff s w N r).mp h).1
  simp [tailForm_eq, hs]

end ColumnTailAnnihilation

#print axioms ColumnTailAnnihilation.annihilate_iff
#print axioms ColumnTailAnnihilation.column_annihilate_iff
#print axioms ColumnTailAnnihilation.endpoint_independent_of_column_annihilation
