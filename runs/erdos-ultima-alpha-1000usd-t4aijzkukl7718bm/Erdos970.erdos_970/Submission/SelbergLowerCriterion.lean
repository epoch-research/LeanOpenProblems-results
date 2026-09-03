import Submission.SelbergLower

/-! A fully quantitative, conditional survivor criterion from the finite Selberg lower weight. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_polynomial_interval_error {α : Type*} (A : Finset α)
    (c : α → ℝ) (S : α → Finset ι) (q : ι → ℝ)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ Finset.range m, ∑ a ∈ A, c a * hitMonomial (S a) (ω j)) -
      (m : ℝ) * average q (fun v => ∑ a ∈ A, c a * hitMonomial (S a) v)| ≤
      ∑ a ∈ A, |c a| := by
  classical
  rw [average_sum, Finset.sum_comm]
  simp_rw [average_mul_const, average_hitMonomial]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ A, |(∑ j ∈ Finset.range m, c a * hitMonomial (S a) (ω j)) -
        (m : ℝ) * (c a * ∏ i ∈ S a, q i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← Finset.mul_sum]
      have heq : c a * (∑ j ∈ Finset.range m, hitMonomial (S a) (ω j)) -
          (m : ℝ) * (c a * ∏ i ∈ S a, q i) =
          c a * ((∑ j ∈ Finset.range m, hitMonomial (S a) (ω j)) -
            (m : ℝ) * ∏ i ∈ S a, q i) := by ring
      rw [heq, abs_mul]
      simpa using mul_le_mul_of_nonneg_left (herr (S a)) (abs_nonneg (c a))

theorem majorant_hit_interval_error (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (U : Finset ι) :
    |(∑ j ∈ Finset.range m, hitMonomial U (ω j) * majorant q D (ω j)) -
      (m : ℝ) * average q (fun v => hitMonomial U v * majorant q D v)| ≤
      (D.card : ℝ)^2 := by
  classical
  have heq (v : ι → Bool) : hitMonomial U v * majorant q D v =
      ∑ a ∈ D ×ˢ D, (coefficient q D a.1 * coefficient q D a.2) *
        hitMonomial (U ∪ (a.1 ∪ a.2)) v := by
    rw [majorant_expansion q D hD, Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    rw [← hitMonomial_mul U (T ∪ R)]
    ring
  simp_rw [heq]
  apply (finite_polynomial_interval_error (D ×ˢ D)
    (fun a => coefficient q D a.1 * coefficient q D a.2)
    (fun a => U ∪ (a.1 ∪ a.2)) q m ω herr).trans
  calc
    _ ≤ ∑ a ∈ D ×ˢ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      simpa using mul_le_mul (coefficient_abs_le_one q hq D hDn hD a.1)
        (coefficient_abs_le_one q hq D hDn hD a.2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [pow_two]

/-- An explicit remainder bound for the signed lower weight. -/
theorem minorant_interval_error (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ Finset.range m, minorant q D (ω j)) -
      (m : ℝ) * (boundaryDefect q D / normalizer q D ^ 2)| ≤
      (Fintype.card ι + 1 : ℝ) * (D.card : ℝ)^2 := by
  classical
  let E (U : Finset ι) :=
    (∑ j ∈ Finset.range m, hitMonomial U (ω j) * majorant q D (ω j)) -
      (m : ℝ) * average q (fun v => hitMonomial U v * majorant q D v)
  have hE (U : Finset ι) : |E U| ≤ (D.card : ℝ)^2 :=
    majorant_hit_interval_error q hq D hDn hD m ω herr U
  have hmono (v : ι → Bool) : minorant q D v =
      hitMonomial ∅ v * majorant q D v - ∑ i, hitMonomial {i} v * majorant q D v := by
    simp only [minorant, hitMonomial, Finset.prod_empty, Finset.prod_singleton, hitCoordinate]
    rw [← Finset.sum_mul]
    ring
  have heq : (∑ j ∈ Finset.range m, minorant q D (ω j)) -
      (m : ℝ) * (boundaryDefect q D / normalizer q D ^ 2) = E ∅ - ∑ i, E {i} := by
    rw [← minorant_average q hq D hD]
    change _ - (m : ℝ) * average q (fun v => minorant q D v) = _
    simp_rw [hmono]
    rw [average_sub, average_sum]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_sub, E]
    rw [Finset.sum_comm]
    ring
  rw [heq]
  calc
    _ ≤ |E ∅| + |∑ i, E {i}| := abs_sub _ _
    _ ≤ (D.card : ℝ)^2 + ∑ i, |E {i}| :=
      add_le_add (hE ∅) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (D.card : ℝ)^2 + ∑ i : ι, (D.card : ℝ)^2 :=
      add_le_add le_rfl (Finset.sum_le_sum (fun i hi => hE {i}))
    _ = _ := by simp; ring

/-- A positive main term exceeding this explicit error guarantees a survivor. This is a
conditional criterion, not a proof that the condition holds at quadratic interval length. -/
theorem survivor_of_boundaryDefect (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (Fintype.card ι + 1 : ℝ) * (D.card : ℝ)^2 <
      (m : ℝ) * (boundaryDefect q D / normalizer q D ^ 2)) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hsum : (∑ j ∈ Finset.range m, minorant q D (ω j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hne : ω j ≠ (fun _ => false) := by
      intro heq
      obtain ⟨i, hi⟩ := hbad j (Finset.mem_range.mp hj)
      exact hi (congrFun heq i)
    simpa only [if_neg hne] using minorant_le_indicator_empty q hq D hDn (ω j)
  have hh := (abs_le.mp (minorant_interval_error q hq D hDn hD m ω herr)).1
  linarith

#print axioms survivor_of_boundaryDefect

end Erdos970.FiniteSelberg
