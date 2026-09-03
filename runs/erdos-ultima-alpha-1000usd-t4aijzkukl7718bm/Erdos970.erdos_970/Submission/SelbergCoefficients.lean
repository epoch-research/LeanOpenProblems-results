import Submission.FiniteSelberg

/-! Ordinary coefficients of the finite Selberg kernel and their uniform bounds. -/

namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weight (q : ι → ℝ) (Q : Finset ι) : ℝ :=
  ∏ i ∈ Q, q i / (1 - q i)

theorem weight_eq_inverse_variance (q : ι → ℝ) (Q : Finset ι) :
    weight q Q = 1 / variance q Q := by
  simp only [weight, variance, one_div, ← Finset.prod_inv_distrib, inv_div]

theorem weight_pos (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) (Q : Finset ι) :
    0 < weight q Q := by
  exact Finset.prod_pos (fun i hi => div_pos (hq i).1 (sub_pos.mpr (hq i).2))

/-- The generating function for all supersets of a fixed set. -/
theorem sum_supersets_prod (w : ι → ℝ) (T : Finset ι) :
    (∑ Q : Finset ι, if T ⊆ Q then ∏ i ∈ Q, w i else 0) =
      ∏ i, if i ∈ T then w i else 1 + w i := by
  classical
  have hcomp (Q : Finset ι) :
      (∏ i ∈ Finset.univ \ Q, if i ∈ T then (0 : ℝ) else 1) =
        if T ⊆ Q then 1 else 0 := by
    by_cases hTQ : T ⊆ Q
    · rw [if_pos hTQ]
      apply Finset.prod_eq_one
      intro i hi
      have hiQ := (Finset.mem_sdiff.mp hi).2
      exact if_neg (fun hiT => hiQ (hTQ hiT))
    · rw [if_neg hTQ]
      obtain ⟨i, hiT, hiQ⟩ := Finset.not_subset.mp hTQ
      exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiQ⟩)
        (if_pos hiT)
  calc
    _ = ∑ Q : Finset ι, (∏ i ∈ Q, w i) *
          ∏ i ∈ Finset.univ \ Q, if i ∈ T then (0 : ℝ) else 1 := by
      simp_rw [hcomp, mul_ite, mul_one, mul_zero]
    _ = ∏ i, (w i + if i ∈ T then 0 else 1) := by
      simpa using (Finset.prod_add w (fun i => if i ∈ T then 0 else 1)
        Finset.univ).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> ring

theorem sum_weight (q : ι → ℝ) :
    (∑ Q : Finset ι, weight q Q) = ∏ i, (1 + q i / (1 - q i)) := by
  simpa [weight] using sum_supersets_prod (fun i => q i / (1 - q i)) (∅ : Finset ι)

theorem sum_supersets_weight (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (T : Finset ι) :
    (∑ Q : Finset ι, if T ⊆ Q then weight q Q else 0) =
      (∏ i ∈ T, q i) * ∑ Q : Finset ι, weight q Q := by
  rw [sum_weight]
  unfold weight
  rw [sum_supersets_prod]
  calc
    _ = ∏ i : ι, (if i ∈ T then q i else 1) * (1 + q i / (1 - q i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiT : i ∈ T
      · simp only [if_pos hiT]
        have hne := (sub_pos.mpr (hq i).2).ne'
        field_simp
        ring
      · simp only [if_neg hiT, one_mul]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_ite_mem]

/-- Conditioning product weights on a downward-closed family decreases the mass of an
increasing principal event. -/
theorem downset_superset_weight_le (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (T : Finset ι) :
    (∑ Q ∈ D, if T ⊆ Q then weight q Q else 0) ≤
      (∏ i ∈ T, q i) * normalizer q D := by
  classical
  let f₁ (Q : Finset ι) := if Q ∈ D ∧ T ⊆ Q then weight q Q else 0
  let f₂ (Q : Finset ι) := weight q Q
  let f₃ (Q : Finset ι) := if Q ∈ D then weight q Q else 0
  let f₄ (Q : Finset ι) := if T ⊆ Q then weight q Q else 0
  have hn (Q : Finset ι) : 0 ≤ weight q Q := (weight_pos q hq Q).le
  have hh := four_functions_theorem_univ f₁ f₂ f₃ f₄
    (fun Q => by dsimp [f₁]; split_ifs <;> first | exact hn Q | exact le_rfl)
    hn
    (fun Q => by dsimp [f₃]; split_ifs <;> first | exact hn Q | exact le_rfl)
    (fun Q => by dsimp [f₄]; split_ifs <;> first | exact hn Q | exact le_rfl)
    (fun A B => ?_)
  · have he₁ : (∑ Q, f₁ Q) = ∑ Q ∈ D, if T ⊆ Q then weight q Q else 0 := by
      simp [f₁, ite_and]
    have he₃ : (∑ Q, f₃ Q) = normalizer q D := by
      simp [f₃, normalizer, weight_eq_inverse_variance]
    rw [he₁, he₃] at hh
    change _ ≤ normalizer q D * (∑ Q, if T ⊆ Q then weight q Q else 0) at hh
    rw [sum_supersets_weight q hq T] at hh
    have hpos : 0 < ∑ Q : Finset ι, weight q Q :=
      Finset.sum_pos (fun Q hQ => weight_pos q hq Q) Finset.univ_nonempty
    dsimp [f₂] at hh
    nlinarith
  · dsimp [f₁, f₂, f₃, f₄]
    by_cases hA : A ∈ D ∧ T ⊆ A
    · have hmem : A ∩ B ∈ D := hD A hA.1 (A ∩ B) Finset.inter_subset_left
      have hsub : T ⊆ A ∪ B := hA.2.trans Finset.subset_union_left
      simp only [if_pos hA, if_pos hmem, if_pos hsub]
      exact le_of_eq (by
        change (∏ i ∈ A, _) * (∏ i ∈ B, _) =
          (∏ i ∈ A ∩ B, _) * (∏ i ∈ A ∪ B, _)
        rw [mul_comm (∏ i ∈ A ∩ B, _), Finset.prod_union_inter])
    · rw [if_neg hA, zero_mul]
      apply mul_nonneg <;> split_ifs <;> first | exact hn _ | exact le_rfl

/-- Ordinary monomial coefficients of the normalized Selberg kernel. -/
noncomputable def coefficient (q : ι → ℝ) (D : Finset (Finset ι))
    (T : Finset ι) : ℝ :=
  (-1) ^ T.card * (∑ Q ∈ D, if T ⊆ Q then weight q Q else 0) /
    ((∏ i ∈ T, q i) * normalizer q D)

theorem coefficient_abs_le_one (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (T : Finset ι) :
    |coefficient q D T| ≤ 1 := by
  have hp : 0 < ∏ i ∈ T, q i := Finset.prod_pos (fun i hi => (hq i).1)
  have hG := normalizer_pos q hq D hDn
  have hN : 0 ≤ ∑ Q ∈ D, if T ⊆ Q then weight q Q else 0 := by
    apply Finset.sum_nonneg
    intro Q hQ
    split_ifs
    · exact (weight_pos q hq Q).le
    · exact le_rfl
  rw [coefficient, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hN, abs_of_pos (mul_pos hp hG)]
  exact (div_le_one (mul_pos hp hG)).mpr (downset_superset_weight_le q hq D hD T)

/-- A monomial of hit indicators, equal to one precisely when all its coordinates are hit. -/
noncomputable def hitMonomial (T : Finset ι) (ω : ι → Bool) : ℝ :=
  ∏ i ∈ T, if ω i then 1 else 0

theorem hitMonomial_eq (T : Finset ι) (ω : ι → Bool) :
    hitMonomial T ω = if ∀ i ∈ T, ω i = true then 1 else 0 := by
  simp [hitMonomial, Finset.prod_boole]

theorem basis_expansion (q : ι → ℝ) (Q : Finset ι) (ω : ι → Bool) :
    basis q Q ω = ∑ T : Finset ι,
      if T ⊆ Q then (-1) ^ T.card / (∏ i ∈ T, q i) * hitMonomial T ω else 0 := by
  classical
  have hb : basis q Q ω = ∏ i ∈ Q, (1 - (if ω i then (1 : ℝ) else 0) / q i) := by
    unfold basis
    calc
      _ = ∏ i ∈ Q, contrast (q i) (ω i) := by simp [Finset.prod_ite_mem]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        cases ω i <;> simp [contrast]
  rw [hb, Finset.prod_sub]
  calc
    _ = ∑ T ∈ Q.powerset, (-1) ^ T.card / (∏ i ∈ T, q i) * hitMonomial T ω := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.prod_const_one, mul_one, Finset.prod_div_distrib, hitMonomial]
      ring
    _ = _ := by simp [← Finset.mem_powerset]

theorem coefficient_eq_zero_of_not_mem (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (T : Finset ι) (hT : T ∉ D) :
    coefficient q D T = 0 := by
  have hh : (∑ Q ∈ D, if T ⊆ Q then weight q Q else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro Q hQ
    exact if_neg (fun hTQ => hT (hD Q hQ T hTQ))
  simp only [coefficient, hh, mul_zero, zero_div]

theorem coefficient_empty (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty) :
    coefficient q D ∅ = 1 := by
  simp only [coefficient, Finset.card_empty, pow_zero, Finset.empty_subset, if_true,
    Finset.prod_empty, one_mul, weight_eq_inverse_variance]
  exact div_self (normalizer_pos q hq D hDn).ne'

/-- The ordinary coefficients expand the normalized kernel, before squaring. -/
theorem kernel_expansion_univ (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) :
    kernel q D ω / normalizer q D =
      ∑ T : Finset ι, coefficient q D T * hitMonomial T ω := by
  classical
  simp only [kernel, basis_expansion, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [coefficient, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [weight_eq_inverse_variance]
  by_cases hTQ : T ⊆ Q <;> simp only [hTQ, if_true, if_false] <;> ring

/-- Downward closure makes the same expansion supported on the selected family. -/
theorem kernel_expansion (q : ι → ℝ) (D : Finset (Finset ι))
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (ω : ι → Bool) :
    kernel q D ω / normalizer q D =
      ∑ T ∈ D, coefficient q D T * hitMonomial T ω := by
  rw [kernel_expansion_univ]
  apply (Finset.sum_subset (Finset.subset_univ D) ?_).symm
  intro T hT hTD
  rw [coefficient_eq_zero_of_not_mem q D hD T hTD, zero_mul]

#print axioms coefficient_abs_le_one
#print axioms coefficient_empty
#print axioms kernel_expansion

end Erdos970.FiniteSelberg
