import Submission.SelbergLowerCriterion

/-! A first-hit lower sieve assembled from different Selberg majorants on preceding coordinates. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem majorant_eq_one_of_avoids_support (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (ω : ι → Bool) (hω : ∀ Q ∈ D, ∀ i ∈ Q, ω i = false) :
    majorant q D ω = 1 := by
  have hb (Q : Finset ι) (hQ : Q ∈ D) : basis q Q ω = 1 := by
    rw [basis_eq_prod]
    apply Finset.prod_eq_one
    intro i hi
    simp [contrast, hω Q hQ i hi]
  have hk : kernel q D ω = normalizer q D := by
    unfold kernel normalizer
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [hb Q hQ]
  unfold majorant
  rw [hk, div_self (normalizer_pos q hq D hDn).ne']
  norm_num

/-- If the support omits a coordinate, its hit is independent of the majorant. -/
theorem majorant_hit_average_of_not_mem (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (D : Finset (Finset ι)) (hDn : D.Nonempty)
    (hD : ∀ A ∈ D, ∀ B ⊆ A, B ∈ D) (i : ι)
    (hi : ∀ Q ∈ D, i ∉ Q) :
    average q (fun ω => hitMonomial {i} ω * majorant q D ω) =
      q i / normalizer q D := by
  classical
  have hB : insertionBoundary D i = D := by
    ext Q
    simp only [insertionBoundary, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hQ
      refine ⟨hQ, hi Q hQ, ?_⟩
      intro hQi
      exact hi (insert i Q) hQi (Finset.mem_insert_self _ _)
  have heq : (fun ω => hitMonomial {i} ω * majorant q D ω) =
      fun ω => (1 / normalizer q D ^ 2) * (hitCoordinate i ω * kernel q D ω ^ 2) := by
    funext ω
    simp only [hitMonomial, Finset.prod_singleton, hitCoordinate, majorant]
    ring
  rw [heq, average_mul_const, kernel_square_hit_average q hq D hD i, hB]
  have hG := (normalizer_pos q hq D hDn).ne'
  field_simp

section Ordered
variable [LinearOrder ι]

/-- The first hit sees a majorant equal to one; all other summands are nonnegative. -/
theorem first_hit_sum_ge_one (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i)
    (ω : ι → Bool) (hω : ω ≠ (fun _ => false)) :
    1 ≤ ∑ i, hitMonomial {i} ω * majorant q (D i) ω := by
  classical
  let B := Finset.univ.filter (fun i => ω i = true)
  have hBn : B.Nonempty := by
    by_contra h
    apply hω
    funext i
    cases hi : ω i
    · rfl
    · exact False.elim (h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
  let i := B.min' hBn
  have hi : ω i = true := (Finset.mem_filter.mp (B.min'_mem hBn)).2
  have hj (j : ι) (hji : j < i) : ω j = false := by
    cases he : ω j
    · rfl
    · have hle : i ≤ j := B.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, he⟩)
      exact False.elim ((not_lt_of_ge hle) hji)
  have hmajor : majorant q (D i) ω = 1 :=
    majorant_eq_one_of_avoids_support q hq (D i) (hDn i) ω
      (fun Q hQ j hjQ => hj j (hprior i Q hQ j hjQ))
  have hnonneg (j : ι) : 0 ≤ hitMonomial {j} ω * majorant q (D j) ω := by
    apply mul_nonneg _ (majorant_nonneg q (D j) ω)
    simp only [hitMonomial, Finset.prod_singleton]
    split_ifs <;> norm_num
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => hitMonomial {j} ω * majorant q (D j) ω)
    (fun j _ => hnonneg j) (Finset.mem_univ i)
  simpa [hitMonomial, hi, hmajor] using hh

/-- An explicit first-hit criterion. Its numerical inequality must still be established
for any proposed asymptotic application. -/
theorem survivor_of_first_hit_normalizers (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : ι → Finset (Finset ι)) (hDn : ∀ i, (D i).Nonempty)
    (hD : ∀ i, ∀ A ∈ D i, ∀ B ⊆ A, B ∈ D i)
    (hprior : ∀ i, ∀ Q ∈ D i, ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (m : ℝ) * (∑ i, q i / normalizer q (D i)) +
      (∑ i, ((D i).card : ℝ)^2) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ Finset.range m,
      ∑ i, hitMonomial {i} (ω j) * majorant q (D i) (ω j) := by
    calc
      _ = ∑ j ∈ Finset.range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply first_hit_sum_ge_one q hq D hDn hprior (ω j)
        intro heq
        obtain ⟨i, hi⟩ := hbad j (Finset.mem_range.mp hj)
        exact hi (congrFun heq i)
  have hbound (i : ι) :
      (∑ j ∈ Finset.range m, hitMonomial {i} (ω j) * majorant q (D i) (ω j)) ≤
      (m : ℝ) * (q i / normalizer q (D i)) + ((D i).card : ℝ)^2 := by
    have he := majorant_hit_interval_error q hq (D i) (hDn i) (hD i) m ω herr {i}
    have hnot (Q : Finset ι) (hQ : Q ∈ D i) : i ∉ Q := by
      intro hi
      exact lt_irrefl i (hprior i Q hQ i hi)
    rw [majorant_hit_average_of_not_mem q hq (D i) (hDn i) (hD i) i hnot] at he
    linarith [(abs_le.mp he).2]
  rw [Finset.sum_comm] at hlower
  have hupper := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hupper
  exact hmain.not_ge (hlower.trans hupper)

end Ordered

#print axioms majorant_hit_average_of_not_mem
#print axioms survivor_of_first_hit_normalizers

end Erdos970.FiniteSelberg
