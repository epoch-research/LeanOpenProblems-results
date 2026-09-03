import FormalConjecturesUtil

/-! An obstruction to linear amplification of quartic representations. -/

namespace Erdos322Research

/-- Disjoint columns are forced by preservation of the quartic norm. -/
theorem quartic_similarity_disjoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : ι → κ → ℝ) (C : ℝ)
    (h : ∀ x : κ → ℝ,
      ∑ i, (∑ j, M i j * x j) ^ 4 = C * ∑ j, x j ^ 4)
    {j l : κ} (hjl : j ≠ l) (i : ι) : M i j * M i l = 0 := by
  classical
  let e : κ → κ → ℝ := fun j k ↦ if k = j then 1 else 0
  have he (j : κ) : ∑ i, M i j ^ 4 = C := by
    have hh := h (e j)
    simpa [e] using hh
  have hp : ∑ i, (M i j + M i l) ^ 4 = 2 * C := by
    have hh := h (fun k ↦ e j k + e l k)
    have hev : ∑ k, (e j k + e l k) ^ 4 = 2 := by
      simp only [e]
      have hx (k : κ) : ((if k = j then (1 : ℝ) else 0) +
          (if k = l then 1 else 0)) ^ 4 =
          (if k = j then 1 else 0) + (if k = l then 1 else 0) := by
        by_cases hj : k = j <;> by_cases hl : k = l <;> simp_all <;> norm_num
      simp_rw [hx]
      norm_num [Finset.sum_add_distrib]
    simpa [mul_add, Finset.sum_add_distrib, e, hev, mul_comm] using hh
  have hm : ∑ i, (M i j - M i l) ^ 4 = 2 * C := by
    have hh := h (fun k ↦ e j k - e l k)
    have hev : ∑ k, (e j k - e l k) ^ 4 = 2 := by
      simp only [e]
      have hx (k : κ) : ((if k = j then (1 : ℝ) else 0) -
          (if k = l then 1 else 0)) ^ 4 =
          (if k = j then 1 else 0) + (if k = l then 1 else 0) := by
        by_cases hj : k = j <;> by_cases hl : k = l <;> simp_all <;> norm_num
      simp_rw [hx]
      norm_num [Finset.sum_add_distrib]
    simpa [mul_sub, Finset.sum_sub_distrib, e, hev, mul_comm] using hh
  have hx : ∀ a b : ℝ, (a + b) ^ 4 + (a - b) ^ 4 =
      2 * a ^ 4 + 12 * (a * b) ^ 2 + 2 * b ^ 4 := by
    intros; ring
  have hs : ∑ i, (M i j * M i l) ^ 2 = 0 := by
    have heq : (∑ i, (M i j + M i l) ^ 4) +
        (∑ i, (M i j - M i l) ^ 4) =
        2 * (∑ i, M i j ^ 4) + 12 * (∑ i, (M i j * M i l) ^ 2) +
        2 * (∑ i, M i l ^ 4) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hx]
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hp, hm, he, he] at heq
    linarith
  have hi := Finset.single_le_sum (f := fun i ↦ (M i j * M i l) ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ i)
  rw [hs] at hi
  nlinarith [sq_nonneg (M i j * M i l)]

/-- A positive linear quartic-norm similarity is a scaled signed permutation. -/
theorem quartic_similarity_support_perm {κ : Type*} [Fintype κ]
    [DecidableEq κ] (M : κ → κ → ℝ) (C : ℝ) (hC : 0 < C)
    (h : ∀ x : κ → ℝ,
      ∑ i, (∑ j, M i j * x j) ^ 4 = C * ∑ j, x j ^ 4) :
    ∃ σ : Equiv.Perm κ, ∀ i,
      M i (σ i) ^ 4 = C ∧ ∀ j, j ≠ σ i → M i j = 0 := by
  classical
  have he (j : κ) : ∑ i, M i j ^ 4 = C := by
    simpa using h (fun k ↦ if k = j then 1 else 0)
  have hn (j : κ) : ∃ i, M i j ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hz := he j
    simp [hh] at hz
    linarith
  choose ρ hρ using hn
  have hinj : Function.Injective ρ := by
    intro j l heq
    by_contra hne
    have hd := quartic_similarity_disjoint M C h hne (ρ j)
    have hlj : M (ρ j) l ≠ 0 := by rw [heq]; exact hρ l
    exact (mul_ne_zero (hρ j) hlj) hd
  let e : Equiv.Perm κ := Equiv.ofBijective ρ
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hen (i : κ) : M i (e.symm i) ≠ 0 := by
    have hh := hρ (e.symm i)
    change M (e (e.symm i)) (e.symm i) ≠ 0 at hh
    simpa using hh
  have hz (i j : κ) (hj : j ≠ e.symm i) : M i j = 0 := by
    have hh := quartic_similarity_disjoint M C h hj i
    exact (mul_eq_zero.mp hh).resolve_right (hen i)
  refine ⟨e.symm, fun i ↦ ⟨?_, hz i⟩⟩
  rw [← he (e.symm i), Finset.sum_eq_single i]
  · intro b _ hbi
    rw [hz b (e.symm i) (fun hh ↦ hbi (e.symm.injective hh).symm)]
    norm_num
  · simp

end Erdos322Research
