import FormalConjecturesUtil

/-!
The finite orthogonal calculation behind a Selberg quadratic upper sieve.
This is an upper majorant construction, not a lower sieve or a quadratic Jacobsthal bound.
-/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def probability (q : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then q i else 1 - q i

noncomputable def average (q : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ ω, probability q ω * f ω

/-- Products of coordinate functions have factorized Bernoulli averages. -/
theorem average_prod (q : ι → ℝ) (f : ι → Bool → ℝ) :
    average q (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (q i * f i true + (1 - q i) * f i false) := by
  classical
  calc
    _ = ∑ ω : ι → Bool, ∏ i, (if ω i then q i else 1 - q i) * f i (ω i) := by
      simp only [average, probability, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, (if b then q i else 1 - q i) * f i b :=
      (Fintype.prod_sum (fun i b => (if b then q i else 1 - q i) * f i b)).symm
    _ = _ := by simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]

theorem average_sum (q : ι → ℝ) {α : Type*} (s : Finset α)
    (f : α → (ι → Bool) → ℝ) :
    average q (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, average q (f a) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_mul_const (q : ι → ℝ) (f : (ι → Bool) → ℝ) (c : ℝ) :
    average q (fun ω => c * f ω) = c * average q f := by
  simp only [average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

theorem average_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ average q f := by
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg _ (hf ω)
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hq i).1
  · exact sub_nonneg.mpr (hq i).2

/-- The centered coordinate, normalized to equal one at an unhit coordinate. -/
noncomputable def contrast (q : ℝ) (b : Bool) : ℝ := if b then 1 - 1 / q else 1

noncomputable def basis (q : ι → ℝ) (Q : Finset ι) (ω : ι → Bool) : ℝ :=
  ∏ i, if i ∈ Q then contrast (q i) (ω i) else 1

noncomputable def variance (q : ι → ℝ) (Q : Finset ι) : ℝ :=
  ∏ i ∈ Q, (1 - q i) / q i

theorem contrast_mean (q : ℝ) (hq : q ≠ 0) :
    q * contrast q true + (1 - q) * contrast q false = 0 := by
  simp only [contrast, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring

theorem contrast_square_mean (q : ℝ) (hq : q ≠ 0) :
    q * (contrast q true * contrast q true) +
      (1 - q) * (contrast q false * contrast q false) = (1 - q) / q := by
  simp only [contrast, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring

theorem basis_at_empty (q : ι → ℝ) (Q : Finset ι) :
    basis q Q (fun _ => false) = 1 := by
  simp [basis, contrast]

theorem variance_pos (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) (Q : Finset ι) :
    0 < variance q Q := by
  exact Finset.prod_pos (fun i hi => div_pos (sub_pos.mpr (hq i).2) (hq i).1)

/-- Distinct subset coordinates are orthogonal, with an explicit diagonal norm. -/
theorem average_basis_mul (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (Q R : Finset ι) :
    average q (fun ω => basis q Q ω * basis q R ω) =
      if Q = R then variance q Q else 0 := by
  classical
  simp only [basis, ← Finset.prod_mul_distrib]
  rw [average_prod q (fun i b =>
    (if i ∈ Q then contrast (q i) b else 1) * (if i ∈ R then contrast (q i) b else 1))]
  by_cases hQR : Q = R
  · subst R
    rw [if_pos rfl]
    calc
      _ = ∏ i : ι, if i ∈ Q then (1 - q i) / q i else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hiQ : i ∈ Q
        · simpa only [if_pos hiQ] using contrast_square_mean (q i) (hq i)
        · simp only [if_neg hiQ, mul_one]
          ring
      _ = variance q Q := by simp [variance, Finset.prod_ite_mem]
  · rw [if_neg hQR]
    have hex : ∃ i, ¬(i ∈ Q ↔ i ∈ R) := by
      by_contra hn
      push_neg at hn
      exact hQR (Finset.ext hn)
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hiQ : i ∈ Q
    · have hiR : i ∉ R := by tauto
      simpa only [if_pos hiQ, if_neg hiR, mul_one] using contrast_mean (q i) (hq i)
    · have hiR : i ∈ R := by tauto
      simpa only [if_neg hiQ, if_pos hiR, one_mul] using contrast_mean (q i) (hq i)

/-- Diagonalization of an arbitrary finite quadratic sieve weight. -/
theorem average_square_sum (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (D : Finset (Finset ι)) (c : Finset ι → ℝ) :
    average q (fun ω => (∑ Q ∈ D, c Q * basis q Q ω) ^ 2) =
      ∑ Q ∈ D, c Q ^ 2 * variance q Q := by
  classical
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [average_sum]
  have heq (R : Finset ι) :
      average q (fun ω => (c Q * basis q Q ω) * (c R * basis q R ω)) =
        (c Q * c R) * (if Q = R then variance q Q else 0) := by
    have hh := average_mul_const q (fun ω => basis q Q ω * basis q R ω) (c Q * c R)
    rw [average_basis_mul q hq] at hh
    convert hh using 1
    congr 1
    funext ω
    ring
  simp_rw [heq]
  simp only [mul_ite, mul_zero]
  simp [hQ, pow_two]

/-- The reciprocal diagonal mass of the chosen support. -/
noncomputable def normalizer (q : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ Q ∈ D, 1 / variance q Q

noncomputable def kernel (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) : ℝ :=
  ∑ Q ∈ D, basis q Q ω / variance q Q

noncomputable def majorant (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) : ℝ :=
  (kernel q D ω / normalizer q D) ^ 2

theorem normalizer_pos (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : D.Nonempty) : 0 < normalizer q D := by
  exact Finset.sum_pos (fun Q hQ => one_div_pos.mpr (variance_pos q hq Q)) hD

theorem kernel_at_empty (q : ι → ℝ) (D : Finset (Finset ι)) :
    kernel q D (fun _ => false) = normalizer q D := by
  simp only [kernel, normalizer, basis_at_empty]

/-- The square of the unnormalized kernel has mean equal to its normalizer. -/
theorem kernel_square_average (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) :
    average q (fun ω => kernel q D ω ^ 2) = normalizer q D := by
  have hk (ω : ι → Bool) : kernel q D ω =
      ∑ Q ∈ D, (1 / variance q Q) * basis q Q ω := by
    unfold kernel
    apply Finset.sum_congr rfl
    intro Q hQ
    ring
  simp_rw [hk]
  rw [average_square_sum q (fun i => (hq i).1.ne')]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hv := (variance_pos q hq Q).ne'
  field_simp

theorem majorant_nonneg (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) :
    0 ≤ majorant q D ω := sq_nonneg _

theorem majorant_at_empty (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : D.Nonempty) :
    majorant q D (fun _ => false) = 1 := by
  simp only [majorant, kernel_at_empty,
    div_self (normalizer_pos q hq D hD).ne', one_pow]

/-- A pointwise upper sieve: one at the empty hit pattern and nonnegative elsewhere. -/
theorem indicator_empty_le_majorant (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : D.Nonempty) (ω : ι → Bool) :
    (if ω = (fun _ => false) then (1 : ℝ) else 0) ≤ majorant q D ω := by
  classical
  by_cases hω : ω = (fun _ => false)
  · subst ω
    simp [majorant_at_empty q hq D hD]
  · simp only [if_neg hω]
    exact majorant_nonneg q D ω

/-- The optimized quadratic majorant has reciprocal-normalizer mean. -/
theorem majorant_average (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hD : D.Nonempty) :
    average q (majorant q D) = 1 / normalizer q D := by
  have heq : majorant q D = fun ω => (1 / normalizer q D) ^ 2 * kernel q D ω ^ 2 := by
    funext ω
    unfold majorant
    ring
  rw [heq, average_mul_const, kernel_square_average q hq D]
  have hG := (normalizer_pos q hq D hD).ne'
  field_simp

/-- No normalized square with this orthogonal support can have a smaller mean. -/
theorem majorant_mean_optimal (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (c : Finset ι → ℝ) (hc : (∑ Q ∈ D, c Q) = 1) :
    1 / normalizer q D ≤
      average q (fun ω => (∑ Q ∈ D, c Q * basis q Q ω) ^ 2) := by
  rw [average_square_sum q (fun i => (hq i).1.ne')]
  have hh := Finset.sq_sum_div_le_sum_sq_div D c
    (g := fun Q => 1 / variance q Q)
    (fun Q hQ => one_div_pos.mpr (variance_pos q hq Q))
  rw [hc, one_pow] at hh
  simpa only [normalizer, one_div, div_inv_eq_mul] using hh

#print axioms majorant_mean_optimal

#print axioms majorant_average
#print axioms indicator_empty_le_majorant


#print axioms average_basis_mul
#print axioms average_square_sum
end Erdos970.FiniteSelberg
