import FormalConjecturesUtil

/-! Finite relative entropy and exponential information-decoupling inequalities.
These lemmas are distributional tools only: no entropy-decrement or arithmetic
independence assertion is assumed or proved here. -/

namespace Erdos371.FiniteInformation
open Finset

/-- A real-valued probability law on a finite space. -/
structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

instance {α : Type*} [Fintype α] : CoeFun (Law α) (fun _ => α → ℝ) := ⟨Law.mass⟩

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def mean (p : Law α) (F : α → ℝ) : ℝ := ∑ a, p a * F a

noncomputable def divergence (p q : Law α) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- This support hypothesis is essential because real logarithms are totalized. -/
def SupportedBy (p q : Law α) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

lemma mean_const (p : Law α) (c : ℝ) : mean p (fun _ => c) = c := by
  simp only [mean, ← sum_mul, p.total, one_mul]

lemma mean_add (p : Law α) (F G : α → ℝ) :
    mean p (fun a => F a + G a) = mean p F + mean p G := by
  simp only [mean, mul_add, sum_add_distrib]

lemma mean_smul (p : Law α) (c : ℝ) (F : α → ℝ) :
    mean p (fun a => c * F a) = c * mean p F := by
  simp only [mean, mul_left_comm (p _ : ℝ) c, mul_sum]

lemma divergence_nonneg (p q : Law α) (h : SupportedBy p q) :
    0 ≤ divergence p q := by
  have hpoint (a : α) : p a - q a ≤ p a * Real.log (p a / q a) := by
    by_cases hq : q a = 0
    · have hp : p a = 0 := by
        by_contra hp
        exact h a hp hq
      simp [hp, hq]
    · have hk := mul_nonneg (q.nonneg a)
        (InformationTheory.klFun_nonneg (div_nonneg (p.nonneg a) (q.nonneg a)))
      rw [InformationTheory.klFun_apply] at hk
      have he : q a * (p a / q a * Real.log (p a / q a) + 1 - p a / q a) =
          p a * Real.log (p a / q a) + q a - p a := by
        field_simp
      rw [he] at hk
      linarith
  have hs := sum_le_sum (fun a (_ : a ∈ (univ : Finset α)) => hpoint a)
  simpa only [sum_sub_distrib, p.total, q.total, sub_self, divergence] using hs

lemma exists_mass_pos (p : Law α) : ∃ a, 0 < p a := by
  by_contra h
  push_neg at h
  have hz : ∑ a, p a = 0 := sum_eq_zero (fun a _ => le_antisymm (h a) (p.nonneg a))
  linarith [p.total]

lemma mean_exp_pos (q : Law α) (F : α → ℝ) :
    0 < mean q (fun a => Real.exp (F a)) := by
  obtain ⟨a, ha⟩ := exists_mass_pos q
  exact sum_pos' (fun a _ => mul_nonneg (q.nonneg a) (Real.exp_pos _).le)
    ⟨a, mem_univ a, mul_pos ha (Real.exp_pos _)⟩

noncomputable def tilt (q : Law α) (F : α → ℝ) : Law α where
  mass a := q a * Real.exp (F a) / mean q (fun a => Real.exp (F a))
  nonneg a := div_nonneg (mul_nonneg (q.nonneg a) (Real.exp_pos _).le)
    (mean_exp_pos q F).le
  total := by
    rw [← sum_div]
    exact div_self (mean_exp_pos q F).ne'

lemma supportedBy_tilt (p q : Law α) (F : α → ℝ) (h : SupportedBy p q) :
    SupportedBy p (tilt q F) := by
  intro a ha
  exact div_ne_zero (mul_ne_zero (h a ha) (Real.exp_pos _).ne')
    (mean_exp_pos q F).ne'

lemma divergence_tilt (p q : Law α) (F : α → ℝ) (h : SupportedBy p q) :
    divergence p (tilt q F) = divergence p q - mean p F +
      Real.log (mean q (fun a => Real.exp (F a))) := by
  have he (a : α) :
      p a * Real.log (p a / tilt q F a) = p a * Real.log (p a / q a) -
        p a * F a + p a * Real.log (mean q (fun a => Real.exp (F a))) := by
    by_cases hp : p a = 0
    · simp [hp]
    · change p a * Real.log (p a / (q a * Real.exp (F a) /
        mean q (fun a => Real.exp (F a)))) = _
      rw [Real.log_div hp (div_ne_zero (mul_ne_zero (h a hp) (Real.exp_pos _).ne')
          (mean_exp_pos q F).ne'),
        Real.log_div (mul_ne_zero (h a hp) (Real.exp_pos _).ne') (mean_exp_pos q F).ne',
        Real.log_mul (h a hp) (Real.exp_pos _).ne', Real.log_exp,
        Real.log_div hp (h a hp)]
      ring
  simp only [divergence, he, sum_add_distrib, sum_sub_distrib, ← sum_mul, p.total,
    one_mul, mean]

/-- Exponential variational bound, with support and normalization explicit. -/
theorem mean_le_divergence_add_log_mgf (p q : Law α) (F : α → ℝ)
    (h : SupportedBy p q) :
    mean p F ≤ divergence p q + Real.log (mean q (fun a => Real.exp (F a))) := by
  have hg := divergence_nonneg p (tilt q F) (supportedBy_tilt p q F h)
  rw [divergence_tilt p q F h] at hg
  linarith

/-- Information decoupling for an observable subgaussian under the reference law. -/
theorem mean_sq_le_of_mgf (p q : Law α) (F : α → ℝ) (h : SupportedBy p q)
    {c : ℝ} (hc : 0 < c)
    (hmgf : ∀ t : ℝ, mean q (fun a => Real.exp (t * F a)) ≤ Real.exp (c * t ^ 2 / 2)) :
    (mean p F) ^ 2 ≤ 2 * c * divergence p q := by
  have hbound (t : ℝ) : t * mean p F ≤ divergence p q + c * t ^ 2 / 2 := by
    have hv := mean_le_divergence_add_log_mgf p q (fun a => t * F a) h
    rw [mean_smul] at hv
    have hl := Real.log_le_log (mean_exp_pos q (fun a => t * F a)) (hmgf t)
    rw [Real.log_exp] at hl
    linarith
  have hh := hbound (mean p F / c)
  have hm := mul_le_mul_of_nonneg_left hh hc.le
  field_simp at hm
  nlinarith

/-- Independent product law. -/
noncomputable def independent (p : Law α) (q : Law β) : Law (α × β) where
  mass ab := p ab.1 * q ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) (q.nonneg ab.2)
  total := by simp only [Fintype.sum_prod_type, ← mul_sum, q.total, mul_one, p.total]

noncomputable def firstMarginal (P : Law (α × β)) : Law α where
  mass a := ∑ b, P (a,b)
  nonneg a := sum_nonneg fun b _ => P.nonneg (a,b)
  total := by simpa only [Fintype.sum_prod_type] using P.total

noncomputable def secondMarginal (P : Law (α × β)) : Law β where
  mass b := ∑ a, P (a,b)
  nonneg b := sum_nonneg fun a _ => P.nonneg (a,b)
  total := by rw [sum_comm]; simpa only [Fintype.sum_prod_type] using P.total

lemma mass_le_firstMarginal (P : Law (α × β)) (a : α) (b : β) :
    P (a,b) ≤ firstMarginal P a :=
  single_le_sum (fun b _ => P.nonneg (a,b)) (mem_univ b)

lemma mass_le_secondMarginal (P : Law (α × β)) (a : α) (b : β) :
    P (a,b) ≤ secondMarginal P b :=
  single_le_sum (fun a _ => P.nonneg (a,b)) (mem_univ a)

lemma supportedBy_independent_marginals (P : Law (α × β)) :
    SupportedBy P (independent (firstMarginal P) (secondMarginal P)) := by
  rintro ⟨a,b⟩ hab
  have hpos := lt_of_le_of_ne (P.nonneg (a,b)) (Ne.symm hab)
  exact mul_ne_zero (lt_of_lt_of_le hpos (mass_le_firstMarginal P a b)).ne'
    (lt_of_lt_of_le hpos (mass_le_secondMarginal P a b)).ne'

noncomputable def mutualInformation (P : Law (α × β)) : ℝ :=
  divergence P (independent (firstMarginal P) (secondMarginal P))

lemma mutualInformation_nonneg (P : Law (α × β)) : 0 ≤ mutualInformation P :=
  divergence_nonneg _ _ (supportedBy_independent_marginals P)

lemma mean_independent (p : Law α) (q : Law β) (F : α × β → ℝ) :
    mean (independent p q) F = mean p (fun a => mean q (fun b => F (a,b))) := by
  simp only [mean, independent, Fintype.sum_prod_type, mul_assoc, mul_sum]

/-- A uniform conditional MGF bound gives decoupling from the product of the
marginals. It is the actual joint law's mutual information that occurs here. -/
theorem mean_sq_le_mutualInformation (P : Law (α × β)) (F : α × β → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hmgf : ∀ (a : α) (t : ℝ),
      mean (secondMarginal P) (fun b => Real.exp (t * F (a,b))) ≤
        Real.exp (c * t ^ 2 / 2)) :
    (mean P F) ^ 2 ≤ 2 * c * mutualInformation P := by
  apply mean_sq_le_of_mgf P _ F (supportedBy_independent_marginals P) hc
  intro t
  rw [mean_independent]
  calc
    _ ≤ mean (firstMarginal P) (fun _ => Real.exp (c * t ^ 2 / 2)) := by
      exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmgf a t)
        ((firstMarginal P).nonneg a)
    _ = _ := mean_const _ _

#print axioms mean_le_divergence_add_log_mgf
#print axioms mean_sq_le_of_mgf
#print axioms mean_sq_le_mutualInformation

end Erdos371.FiniteInformation
