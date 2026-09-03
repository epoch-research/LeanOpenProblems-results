import Submission.RecursiveSieveTransfer

/-! Quantitative control of a polynomial remainder under virtual OR hits.
Unlike exact packing preservation, this allows an explicit small transfer error. -/
namespace Erdos970.FiniteSelberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem probability_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (ω : ι → Bool) : 0 ≤ probability q ω := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hq i).1
  · exact sub_nonneg.mpr (hq i).2

theorem abs_average_le_average_abs (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (f : (ι → Bool) → ℝ) :
    |average q f| ≤ average q (fun ω => |f ω|) := by
  unfold average
  calc
    _ ≤ ∑ ω : ι → Bool, |probability q ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [abs_mul, abs_of_nonneg (probability_nonneg q hq ω)]

theorem average_abs_le_of_bound (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (f : (ι → Bool) → ℝ) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : |average q f| ≤ C := by
  apply (abs_average_le_average_abs q hq f).trans
  simpa only [average_const] using average_mono q hq (fun ω => |f ω|) (fun _ => C) hC

/-- A bounded function which agrees with its baseline when no support coordinate is
hit has a small average change, controlled by the sum of added hit probabilities. -/
theorem average_change_le_support_sum (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (B : Finset ι)
    (f : (ι → Bool) → ℝ) (e C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ η, |f η - e| ≤ C)
    (hzero : ∀ η, (∀ i ∈ B, η i = false) → f η = e) :
    |average a f - e| ≤ C * ∑ i ∈ B, a i := by
  classical
  have hpoint (η : ι → Bool) : |f η - e| ≤
      C * ∑ i ∈ B, hitMonomial {i} η := by
    by_cases hz : ∀ i ∈ B, η i = false
    · rw [hzero η hz, sub_self, abs_zero]
      apply mul_nonneg hC
      apply Finset.sum_nonneg
      intro i hi
      simp only [hitMonomial, Finset.prod_singleton]
      split_ifs <;> norm_num
    · push_neg at hz
      obtain ⟨i, hiB, hi⟩ := hz
      have hit : η i = true := by cases h : η i <;> simp_all
      have hsum : (1 : ℝ) ≤ ∑ j ∈ B, hitMonomial {j} η := by
        have hh := Finset.single_le_sum (s := B) (f := fun j => hitMonomial {j} η)
          (fun j hj => by
            simp only [hitMonomial, Finset.prod_singleton]
            split_ifs <;> norm_num) hiB
        simpa [hitMonomial, hit] using hh
      exact (hf η).trans (by nlinarith)
  have hh := (abs_average_le_average_abs a ha (fun η => f η - e)).trans
    (average_mono a ha (fun η => |f η - e|)
      (fun η => C * ∑ i ∈ B, hitMonomial {i} η) hpoint)
  rw [average_sub, average_const, average_mul_const, average_sum] at hh
  simp only [average_hitMonomial, Finset.prod_singleton] at hh
  exact hh

/-- The entire boosted polynomial retains the unit-error L1 bound. -/
theorem boosted_polynomial_interval_error {α : Type*} (A : Finset α)
    (c : α → ℝ) (S : α → Finset ι) (a q : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ Finset.range m, average a (fun η =>
        ∑ t ∈ A, c t * hitMonomial (S t) (fun i => ω j i || η i))) -
      (m : ℝ) * average (fun i => a i + (1 - a i) * q i)
        (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v)| ≤
      ∑ t ∈ A, |c t| := by
  classical
  let P (η v : ι → Bool) := ∑ t ∈ A, c t *
    hitMonomial ((S t).filter (fun i => η i = false)) v
  let E (η : ι → Bool) := (∑ j ∈ Finset.range m, P η (ω j)) -
    (m : ℝ) * average q (P η)
  have hE (η : ι → Bool) : |E η| ≤ ∑ t ∈ A, |c t| :=
    finite_polynomial_interval_error A c
      (fun t => (S t).filter (fun i => η i = false)) q m ω herr
  have hh := average_abs_le_of_bound a ha E _ hE
  have hmean : average a (fun η => average q (P η)) =
      average (fun i => a i + (1 - a i) * q i)
        (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v) := by
    simp only [P, average_sum, average_mul_const, average_hitMonomial,
      average_restricted_prod]
  have hvalue : average a (fun η => ∑ j ∈ Finset.range m, P η (ω j)) =
      ∑ j ∈ Finset.range m, average a (fun η =>
        ∑ t ∈ A, c t * hitMonomial (S t) (fun i => ω j i || η i)) := by
    rw [average_sum]
    simp only [P, hitMonomial_or]
  change |average a (fun η => (∑ j ∈ Finset.range m, P η (ω j)) -
    (m : ℝ) * average q (P η))| ≤ _ at hh
  rw [average_sub, hvalue, average_mul_const, hmean] at hh
  exact hh

/-- More precisely, the *change* in the polynomial remainder is small if the
added coordinates have small total probability on its support. -/
theorem polynomial_boost_remainder_change {α : Type*} (A : Finset α)
    (c : α → ℝ) (S : α → Finset ι) (B : Finset ι)
    (hS : ∀ t ∈ A, S t ⊆ B) (a q : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ Finset.range m, hitMonomial T (ω j)) -
        (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |((∑ j ∈ Finset.range m, average a (fun η =>
        ∑ t ∈ A, c t * hitMonomial (S t) (fun i => ω j i || η i))) -
      ∑ j ∈ Finset.range m, ∑ t ∈ A, c t * hitMonomial (S t) (ω j)) -
      (m : ℝ) * (average (fun i => a i + (1 - a i) * q i)
        (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v) -
        average q (fun v => ∑ t ∈ A, c t * hitMonomial (S t) v))| ≤
      2 * (∑ t ∈ A, |c t|) * ∑ i ∈ B, a i := by
  classical
  let P (η v : ι → Bool) := ∑ t ∈ A, c t *
    hitMonomial ((S t).filter (fun i => η i = false)) v
  let F (v : ι → Bool) := ∑ t ∈ A, c t * hitMonomial (S t) v
  let E (η : ι → Bool) := (∑ j ∈ Finset.range m, P η (ω j)) -
    (m : ℝ) * average q (P η)
  let e := (∑ j ∈ Finset.range m, F (ω j)) - (m : ℝ) * average q F
  let C := ∑ t ∈ A, |c t|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hE (η : ι → Bool) : |E η| ≤ C :=
    finite_polynomial_interval_error A c
      (fun t => (S t).filter (fun i => η i = false)) q m ω herr
  have he : |e| ≤ C := finite_polynomial_interval_error A c S q m ω herr
  have hchange (η : ι → Bool) : |E η - e| ≤ 2 * C := by
    calc
      _ ≤ |E η| + |e| := abs_sub _ _
      _ ≤ C + C := add_le_add (hE η) he
      _ = 2 * C := by ring
  have hzero (η : ι → Bool) (hη : ∀ i ∈ B, η i = false) : E η = e := by
    have hP : P η = F := by
      funext v
      apply Finset.sum_congr rfl
      intro t ht
      have hfilter : (S t).filter (fun i => η i = false) = S t :=
        Finset.filter_eq_self.mpr (fun i hi => hη i (hS t ht hi))
      simp only [hfilter]
    simp only [E, e, hP]
  have hh := average_change_le_support_sum a ha B E e (2 * C)
    (by positivity) hchange hzero
  have hmean : average a (fun η => average q (P η)) =
      average (fun i => a i + (1 - a i) * q i) F := by
    simp only [P, F, average_sum, average_mul_const, average_hitMonomial,
      average_restricted_prod]
  have hvalue : average a (fun η => ∑ j ∈ Finset.range m, P η (ω j)) =
      ∑ j ∈ Finset.range m, average a (fun η => F (fun i => ω j i || η i)) := by
    rw [average_sum]
    simp only [P, F, hitMonomial_or]
  change |average a (fun η => (∑ j ∈ Finset.range m, P η (ω j)) -
    (m : ℝ) * average q (P η)) - e| ≤ _ at hh
  rw [average_sub, hvalue, average_mul_const, hmean] at hh
  dsimp only [e, C, F] at hh
  convert hh using 1 <;> congr 1 <;> ring

#print axioms boosted_polynomial_interval_error
#print axioms polynomial_boost_remainder_change

end Erdos970.FiniteSelberg
