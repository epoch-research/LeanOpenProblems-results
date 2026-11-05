/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil

/-!
# The finite extremal function for Erdős problem 126

The least number of distinct prime factors of an off-diagonal pair-sum product
is attained for each prescribed cardinality. It is also the greatest universal
lower bound, and these bounds define a unique function. These finite extremal
facts do not assert the asymptotic conclusion of Erdős problem 126.

This file is independent of `Submission.Spec`.
-/

open scoped BigOperators

namespace Erdos126Aux

/-- The number of distinct prime factors in the off-diagonal pair-sum product. -/
def supportCount (A : Finset ℕ) : ℕ :=
  (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card

/-- The least support count among finite sets of cardinality `n`. -/
noncomputable def extremal (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ supportCount A = m}

/-- Distinct natural numbers cannot have sum zero. -/
theorem add_ne_zero_of_mem_offDiag {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) : a + b ≠ 0 := by
  intro hzero
  obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp hzero
  exact (Finset.mem_offDiag.mp hab).2.2 (ha.trans hb.symm)

/-- The pair-sum product is nonzero, including when the off-diagonal is empty. -/
theorem offDiag_prod_ne_zero (A : Finset ℕ) :
    (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  rintro ⟨a, b⟩ hab
  exact add_ne_zero_of_mem_offDiag hab

/-- Every off-diagonal pair sum divides the pair-sum product. -/
theorem add_dvd_offDiag_prod {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) :
    a + b ∣ (∏ ⟨c, d⟩ ∈ A.offDiag, (c + d)) := by
  exact Finset.dvd_prod_of_mem (fun p : ℕ × ℕ => p.1 + p.2) hab

/-- A prime dividing one pair sum belongs to the support of the whole product. -/
theorem mem_primeFactors_offDiag_prod {A : Finset ℕ} {a b p : ℕ}
    (hab : (a, b) ∈ A.offDiag) (hp : p.Prime) (hpdvd : p ∣ a + b) :
    p ∈ (∏ ⟨c, d⟩ ∈ A.offDiag, (c + d)).primeFactors := by
  exact hp.mem_primeFactors (hpdvd.trans (add_dvd_offDiag_prod hab))
    (offDiag_prod_ne_zero A)

/-- The prime factors of one pair sum are contained in those of the product. -/
theorem primeFactors_add_subset {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) :
    (a + b).primeFactors ⊆ (∏ ⟨c, d⟩ ∈ A.offDiag, (c + d)).primeFactors := by
  exact Nat.primeFactors_mono (add_dvd_offDiag_prod hab) (offDiag_prod_ne_zero A)

/-- A pair sum gives a lower bound on the support count of the whole product. -/
theorem primeFactors_card_add_le_supportCount {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) : (a + b).primeFactors.card ≤ supportCount A := by
  exact Finset.card_le_card (primeFactors_add_subset hab)

/-- There is a support count of every prescribed cardinality. -/
theorem supportCount_values_nonempty (n : ℕ) :
    {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ supportCount A = m}.Nonempty := by
  exact ⟨supportCount (Finset.range n), Finset.range n, Finset.card_range n, rfl⟩

/-- The minimum defining `extremal n` is attained by a finite set. -/
theorem extremal_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ supportCount A = extremal n := by
  exact Nat.sInf_mem (supportCount_values_nonempty n)

/-- The extremal value is a universal lower bound at cardinality `n`. -/
theorem extremal_le_supportCount {n : ℕ} {A : Finset ℕ} (hA : A.card = n) :
    extremal n ≤ supportCount A := by
  unfold extremal
  exact Nat.sInf_le ⟨A, hA, rfl⟩

/-- All universal lower bounds are exactly the numbers below the extremal value. -/
theorem le_extremal_iff {m n : ℕ} :
    m ≤ extremal n ↔ ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A := by
  constructor
  · intro hm A hA
    exact hm.trans (extremal_le_supportCount hA)
  · intro hm
    obtain ⟨A, hA, hmin⟩ := extremal_attained n
    simpa only [hmin] using hm A hA

/-- The extremal value is the greatest universal lower bound. -/
theorem isGreatest_extremal (n : ℕ) :
    IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A}
      (extremal n) := by
  refine ⟨le_extremal_iff.mp le_rfl, ?_⟩
  intro m hm
  exact le_extremal_iff.mpr hm

/-- The greatest universal lower bound is characterized uniquely. -/
theorem isGreatest_iff_eq_extremal {n m : ℕ} :
    IsGreatest {k : ℕ | ∀ A : Finset ℕ, A.card = n → k ≤ supportCount A} m ↔
      m = extremal n := by
  constructor
  · intro hm
    exact hm.unique (isGreatest_extremal n)
  · rintro rfl
    exact isGreatest_extremal n

/-- The greatest-bound property holds pointwise for the function `extremal`. -/
theorem extremal_spec :
    ∀ n, IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A}
      (extremal n) :=
  isGreatest_extremal

/-- A function satisfying the pointwise greatest-bound property exists. -/
theorem exists_extremal_function :
    ∃ f : ℕ → ℕ, ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n) := by
  exact ⟨extremal, extremal_spec⟩

/-- Any function satisfying the greatest-bound property is `extremal`. -/
theorem eq_extremal_of_isGreatest {f : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n)) :
    f = extremal := by
  funext n
  exact (hf n).unique (isGreatest_extremal n)

/-- Function-level characterization of the greatest-bound property. -/
theorem isGreatest_function_iff_eq_extremal {f : ℕ → ℕ} :
    (∀ n, IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n)) ↔
      f = extremal := by
  constructor
  · exact eq_extremal_of_isGreatest
  · rintro rfl
    exact extremal_spec

/-- Two functions satisfying the pointwise greatest-bound property coincide. -/
theorem unique_extremal_function {f g : ℕ → ℕ}
    (hf : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n))
    (hg : ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (g n)) :
    f = g := by
  exact (eq_extremal_of_isGreatest hf).trans (eq_extremal_of_isGreatest hg).symm

/-- There is exactly one function satisfying the greatest-bound property. -/
theorem existsUnique_extremal_function :
    ∃! f : ℕ → ℕ, ∀ n,
      IsGreatest {m : ℕ | ∀ A : Finset ℕ, A.card = n → m ≤ supportCount A} (f n) := by
  exact ⟨extremal, extremal_spec, fun f hf => eq_extremal_of_isGreatest hf⟩

end Erdos126Aux
