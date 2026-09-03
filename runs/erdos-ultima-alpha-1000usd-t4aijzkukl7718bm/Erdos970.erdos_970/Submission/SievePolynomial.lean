import Submission.RefinedBrun

/-!
Finite sieve polynomials and products on disjoint prime blocks. The coefficients
and all error estimates are explicit; no new analytic estimate is assumed.
-/
namespace Erdos970.BlockSieve

open Erdos970.BrunCriterion

structure SievePolynomial where
  Term : Type
  fintypeTerm : Fintype Term
  primes : Term → Finset ℕ
  coefficient : Term → ℝ

attribute [instance] SievePolynomial.fintypeTerm

namespace SievePolynomial

noncomputable def value (S : SievePolynomial) (r : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑ a : S.Term, S.coefficient a * if (∀ p ∈ S.primes a, i ≡ r p [MOD p]) then 1 else 0

noncomputable def mean (S : SievePolynomial) : ℝ :=
  ∑ a : S.Term, S.coefficient a / ∏ p ∈ S.primes a, (p : ℝ)

noncomputable def cost (S : SievePolynomial) : ℝ :=
  ∑ a : S.Term, |S.coefficient a|

def SupportedOn (S : SievePolynomial) (P : Finset ℕ) : Prop :=
  ∀ a : S.Term, S.primes a ⊆ P

theorem cost_nonneg (S : SievePolynomial) : 0 ≤ S.cost :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Each term has one CRT remainder of size at most one. -/
theorem interval_error (S : SievePolynomial) (hS : ∀ a, ∀ p ∈ S.primes a, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    |(∑ i ∈ Finset.range m, S.value r i) - (m : ℝ) * S.mean| ≤ S.cost := by
  classical
  let C (a : S.Term) := ((Finset.range m).filter (fun i => ∀ p ∈ S.primes a, i ≡ r p [MOD p])).card
  have hcount : (∑ i ∈ Finset.range m, S.value r i) = ∑ a : S.Term, S.coefficient a * C a := by
    simp only [value]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, C]
  have hmain : (m : ℝ) * S.mean = ∑ a : S.Term,
      S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ)) := by
    rw [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hcount, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : S.Term, |S.coefficient a * C a -
        S.coefficient a * ((m : ℝ) / ∏ p ∈ S.primes a, (p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S.cost := by
      apply Finset.sum_le_sum
      intro a ha
      rw [← mul_sub, abs_mul]
      have hh := intersection_count_error (S.primes a) (hS a) r m
      change |(C a : ℝ) - _| ≤ 1 at hh
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (abs_nonneg (S.coefficient a))

noncomputable def product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) : SievePolynomial := by
  classical
  exact {
    Term := ∀ j, (S j).Term
    fintypeTerm := inferInstance
    primes := fun a => Finset.univ.biUnion (fun j => (S j).primes (a j))
    coefficient := fun a => ∏ j, (S j).coefficient (a j)
  }

theorem product_supportedOn {ι : Type} [Fintype ι] (S : ι → SievePolynomial)
    (P : ι → Finset ℕ) (hS : ∀ j, (S j).SupportedOn (P j)) :
    (product S).SupportedOn (Finset.univ.biUnion P) := by
  classical
  intro a p hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j, hj, hS j (a j) hpj⟩

/-- Evaluation factorizes even without disjointness, since hit indicators are idempotent. -/
theorem value_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) (r : ℕ → ℕ) (i : ℕ) :
    (product S).value r i = ∏ j, (S j).value r i := by
  classical
  simp only [value, product, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  congr 1
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
  aesop

/-- Absolute coefficient costs multiply exactly. -/
theorem cost_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial) :
    (product S).cost = ∏ j, (S j).cost := by
  classical
  simp only [cost, Fintype.prod_sum]
  change (∑ a : ∀ j, (S j).Term, |∏ j, (S j).coefficient (a j)|) = _
  simp only [Finset.abs_prod]

/-- Main terms multiply when the prime supports are disjoint. -/
theorem mean_product {ι : Type} [Fintype ι] (S : ι → SievePolynomial)
    (P : ι → Finset ℕ) (hS : ∀ j, (S j).SupportedOn (P j))
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) :
    (product S).mean = ∏ j, (S j).mean := by
  classical
  simp only [mean, Fintype.prod_sum]
  change (∑ a : ∀ j, (S j).Term, (∏ j, (S j).coefficient (a j)) /
      ∏ p ∈ Finset.univ.biUnion (fun j => (S j).primes (a j)), (p : ℝ)) = _
  apply Finset.sum_congr rfl
  intro a ha
  have hd : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun j => (S j).primes (a j)) := by
    intro i hi j hj hij
    exact (hdis hij).mono (hS i (a i)) (hS j (a j))
  rw [Finset.prod_biUnion hd, Finset.prod_div_distrib]

noncomputable def upper (P : Finset ℕ) (t : ℕ) : SievePolynomial := by
  classical
  exact {
    Term := ↥(truncSets P t)
    fintypeTerm := inferInstance
    primes := Subtype.val
    coefficient := fun Q => (-1 : ℝ) ^ Q.val.card
  }

noncomputable def errorTerm (P : Finset ℕ) (t : ℕ) : SievePolynomial := by
  classical
  exact {
    Term := ↥(P.powersetCard (t + 1))
    fintypeTerm := inferInstance
    primes := Subtype.val
    coefficient := fun _ => 1
  }

theorem upper_supportedOn (P : Finset ℕ) (t : ℕ) : (upper P t).SupportedOn P := by
  intro Q
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp Q.property).1

theorem errorTerm_supportedOn (P : Finset ℕ) (t : ℕ) : (errorTerm P t).SupportedOn P := by
  intro Q
  exact (Finset.mem_powersetCard.mp Q.property).1

theorem mean_upper (P : Finset ℕ) (t : ℕ) : (upper P t).mean = truncDensity P t := by
  classical
  exact Finset.sum_coe_sort (truncSets P t) (fun Q => (-1 : ℝ) ^ Q.card / ∏ p ∈ Q, (p : ℝ))

theorem cost_upper (P : Finset ℕ) (t : ℕ) : (upper P t).cost = (truncSets P t).card := by
  classical
  change (∑ Q : ↥(truncSets P t), |(-1 : ℝ) ^ Q.val.card|) = _
  simp

theorem cost_errorTerm (P : Finset ℕ) (t : ℕ) : (errorTerm P t).cost = P.card.choose (t + 1) := by
  classical
  change (∑ _Q : ↥(P.powersetCard (t + 1)), |(1 : ℝ)|) = _
  simp

#print axioms interval_error
#print axioms value_product
#print axioms mean_product
end SievePolynomial
end Erdos970.BlockSieve
