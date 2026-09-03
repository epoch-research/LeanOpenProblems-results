import Submission.BoostedMixedAffine
import Submission.MixedCardinalityAffine

/-! A sound reference-marginal transport of smaller-cardinality count bounds.
The reference survival-density factor is retained explicitly. This supplies a
conditional recursive source, not a proof of uniform quadratic positivity. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mixedMass_prime_eq (p : ι → ℕ) (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) :
    mixedMass m A B (fun x i => decide (x ≡ r (p i) [MOD p i])) =
      (MixedPattern.mixedCount m (A.image p) (B.image p) r : ℝ) := by
  classical
  have hv (x : ℕ) : mixedMonomial A B (fun i => decide (x ≡ r (p i) [MOD p i])) =
      if (∀ i ∈ A, x ≡ r (p i) [MOD p i]) ∧
        (∀ i ∈ B, ¬x ≡ r (p i) [MOD p i]) then (1 : ℝ) else 0 := by
    simp only [mixedMonomial, hitMonomial_eq, avoidMonomial,
      decide_eq_true_eq, decide_eq_false_iff_not]
    split_ifs <;> simp_all
  unfold mixedMass
  simp_rw [hv]
  rw [sum_boole]
  unfold MixedPattern.mixedCount MixedPattern.positions
  congr 2
  ext x
  simp only [mem_filter, forall_mem_image]

lemma prime_image_prod_inv (p : ι → ℕ) (hinj : Function.Injective p) (U : Finset ι) :
    (∏ i ∈ U, (1 : ℝ)/(p i : ℝ)) = 1/(∏ q ∈ U.image p, (q : ℝ)) := by
  rw [prod_image hinj.injOn]
  simp only [one_div, prod_inv_distrib]

/-- Affine block lower bounds hold for every actual required-hit subset.
No virtual hits or first-prime comparison has been used at this stage. -/
theorem prime_mixed_affine_source {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    ((j+1-B.card : ℕ) : ℝ)/(g : ℝ)*
      ((m : ℝ)*∏ i ∈ A, (1 : ℝ)/(p i : ℝ)-1)-((j+1-B.card : ℕ) : ℝ) ≤
        mixedMass m A B (fun x i => decide (x ≡ r (p i) [MOD p i])) := by
  have hA : ∀ q ∈ A.image p, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact hp i
  have hB : ∀ q ∈ B.image p, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact hp i
  have hdis := (disjoint_image hinj).mpr hd
  have hh := MixedPattern.mixedCount_affine_lower h hg m (A.image p) (B.image p) r hA hB hdis
  rw [card_image_of_injective B hinj] at hh
  rw [mixedMass_prime_eq, prime_image_prod_inv p hinj A, mul_one_div]
  exact hh

/-- An already valid Jacobsthal bound yields a rigorously density-discounted
source after boosting arbitrary distinct primes to larger reference marginals.
In particular, a bound for a smaller budget is not inserted unchanged. -/
theorem reference_cardinality_mixed_lower {j g : ℕ}
    (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (q' : ι → ℝ) (hq' : ∀ i, (1 : ℝ)/(p i : ℝ) ≤ q' i ∧ q' i ≤ 1)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    (∏ i ∈ B, (1-q' i)) * max 0
      (((j+1-B.card : ℕ) : ℝ)/(g : ℝ)*
        ((m : ℝ)*∏ i ∈ A, q' i-1)-((j+1-B.card : ℕ) : ℝ)) ≤
      average (fun i => (q' i-1/(p i : ℝ))/(1-1/(p i : ℝ)))
        (fun η => mixedMass m A B
          (fun x i => decide (x ≡ r (p i) [MOD p i]) || η i)) := by
  have hq (i : ι) : 0 ≤ (1 : ℝ)/(p i : ℝ) ∧ (1 : ℝ)/(p i : ℝ) < 1 ∧
      (1 : ℝ)/(p i : ℝ) ≤ q' i ∧ q' i ≤ 1 := by
    have hpR : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    refine ⟨by positivity, ?_, (hq' i).1, (hq' i).2⟩
    exact (div_lt_one (by linarith : (0 : ℝ) < p i)).mpr hpR
  apply reference_mixed_affine_lower (fun i => 1/(p i : ℝ)) q' hq m A B hd
  intro U hU
  exact prime_mixed_affine_source h hg p hp hinj r m U B (hd.mono_left hU)

/-- Specialization for a proposed strong induction. The terminal budget is
explicitly excluded from the source hypotheses. -/
theorem reference_mixed_lower_of_smaller_quadratic {C K j : ℕ} (hC : 0 < C)
    (h : ∀ i, 0 < i → i < K → IsJacobsthalBound i (C*i^2))
    (hj : 0 < j) (hjK : j < K)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (q' : ι → ℝ) (hq' : ∀ i, (1 : ℝ)/(p i : ℝ) ≤ q' i ∧ q' i ≤ 1)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    (∏ i ∈ B, (1-q' i)) * max 0
      (((j+1-B.card : ℕ) : ℝ)/((C*j^2 : ℕ) : ℝ)*
        ((m : ℝ)*∏ i ∈ A, q' i-1)-((j+1-B.card : ℕ) : ℝ)) ≤
      average (fun i => (q' i-1/(p i : ℝ))/(1-1/(p i : ℝ)))
        (fun η => mixedMass m A B
          (fun x i => decide (x ≡ r (p i) [MOD p i]) || η i)) :=
  reference_cardinality_mixed_lower (h j hj hjK) (mul_pos hC (pow_pos hj 2))
    p hp hinj q' hq' r m A B hd

#print axioms prime_mixed_affine_source
#print axioms reference_cardinality_mixed_lower
#print axioms reference_mixed_lower_of_smaller_quadratic
end Erdos970.FiniteSelberg
