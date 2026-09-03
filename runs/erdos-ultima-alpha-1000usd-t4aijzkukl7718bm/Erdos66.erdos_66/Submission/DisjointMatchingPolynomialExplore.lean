import Submission.BernoulliMatchingPolynomialExplore

/-! On disjoint supports, the matching polynomial is exactly the exponential
of the Boolean realized-support count. -/
namespace Erdos66DisjointMatchingPolynomial
open Erdos66FiniteBernoulli Erdos66BernoulliMatchingPolynomial
  Erdos66MatchingPartition Erdos66PositiveBinaryExpansion
open scoped Classical
variable {ι κ : Type*} [Fintype ι]
set_option maxHeartbeats 1200000

lemma monomial_sum_eq_count (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) :
    (∑ e∈S, monomial (E e) ω)=((realized S E ω).card:ℝ) := by
  rw [realized,Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : ∀ i∈E e, ω i=true
  · rw [if_pos h,monomial_eq_one _ _ h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi,hω⟩ := h
    exact monomial_eq_zero _ _ i hi (Bool.eq_false_iff.mpr hω)

lemma matchingPoly_disjoint (S : Finset κ) (E : κ → Finset ι)
    (hdis : (S : Set κ).Pairwise (fun a b ↦ Disjoint (E a) (E b))) (t : ℝ) (p : ι → ℝ) :
    matchingPoly S E t p=multilinearExp S E (fun _ ↦ 1) t p := by
  have hm : matchings S E=S.powerset := by
    ext M
    simp only [matchings,Finset.mem_filter,Finset.mem_powerset]
    exact ⟨And.left,fun h ↦ ⟨h,hdis.mono h⟩⟩
  simp only [matchingPoly,hm,multilinearExp,mul_one,Finset.prod_const]

lemma matchingPoly_binary_disjoint (S : Finset κ) (E : κ → Finset ι)
    (hdis : (S : Set κ).Pairwise (fun a b ↦ Disjoint (E a) (E b))) (t : ℝ) (ω : ι → Bool) :
    matchingPoly S E t (fun i ↦ bit (ω i))=Real.exp (t*((realized S E ω).card:ℝ)) := by
  rw [matchingPoly_disjoint S E hdis,multilinearExp_binary]
  simp only [one_mul,monomial_sum_eq_count]

end Erdos66DisjointMatchingPolynomial
