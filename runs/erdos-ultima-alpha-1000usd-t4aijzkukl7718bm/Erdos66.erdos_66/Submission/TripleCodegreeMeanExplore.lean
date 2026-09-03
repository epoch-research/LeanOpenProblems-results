import Submission.TripleCodegreeGeometryExplore
import Submission.BernoulliMatchingExplore
import Submission.RandomConstantProfileExplore

/-! The expected nondegenerate triple count is bounded by the maximum
selection probability times a pair mean, rather than by the ambient length. -/
namespace Erdos66TripleCodegreeMean
open Erdos66TripleCodegreeGeometry Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66BernoulliMatching Erdos66RandomConstantProfile Erdos66ConstantProfile
open scoped Classical
set_option maxHeartbeats 1800000

lemma triple_monomial_mass (L b q : ℕ) (p : Fin (L+1) → ℝ) (P : ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ P) :
    (∑ x∈tripleEvents L b q, ∏ i∈tripleSupport x, p i) ≤
      P*(∑ a∈pairs L q, p a.1*p a.2) := by
  let S := tripleEvents L b q
  let f : Triple L → Fin (L+1) × Fin (L+1) := fun x ↦ (x.1,x.2.2)
  have hP : 0 ≤ P := (hp 0).1.trans (hp 0).2
  have hs : S.image f ⊆ pairs L q := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact mem_pairs.mpr (mem_tripleEvents.mp hx).2.1
  have hinj : Set.InjOn f (S : Set (Triple L)) := by
    intro x hx y hy he
    have hx' := mem_tripleEvents.mp hx
    have hy' := mem_tripleEvents.mp hy
    have he' : (x.1,x.2.2)=(y.1,y.2.2) := he
    have he₁ := congrArg (fun z : Fin (L+1) × Fin (L+1) ↦ z.1) he'
    change x.1=y.1 at he₁
    have he₂ := congrArg (fun z : Fin (L+1) × Fin (L+1) ↦ z.2) he'
    change x.2.2=y.2.2 at he₂
    have hv := congrArg Fin.val he₁
    exact Prod.ext he₁ (Prod.ext (Fin.ext (by omega)) he₂)
  have hprod (x : Triple L) (hx : x∈S) :
      (∏ i∈tripleSupport x, p i) ≤ P*(p x.1*p x.2.2) := by
    have hx' := mem_tripleEvents.mp hx
    have hn₁ : x.1 ∉ ({x.2.1,x.2.2} : Finset _) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨hx'.2.2.1,hx'.2.2.2.1⟩
    have hn₂ : x.2.1 ∉ ({x.2.2} : Finset _) := by
      simpa only [Finset.mem_singleton] using hx'.2.2.2.2
    rw [tripleSupport,Finset.prod_insert hn₁,Finset.prod_insert hn₂,Finset.prod_singleton]
    have hh := mul_le_mul_of_nonneg_right (hp x.2.1).2 (mul_nonneg (hp x.1).1 (hp x.2.2).1)
    nlinarith
  calc
    _ ≤ ∑ x∈S, P*(p x.1*p x.2.2) := Finset.sum_le_sum hprod
    _ = P*(∑ x∈S, p x.1*p x.2.2) := (Finset.mul_sum _ _ _).symm
    _ = P*(∑ a∈S.image f, p a.1*p a.2) := by rw [Finset.sum_image]; exact hinj
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hs (fun a _ _ ↦ mul_nonneg (hp a.1).1 (hp a.2).1)) hP

lemma shifted_triple_mass (μ : ℝ) (s L b q : ℕ) (hμ : 0 ≤ μ) :
    (∑ x∈tripleEvents L b q, ∏ i∈tripleSupport x, probability μ s L i) ≤
      μ*Real.sqrt μ*Erdos66ConstantProfile.b s := by
  have hp (i : Fin (L+1)) : 0 ≤ probability μ s L i ∧ probability μ s L i ≤ Real.sqrt μ*Erdos66ConstantProfile.b s := by
    constructor
    · exact mul_nonneg (Real.sqrt_nonneg μ) (b_pos _).le
    · exact mul_le_mul_of_nonneg_left (b_antitone (by omega : s ≤ i.val+s)) (Real.sqrt_nonneg μ)
  have h₁ := triple_monomial_mass L b q (probability μ s L) (Real.sqrt μ*Erdos66ConstantProfile.b s) hp
  have h₂ := mul_le_mul_of_nonneg_left (full_mean_upper μ s L q hμ)
    (mul_nonneg (Real.sqrt_nonneg μ) (b_pos s).le)
  nlinarith

end Erdos66TripleCodegreeMean
