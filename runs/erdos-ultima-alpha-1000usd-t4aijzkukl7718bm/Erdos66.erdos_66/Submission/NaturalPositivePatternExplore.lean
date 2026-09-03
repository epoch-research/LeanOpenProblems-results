import Submission.PositiveBinaryExpansionExplore
import Submission.PrefixBalancedCostCompactnessExplore

/-! Positive finite-coordinate polynomial patterns on natural-number Boolean
sequences, with a lift to the finite ordered-rounding interface. -/
namespace Erdos66NaturalPositivePattern
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66OrderedPositiveRounding Erdos66OrderedPipagePrefix
  Erdos66PositiveBinaryExpansion
open scoped Classical Topology
set_option maxHeartbeats 2000000

structure Pattern where
  Term : Type
  terms : Finset Term
  coeff : Term → ℝ
  support : Term → Finset ℕ
  nonneg : ∀ k∈terms, 0 ≤ coeff k

noncomputable def Pattern.eval (P : Pattern) (x : ℕ → ℝ) : ℝ :=
  ∑ k∈P.terms, P.coeff k*∏ i∈P.support k, x i

noncomputable def Pattern.value (P : Pattern) (f : ℕ → Bool) : ℝ :=
  P.eval (fun i ↦ bit (f i))

lemma Pattern.eval_nonneg (P : Pattern) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ P.eval x :=
  Finset.sum_nonneg (fun k hk ↦ mul_nonneg (P.nonneg k hk) (Finset.prod_nonneg (fun i _ ↦ hx i)))

lemma Pattern.value_nonneg (P : Pattern) (f : ℕ → Bool) : 0 ≤ P.value f :=
  P.eval_nonneg _ (fun i ↦ by cases f i <;> norm_num [bit])

lemma Pattern.continuous_value (P : Pattern) : Continuous P.value := by
  apply continuous_finset_sum
  intro k hk
  apply continuous_const.mul
  apply continuous_finset_prod
  intro i hi
  exact (continuous_of_discreteTopology (f := bit)).comp (continuous_apply i)

noncomputable def liftSupport (L : ℕ) (S : Finset ℕ) : Finset (Fin (L+1)) :=
  Finset.univ.filter (fun i ↦ i.val∈S)

lemma prod_liftSupport (L : ℕ) (S : Finset ℕ) (hS : ∀ i∈S, i ≤ L) (x : ℕ → ℝ) :
    (∏ i∈liftSupport L S, x i.val)=∏ i∈S, x i := by
  apply Finset.prod_bij (fun i hi ↦ i.val)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj he
    exact Fin.ext he
  · intro i hi
    exact ⟨⟨i,by have := hS i hi; omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  · intro i hi
    rfl

noncomputable def Pattern.bound (P : Pattern) : ℕ :=
  P.terms.sup (fun k ↦ (P.support k).sup id)

lemma Pattern.le_bound (P : Pattern) (k : P.Term) (hk : k∈P.terms) (i : ℕ) (hi : i∈P.support k) :
    i ≤ P.bound := by
  exact (Finset.le_sup (f := id) hi).trans (Finset.le_sup (f := fun k ↦ (P.support k).sup id) hk)

lemma selected_bit (L : ℕ) (ω : Fin (L+1) → Bool) (i : Fin (L+1)) :
    bit (decide (i.val∈selected L ω))=bit (ω i) := by
  simp only [mem_selected,Bool.decide_eq_true]

 theorem exists_pattern_selection {α κ : Type*} (L : ℕ) (J : Finset α) (P : α → Pattern)
    (hL : ∀ j∈J, (P j).bound ≤ L)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0 ≤ w k)
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ∃ ω : Fin (L+1) → Bool, Brackets (fun i ↦ p i.val) (fun i ↦ bit (ω i)) ∧
      (∑ j∈J, (P j).value (fun i ↦ decide (i∈selected L ω)))+
      (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k):ℝ))) ≤
      (∑ j∈J, (P j).eval p)+
      ∑ k∈T, w k*(Real.exp (2*|t k|)*expect (fun i : Fin (L+1) ↦ p i.val)
        (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k):ℝ)))) := by
  let Q : Finset (Σ j : α, (P j).Term) := J.sigma (fun j ↦ (P j).terms)
  let c : (Σ j : α, (P j).Term) → ℝ := fun q ↦ (P q.1).coeff q.2
  let E : (Σ j : α, (P j).Term) → Finset (Fin (L+1)) := fun q ↦ liftSupport L ((P q.1).support q.2)
  have hc : ∀ q∈Q, 0 ≤ c q := by
    intro q hq
    exact (P q.1).nonneg q.2 (Finset.mem_sigma.mp hq).2
  have hpoly (x : ℕ → ℝ) : poly Q c E (fun i ↦ x i.val)=∑ j∈J, (P j).eval x := by
    simp only [poly,Q,c,E,Finset.sum_sigma,Pattern.eval]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    exact prod_liftSupport L _ (fun i hi ↦ ((P j).le_bound k hk i hi).trans (hL j hj)) x
  obtain ⟨ω,hbr,hcost⟩ := exists_combined_selection L Q c E hc T n t w hw
    (fun i ↦ p i.val) (fun i ↦ hp i.val)
  have hω : poly Q c E (fun i ↦ bit (ω i))=∑ j∈J, (P j).value (fun i ↦ decide (i∈selected L ω)) := by
    have hh := hpoly (fun i ↦ bit (decide (i∈selected L ω)))
    simpa only [selected_bit,Pattern.value] using hh
  refine ⟨ω,hbr,?_⟩
  rw [←poly_eq_expect,hpoly,hω] at hcost
  exact hcost

end Erdos66NaturalPositivePattern
