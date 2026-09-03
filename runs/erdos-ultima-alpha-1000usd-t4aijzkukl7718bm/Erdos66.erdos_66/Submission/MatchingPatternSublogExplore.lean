import Submission.PatternSublogRoundingExplore

/-! Countable sublogarithmic rounding for weighted disjoint-coordinate
patterns. This includes linear/quadratic insertion matchings once their
fractional means have been established. -/
namespace Erdos66MatchingPatternSublog
open Filter Erdos66NaturalPositivePattern Erdos66PatternSublogRounding
  Erdos66FiniteBernoulli Erdos66ClampedPrefixContinuation
open scoped Classical Topology
set_option maxHeartbeats 3000000

noncomputable def expPattern (P : Pattern) (t : ℝ) (ht : 0 ≤ t) : Pattern where
  Term := Finset P.Term
  terms := P.terms.powerset
  coeff := fun T ↦ ∏ k∈T, (Real.exp (t*P.coeff k)-1)
  support := fun T ↦ T.biUnion P.support
  nonneg := by
    intro T hT
    exact Finset.prod_nonneg (fun k hk ↦ sub_nonneg.mpr (Real.one_le_exp
      (mul_nonneg ht (P.nonneg k (Finset.mem_powerset.mp hT hk)))))

lemma expPattern_eval_factor (P : Pattern)
    (hdisj : (P.terms : Set P.Term).PairwiseDisjoint P.support)
    (t : ℝ) (ht : 0 ≤ t) (p : ℕ → ℝ) :
    (expPattern P t ht).eval p =
      ∏ k∈P.terms, (1+(Real.exp (t*P.coeff k)-1)*(∏ i∈P.support k, p i)) := by
  rw [Finset.prod_one_add]
  simp only [Pattern.eval,expPattern]
  apply Finset.sum_congr rfl
  intro T hT
  have hTD : (T : Set P.Term).PairwiseDisjoint P.support := by
    intro i hi j hj hij
    exact hdisj ((Finset.mem_powerset.mp hT) hi) ((Finset.mem_powerset.mp hT) hj) hij
  rw [Finset.prod_biUnion hTD,Finset.prod_mul_distrib]

lemma prod_bits_binary (S : Finset ℕ) (f : ℕ → Bool) :
    (∏ i∈S, bit (f i))=0 ∨ (∏ i∈S, bit (f i))=1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    cases hf : f a <;> simp_all [bit]

lemma expPattern_value (P : Pattern)
    (hdisj : (P.terms : Set P.Term).PairwiseDisjoint P.support)
    (t : ℝ) (ht : 0 ≤ t) (f : ℕ → Bool) :
    (expPattern P t ht).value f=Real.exp (t*P.value f) := by
  rw [Pattern.value,expPattern_eval_factor P hdisj]
  simp only [Pattern.value,Pattern.eval,Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  rcases prod_bits_binary (P.support k) f with h | h <;> rw [h] <;> simp

lemma expPattern_mean_bound (P : Pattern)
    (hdisj : (P.terms : Set P.Term).PairwiseDisjoint P.support)
    (hc : ∀ k∈P.terms, 1 ≤ P.coeff k ∧ P.coeff k ≤ 2)
    (t : ℝ) (ht : 0 ≤ t) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (expPattern P t ht).eval p ≤ Real.exp (Real.exp (2*t)*P.eval p) := by
  rw [expPattern_eval_factor P hdisj]
  simp only [Pattern.eval,Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_le_prod
  · intro k hk
    exact add_nonneg zero_le_one (mul_nonneg
      (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg ht (P.nonneg k hk))))
      (Finset.prod_nonneg (fun i _ ↦ hp i)))
  · intro k hk
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hc k hk).2 ht)
    have he' : Real.exp (t*P.coeff k)-1 ≤ Real.exp (2*t)*P.coeff k := by
      have hh := mul_le_mul_of_nonneg_left (hc k hk).1 (Real.exp_pos (2*t)).le
      rw [mul_one] at hh
      have hcomm : t*2=2*t := by ring
      rw [hcomm] at he
      linarith
    have hv : 0 ≤ ∏ i∈P.support k, p i := Finset.prod_nonneg (fun i _ ↦ hp i)
    have hh := mul_le_mul_of_nonneg_right he' hv
    have hb := Real.add_one_le_exp (Real.exp (2*t)*(P.coeff k*∏ i∈P.support k, p i))
    nlinarith

 theorem exists_matching_sublog_rounding (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : ℕ → Pattern)
    (hdisj : ∀ n, ((P n).terms : Set (P n).Term).PairwiseDisjoint (P n).support)
    (hc : ∀ n k, k∈(P n).terms → 1 ≤ (P n).coeff k ∧ (P n).coeff k ≤ 2)
    (hmean : Tendsto (fun n : ℕ ↦ (P n).eval p/Real.log ((n : ℝ)+2)) atTop (𝓝 0)) :
    ∃ A : Set ℕ, (∀ L, PrefixBrackets p A L) ∧ (∀ i∈A, p i≠0) ∧
      Tendsto (fun n : ℕ ↦ (P n).value (fun i ↦ decide (i∈A))/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  let Q (j n : ℕ) := expPattern (P n) ((j : ℝ)+1) (by positivity)
  apply exists_supported_sublog_rounding p hp Q (fun n ↦ (P n).value)
    (fun n f ↦ (P n).value_nonneg f) (fun n ↦ (P n).eval p)
    (fun j ↦ Real.exp (2*((j : ℝ)+1))) hmean
  · intro j n
    exact expPattern_mean_bound (P n) (hdisj n) (hc n) _ (by positivity) p (fun i ↦ (hp i).1)
  · intro j n f
    exact (expPattern_value (P n) (hdisj n) _ (by positivity) f).symm.le

end Erdos66MatchingPatternSublog
