import Submission.FiniteBernoulliExplore
import Submission.MatchingPartitionExplore
import Submission.BoundedConflictExplore

/-! Matching-partition concentration for nonuniform Bernoulli coordinates.
A bounded-conflict family of monomials need not be pairwise disjoint. -/
namespace Erdos66BernoulliMatching
open Erdos66FiniteBernoulli Erdos66MatchingPartition Erdos66BoundedConflict
open scoped Classical
set_option maxHeartbeats 1800000
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

noncomputable def realized (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) : Finset κ :=
  S.filter (fun e ↦ monomial (E e) ω=1)

lemma expect_partition_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (ht : 0 ≤ t) :
    expect p (partition S E (fun e ω ↦ monomial (E e) ω) t) ≤
      Real.exp ((Real.exp t-1)*(∑ e∈S, ∏ i∈E e, p i)) := by
  have hw : 0 ≤ Real.exp t-1 := sub_nonneg.mpr (Real.one_le_exp ht)
  unfold partition
  rw [expect_sum]
  have he (M : Finset κ) (hM : M∈matchings S E) :
      expect p (fun ω ↦ ∏ e∈M, (Real.exp t-1)*monomial (E e) ω) =
        ∏ e∈M, (Real.exp t-1)*(∏ i∈E e, p i) := by
    have hdis := (Finset.mem_filter.mp hM).2
    simp_rw [Finset.prod_mul_distrib]
    rw [expect_const_mul,expect_product_monomials p M E hdis]
  rw [Finset.sum_congr rfl he]
  calc
    _ ≤ ∑ M∈S.powerset, ∏ e∈M, (Real.exp t-1)*(∏ i∈E e, p i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro M hM hn
      exact Finset.prod_nonneg (fun e he ↦ mul_nonneg hw (Finset.prod_nonneg (fun i hi ↦ (hp i).1)))
    _ = ∏ e∈S, (1+(Real.exp t-1)*(∏ i∈E e, p i)) := (Finset.prod_one_add S).symm
    _ ≤ ∏ e∈S, Real.exp ((Real.exp t-1)*(∏ i∈E e, p i)) := by
      apply Finset.prod_le_prod
      · intro e he
        exact add_nonneg (by norm_num) (mul_nonneg hw (Finset.prod_nonneg (fun i hi ↦ (hp i).1)))
      · intro e he
        linarith [Real.add_one_le_exp ((Real.exp t-1)*(∏ i∈E e, p i))]
    _ = _ := by rw [←Real.exp_sum,←Finset.mul_sum]

lemma realized_exp_le_partition (S : Finset κ) (E : κ → Finset ι) (d : ℕ)
    (hne : ∀ e∈S, (E e).Nonempty)
    (hdeg : ∀ e∈S, (S.filter (fun f ↦ ¬Disjoint (E e) (E f))).card ≤ d)
    (ω : ι → Bool) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t*(realized S E ω).card) ≤
      partition S E (fun e ω ↦ monomial (E e) ω) (d*t) ω := by
  let R := realized S E ω
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hdegR (e : κ) (he : e∈R) : (R.filter (fun f ↦ ¬Disjoint (E e) (E f))).card ≤ d :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hRS)).trans (hdeg e (hRS he))
  obtain ⟨M,hMR,hM,hcard⟩ := exists_large_disjoint R E d (fun e he ↦ hne e (hRS he)) hdegR
  have hc : (R.card : ℝ) ≤ d*(M.card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ Real.exp (((d : ℝ)*t)*M.card) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := exp_card_le_partition S M E (fun e ω ↦ monomial (E e) ω) (d*t)
      (by positivity) ω (fun e _ ↦ by
        change 0 ≤ monomial (E e) ω
        rcases monomial_binary (E e) ω with he | he <;> rw [he] <;> norm_num)
      (hMR.trans hRS) hM (fun e he ↦ (Finset.mem_filter.mp (hMR he)).2)

/-- Bounded conflict replaces independence of all events. The exponential
scale depends on d but the mean still charges the actual monomial masses. -/
theorem expect_exp_realized_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (E : κ → Finset ι) (d : ℕ)
    (hne : ∀ e∈S, (E e).Nonempty)
    (hdeg : ∀ e∈S, (S.filter (fun f ↦ ¬Disjoint (E e) (E f))).card ≤ d)
    (t : ℝ) (ht : 0 ≤ t) :
    expect p (fun ω ↦ Real.exp (t*(realized S E ω).card)) ≤
      Real.exp ((Real.exp (d*t)-1)*(∑ e∈S, ∏ i∈E e, p i)) := by
  exact (expect_mono p hp _ _ (fun ω ↦ realized_exp_le_partition S E d hne hdeg ω t ht)).trans
    (expect_partition_le p hp S E (d*t) (by positivity))

end Erdos66BernoulliMatching
