import Submission.PositiveBinaryExpansionExplore
import Submission.MatchingPartitionExplore
import Submission.BoundedConflictExplore

/-! Positive matching polynomials for rare-pattern constraints in ordered
Bernoulli rounding. This is a finite selection tool, not an Erdos 66 witness. -/
namespace Erdos66BernoulliMatchingPolynomial
open Erdos66FiniteBernoulli Erdos66MatchingPartition Erdos66BoundedConflict
  Erdos66PositiveBinaryExpansion
open scoped Classical
set_option maxHeartbeats 2200000
variable {ι κ : Type*} [Fintype ι]

noncomputable def matchingPoly (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ M ∈ matchings S E, (Real.exp t-1)^M.card * ∏ i ∈ M.biUnion E, p i

lemma matchingPoly_nonneg (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (ht : 0 ≤ t)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ matchingPoly S E t p := by
  apply Finset.sum_nonneg
  intro M hM
  exact mul_nonneg (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)) _)
    (Finset.prod_nonneg (fun i _ ↦ hp i))

lemma matchingPoly_binary (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (ω : ι → Bool) :
    matchingPoly S E t (fun i ↦ bit (ω i)) = partition S E (fun e ↦ monomial (E e)) t ω := by
  unfold matchingPoly partition
  apply Finset.sum_congr rfl
  intro M hM
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  exact (product_monomials_overlapping M E ω).symm

lemma matchingPoly_expect (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (p : ι → ℝ) :
    expect p (fun ω ↦ matchingPoly S E t (fun i ↦ bit (ω i))) = matchingPoly S E t p := by
  simp only [matchingPoly, expect_sum, expect_const_mul]
  apply Finset.sum_congr rfl
  intro M hM
  rw [show (fun ω : ι → Bool ↦ ∏ i∈M.biUnion E, bit (ω i)) = monomial (M.biUnion E) from rfl,
    expect_monomial]

lemma matchingPoly_upper (S : Finset κ) (E : κ → Finset ι) (t : ℝ) (ht : 0 ≤ t)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    matchingPoly S E t p ≤ Real.exp ((Real.exp t-1)*∑ e∈S, ∏ i∈E e, p i) := by
  have hw : 0 ≤ Real.exp t-1 := sub_nonneg.mpr (Real.one_le_exp ht)
  have he : matchingPoly S E t p = ∑ M∈matchings S E,
      ∏ e∈M, (Real.exp t-1)*(∏ i∈E e, p i) := by
    apply Finset.sum_congr rfl
    intro M hM
    obtain ⟨hMS,hM⟩ := Finset.mem_filter.mp hM
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_biUnion hM]
  rw [he]
  calc
    _ ≤ ∑ M∈S.powerset, ∏ e∈M, (Real.exp t-1)*(∏ i∈E e, p i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro M hM hn
      exact Finset.prod_nonneg (fun e he ↦ mul_nonneg hw (Finset.prod_nonneg (fun i _ ↦ hp i)))
    _ = ∏ e∈S, (1+(Real.exp t-1)*(∏ i∈E e, p i)) := (Finset.prod_one_add S).symm
    _ ≤ ∏ e∈S, Real.exp ((Real.exp t-1)*(∏ i∈E e, p i)) := by
      apply Finset.prod_le_prod
      · intro e he
        exact add_nonneg (by norm_num) (mul_nonneg hw (Finset.prod_nonneg (fun i _ ↦ hp i)))
      · intro e he
        linarith [Real.add_one_le_exp ((Real.exp t-1)*(∏ i∈E e, p i))]
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

noncomputable def realized (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) : Finset κ :=
  S.filter (fun e ↦ ∀ i∈E e, ω i=true)

lemma mem_realized (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) (e : κ) :
    e∈realized S E ω ↔ e∈S ∧ ∀ i∈E e, ω i=true := by
  simp only [realized,Finset.mem_filter]

lemma realized_subset (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) :
    realized S E ω ⊆ S := Finset.filter_subset _ _

lemma matchingPoly_bounds_realized (S : Finset κ) (E : κ → Finset ι)
    (D k : ℕ) (hne : ∀ e∈S, (E e).Nonempty)
    (hdeg : ∀ e∈S, (S.filter (fun f ↦ ¬ Disjoint (E e) (E f))).card ≤ D)
    (t : ℝ) (ht : 0 < t) (ω : ι → Bool)
    (hcost : matchingPoly S E t (fun i ↦ bit (ω i)) < Real.exp (t*(k+1))) :
    (realized S E ω).card ≤ D*k := by
  let R := realized S E ω
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hdegR : ∀ e∈R, (R.filter (fun f ↦ ¬ Disjoint (E e) (E f))).card ≤ D := by
    intro e he
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hRS)).trans (hdeg e (hRS he))
  obtain ⟨M,hMR,hM,hcard⟩ := exists_large_disjoint R E D (fun e he ↦ hne e (hRS he)) hdegR
  have hreal : ∀ e∈M, monomial (E e) ω=1 := by
    intro e he
    exact monomial_eq_one _ _ (Finset.mem_filter.mp (hMR he)).2
  have hnon : ∀ e∈S, 0 ≤ monomial (E e) ω := by
    intro e he
    rcases monomial_binary (E e) ω with h | h <;> rw [h] <;> norm_num
  have hh := exp_card_le_partition S M E (fun e ↦ monomial (E e)) t ht.le ω hnon
    (hMR.trans hRS) hM hreal
  rw [← matchingPoly_binary] at hh
  by_contra hn
  have hkM : k+1 ≤ M.card := by
    have hg : D*k < R.card := by exact lt_of_not_ge hn
    by_contra hm
    have hh' := Nat.mul_le_mul_left D (show M.card ≤ k by omega)
    omega
  have hkR : (k : ℝ)+1 ≤ M.card := by exact_mod_cast hkM
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkR ht.le)
  exact (not_lt_of_ge (he.trans hh)) hcost

end Erdos66BernoulliMatchingPolynomial
