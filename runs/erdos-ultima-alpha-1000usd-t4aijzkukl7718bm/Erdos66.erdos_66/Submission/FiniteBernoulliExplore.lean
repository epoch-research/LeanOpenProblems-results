import FormalConjecturesUtil

/-! Finite Bernoulli product averages and exact moment generating functions
for disjoint binary monomials. No probabilistic existence claim for Erdos 66
is made in this file. -/
namespace Erdos66FiniteBernoulli
open scoped Classical
variable {ι κ : Type*} [Fintype ι]

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0
noncomputable def weight (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then p i else 1 - p i
noncomputable def expect (p : ι → ℝ) (F : (ι → Bool) → ℝ) : ℝ :=
  ∑ ω, weight p ω * F ω
noncomputable def monomial (S : Finset ι) (ω : ι → Bool) : ℝ := ∏ i ∈ S, bit (ω i)

lemma weight_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (ω : ι → Bool) :
    0 ≤ weight p ω := by
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

lemma expect_add (p : ι → ℝ) (F G : (ι → Bool) → ℝ) :
    expect p (fun ω ↦ F ω + G ω) = expect p F + expect p G := by
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_const_mul (p : ι → ℝ) (c : ℝ) (F : (ι → Bool) → ℝ) :
    expect p (fun ω ↦ c * F ω) = c * expect p F := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

lemma expect_sum (p : ι → ℝ) (S : Finset κ) (F : κ → (ι → Bool) → ℝ) :
    expect p (fun ω ↦ ∑ k ∈ S, F k ω) = ∑ k ∈ S, expect p (F k) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (F G : (ι → Bool) → ℝ) (h : ∀ ω, F ω ≤ G ω) : expect p F ≤ expect p G := by
  exact Finset.sum_le_sum (fun ω _ ↦ mul_le_mul_of_nonneg_left (h ω) (weight_nonneg p hp ω))

lemma expect_product (p : ι → ℝ) (S : Finset ι) (g : ι → Bool → ℝ) :
    expect p (fun ω ↦ ∏ i ∈ S, g i (ω i)) =
      ∏ i ∈ S, ((1 - p i) * g i false + p i * g i true) := by
  have hprod (ω : ι → Bool) : (∏ i ∈ S, g i (ω i)) =
      ∏ i : ι, if i ∈ S then g i (ω i) else 1 := by simp
  simp_rw [hprod]
  unfold expect weight
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) ↦ (if b then p i else 1 - p i) * (if i ∈ S then g i b else 1))]
  have hsum (i : ι) : (∑ b : Bool, (if b then p i else 1 - p i) *
      (if i ∈ S then g i b else 1)) =
      if i ∈ S then (1 - p i) * g i false + p i * g i true else 1 := by
    by_cases hi : i ∈ S <;> simp [hi] <;> ring
  simp_rw [hsum]
  simp

lemma expect_one (p : ι → ℝ) : expect p (fun _ ↦ (1 : ℝ)) = 1 := by
  simpa using expect_product p ∅ (fun _ _ ↦ (1 : ℝ))

lemma expect_const (p : ι → ℝ) (c : ℝ) : expect p (fun _ ↦ c) = c := by
  simpa using (expect_const_mul p c (fun _ ↦ (1 : ℝ))).trans (by rw [expect_one, mul_one])

lemma expect_monomial (p : ι → ℝ) (S : Finset ι) :
    expect p (monomial S) = ∏ i ∈ S, p i := by
  simpa [monomial, bit] using expect_product p S (fun _ ↦ bit)

lemma monomial_binary (S : Finset ι) (ω : ι → Bool) : monomial S ω = 0 ∨ monomial S ω = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih =>
    simp only [monomial, Finset.prod_insert hi] at ih ⊢
    rcases ih with ih | ih <;> rw [ih] <;> cases hω : ω i <;> simp [bit, hω]

lemma product_monomials (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j))) (ω : ι → Bool) :
    (∏ k ∈ S, monomial (E k) ω) = monomial (S.biUnion E) ω := by
  simp only [monomial]
  exact (Finset.prod_biUnion hE).symm

lemma expect_product_monomials (p : ι → ℝ) (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j))) :
    expect p (fun ω ↦ ∏ k ∈ S, monomial (E k) ω) = ∏ k ∈ S, ∏ i ∈ E k, p i := by
  simp_rw [product_monomials S E hE]
  rw [expect_monomial, Finset.prod_biUnion hE]

/-- Exact factorization for affine functions of monomials on disjoint sets
of Bernoulli coordinates. -/
lemma expect_product_affine (p : ι → ℝ) (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j))) (c : κ → ℝ) :
    expect p (fun ω ↦ ∏ k ∈ S, (1 + c k * monomial (E k) ω)) =
      ∏ k ∈ S, (1 + c k * ∏ i ∈ E k, p i) := by
  have hexp (ω : ι → Bool) : (∏ k ∈ S, (1 + c k * monomial (E k) ω)) =
      ∑ T ∈ S.powerset, (∏ k ∈ T, c k) * ∏ k ∈ T, monomial (E k) ω := by
    simp_rw [add_comm (1 : ℝ)]
    rw [Finset.prod_add]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [expect_sum]
  simp_rw [expect_const_mul]
  have hprod : (∑ T ∈ S.powerset, (∏ k ∈ T, c k) * expect p (fun ω ↦ ∏ k ∈ T, monomial (E k) ω)) =
      ∑ T ∈ S.powerset, (∏ k ∈ T, c k) * ∏ k ∈ T, ∏ i ∈ E k, p i := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [expect_product_monomials p T E (hE.mono (Finset.mem_powerset.mp hT))]
  rw [hprod]
  symm
  simp_rw [add_comm (1 : ℝ)]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]

/-- Exact MGF formula for a weighted sum of disjoint binary monomials. -/
theorem expect_exp_disjoint_monomials (p : ι → ℝ) (S : Finset κ) (E : κ → Finset ι)
    (hE : (S : Set κ).Pairwise (fun i j ↦ Disjoint (E i) (E j))) (w : κ → ℝ) (t : ℝ) :
    expect p (fun ω ↦ Real.exp (t * ∑ k ∈ S, w k * monomial (E k) ω)) =
      ∏ k ∈ S, (1 + (Real.exp (t * w k) - 1) * ∏ i ∈ E k, p i) := by
  have he (ω : ι → Bool) : Real.exp (t * ∑ k ∈ S, w k * monomial (E k) ω) =
      ∏ k ∈ S, (1 + (Real.exp (t * w k) - 1) * monomial (E k) ω) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro k hk
    rcases monomial_binary (E k) ω with hm | hm <;> rw [hm] <;> simp <;> ring
  simp_rw [he]
  exact expect_product_affine p S E hE (fun k ↦ Real.exp (t * w k) - 1)

end Erdos66FiniteBernoulli
