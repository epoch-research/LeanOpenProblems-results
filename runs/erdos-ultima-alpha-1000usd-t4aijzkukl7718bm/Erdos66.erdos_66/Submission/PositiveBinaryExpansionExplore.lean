import Submission.CombinedPipageExplore

/-! Positive multilinear expansions of exponentials of arbitrary nonnegative
binary monomial sums. Overlapping supports are permitted. -/
namespace Erdos66PositiveBinaryExpansion
open Erdos66FiniteBernoulli Erdos66OrderedPositiveRounding Erdos66CombinedPipage
  Erdos66OrderedPipagePrefix Erdos66PrefixBalancedUpperSelection Erdos66FiniteRepBernoulli
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2200000

variable {ι κ : Type*} [Fintype ι]

lemma monomial_eq_one (S : Finset ι) (ω : ι → Bool) (h : ∀ i∈S, ω i=true) :
    monomial S ω=1 := by
  apply Finset.prod_eq_one
  intro i hi
  simp only [bit,h i hi,if_true]

lemma monomial_eq_zero (S : Finset ι) (ω : ι → Bool) (i : ι) (hi : i∈S) (h : ω i=false) :
    monomial S ω=0 := by
  apply Finset.prod_eq_zero hi
  simp only [bit,h,Bool.false_eq_true,if_false]

lemma product_monomials_overlapping (S : Finset κ) (E : κ → Finset ι) (ω : ι → Bool) :
    (∏ k∈S, monomial (E k) ω)=monomial (S.biUnion E) ω := by
  by_cases hall : ∀ i∈S.biUnion E, ω i=true
  · rw [monomial_eq_one _ _ hall]
    apply Finset.prod_eq_one
    intro k hk
    exact monomial_eq_one _ _ (fun i hi ↦ hall i (Finset.mem_biUnion.mpr ⟨k,hk,hi⟩))
  · push_neg at hall
    obtain ⟨i,hi,hω⟩ := hall
    have hω' : ω i=false := Bool.eq_false_iff.mpr hω
    rw [monomial_eq_zero _ _ i hi hω']
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hi
    exact Finset.prod_eq_zero hk (monomial_eq_zero _ _ i hik hω')

noncomputable def multilinearExp (S : Finset κ) (E : κ → Finset ι) (w : κ → ℝ)
    (t : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ T∈S.powerset, (∏ k∈T, (Real.exp (t*w k)-1))*(∏ i∈T.biUnion E, p i)

lemma multilinearExp_binary (S : Finset κ) (E : κ → Finset ι) (w : κ → ℝ)
    (t : ℝ) (ω : ι → Bool) :
    multilinearExp S E w t (fun i ↦ bit (ω i))=
      Real.exp (t*∑ k∈S, w k*monomial (E k) ω) := by
  have he : Real.exp (t*∑ k∈S, w k*monomial (E k) ω)=
      ∏ k∈S, (1+(Real.exp (t*w k)-1)*monomial (E k) ω) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro k hk
    rcases monomial_binary (E k) ω with hm | hm <;> rw [hm] <;> simp <;> ring
  rw [he]
  simp_rw [add_comm (1:ℝ)]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one,mul_one,Finset.prod_mul_distrib]
  unfold multilinearExp
  apply Finset.sum_congr rfl
  intro T hT
  rw [product_monomials_overlapping]
  rfl

lemma multilinearExp_eq_expect (S : Finset κ) (E : κ → Finset ι) (w : κ → ℝ)
    (t : ℝ) (p : ι → ℝ) :
    multilinearExp S E w t p=expect p
      (fun ω ↦ Real.exp (t*∑ k∈S, w k*monomial (E k) ω)) := by
  simp_rw [←multilinearExp_binary]
  simp only [multilinearExp,expect_sum,expect_const_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show (fun ω : ι → Bool ↦ ∏ i∈T.biUnion E, bit (ω i))=monomial (T.biUnion E) from rfl,
    expect_monomial]

lemma multilinearExp_coeff_nonneg (S : Finset κ) (w : κ → ℝ) (hw : ∀ k∈S, 0≤w k)
    (t : ℝ) (ht : 0≤t) (T : Finset κ) (hT : T∈S.powerset) :
    0≤∏ k∈T, (Real.exp (t*w k)-1) := by
  apply Finset.prod_nonneg
  intro k hk
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (mul_nonneg ht (hw k (Finset.mem_powerset.mp hT hk))))

lemma poly_eq_expect {N : ℕ} {η : Type*} (S : Finset η) (c : η → ℝ)
    (E : η → Finset (Fin N)) (p : Fin N → ℝ) :
    poly S c E p=expect p (fun ω ↦ poly S c E (fun i ↦ bit (ω i))) := by
  simp only [poly,expect_sum,expect_const_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (fun ω : Fin N → Bool ↦ ∏ i∈E k, bit (ω i))=monomial (E k) from rfl,expect_monomial]

 theorem exists_combined_selection {η : Type*} (L : ℕ)
    (S : Finset η) (c : η → ℝ) (E : η → Finset (Fin (L+1))) (hc : ∀ k∈S, 0≤c k)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ) (hw : ∀ k∈T, 0≤w k)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1) :
    ∃ ω : Fin (L+1) → Bool, Brackets p (fun i ↦ bit (ω i)) ∧
      poly S c E (fun i ↦ bit (ω i))+(∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ)))≤
        expect p (fun σ ↦ poly S c E (fun i ↦ bit (σ i)))+
        ∑ k∈T, w k*(Real.exp (2*|t k|)*expect p
          (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ)))) := by
  obtain ⟨y,hy,hbr,hcost⟩ := exists_compensated_rounding_with_poly L S c E hc T n t w hw p hp
  let ω : Fin (L+1) → Bool := fun i ↦ decide (y i=1)
  have he : (fun i ↦ bit (ω i))=y := by
    funext i
    rcases hy i with hi | hi <;> simp [ω,bit,hi]
  refine ⟨ω,by simpa only [he] using hbr,?_⟩
  rw [←he] at hcost
  simp only [expPoly_eq_expect,expect_pure] at hcost
  rw [poly_eq_expect S c E p] at hcost
  exact hcost

end Erdos66PositiveBinaryExpansion
