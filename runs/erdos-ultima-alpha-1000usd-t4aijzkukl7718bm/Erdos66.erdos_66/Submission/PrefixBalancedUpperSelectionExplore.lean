import Submission.OrderedPositiveRoundingExplore

/-! Simultaneous upper-tail potential selection while retaining all prefix
floor/ceiling bounds. This provides no shrinking-error pointwise limit. -/
namespace Erdos66PrefixBalancedUpperSelection
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66OrderedPipagePrefix Erdos66OrderedPositiveRounding
open scoped Classical
set_option maxHeartbeats 2200000

variable {ι : Type*} [Fintype ι]
lemma expect_pure (ω : ι → Bool) (F : (ι → Bool) → ℝ) :
    expect (fun i ↦ bit (ω i)) F=F ω := by
  have hw (σ : ι → Bool) : weight (fun i ↦ bit (ω i)) σ=if σ=ω then 1 else 0 := by
    by_cases h : σ=ω
    · subst σ
      simp only [weight,ite_true]
      have he (i : ι) : (if ω i then bit (ω i) else 1-bit (ω i))=(1:ℝ) := by
        cases hi : ω i <;> simp [bit,hi]
      simp only [he,Finset.prod_const_one]
    · rw [if_neg h]
      obtain ⟨i,hi⟩ : ∃ i, σ i≠ω i := by
        by_contra hn
        push_neg at hn
        exact h (funext hn)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases hs : σ i <;> cases ho : ω i <;> simp_all [bit]
  simp only [expect,hw,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

noncomputable def expPoly (L n : ℕ) (t : ℝ) (p : Fin (L+1) → ℝ) : ℝ :=
  ∏ a∈halfPairs L n, (1+(Real.exp (t*pairWeight a)-1)*∏ i∈pairCoords a, p i)

lemma expPoly_eq_expect (L n : ℕ) (t : ℝ) (p : Fin (L+1) → ℝ) :
    expPoly L n t p=expect p (fun ω ↦ Real.exp (t*(sumRep (selected L ω) n : ℝ))) := by
  simp_rw [selected_rep]
  exact (expect_exp_disjoint_monomials p (halfPairs L n) pairCoords
    (pairCoords_disjoint L n) pairWeight t).symm

lemma expPoly_expansion (L n : ℕ) (t : ℝ) (p : Fin (L+1) → ℝ) :
    expPoly L n t p =
      ∑ S∈(halfPairs L n).powerset,
        (∏ a∈S, (Real.exp (t*pairWeight a)-1))*(∏ i∈S.biUnion pairCoords, p i) := by
  unfold expPoly
  simp_rw [add_comm (1:ℝ)]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one,mul_one,Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_biUnion ((pairCoords_disjoint L n).mono (Finset.mem_powerset.mp hS))]

/-- Any finite nonnegative combination of upper exponential potentials can
be rounded without increasing its independent-Bernoulli mean, while every
prefix remains between the floor and ceiling of its fractional mass. -/
theorem exists_prefix_balanced_upper_selection {κ : Type*} (L : ℕ)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0≤p i ∧ p i≤1)
    (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ)
    (ht : ∀ k∈T, 0≤t k) (hw : ∀ k∈T, 0≤w k) :
    ∃ ω : Fin (L+1) → Bool,
      Brackets p (fun i ↦ bit (ω i)) ∧
      (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ)))≤
        expect p (fun σ ↦ ∑ k∈T, w k*Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ))) := by
  let U : Finset (Σ _k : κ, Finset (Fin (L+1) × Fin (L+1))) :=
    T.sigma (fun k ↦ (halfPairs L (n k)).powerset)
  let c : (Σ _k : κ, Finset (Fin (L+1) × Fin (L+1))) → ℝ :=
    fun z ↦ w z.1*∏ a∈z.2, (Real.exp (t z.1*pairWeight a)-1)
  let E : (Σ _k : κ, Finset (Fin (L+1) × Fin (L+1))) → Finset (Fin (L+1)) :=
    fun z ↦ z.2.biUnion pairCoords
  have hc : ∀ z∈U, 0≤c z := by
    intro z hz
    obtain ⟨hk,hS⟩ := Finset.mem_sigma.mp hz
    apply mul_nonneg (hw z.1 hk)
    apply Finset.prod_nonneg
    intro a ha
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg (ht z.1 hk) (pairWeight_bounds a).1))
  have hpoly (x : Fin (L+1) → ℝ) :
      poly U c E x=∑ k∈T, w k*expPoly L (n k) (t k) x := by
    simp only [poly,U,Finset.sum_sigma,c,E,expPoly_expansion,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro S hS
    ring
  obtain ⟨y,hy,hbr,hcost⟩ := exists_prefix_balanced_rounding U c E hc p hp
  let ω : Fin (L+1) → Bool := fun i ↦ decide (y i=1)
  have he : (fun i ↦ bit (ω i))=y := by
    funext i
    rcases hy i with hi | hi <;> simp [ω,bit,hi]
  refine ⟨ω,by simpa only [he] using hbr,?_⟩
  rw [hpoly,hpoly,←he] at hcost
  simp only [expPoly_eq_expect,expect_pure] at hcost
  rw [expect_sum]
  simp only [expect_const_mul]
  exact hcost

end Erdos66PrefixBalancedUpperSelection
