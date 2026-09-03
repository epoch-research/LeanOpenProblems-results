import Submission.FiniteRepBernoulliExplore
import Submission.AffineRootAggregateExplore

/-! Simultaneous Bernoulli control of unsigned representation counts and a
bounded signed quadratic convolution. Positive and negative monomials are
selected together; the signed mean retains its diagonal correction. -/
namespace Erdos66SignedRepBernoulli
open Erdos66FiniteBernoulli Erdos66BernoulliConcentration Erdos66FiniteRepBernoulli
  Erdos66AffineRootAggregate Erdos66SharedParameterKernel AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def signedRep (L q : ℕ) (σ : ℕ → ℝ) (ω : Fin (L+1) → Bool) : ℝ :=
  ∑ a∈halfPairs L q, pairWeight a*(σ a.1.val*σ a.2.val)*monomial (pairCoords a) ω

noncomputable def signedMean (L q : ℕ) (σ : ℕ → ℝ) (p : Fin (L+1) → ℝ) : ℝ :=
  ∑ a∈halfPairs L q, pairWeight a*(σ a.1.val*σ a.2.val)*∏ i∈pairCoords a, p i

noncomputable def testWeight {L : ℕ} (σ : ℕ → ℝ) (k : Fin 3)
    (a : Fin (L+1) × Fin (L+1)) : ℝ :=
  if k.val=0 then pairWeight a else
    if k.val=1 then pairWeight a*max (σ a.1.val*σ a.2.val) 0
    else pairWeight a*max (-(σ a.1.val*σ a.2.val)) 0

lemma testWeight_bounds {L : ℕ} (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (k : Fin 3) (a : Fin (L+1) × Fin (L+1)) :
    0 ≤ testWeight σ k a ∧ testWeight σ k a ≤ pairWeight a := by
  have hab : |σ a.1.val*σ a.2.val| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (hσ _) (hσ _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hpos : 0 ≤ max (σ a.1.val*σ a.2.val) 0 := le_max_right _ _
  have hneg : 0 ≤ max (-(σ a.1.val*σ a.2.val)) 0 := le_max_right _ _
  have hpos1 : max (σ a.1.val*σ a.2.val) 0 ≤ 1 := max_le (abs_le.mp hab).2 (by norm_num)
  have hneg1 : max (-(σ a.1.val*σ a.2.val)) 0 ≤ 1 := max_le (by linarith [(abs_le.mp hab).1]) (by norm_num)
  unfold testWeight
  split_ifs
  · exact ⟨(pairWeight_bounds a).1,le_rfl⟩
  · exact ⟨mul_nonneg (pairWeight_bounds a).1 hpos,by nlinarith [(pairWeight_bounds a).1]⟩
  · exact ⟨mul_nonneg (pairWeight_bounds a).1 hneg,by nlinarith [(pairWeight_bounds a).1]⟩

lemma testWeight_difference {L : ℕ} (σ : ℕ → ℝ) (a : Fin (L+1) × Fin (L+1)) :
    testWeight σ 1 a-testWeight σ 2 a=pairWeight a*(σ a.1.val*σ a.2.val) := by
  norm_num [testWeight]
  by_cases hh : 0 ≤ σ a.1.val*σ a.2.val
  · rw [max_eq_left hh,max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
    ring

/-- The number of concentration tests is three times the number of coarse
sums, with no fine-field target factor. -/
theorem exists_unsigned_signed_bound_with_potential (L Q : ℕ) (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (V δ : ℝ)
    (hV : 0<V) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hm : ∀ q ≤ Q, repMean L q p ≤ V)
    (Ψ : (Fin (L+1) → Bool) → ℝ) (hΨ : ∀ ω, 0 ≤ Ψ ω)
    (hsmall : 6*((Q : ℝ)+1)*Real.exp (-δ^2*V/8) + expect p Ψ < 1) :
    ∃ ω : Fin (L+1) → Bool, (∀ q ≤ Q,
      |(sumRep (selected L ω) q : ℝ)-repMean L q p| < δ*V ∧
      |signedRep L q σ ω-signedMean L q σ p| < 2*δ*V) ∧ Ψ ω < 1 := by
  let S : Finset (ℕ × Fin 3) := (Finset.range (Q+1)) ×ˢ Finset.univ
  let F := fun (k : ℕ × Fin 3) (ω : Fin (L+1) → Bool) ↦
    ∑ a∈halfPairs L k.1, testWeight σ k.2 a*monomial (pairCoords a) ω
  let m := fun (k : ℕ × Fin 3) ↦
    ∑ a∈halfPairs L k.1, testWeight σ k.2 a*∏ i∈pairCoords a, p i
  have hmean (k : ℕ × Fin 3) (hk : k∈S) : m k ≤ V := by
    apply le_trans (b := repMean L k.1 p) ?_ (hm k.1 (by
      have := Finset.mem_range.mp (Finset.mem_product.mp hk).1; omega))
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (testWeight_bounds σ hσ k.2 a).2
      (product_probability_bounds p hp (pairCoords a)).1
  have hmgf (k : ℕ × Fin 3) (hk : k∈S) (t : ℝ) (ht : |t| ≤ 1/2) :
      expect p (fun ω ↦ Real.exp (t*(F k ω-m k))) ≤ Real.exp (2*t^2*m k) := by
    exact centered_mgf_bound p hp (halfPairs L k.1) pairCoords (pairCoords_disjoint L k.1)
      (testWeight σ k.2) (fun a _ ↦ ⟨(testWeight_bounds σ hσ k.2 a).1,
        (testWeight_bounds σ hσ k.2 a).2.trans (pairWeight_bounds a).2⟩) t ht
  have hsmall' : 2*S.card*Real.exp (-δ^2*V/8) + expect p Ψ < 1 := by
    have hc : (S.card : ℝ)=3*((Q : ℝ)+1) := by
      simp [S,Finset.card_product,Finset.card_range,mul_comm]
    rw [hc]
    nlinarith
  obtain ⟨ω,hω,hΨω⟩ := exists_simultaneous_bound_with_potential p hp S F m V δ hV hδ hδ1 hmean hmgf Ψ hΨ hsmall'
  refine ⟨ω,fun q hq ↦ ?_,hΨω⟩
  have hk (k : Fin 3) : (q,k)∈S := Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega),Finset.mem_univ _⟩
  constructor
  · have hh := hω (q,0) (hk 0)
    simpa only [F,m,testWeight,Fin.val_zero,if_true,selected_rep,repMean] using hh
  · have h₁ := hω (q,1) (hk 1)
    have h₂ := hω (q,2) (hk 2)
    have he : signedRep L q σ ω-signedMean L q σ p =
        (F (q,1) ω-m (q,1))-(F (q,2) ω-m (q,2)) := by
      simp only [F,m,signedRep,signedMean]
      have hw (a : Fin (L+1) × Fin (L+1)) (x : ℝ) :
          pairWeight a*(σ a.1.val*σ a.2.val)*x=
            testWeight σ 1 a*x-testWeight σ 2 a*x := by rw [←sub_mul,testWeight_difference]
      simp_rw [hw,Finset.sum_sub_distrib]
      ring
    rw [he]
    exact (abs_sub _ _).trans_lt (by linarith)

theorem exists_unsigned_signed_bound (L Q : ℕ) (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (V δ : ℝ)
    (hV : 0<V) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hm : ∀ q ≤ Q, repMean L q p ≤ V)
    (hsmall : 6*((Q : ℝ)+1)*Real.exp (-δ^2*V/8) < 1) :
    ∃ ω : Fin (L+1) → Bool, ∀ q ≤ Q,
      |(sumRep (selected L ω) q : ℝ)-repMean L q p| < δ*V ∧
      |signedRep L q σ ω-signedMean L q σ p| < 2*δ*V := by
  have hs : 6*((Q : ℝ)+1)*Real.exp (-δ^2*V/8) + expect p (fun _ ↦ (0 : ℝ)) < 1 := by
    simpa only [expect_const,add_zero] using hsmall
  obtain ⟨ω,hω,_⟩ := exists_unsigned_signed_bound_with_potential L Q σ hσ p hp V δ hV hδ hδ1 hm
    (fun _ ↦ 0) (fun _ ↦ le_rfl) hs
  exact ⟨ω,hω⟩

lemma signedMean_decomposition (L q : ℕ) (σ : ℕ → ℝ) (p : Fin (L+1) → ℝ) :
    signedMean L q σ p =
      (∑ a∈pairs L q, (σ a.1.val*p a.1)*(σ a.2.val*p a.2))+
      ∑ a∈(halfPairs L q).filter (fun a ↦ a.1=a.2),
        (σ a.1.val)^2*(p a.1-(p a.1)^2) := by
  rw [signedMean,symmetric_sum L q _ (fun a ↦ mul_comm _ _),Finset.sum_filter,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : a.1=a.2
  · simp [pairWeight,pairCoords,he]
    ring
  · simp [pairWeight,pairCoords,he]
    ring

lemma signedMean_correction_bounds (L q : ℕ) (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (p : Fin (L+1) → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ signedMean L q σ p-(∑ a∈pairs L q, (σ a.1.val*p a.1)*(σ a.2.val*p a.2)) ∧
    signedMean L q σ p-(∑ a∈pairs L q, (σ a.1.val*p a.1)*(σ a.2.val*p a.2)) ≤ 1 := by
  rw [signedMean_decomposition,add_sub_cancel_left]
  have hp0 (i : Fin (L+1)) : 0 ≤ p i-(p i)^2 := by nlinarith [(hp i).1,(hp i).2]
  constructor
  · exact Finset.sum_nonneg (fun a _ ↦ mul_nonneg (sq_nonneg _) (hp0 _))
  · apply le_trans (b := diagCorrection L q p) ?_ (diagCorrection_bounds L q p hp).2
    apply Finset.sum_le_sum
    intro a ha
    have hs : (σ a.1.val)^2 ≤ 1 := by nlinarith [(abs_le.mp (hσ a.1.val)).1,(abs_le.mp (hσ a.1.val)).2]
    nlinarith [mul_le_mul_of_nonneg_right hs (hp0 a.1)]


noncomputable def selectedFinset (L : ℕ) (ω : Fin (L+1) → Bool) : Finset ℕ :=
  (selected_finite L ω).toFinset

lemma coe_selectedFinset (L : ℕ) (ω : Fin (L+1) → Bool) :
    (selectedFinset L ω : Set ℕ)=selected L ω := Set.Finite.coe_toFinset _

lemma selectedFinset_subset (L : ℕ) (ω : Fin (L+1) → Bool) :
    selectedFinset L ω ⊆ Finset.range (L+1) := by
  intro n hn
  have hh : n∈selected L ω := (Set.Finite.mem_toFinset _).mp hn
  obtain ⟨i,rfl,hi⟩ := hh
  exact Finset.mem_range.mpr i.isLt

lemma selectedWeight_eq_bit (L : ℕ) (ω : Fin (L+1) → Bool) (i : Fin (L+1)) :
    selectedWeight (selectedFinset L ω) i.val=bit (ω i) := by
  simp only [selectedWeight,selectedFinset,Set.Finite.mem_toFinset,mem_selected,bit]

lemma full_pairs_eq_labelFiber_all (L q : ℕ) (f : ℕ → ℝ) :
    (∑ a∈pairs L q, f a.1.val*f a.2.val)=labelFiber (L+1) f q := by
  unfold pairs
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  have he (i : Fin (L+1)) :
      (∑ j : Fin (L+1), if i.val+j.val=q then f i.val*f j.val else 0) =
      ∑ j∈Finset.range (L+1), if i.val+j=q then f i.val*f j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j ↦ if i.val+j=q then f i.val*f j else 0) (L+1)
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ ∑ j∈Finset.range (L+1), if i+j=q then f i*f j else 0) (L+1)

lemma full_pairs_eq_labelFiber (L q : ℕ) (hq : q ≤ L) (f : ℕ → ℝ) :
    (∑ a∈pairs L q, f a.1.val*f a.2.val)=labelFiber (L+1) f q := by
  rw [pairs_sum_range L q (fun i j ↦ f i*f j),labelFiber,
    diagonal_sum (L+1) q (by omega) (fun i j ↦ f i*f j)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (show i ≤ L ∧ q-i ≤ L by have := Finset.mem_range.mp hi; omega)]

lemma signedRep_eq_labelFiber_all (L q : ℕ) (σ : ℕ → ℝ)
    (ω : Fin (L+1) → Bool) :
    signedRep L q σ ω =
      labelFiber (L+1) (fun i ↦ selectedWeight (selectedFinset L ω) i*σ i) q := by
  calc
    _ = ∑ a∈pairs L q,
        (selectedWeight (selectedFinset L ω) a.1.val*σ a.1.val)*
        (selectedWeight (selectedFinset L ω) a.2.val*σ a.2.val) := by
      rw [symmetric_sum L q _ (fun a ↦ mul_comm _ _)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [selectedWeight_eq_bit,selectedWeight_eq_bit,pair_monomial]
      ring
    _ = _ := full_pairs_eq_labelFiber_all L q (fun i ↦ selectedWeight (selectedFinset L ω) i*σ i)

lemma signedMean_nat_correction_bounds_all (L q : ℕ) (σ v : ℕ → ℝ)
    (hσ : ∀ i, |σ i| ≤ 1) (hv : ∀ i : Fin (L+1), 0 ≤ v i.val ∧ v i.val ≤ 1) :
    0 ≤ signedMean L q σ (fun i ↦ v i.val)-labelFiber (L+1) (fun i ↦ v i*σ i) q ∧
    signedMean L q σ (fun i ↦ v i.val)-labelFiber (L+1) (fun i ↦ v i*σ i) q ≤ 1 := by
  have he : (∑ a∈pairs L q, (σ a.1.val*v a.1.val)*(σ a.2.val*v a.2.val)) =
      labelFiber (L+1) (fun i ↦ v i*σ i) q := by
    rw [←full_pairs_eq_labelFiber_all L q]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simpa only [he] using signedMean_correction_bounds L q σ hσ (fun i ↦ v i.val) hv


lemma signedRep_eq_labelFiber (L q : ℕ) (_hq : q ≤ L) (σ : ℕ → ℝ)
    (ω : Fin (L+1) → Bool) :
    signedRep L q σ ω =
      labelFiber (L+1) (fun i ↦ selectedWeight (selectedFinset L ω) i*σ i) q :=
  signedRep_eq_labelFiber_all L q σ ω

lemma signedMean_nat_correction_bounds (L q : ℕ) (_hq : q ≤ L) (σ v : ℕ → ℝ)
    (hσ : ∀ i, |σ i| ≤ 1) (hv : ∀ i : Fin (L+1), 0 ≤ v i.val ∧ v i.val ≤ 1) :
    0 ≤ signedMean L q σ (fun i ↦ v i.val)-labelFiber (L+1) (fun i ↦ v i*σ i) q ∧
    signedMean L q σ (fun i ↦ v i.val)-labelFiber (L+1) (fun i ↦ v i*σ i) q ≤ 1 :=
  signedMean_nat_correction_bounds_all L q σ v hσ hv

end Erdos66SignedRepBernoulli
