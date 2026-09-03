import Submission.DisjointProductPipageExplore
import Submission.PrefixBalancedUpperSelectionExplore

/-! Both-sign exponential representation potentials under a pipage step.
Only a step rounding the endpoints of the same representation pair needs
a multiplicative penalty. -/
namespace Erdos66RepresentationPipage
open Erdos66OrderedPipageGeometry Erdos66DisjointProductPipage
  Erdos66PrefixBalancedUpperSelection Erdos66FiniteRepBernoulli
open scoped Classical
set_option maxHeartbeats 2400000

lemma pair_coords_sum {L n : ℕ} (a : Fin (L+1) × Fin (L+1)) (ha : a∈halfPairs L n)
    (i j : Fin (L+1)) (hij : i≠j) (hi : i∈pairCoords a) (hj : j∈pairCoords a) :
    i.val+j.val=n := by
  have hs := (mem_halfPairs.mp ha).1
  simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst_vars <;> simp_all <;> omega

lemma expPoly_nonneg (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (hx : ∀ i, 0≤x i ∧ x i≤1) : 0≤expPoly L n t x := by
  apply Finset.prod_nonneg
  intro a ha
  exact product_factor_nonneg (pairCoords a) (Real.exp (t*pairWeight a)-1)
    (by linarith [Real.exp_pos (t*pairWeight a)]) x hx

lemma exp_coeff_same_sign {L : ℕ} (t : ℝ)
    (a b : Fin (L+1) × Fin (L+1)) :
    0≤(Real.exp (t*pairWeight a)-1)*(Real.exp (t*pairWeight b)-1) := by
  by_cases ht : 0≤t
  · apply mul_nonneg <;> apply sub_nonneg.mpr <;> apply Real.one_le_exp_iff.mpr
    · exact mul_nonneg ht (pairWeight_bounds a).1
    · exact mul_nonneg ht (pairWeight_bounds b).1
  · apply mul_nonneg_of_nonpos_of_nonpos <;> apply sub_nonpos.mpr <;> apply Real.exp_le_one_iff.mpr
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) (pairWeight_bounds a).1
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) (pairWeight_bounds b).1

lemma expPoly_pipage_distinct (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (hx : ∀ i, 0≤x i ∧ x i≤1) (i j : Fin (L+1)) (hij : i≠j) (hn : i.val+j.val≠n)
    (a b d e w : ℝ) (hi : w*a+(1-w)*d=x i) (hj : w*b+(1-w)*e=x j)
    (hp : w*(a*b)+(1-w)*(d*e)≤x i*x j) :
    w*expPoly L n t (replaceTwo x i j a b)+
      (1-w)*expPoly L n t (replaceTwo x i j d e)≤expPoly L n t x := by
  exact product_pipage_distinct (halfPairs L n) pairCoords
    (fun r ↦ Real.exp (t*pairWeight r)-1) (pairCoords_disjoint L n)
    (fun r _ ↦ by linarith [Real.exp_pos (t*pairWeight r)])
    (fun r _ s _ ↦ exp_coeff_same_sign t r s) x hx i j hij
    (fun r hr h ↦ hn (pair_coords_sum r hr i j hij h.1 h.2)) a b d e w hi hj hp

lemma exp_factor_ratio (v a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) :
    1+(Real.exp v-1)*a≤Real.exp |v| *(1+(Real.exp v-1)*b) := by
  by_cases hv : 0≤v
  · rw [abs_of_nonneg hv]
    have he : 1≤Real.exp v := Real.one_le_exp_iff.mpr hv
    have h₁ := mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr he)
    have h₂ := mul_nonneg (sub_nonneg.mpr he) hb.1
    have h₃ := mul_le_mul_of_nonneg_left (show (1:ℝ)≤1+(Real.exp v-1)*b by linarith) (Real.exp_pos v).le
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hv)]
    have he : Real.exp v≤1 := Real.exp_le_one_iff.mpr (le_of_not_ge hv)
    have h₁ := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) ha.1
    have h₂ := mul_le_mul_of_nonpos_left hb.2 (sub_nonpos.mpr he)
    have h₃ := mul_le_mul_of_nonneg_left
      (show Real.exp v≤1+(Real.exp v-1)*b by linarith) (Real.exp_pos (-v)).le
    have heq : Real.exp (-v)*Real.exp v=1 := by rw [←Real.exp_add]; simp
    rw [heq] at h₃
    linarith

lemma expPoly_pair_ratio (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (hx : ∀ i, 0≤x i ∧ x i≤1) (i j : Fin (L+1)) (hij : i<j) (hn : i.val+j.val=n)
    (a b : ℝ) (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) :
    expPoly L n t (replaceTwo x i j a b)≤Real.exp (2*|t|)*expPoly L n t x := by
  let r : Fin (L+1) × Fin (L+1) := (i,j)
  have hr : r∈halfPairs L n := mem_halfPairs.mpr ⟨hn,hij.le⟩
  let R : ℝ := ∏ s∈(halfPairs L n).erase r,
    (1+(Real.exp (t*pairWeight s)-1)*∏ k∈pairCoords s, x k)
  have hR : 0≤R := Finset.prod_nonneg (fun s hs ↦
    product_factor_nonneg (pairCoords s) (Real.exp (t*pairWeight s)-1)
      (by linarith [Real.exp_pos (t*pairWeight s)]) x hx)
  have hrest : (∏ s∈(halfPairs L n).erase r,
      (1+(Real.exp (t*pairWeight s)-1)*∏ k∈pairCoords s, replaceTwo x i j a b k))=R := by
    apply Finset.prod_congr rfl
    intro s hs
    have hdis := pairCoords_disjoint L n hr (Finset.mem_erase.mp hs).2
      (Ne.symm (Finset.mem_erase.mp hs).1)
    have hi : i∉pairCoords s := fun hi ↦ Finset.disjoint_left.mp hdis (by simp [r,pairCoords]) hi
    have hj : j∉pairCoords s := fun hj ↦ Finset.disjoint_left.mp hdis (by simp [r,pairCoords]) hj
    congr 2
    apply Finset.prod_congr rfl
    intro k hk
    simp only [replaceTwo,if_neg (show k≠i from fun h ↦ hi (h ▸ hk)),
      if_neg (show k≠j from fun h ↦ hj (h ▸ hk))]
  have hform (y : Fin (L+1) → ℝ) : expPoly L n t y=
      (1+(Real.exp (2*t)-1)*(y i*y j))*
        ∏ s∈(halfPairs L n).erase r, (1+(Real.exp (t*pairWeight s)-1)*∏ k∈pairCoords s, y k) := by
    unfold expPoly
    rw [←Finset.mul_prod_erase _ _ hr]
    simp only [r,pairWeight,pairCoords,if_neg (ne_of_lt hij),
      Finset.prod_insert (show i∉({j}:Finset (Fin (L+1))) by simp [ne_of_lt hij]),
      Finset.prod_singleton]
    rw [mul_comm t 2]
  rw [hform,hform,hrest]
  simp only [replaceTwo,ite_true,if_neg (Ne.symm (ne_of_lt hij))]
  have hp : 0≤a*b ∧ a*b≤1 := ⟨mul_nonneg ha.1 hb.1,
    (mul_le_mul ha.2 hb.2 hb.1 (by norm_num)).trans_eq (by ring)⟩
  have hxp : 0≤x i*x j ∧ x i*x j≤1 := ⟨mul_nonneg (hx i).1 (hx j).1,
    (mul_le_mul (hx i).2 (hx j).2 (hx j).1 (by norm_num)).trans_eq (by ring)⟩
  have hh := mul_le_mul_of_nonneg_right (exp_factor_ratio (2*t) (a*b) (x i*x j) hp hxp) hR
  simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),mul_assoc] using hh

noncomputable def replaceOne {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (i : ι) (a : ℝ) : ι → ℝ :=
  fun k ↦ if k=i then a else x k

lemma monomial_single_average {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (i : ι) (a b w : ℝ) (hm : w*a+(1-w)*b=x i) :
    w*(∏ k∈S, replaceOne x i a k)+(1-w)*(∏ k∈S, replaceOne x i b k)=∏ k∈S, x k := by
  have hf (a : ℝ) : (∏ k∈S, replaceOne x i a k)=
      (if i∈S then a else 1)*∏ k∈S, if k=i then 1 else x k := by
    have he (k : ι) : replaceOne x i a k=(if k=i then a else 1)*(if k=i then 1 else x k) := by
      by_cases h : k=i <;> simp [replaceOne,h]
    simp only [he,Finset.prod_mul_distrib,Finset.prod_ite_eq']
  have hself : replaceOne x i (x i)=x := by funext k; dsimp [replaceOne]; split_ifs <;> simp_all
  have hfx := hf (x i)
  rw [hself] at hfx
  rw [hf,hf,hfx]
  split_ifs
  · rw [←mul_assoc,←mul_assoc,←add_mul,hm]
  · ring

lemma expPoly_single_average (L n : ℕ) (t : ℝ) (x : Fin (L+1) → ℝ)
    (i : Fin (L+1)) (a b w : ℝ) (hm : w*a+(1-w)*b=x i) :
    w*expPoly L n t (replaceOne x i a)+(1-w)*expPoly L n t (replaceOne x i b)=expPoly L n t x := by
  simp only [expPoly_expansion,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  have hh := congrArg (fun z : ℝ ↦ (∏ r∈S, (Real.exp (t*pairWeight r)-1))*z)
    (monomial_single_average (S.biUnion pairCoords) x i a b w hm)
  nlinarith only [hh]

end Erdos66RepresentationPipage
