import Submission.MatchingPatternSublogExplore
import Submission.HarmonicRefreshExplore

/-! Actual insertion increments as disjoint positive patterns. The resulting
simultaneous selection theorem keeps its fractional mean hypothesis explicit. -/
namespace Erdos66InsertionMatchingPattern
open Filter AdditiveCombinatorics Erdos66NaturalPositivePattern
  Erdos66MatchingPatternSublog Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli
  Erdos66Generating Erdos66Rounding Erdos66HarmonicRefresh
  Erdos66ClampedPrefixContinuation
open scoped Classical Topology
set_option maxHeartbeats 3000000

noncomputable def insertionPattern (A : Set ℕ) (n : ℕ) : Pattern where
  Term := Fin (n+1) × Fin (n+1)
  terms := (halfPairs n n).filter (fun a ↦ ¬ (a.1.val∈A ∧ a.2.val∈A))
  coeff := pairWeight
  support := fun a ↦ ((pairCoords a).image Fin.val).filter (fun i ↦ i∉A)
  nonneg := fun a _ ↦ (pairWeight_bounds a).1

lemma insertionPattern_coeff (A : Set ℕ) (n : ℕ) (k : (insertionPattern A n).Term) :
    1 ≤ (insertionPattern A n).coeff k ∧ (insertionPattern A n).coeff k ≤ 2 := by
  change 1 ≤ pairWeight k ∧ pairWeight k ≤ 2
  unfold pairWeight
  split_ifs <;> norm_num

lemma insertionPattern_disjoint (A : Set ℕ) (n : ℕ) :
    ((insertionPattern A n).terms : Set (insertionPattern A n).Term).PairwiseDisjoint
      (insertionPattern A n).support := by
  intro a ha b hb hab
  have hd := pairCoords_disjoint n n (Finset.mem_filter.mp ha).1
    (Finset.mem_filter.mp hb).1 hab
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a',ha',he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).1
  obtain ⟨b',hb',he'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).1
  have hab' : a'=b' := Fin.ext (he.trans he'.symm)
  exact Finset.disjoint_left.mp hd ha' (hab' ▸ hb')

noncomputable def extension (A : Set ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i∈A then 1 else p i

lemma product_extension (A : Set ℕ) (p : ℕ → ℝ) (n : ℕ)
    (a : Fin (n+1) × Fin (n+1)) :
    (if ¬ (a.1.val∈A ∧ a.2.val∈A) then
      ∏ i∈((pairCoords a).image Fin.val).filter (fun i ↦ i∉A), p i else 0) +
      (∏ i∈pairCoords a, indicator A i.val) =
      ∏ i∈pairCoords a, extension A p i.val := by
  by_cases he : a.1=a.2
  · simp only [pairCoords,he,Finset.insert_eq_of_mem,Finset.mem_singleton_self,
      Finset.image_singleton,Finset.prod_singleton]
    by_cases ha : a.2.val∈A <;> simp [Finset.prod_filter,ha,indicator,extension]
  · have hev : a.1.val≠a.2.val := fun h ↦ he (Fin.ext h)
    by_cases ha : a.1.val∈A <;> by_cases hb : a.2.val∈A <;>
      simp [pairCoords,Finset.prod_filter,he,hev,ha,hb,indicator,extension]

lemma insertionPattern_eval_add (A : Set ℕ) (p : ℕ → ℝ) (n : ℕ) :
    (insertionPattern A n).eval p + repMean n n (fun i ↦ indicator A i.val) =
      repMean n n (fun i ↦ extension A p i.val) := by
  simp only [Pattern.eval,insertionPattern,repMean,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hh := congrArg (fun x ↦ pairWeight a*x) (product_extension A p n a)
  dsimp only at hh
  rw [mul_add] at hh
  by_cases ha : ¬ (a.1.val∈A ∧ a.2.val∈A) <;> simpa only [ha,if_true,if_false,mul_zero] using hh

lemma repMean_indicator (A : Set ℕ) (n : ℕ) :
    repMean n n (fun i ↦ indicator A i.val)=(sumRep A n : ℝ) := by
  rw [←selected_prefix_count n n A le_rfl,selected_rep]
  simp only [repMean,monomial]
  simp_rw [bit_decide_indicator]

lemma insertionPattern_value (A F : Set ℕ) (n : ℕ) :
    (insertionPattern A n).value (fun i ↦ decide (i∈F))=
      (sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ) := by
  have he : extension A (fun i ↦ bit (decide (i∈F)))=indicator (A∪F) := by
    funext i
    by_cases ha : i∈A <;> by_cases hf : i∈F <;> simp [extension,indicator,bit,ha,hf]
  have hh := insertionPattern_eval_add A (fun i ↦ bit (decide (i∈F))) n
  rw [he,repMean_indicator,repMean_indicator] at hh
  exact eq_sub_of_add_eq hh

lemma insertionPattern_mean_bound (A : Set ℕ) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hpA : ∀ i∈A, p i=0) (n : ℕ) :
    (insertionPattern A n).eval p ≤
      2*sumConv p (indicator A) n+sumConv p p n+1 := by
  let u := extension A p
  have hu (i : Fin (n+1)) : 0 ≤ u i.val ∧ u i.val ≤ 1 := by
    dsimp only [u,extension]
    split_ifs <;> simp_all
  have he : u=fun i ↦ indicator A i+p i := by
    funext i
    by_cases hi : i∈A <;> simp [u,extension,indicator,hi,hpA i]
  have hh := insertionPattern_eval_add A p n
  rw [repMean_indicator,mean_decomposition] at hh
  have hpair : (∑ a∈pairs n n, u a.1.val*u a.2.val)=sumConv u u n := by
    rw [pairs_sum_range n n (fun i j ↦ u i*u j)]
    simp only [sumConv,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [if_pos (by omega)]
  change (insertionPattern A n).eval p+(sumRep A n : ℝ)=
    (∑ a∈pairs n n, u a.1.val*u a.2.val)+diagCorrection n n (fun i ↦ u i.val) at hh
  rw [hpair,he,sumConv_add_self,sumConv_comm_real (indicator A) p,
    show sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) from sum_indicator_antidiagonal A n] at hh
  have hd := (diagCorrection_bounds n n (fun i ↦ u i.val) hu).2
  rw [he] at hd
  linarith

/-- A single inserted set, with exact brackets for its fractional profile,
changes every representation count by `o(log n)` if its actual mixed and
self-convolution means are `o(log n)`. -/
theorem exists_sublog_insertion (A : Set ℕ) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hpA : ∀ i∈A, p i=0)
    (hmean : Tendsto (fun n : ℕ ↦
      (2*sumConv p (indicator A) n+sumConv p p n+1)/Real.log ((n : ℝ)+2)) atTop (𝓝 0)) :
    ∃ F : Set ℕ, Disjoint F A ∧ (∀ L, PrefixBrackets p F L) ∧
      (∀ i∈F, p i≠0) ∧ Tendsto (fun n : ℕ ↦
        ((sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ))/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  have hm : Tendsto (fun n : ℕ ↦
      (insertionPattern A n).eval p/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ div_nonneg ((insertionPattern A n).eval_nonneg p
      (fun i ↦ (hp i).1)) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))
      (fun n ↦ div_le_div_of_nonneg_right (insertionPattern_mean_bound A p hp hpA n)
        (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))) hmean
  obtain ⟨F,hbr,hs,hF⟩ := exists_matching_sublog_rounding p hp (insertionPattern A)
    (insertionPattern_disjoint A) (fun n k _ ↦ insertionPattern_coeff A n k) hm
  refine ⟨F,Set.disjoint_left.mpr (fun i hi hiA ↦ hs i hi (hpA i hiA)),hbr,hs,?_⟩
  simpa only [insertionPattern_value] using hF

end Erdos66InsertionMatchingPattern
