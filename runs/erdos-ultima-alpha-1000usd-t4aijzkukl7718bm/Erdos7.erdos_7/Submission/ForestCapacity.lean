import Submission.ForestUnion

/-! Slack, compensated overlaps, and threshold certificates for finite forest bounds. -/
namespace Erdos7ForestCapacity
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def neighbor (E : Finset (ι × ι)) (w : ι → ℚ) (i : ι) : ℚ :=
  ∑ e ∈ E,((if e.1 = i then w e.2 else 0)+(if e.2 = i then w e.1 else 0))

def edgeProduct (E : Finset (ι × ι)) (a : ι → ℚ) : ℚ := ∑ e ∈ E,a e.1*a e.2

def polynomial (E : Finset (ι × ι)) (a : ι → ℚ) : ℚ := (∑ i,a i)-edgeProduct E a

lemma sum_neighbor (E : Finset (ι × ι)) (δ w : ι → ℚ) :
    (∑ i,δ i*neighbor E w i) = ∑ e ∈ E,(δ e.1*w e.2+w e.1*δ e.2) := by
  classical
  unfold neighbor
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [mul_add,mul_ite,mul_zero,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

lemma neighbor_mono (E : Finset (ι × ι)) (v w : ι → ℚ)
    (hvw : ∀ i,v i ≤ w i) (i : ι) : neighbor E v i ≤ neighbor E w i := by
  classical
  unfold neighbor
  apply Finset.sum_le_sum
  intro e _
  apply add_le_add <;> split_ifs <;> first | exact hvw _ | exact le_rfl

/-- Raising event weights incurs a controlled slack even before imposing
any degree restriction. -/
theorem polynomial_slack (E : Finset (ι × ι)) (a w : ι → ℚ)
    (haw : ∀ i,a i ≤ w i) :
    (∑ i,(w i-a i)*(1-neighbor E w i)) ≤ polynomial E w-polynomial E a := by
  have he : edgeProduct E w-edgeProduct E a ≤
      ∑ i,(w i-a i)*neighbor E w i := by
    rw [sum_neighbor]
    unfold edgeProduct
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have hh := mul_nonneg (sub_nonneg.mpr (haw e.1)) (sub_nonneg.mpr (haw e.2))
    nlinarith
  simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib]
  unfold polynomial
  linarith

theorem polynomial_mono (E : Finset (ι × ι)) (a w : ι → ℚ)
    (haw : ∀ i,a i ≤ w i) (hdegree : ∀ i,neighbor E w i ≤ 1) :
    polynomial E a ≤ polynomial E w := by
  have hs := polynomial_slack E a w haw
  have hn : 0 ≤ ∑ i,(w i-a i)*(1-neighbor E w i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (haw i))
      (sub_nonneg.mpr (hdegree i)))
  linarith

/-- A forced overlap may be replaced by a uniform charge if any loss in
that overlap is compensated by the vertex-weight deficits. -/
theorem compensated_overlap_bound (E : Finset (ι × ι)) (a w : ι → ℚ)
    (haw : ∀ i,a i ≤ w i) (union overlap charge : ℚ)
    (hu : union ≤ polynomial E a-overlap)
    (hcomp : charge ≤ overlap+∑ i,(w i-a i)*(1-neighbor E w i)) :
    union ≤ polynomial E w-charge := by
  have hs := polynomial_slack E a w haw
  linarith

def incident (E : Finset (ι × ι)) (ell : ι × ι → ℚ) (i : ι) : ℚ :=
  ∑ e ∈ E,((if e.1 = i then ell e else 0)+(if e.2 = i then ell e else 0))

lemma sum_incident (E : Finset (ι × ι)) (ell : ι × ι → ℚ) (x : ι → ℚ) :
    (∑ i,incident E ell i*x i) = ∑ e ∈ E,ell e*(x e.1+x e.2) := by
  classical
  unfold incident
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [add_mul,ite_mul,zero_mul,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

lemma product_penalty (x y c ell : ℚ) (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hl : 0 ≤ ell ∧ ell ≤ c) :
    ell*(x+y-1) ≤ c*x*y := by
  have hxy := mul_nonneg hx.1 hy.1
  have hc := mul_nonneg (sub_nonneg.mpr hl.2) hxy
  have ht := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  have hd := mul_nonneg hl.1 ht
  nlinarith

/-- A finite linear upper certificate for a quadratic overlap penalty. -/
theorem penalized_selection_bound (E : Finset (ι × ι)) (w x : ι → ℚ)
    (c ell : ι × ι → ℚ) (hx : ∀ i,0 ≤ x i ∧ x i ≤ 1)
    (hl : ∀ e ∈ E,0 ≤ ell e ∧ ell e ≤ c e) :
    (∑ i,w i*x i)-(∑ e ∈ E,c e*x e.1*x e.2) ≤
      (∑ i,(w i-incident E ell i)*x i)+∑ e ∈ E,ell e := by
  have hh : (∑ e ∈ E,ell e*(x e.1+x e.2-1)) ≤
      ∑ e ∈ E,c e*x e.1*x e.2 :=
    Finset.sum_le_sum (fun e he => product_penalty _ _ _ _ (hx e.1) (hx e.2) (hl e he))
  have hi := sum_incident E ell x
  simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib] at hh
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  linarith

lemma selected_linear_threshold (a x : ι → ℚ) (K t : ℚ)
    (hx : ∀ i,0 ≤ x i ∧ x i ≤ 1) (hK : (∑ i,x i) ≤ K) (ht : 0 ≤ t) :
    (∑ i,a i*x i) ≤ K*t+∑ i,max (a i-t) 0 := by
  have hp (i : ι) : a i*x i ≤ t*x i+max (a i-t) 0 := by
    by_cases h : a i ≤ t
    · rw [max_eq_right (sub_nonpos.mpr h)]
      have hh := mul_le_mul_of_nonneg_right h (hx i).1
      linarith
    · rw [max_eq_left (by linarith : 0 ≤ a i-t)]
      have hh := mul_nonneg (by linarith : 0 ≤ a i-t) (sub_nonneg.mpr (hx i).2)
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hK ht
  nlinarith

/-- The only hypotheses for the final rational certificate are interval,
cardinality, and edge-multiplier checks. -/
theorem forest_threshold_bound (E : Finset (ι × ι)) (w x : ι → ℚ)
    (c ell : ι × ι → ℚ) (K t : ℚ) (hx : ∀ i,0 ≤ x i ∧ x i ≤ 1)
    (hK : (∑ i,x i) ≤ K) (ht : 0 ≤ t)
    (hl : ∀ e ∈ E,0 ≤ ell e ∧ ell e ≤ c e) :
    (∑ i,w i*x i)-(∑ e ∈ E,c e*x e.1*x e.2) ≤
      K*t+(∑ i,max (w i-incident E ell i-t) 0)+∑ e ∈ E,ell e := by
  have h₁ := penalized_selection_bound E w x c ell hx hl
  have h₂ := selected_linear_threshold (fun i => w i-incident E ell i) x K t hx hK ht
  linarith

#print axioms polynomial_slack
#print axioms compensated_overlap_bound
#print axioms forest_threshold_bound
end Erdos7ForestCapacity
