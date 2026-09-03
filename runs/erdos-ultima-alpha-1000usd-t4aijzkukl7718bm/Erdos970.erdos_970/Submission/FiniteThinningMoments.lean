import Submission.SoftEndpointReduction

/-! Exact finite inclusion-exclusion formulas for adjoining large prime
moduli. These are identities of the genuine residue-phase model. -/
namespace Erdos970.GapAverages.FiniteThinning
open Finset Real

noncomputable def joint (P A : Finset ℕ) : ℝ :=
  phaseMean P (fun r => ∏ x ∈ A, point P x r)

noncomputable def coordinateJoint (p : ℕ) (A : Finset ℕ) : ℝ :=
  (∑ a : Fin p, ∏ x ∈ A, (1 - if x % p = a.val then (1 : ℝ) else 0)) / p

lemma joint_factor (P A : Finset ℕ) : joint P A = ∏ p ∈ P, coordinateJoint p A := by
  unfold joint point
  have he (r : Phase P) :
      (∏ x ∈ A, ∏ p : P, (1 - if x % p.val = (r p).val then (1 : ℝ) else 0)) =
      ∏ p : P, ∏ x ∈ A, (1 - if x % p.val = (r p).val then (1 : ℝ) else 0) :=
    prod_comm
  simp_rw [he]
  rw [phaseMean_prod P (fun p a => ∏ x ∈ A, (1 - if x % p.val = a.val then (1 : ℝ) else 0))]
  exact prod_attach P (fun p => coordinateJoint p A)

lemma coordinateJoint_large (A : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (hA : A ⊆ range p) : coordinateJoint p A = 1-(A.card : ℝ)/p := by
  classical
  have he (a : Fin p) :
      (∏ x ∈ A, (1 - if x % p = a.val then (1 : ℝ) else 0)) =
      1 - if a.val ∈ A then (1 : ℝ) else 0 := by
    by_cases ha : a.val ∈ A
    · rw [if_pos ha, sub_self]
      apply prod_eq_zero ha
      simp [Nat.mod_eq_of_lt a.isLt]
    · rw [if_neg ha, sub_zero]
      apply prod_eq_one
      intro x hx
      have hxp : x < p := mem_range.mp (hA hx)
      have hne : x % p ≠ a.val := by
        rw [Nat.mod_eq_of_lt hxp]
        intro heq
        exact ha (heq ▸ hx)
      simp [hne]
  have hs : (∑ a : Fin p, if a.val ∈ A then (1 : ℝ) else 0) = A.card := by
    rw [Fin.sum_univ_eq_sum_range (fun a => if a ∈ A then (1 : ℝ) else 0)]
    rw [sum_boole]
    have hf : (range p).filter (fun x => x ∈ A) = A := by
      ext x
      simp only [mem_filter, mem_range]
      exact ⟨fun h => h.2, fun h => ⟨mem_range.mp (hA h), h⟩⟩
    rw [hf]
  unfold coordinateJoint
  simp_rw [he]
  rw [sum_sub_distrib, hs]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

lemma joint_union_large (P R A : Finset ℕ) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, 0 < p ∧ A ⊆ range p) :
    joint (P ∪ R) A = joint P A * ∏ p ∈ R, (1-(A.card : ℝ)/p) := by
  rw [joint_factor, prod_union hdis, ← joint_factor]
  congr 1
  exact prod_congr rfl (fun p hp => coordinateJoint_large A p (hR p hp).1 (hR p hp).2)

lemma covered_indicator_product (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    (if intervalCount P m r = 0 then (1 : ℝ) else 0) =
      ∏ x ∈ range m, (1-point P x r) := by
  classical
  by_cases h : ∃ x ∈ range m, point P x r = 1
  · obtain ⟨x,hx,hx1⟩ := h
    have hs : 1 ≤ intervalCount P m r := by
      rw [← hx1]
      exact single_le_sum (f := fun y => point P y r) (fun y _ => by rcases point_eq_zero_or_one P y r with h | h <;> simp [h]) hx
    rw [if_neg (by linarith)]
    symm
    apply prod_eq_zero hx
    simp [hx1]
  · have hz (x : ℕ) (hx : x ∈ range m) : point P x r = 0 := by
      rcases point_eq_zero_or_one P x r with hh | hh
      · exact hh
      · exact (h ⟨x,hx,hh⟩).elim
    have hc : intervalCount P m r = 0 := sum_eq_zero hz
    rw [if_pos hc]
    symm
    exact prod_eq_one (fun x hx => by rw [hz x hx]; norm_num)

lemma covered_expansion (P : Finset ℕ) (m : ℕ) :
    coveredFraction P m =
      ∑ A ∈ (range m).powerset, (-1 : ℝ)^A.card * joint P A := by
  classical
  unfold coveredFraction
  simp_rw [covered_indicator_product, prod_sub]
  simp only [prod_const_one, mul_one]
  rw [phaseMean_sum]
  exact sum_congr rfl (fun A _ => phaseMean_mul P ((-1 : ℝ)^A.card) _)

lemma laplace_expansion_64 (P : Finset ℕ) (m : ℕ) :
    countLaplace P (log 64) m = ∑ A ∈ (range m).powerset,
      (-1 : ℝ)^A.card * (63/64 : ℝ)^A.card * joint P A := by
  classical
  have hp (r : Phase P) (x : ℕ) :
      exp (-log 64 * point P x r) = 1-(63/64 : ℝ)*point P x r := by
    rcases point_eq_zero_or_one P x r with h | h <;> rw [h]
    · norm_num
    · rw [mul_one, exp_neg, exp_log (by norm_num : (0 : ℝ) < 64)]
      norm_num
  have he (r : Phase P) : exp (-log 64 * intervalCount P m r) =
      ∏ x ∈ range m, (1-(63/64 : ℝ)*point P x r) := by
    unfold intervalCount
    rw [mul_sum, exp_sum]
    exact prod_congr rfl (fun x _ => hp r x)
  unfold countLaplace
  simp_rw [he, prod_sub]
  simp only [prod_const_one, mul_one, prod_mul_distrib, prod_const]
  rw [phaseMean_sum]
  apply sum_congr rfl
  intro A hA
  simp_rw [← mul_assoc]
  exact phaseMean_mul P (((-1 : ℝ)^A.card)*(63/64 : ℝ)^A.card) _

#print axioms joint_union_large
#print axioms covered_expansion
#print axioms laplace_expansion_64
end Erdos970.GapAverages.FiniteThinning
