import FormalConjecturesUtil

/-! Finite weighted union bounds using an oriented forest of intersections.
These are auxiliary inequalities, not a settlement of the odd covering problem. -/
namespace Erdos7ForestUnion
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

section Pointwise
variable {ι : Type*} [Fintype ι]

/-- Every nonempty induced subforest has a vertex with no active parent. -/
lemma exists_root (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i)
    (hit : ι → Prop) (hhit : ∃ i,hit i) :
    ∃ i,hit i ∧ ∀ j,parent i = some j → ¬hit j := by
  classical
  let S := Finset.univ.filter hit
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hhit
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨i,hi,hmin⟩ := S.exists_min_image rank hS
  refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
  intro j hp hj
  have hm := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  exact (Nat.not_lt_of_ge hm) (hparent i j hp)

noncomputable def bit (P : Prop) : ℚ := by
  classical
  exact if P then 1 else 0
noncomputable def parentBit (parent : ι → Option ι) (hit : ι → Prop) (i : ι) : ℚ :=
  (parent i).elim 0 (fun j => bit (hit j))

lemma bit_bounds (P : Prop) : 0 ≤ bit P ∧ bit P ≤ 1 := by
  classical
  by_cases h : P <;> simp [bit,h]

lemma parentBit_bounds (parent : ι → Option ι) (hit : ι → Prop) (i : ι) :
    0 ≤ parentBit parent hit i ∧ parentBit parent hit i ≤ 1 := by
  cases h : parent i with
  | none => simp [parentBit,h]
  | some j => simpa [parentBit,h] using bit_bounds (hit j)

/-- The indicator of a union is at most the number of active forest roots. -/
theorem indicator_forest_bound (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i) (hit : ι → Prop) :
    bit (∃ i,hit i) ≤
      (∑ i,bit (hit i)) - ∑ i,bit (hit i)*parentBit parent hit i := by
  classical
  have hn (i : ι) : 0 ≤ bit (hit i)-bit (hit i)*parentBit parent hit i := by
    have hb := bit_bounds (hit i)
    have hp := parentBit_bounds parent hit i
    nlinarith
  rw [← Finset.sum_sub_distrib]
  by_cases hh : ∃ i,hit i
  · obtain ⟨i,hi,hp⟩ := exists_root parent rank hparent hit hh
    have hzero : parentBit parent hit i = 0 := by
      cases he : parent i with
      | none => simp [parentBit,he]
      | some j => simp [parentBit,he,bit,hp j he]
    have hs := Finset.single_le_sum (s := Finset.univ) (fun j _ => hn j)
      (Finset.mem_univ i)
    simpa only [bit,if_pos hh,if_pos hi,hzero,mul_zero,sub_zero] using hs
  · rw [show bit (∃ i,hit i) = 0 by simp [bit,hh]]
    exact Finset.sum_nonneg (fun i _ => hn i)
end Pointwise

section Mass
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

noncomputable def mass (μ : Ω → ℚ) (A : Ω → Prop) : ℚ :=
  ∑ x,μ x*bit (A x)

lemma mass_nonneg (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x) (A : Ω → Prop) :
    0 ≤ mass μ A :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (bit_bounds (A x)).1)

lemma bit_and (P Q : Prop) : bit (P ∧ Q) = bit P*bit Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp [bit,hp,hq]

/-- Hunter's forest bound, in a form that allows arbitrary nonnegative weights. -/
theorem weighted_forest_union_bound (μ : Ω → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (A : ι → Ω → Prop) (parent : ι → Option ι) (rank : ι → ℕ)
    (hparent : ∀ i j,parent i = some j → rank j < rank i) :
    mass μ (fun x => ∃ i,A i x) ≤
      (∑ i,mass μ (A i)) -
        ∑ i,(parent i).elim 0 (fun j => mass μ (fun x => A i x ∧ A j x)) := by
  classical
  have hp (x : Ω) := mul_le_mul_of_nonneg_left
    (indicator_forest_bound parent rank hparent (fun i => A i x)) (hμ x)
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hp x)
  have he₁ : (∑ x,μ x * ∑ i,bit (A i x)) = ∑ i,mass μ (A i) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have he₂ : (∑ x,μ x * ∑ i,bit (A i x)*parentBit parent (fun j => A j x) i) =
      ∑ i,(parent i).elim 0 (fun j => mass μ (fun x => A i x ∧ A j x)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    cases he : parent i with
    | none => simp [parentBit,he]
    | some j => simp only [parentBit,he,Option.elim_some,mass,bit_and]
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hh
  rw [he₁,he₂] at hh
  exact hh
/-- Replace the parent-indexed sum by an edge-indexed sum. -/
lemma parent_sum [DecidableEq ι] (parent : ι → Option ι)
    (E : Finset (ι × ι)) (hE : ∀ i j,(i,j) ∈ E ↔ parent i = some j)
    (f : ι × ι → ℚ) :
    (∑ i,(parent i).elim 0 (fun j => f (i,j))) = ∑ e ∈ E,f e := by
  classical
  have he : (∑ e ∈ E,f e) = ∑ e : ι × ι,if e ∈ E then f e else 0 := by simp
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [hE]
  cases hp : parent i with
  | none => simp [hp]
  | some j => simp [hp]

end Mass

#print axioms weighted_forest_union_bound
end Erdos7ForestUnion
