import Submission.CommonOriginFamilyExplore

/-! Exact convolution and mass corrections for a family with overlap
multiplicity at most two. No smallness of the collision term is assumed. -/
namespace Erdos66TwofoldFamily
open Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CommonOriginFamily
  Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1600000
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {ι : Type*} [DecidableEq ι]

def familyMult (S : Finset ι) (C : ι → Finset G) (x : G) : ℕ :=
  (S.filter (fun i ↦ x∈C i)).card

def collisions (S : Finset ι) (C : ι → Finset G) : Finset G :=
  Finset.univ.filter (fun x ↦ 2≤familyMult S C x)

omit [AddCommGroup G] [Fintype G] [DecidableEq ι] in
lemma familyMult_pos_iff (S : Finset ι) (C : ι → Finset G) (x : G) :
    0<familyMult S C x ↔ x∈S.biUnion C := by
  simp [familyMult,Finset.card_pos,Finset.filter_nonempty_iff,Finset.mem_biUnion]

omit [AddCommGroup G] [Fintype G] [DecidableEq ι] in
lemma sum_indicators_eq_mult (S : Finset ι) (C : ι → Finset G) (x : G) :
    (∑i∈S, indicator (C i) x)=(familyMult S C x : ℝ) := by
  simp only [familyMult,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,indicator]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : x∈C i <;> simp [hx]

omit [AddCommGroup G] [DecidableEq ι] in
lemma mult_decomposition (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) (x : G) :
    (familyMult S C x : ℝ)=indicator (S.biUnion C) x+indicator (collisions S C) x := by
  have hm := h x
  have hp := familyMult_pos_iff S C x
  have hd : x∈collisions S C ↔ 2≤familyMult S C x := by simp [collisions]
  unfold indicator
  rcases show familyMult S C x=0 ∨ familyMult S C x=1 ∨ familyMult S C x=2 by omega with
    h0 | h1 | h2
  · simp only [h0] at hp hd ⊢
    simp only [Nat.cast_zero,show x∉S.biUnion C by simpa using hp.symm,
      show x∉collisions S C by simpa using hd,if_false,zero_add]
  · have hb : x∈S.biUnion C := hp.mp (by omega)
    have hn : x∉collisions S C := fun hh ↦ by have := hd.mp hh; omega
    simp [h1,hb,hn]
  · have hb : x∈S.biUnion C := hp.mp (by omega)
    have hc : x∈collisions S C := hd.mpr (by omega)
    norm_num [h2,hb,hc]

omit [AddCommGroup G] [DecidableEq G] in
lemma sum_indicator (A : Finset G) : (∑x : G, indicator A x)=(A.card : ℝ) := by
  simp [indicator]

omit [AddCommGroup G] [DecidableEq ι] in
lemma sum_familyMult (S : Finset ι) (C : ι → Finset G) :
    (∑x : G, (familyMult S C x : ℝ))=∑i∈S, ((C i).card : ℝ) := by
  simp_rw [← sum_indicators_eq_mult]
  rw [Finset.sum_comm]
  simp_rw [sum_indicator]

omit [AddCommGroup G] [DecidableEq ι] in
/-- The excess mass is exactly the number of double-covered points. -/
theorem mass_correction (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) :
    (∑i∈S, ((C i).card : ℝ))=((S.biUnion C).card : ℝ)+(collisions S C).card := by
  rw [← sum_familyMult]
  simp_rw [mult_decomposition S C h,Finset.sum_add_distrib,sum_indicator]

omit [DecidableEq ι] in
/-- The collision correction is nonnegative, but need not be small. -/
theorem representation_correction (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) (z : G) :
    (∑i∈S,∑j∈S, (pairCount (C i) (C j) z : ℝ))=
      (pairCount (S.biUnion C) (S.biUnion C) z : ℝ)+
        2*pairCount (S.biUnion C) (collisions S C) z+
        pairCount (collisions S C) (collisions S C) z := by
  rw [← conv_sum_indicators]
  have he : (fun x ↦ ∑i∈S, indicator (C i) x)=
      fun x ↦ indicator (S.biUnion C) x+indicator (collisions S C) x := by
    funext x
    rw [sum_indicators_eq_mult,mult_decomposition S C h]
  rw [he]
  have expand (a b c d : ℝ) : (a+b)*(c+d)=a*c+a*d+b*c+b*d := by ring
  unfold conv
  simp_rw [expand,Finset.sum_add_distrib]
  change conv (indicator (S.biUnion C)) (indicator (S.biUnion C)) z+
    conv (indicator (S.biUnion C)) (indicator (collisions S C)) z+
    conv (indicator (collisions S C)) (indicator (S.biUnion C)) z+
    conv (indicator (collisions S C)) (indicator (collisions S C)) z=_
  simp_rw [conv_indicators]
  rw [pairCount_comm (collisions S C) (S.biUnion C)]
  ring

omit [DecidableEq ι] in
lemma union_count_le_weighted (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) (z : G) :
    (pairCount (S.biUnion C) (S.biUnion C) z : ℝ)≤
      ∑i∈S,∑j∈S, (pairCount (C i) (C j) z : ℝ) := by
  rw [representation_correction S C h z]
  have h1 := Nat.cast_nonneg (pairCount (S.biUnion C) (collisions S C) z) (α := ℝ)
  have h2 := Nat.cast_nonneg (pairCount (collisions S C) (collisions S C) z) (α := ℝ)
  linarith

omit [AddCommGroup G] [DecidableEq ι] in
lemma collision_double_indicator (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) (x : G) :
    (familyMult S C x : ℝ)^2-familyMult S C x=2*indicator (collisions S C) x := by
  have hm := h x
  have hd : x∈collisions S C ↔ 2≤familyMult S C x := by simp [collisions]
  rcases show familyMult S C x=0 ∨ familyMult S C x=1 ∨ familyMult S C x=2 by omega with
    h0 | h1 | h2
  · have hn : x∉collisions S C := fun hh ↦ by have := hd.mp hh; omega
    simp [h0,indicator,hn]
  · have hn : x∉collisions S C := fun hh ↦ by have := hd.mp hh; omega
    simp [h1,indicator,hn]
  · have hc : x∈collisions S C := hd.mpr (by omega)
    norm_num [h2,indicator,hc]

omit [AddCommGroup G] [DecidableEq ι] in
lemma sum_square_mult (S : Finset ι) (C : ι → Finset G) :
    (∑x : G, (familyMult S C x : ℝ)^2)=
      ∑i∈S,∑j∈S, ((C i∩C j).card : ℝ) := by
  simp_rw [← sum_indicators_eq_mult,pow_two,Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have he (x : G) : indicator (C i) x*indicator (C j) x=indicator (C i∩C j) x := by
    simp only [indicator,Finset.mem_inter]
    split_ifs <;> simp_all
  simp_rw [he,sum_indicator]

omit [AddCommGroup G] [DecidableEq ι] in
/-- A count of pairwise intersections determines the collision cardinality. -/
theorem collision_mass_formula (S : Finset ι) (C : ι → Finset G)
    (h : ∀x, familyMult S C x≤2) :
    2*(collisions S C).card=
      (∑i∈S,∑j∈S, ((C i∩C j).card : ℝ))-∑i∈S, ((C i).card : ℝ) := by
  rw [← sum_square_mult,← sum_familyMult,← Finset.sum_sub_distrib]
  simp_rw [collision_double_indicator S C h,← Finset.mul_sum,sum_indicator]

end Erdos66TwofoldFamily
