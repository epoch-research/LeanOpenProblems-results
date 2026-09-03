import Submission.BooleanCoupledDuality

/-! Cardinality reductions for symmetric weights on finite Boolean cubes. -/
namespace Erdos970.FiniteSelberg.BooleanSymmetric
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def patternSet (ω : ι → Bool) : Finset ι := univ.filter (fun i => ω i = true)

@[simp] lemma mem_patternSet (ω : ι → Bool) (i : ι) : i ∈ patternSet ω ↔ ω i = true := by
  simp [patternSet]

def patternEquivFinset : (ι → Bool) ≃ Finset ι where
  toFun := patternSet
  invFun := fun S i => decide (i ∈ S)
  left_inv := by intro ω; funext i; simp
  right_inv := by intro S; ext i; simp

lemma sum_card_powerset {R : Type*} [Semiring R] (S : Finset ι) (f : ℕ → R) :
    (∑ A ∈ S.powerset, f A.card) =
      ∑ t ∈ range (S.card + 1), (S.card.choose t : R) * f t := by
  rw [sum_powerset]
  simp only [sum_powersetCard, nsmul_eq_mul]

lemma sum_card {R : Type*} [Semiring R] (f : ℕ → R) :
    (∑ A : Finset ι, f A.card) =
      ∑ t ∈ range (Fintype.card ι + 1), (Nat.choose (Fintype.card ι) t : R) * f t := by
  simpa using sum_card_powerset (univ : Finset ι) f

lemma fixed_subset_sum {R : Type*} [Semiring R]
    (S T : Finset ι) (hTS : T ⊆ S) (f : ℕ → R) :
    (∑ A : Finset ι, if A ⊆ S ∧ T ⊆ A then f A.card else 0) =
      ∑ t ∈ range (S.card - T.card + 1),
        ((S.card - T.card).choose t : R) * f (T.card + t) := by
  classical
  rw [← sum_filter]
  have he : (∑ A ∈ univ.filter (fun A : Finset ι => A ⊆ S ∧ T ⊆ A), f A.card) =
      ∑ B ∈ (S \ T).powerset, f (T.card + B.card) := by
    symm
    apply sum_bij (fun B _ => T ∪ B)
    · intro B hB
      have hb := mem_powerset.mp hB
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨union_subset hTS (hb.trans sdiff_subset), subset_union_left⟩
    · intro A hA B hB heq
      have ha : Disjoint T A := by
        rw [disjoint_left]
        intro x hx hxa
        exact (mem_sdiff.mp (mem_powerset.mp hA hxa)).2 hx
      have hb : Disjoint T B := by
        rw [disjoint_left]
        intro x hx hxb
        exact (mem_sdiff.mp (mem_powerset.mp hB hxb)).2 hx
      have hh := congrArg (fun U => U \ T) heq
      simpa only [union_sdiff_cancel_left ha, union_sdiff_cancel_left hb] using hh
    · intro A hA
      obtain ⟨hAS, hTA⟩ := (mem_filter.mp hA).2
      refine ⟨A \ T, mem_powerset.mpr ?_, ?_⟩
      · intro x hx
        exact mem_sdiff.mpr ⟨hAS (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
      · rw [union_comm, sdiff_union_of_subset hTA]
    · intro B hB
      have hb : Disjoint T B := by
        rw [disjoint_left]
        intro x hx hxb
        exact (mem_sdiff.mp (mem_powerset.mp hB hxb)).2 hx
      rw [card_union_of_disjoint hb]
  rw [he, sum_card_powerset (S \ T) (fun t => f (T.card + t)), card_sdiff_of_subset hTS]

lemma symmetric_moment {R : Type*} [Semiring R]
    (S T : Finset ι) (hTS : T ⊆ S) (f : ℕ → R) :
    (∑ ω : ι → Bool, if patternSet ω ⊆ S ∧ T ⊆ patternSet ω
      then f (patternSet ω).card else 0) =
      ∑ t ∈ range (S.card - T.card + 1),
        ((S.card - T.card).choose t : R) * f (T.card + t) := by
  rw [← fixed_subset_sum S T hTS f]
  apply Fintype.sum_equiv patternEquivFinset
  intro ω
  rfl

lemma symmetric_value {R : Type*} [Semiring R] (f : ℕ → R) (ω : ι → Bool) :
    (∑ T : Finset ι, f T.card * if T ⊆ patternSet ω then 1 else 0) =
      ∑ t ∈ range ((patternSet ω).card + 1),
        ((patternSet ω).card.choose t : R) * f t := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  have he : univ.filter (fun T => T ⊆ patternSet ω) = (patternSet ω).powerset := by
    ext T; simp
  rw [he, sum_card_powerset]

@[simp] lemma patternSet_empty : patternSet (fun _ : ι => false) = ∅ := by
  ext i; simp

lemma patternSet_eq_empty (ω : ι → Bool) : patternSet ω = ∅ ↔ ω = (fun _ => false) := by
  constructor
  · intro h; funext i
    have hi : ¬ ω i = true := by
      rw [← mem_patternSet, h]; simp
    exact Bool.eq_false_iff.mpr hi
  · rintro rfl; exact patternSet_empty

#print axioms symmetric_moment
#print axioms symmetric_value
end Erdos970.FiniteSelberg.BooleanSymmetric
