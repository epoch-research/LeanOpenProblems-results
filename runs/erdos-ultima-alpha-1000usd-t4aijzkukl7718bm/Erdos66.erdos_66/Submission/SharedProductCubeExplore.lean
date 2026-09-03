import Submission.SharedParameterSetExplore

/-! Every Cartesian product of nontrivial two-point sets forces an
exponential representation peak. In particular, an unmodified shared-label
product cannot have bounded mean through arbitrarily many factors. -/
namespace Erdos66SharedProductCube
open Erdos66OriginRepair Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, DecidableEq (G i)]

lemma pairCount_pi (A B : ∀ i, Finset (G i)) (z : ∀ i, G i) :
    pairCount (Fintype.piFinset A) (Fintype.piFinset B) z = ∏ i, pairCount (A i) (B i) (z i) := by
  unfold pairCount
  have he : ((Fintype.piFinset A).filter (fun x ↦ z-x∈Fintype.piFinset B)) =
      Fintype.piFinset (fun i ↦ (A i).filter (fun x ↦ z i-x∈B i)) := by
    ext x
    simp only [Finset.mem_filter,Fintype.mem_piFinset,Pi.sub_apply]
    exact forall_and.symm
  rw [he,Fintype.card_piFinset]

lemma pairCount_two_points {H : Type*} [AddCommGroup H] [DecidableEq H]
    (a b : H) (hab : a ≠ b) : pairCount {a,b} {a,b} (a+b)=2 := by
  have he : ({a,b} : Finset H).filter (fun x ↦ a+b-x∈({a,b} : Finset H))={a,b} := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  rw [pairCount,he,Finset.card_pair hab]

/-- Coordinatewise choices between two distinct points yield 2^|ι|
representations of their coordinatewise sum in every containing set. -/
theorem cube_peak (a b : ∀ i, G i) (hab : ∀ i, a i ≠ b i)
    (A : Finset (∀ i, G i)) (hA : Fintype.piFinset (fun i ↦ {a i,b i}) ⊆ A) :
    2^Fintype.card ι ≤ pairCount A A (a+b) := by
  have he := pairCount_pi (fun i ↦ ({a i,b i} : Finset (G i)))
    (fun i ↦ ({a i,b i} : Finset (G i))) (a+b)
  simp only [Pi.add_apply,pairCount_two_points _ _ (hab _),Finset.prod_const,Finset.card_univ] at he
  rw [← he]
  exact pairCount_mono hA hA _

variable {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]

/-- This bound uses only one label, so adding more labels or repair points
cannot remove the peak. It does not depend on quadratic-character estimates. -/
theorem product_curve_peak (u : ∀ i, F i) (A : Finset (∀ i, F i × F i))
    (hA : Fintype.piFinset (fun i ↦ curve (u i)) ⊆ A) :
    2^Fintype.card ι ≤ pairCount A A (fun i ↦ (1,1/u i)) := by
  have hab : ∀ i, (0 : F i × F i) ≠ (1,1/u i) := by
    intro i he
    exact zero_ne_one (congrArg Prod.fst he)
  have hsub : Fintype.piFinset (fun i ↦ ({0,(1,1/u i)} : Finset (F i × F i))) ⊆
      Fintype.piFinset (fun i ↦ curve (u i)) := by
    apply Fintype.piFinset_subset
    intro i x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [mem_curve]
  have he := cube_peak (fun i ↦ (0 : F i × F i)) (fun i ↦ (1,1/u i)) hab A (hsub.trans hA)
  change 2^Fintype.card ι ≤ pairCount A A ((0 : ∀ i, F i × F i)+(fun i ↦ (1,1/u i))) at he
  simpa only [zero_add] using he

end Erdos66SharedProductCube
