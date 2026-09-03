import Mathlib.Data.Nat.Basic

/-! Assembly of finite checks on consecutive intervals of natural numbers. -/
namespace Erdos184Work.FiniteIntervals

def Covers (P : ℕ → Prop) (lo hi : ℕ) : Prop :=
  ∀ j, lo ≤ j → j < hi → P j

lemma of_fin {P : ℕ → Prop} (lo width : ℕ)
    (h : ∀ i : Fin width, P (lo + i.val)) : Covers P lo (lo + width) := by
  intro j hlo hhi
  have hs : j - lo < width := by omega
  have he : lo + (j - lo) = j := by omega
  simpa only [he] using h ⟨j-lo,hs⟩

lemma merge {P : ℕ → Prop} {lo mid hi : ℕ}
    (hL : Covers P lo mid) (hR : Covers P mid hi) : Covers P lo hi := by
  intro j hjlo hjhi
  by_cases hj : j < mid
  · exact hL j hjlo hj
  · exact hR j (Nat.le_of_not_gt hj) hjhi

#print axioms of_fin
#print axioms merge
end Erdos184Work.FiniteIntervals
