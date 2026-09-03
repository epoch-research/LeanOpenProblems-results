import Submission.ForestCapacity

/-! The loss of intersection between the first 3-adic branches is paid for
by their unequal surviving sizes. Auxiliary finite geometry only. -/
namespace Erdos7RootOverlapCompensation
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option autoImplicit false

/-- Surviving residues after deleting one class modulo3 and a disjoint
singleton class modulo9. -/
def survivors (a : Fin 3) (b : Fin 9) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => x.val%3 ≠ a.val ∧ x ≠ b)

def branch (a : Fin 3) (b : Fin 9) (r : Fin 3) : Finset (Fin 9) :=
  (survivors a b).filter (fun x => x.val%3 = r.val)

lemma survivors_card : ∀ (a : Fin 3) (b : Fin 9),b.val%3 ≠ a.val →
    (survivors a b).card = 5 := by decide +kernel

lemma branch_card : ∀ (a : Fin 3) (b : Fin 9) (r : Fin 3),
    b.val%3 ≠ a.val → r ≠ a →
    (branch a b r).card = if r.val = b.val%3 then 2 else 3 := by decide +kernel

lemma branch_intersection : ∀ (a : Fin 3) (b : Fin 9) (r s : Fin 3),
    branch a b r ∩ branch a b s = if r = s then branch a b r else ∅ := by
  decide +kernel

lemma equal_size_branch : ∀ (a : Fin 3) (b : Fin 9) (r s : Fin 3),
    b.val%3 ≠ a.val → r ≠ a → s ≠ a →
    (branch a b r).card = (branch a b s).card → r = s := by decide +kernel

/-- The uniform forced charge is1/40. Smaller branch probabilities compensate
a missing intersection even after the rest of the forest spends its degree
budgets at the two pivots. -/
theorem branch_overlap_charge (u v d₁ d₂ : ℚ)
    (hu : u = 2/5 ∨ u = 3/5) (hv : v = 2/5 ∨ v = 3/5)
    (hd₁ : d₁ ≤ 1/2) (hd₂ : d₂ ≤ 1/4) :
    1/40 ≤ (if u = v then u/24 else 0)+
      (3/20-u/4)*(1-d₁)+(1/10-v/6)*(1-d₂) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  all_goals norm_num <;> linarith

/-- Finite residue form of the same compensation inequality. -/
theorem residue_overlap_charge (a : Fin 3) (b : Fin 9) (r s : Fin 3)
    (hab : b.val%3 ≠ a.val) (hr : r ≠ a) (hs : s ≠ a)
    (d₁ d₂ : ℚ) (hd₁ : d₁ ≤ 1/2) (hd₂ : d₂ ≤ 1/4) :
    1/40 ≤ ((branch a b r ∩ branch a b s).card : ℚ)/120+
      (3/20-((branch a b r).card : ℚ)/20)*(1-d₁)+
      (1/10-((branch a b s).card : ℚ)/30)*(1-d₂) := by
  let u : ℚ := (branch a b r).card/5
  let v : ℚ := (branch a b s).card/5
  have hu : u = 2/5 ∨ u = 3/5 := by
    dsimp only [u]
    rw [branch_card a b r hab hr]
    split_ifs <;> simp
  have hv : v = 2/5 ∨ v = 3/5 := by
    dsimp only [v]
    rw [branch_card a b s hab hs]
    split_ifs <;> simp
  have huv : u = v ↔ r = s := by
    constructor
    · intro h
      apply equal_size_branch a b r s hab hr hs
      have hh : ((branch a b r).card : ℚ) = ((branch a b s).card : ℚ) := by
        dsimp only [u,v] at h
        linarith
      exact_mod_cast hh
    · rintro rfl
      rfl
  have he : (if u = v then u/24 else 0) = ((branch a b r ∩ branch a b s).card : ℚ)/120 := by
    rw [branch_intersection]
    by_cases h : r = s
    · rw [if_pos h,if_pos (huv.mpr h)]
      dsimp only [u]
      ring
    · rw [if_neg h,if_neg (fun hh => h (huv.mp hh)),Finset.card_empty,Nat.cast_zero,zero_div]
  have hh := branch_overlap_charge u v d₁ d₂ hu hv hd₁ hd₂
  rw [he] at hh
  dsimp only [u,v] at hh
  convert hh using 1 <;> ring

#print axioms branch_overlap_charge
#print axioms residue_overlap_charge
end Erdos7RootOverlapCompensation
