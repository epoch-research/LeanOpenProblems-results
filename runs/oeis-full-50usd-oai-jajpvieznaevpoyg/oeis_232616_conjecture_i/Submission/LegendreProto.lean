import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

open Finset Nat Classical

variable (pAt : Nat → Nat)

def noDiv (pAt : Nat → Nat) (a m : Nat) : Prop := ∀ i, i < a → ¬ pAt i ∣ m

noncomputable def roughSet (pAt : Nat → Nat) (a n : Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun m => noDiv pAt a m)

lemma noDiv_succ_iff (a m : Nat) :
    noDiv pAt (a+1) m ↔ noDiv pAt a m ∧ ¬ pAt a ∣ m := by
  constructor
  · intro h; constructor
    · intro i hi; exact h i (by omega)
    · exact h a (by omega)
  · intro h i hi
    by_cases hia : i = a
    · subst i; exact h.2
    · exact h.1 i (by omega)

lemma roughSet_succ_card (a n : Nat) :
    (roughSet pAt (a+1) n).card = (roughSet pAt a n).card - ((roughSet pAt a n).filter (fun m => pAt a ∣ m)).card := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := roughSet pAt a n) (p := fun m => pAt a ∣ m)
  have hpart : (roughSet pAt (a+1) n) = (roughSet pAt a n).filter (fun m => ¬ pAt a ∣ m) := by
    ext m
    simp [roughSet, noDiv_succ_iff, and_assoc]
  rw [hpart]
  omega

lemma card_divisible_eq (a n : Nat) (hp_pos : 0 < pAt a)
    (hcop : ∀ i, i < a → Nat.Coprime (pAt i) (pAt a)) :
    ((roughSet pAt a n).filter (fun m => pAt a ∣ m)).card = (roughSet pAt a (n / pAt a)).card := by
  classical
  let p := pAt a
  apply Eq.symm
  apply Finset.card_bij (fun m _ => p * m)
  · intro m hm
    simp only [roughSet, mem_filter, mem_Icc] at hm ⊢
    constructor
    · constructor
      · constructor
        · exact Nat.mul_pos hp_pos (lt_of_lt_of_le zero_lt_one hm.1.1)
        · simpa [p, mul_comm] using (Nat.le_div_iff_mul_le hp_pos).mp hm.1.2
      · intro i hi hdiv
        exact hm.2 i hi ((hcop i hi).dvd_mul_right.mp (by simpa [p, mul_comm] using hdiv))
    · exact dvd_mul_right p m
  · intro m hm m' hm' hEq
    exact Nat.eq_of_mul_eq_mul_left hp_pos hEq
  · intro y hy
    simp only [roughSet, mem_filter, mem_Icc] at hy
    rcases hy.2 with ⟨m, rfl⟩
    refine ⟨m, ?_, rfl⟩
    simp only [roughSet, mem_filter, mem_Icc]
    constructor
    · constructor
      · cases m with
        | zero => simp at hy
        | succ m => omega
      · simpa [p, mul_comm] using (Nat.le_div_iff_mul_le hp_pos).mpr (by simpa [p, mul_comm] using hy.1.1.2)
    · intro i hi hdiv
      exact hy.1.2 i hi (dvd_mul_of_dvd_right hdiv p)

lemma rough_card_rec (a n : Nat) (hp_pos : 0 < pAt a)
    (hcop : ∀ i, i < a → Nat.Coprime (pAt i) (pAt a)) :
    (roughSet pAt (a+1) n).card = (roughSet pAt a n).card - (roughSet pAt a (n / pAt a)).card := by
  rw [roughSet_succ_card, card_divisible_eq pAt a n hp_pos hcop]

