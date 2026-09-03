import FormalConjecturesUtil

/-!
A character-sum parameter lemma in characteristic three. It is an ingredient
for an obstruction to a proposed construction, not a solution to Erdős 714.
-/

open Finset Classical

namespace Erdos714ConsecutiveSquares

variable {F : Type*} [Field F] [Fintype F] [CharP F 3]

/-- With -1 nonsquare, the three-square indicator has sum |F|-3. -/
theorem indicator_sum (hns : ¬IsSquare (-1 : F)) :
    (∑ x : F, (1 + quadraticChar F x) * (1 + quadraticChar F (x-1)) *
      (1 + quadraticChar F (x+1))) = (Fintype.card F : ℤ)-3 := by
  let χ := quadraticChar F
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; decide
  have hn : χ (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hns
  have hneg (x : F) : χ (-x) = -χ x := by
    rw [show -x = (-1)*x by ring, map_mul, hn]
    ring
  have hsum : ∑ x : F, χ x = 0 := quadraticChar_sum_zero hchar
  have hm : ∑ x : F, χ (x-1) = 0 := by
    have h := (Equiv.subRight (1 : F)).sum_comp χ
    simpa only [Equiv.subRight_apply, hsum] using h
  have hp : ∑ x : F, χ (x+1) = 0 := by
    have h := Equiv.sum_comp (Equiv.addRight (1 : F)) χ
    simpa only [Equiv.coe_addRight, hsum] using h
  have hpair : ∑ x : F, χ x * χ (x-1) = -1 := by
    have hj := jacobiSum_nontrivial_inv (quadraticChar_ne_one hchar)
    rw [(quadraticChar_isQuadratic F).inv] at hj
    change (∑ x : F, χ x * χ (1-x)) = -χ (-1) at hj
    have ht (x : F) : χ x * χ (1-x) = -(χ x * χ (x-1)) := by
      rw [show 1-x = -(x-1) by ring, hneg]
      ring
    simp_rw [ht] at hj
    rw [sum_neg_distrib, hn] at hj
    omega
  have hpairplus : ∑ x : F, χ x * χ (x+1) = -1 := by
    have h := Equiv.sum_comp (Equiv.addRight (1 : F)) (fun x => χ x * χ (x-1))
    simpa only [Equiv.coe_addRight, add_sub_cancel_right, mul_comm, hpair] using h
  have hthree (x : F) : x-1-1 = x+1 := by
    have h := CharP.cast_eq_zero F 3
    linear_combination -h
  have hpairouter : ∑ x : F, χ (x-1) * χ (x+1) = -1 := by
    have h := (Equiv.subRight (1 : F)).sum_comp (fun x => χ x * χ (x-1))
    simpa only [Equiv.subRight_apply, hthree, hpair] using h
  have htriple : ∑ x : F, χ x * χ (x-1) * χ (x+1) = 0 := by
    let t (x : F) := χ x * χ (x-1) * χ (x+1)
    have he := Equiv.sum_comp (Equiv.neg F) t
    have ht (x : F) : t (-x) = -t x := by
      dsimp [t]
      rw [show -x-1 = -(x+1) by ring, show -x+1 = -(x-1) by ring]
      simp only [hneg]
      ring
    simp only [Equiv.neg_apply, ht, sum_neg_distrib] at he
    change ∑ x, t x = 0
    omega
  have hex (x : F) : (1+χ x)*(1+χ (x-1))*(1+χ (x+1)) =
      1 + χ x + χ (x-1) + χ (x+1) + χ x*χ (x-1) + χ x*χ (x+1) +
        χ (x-1)*χ (x+1) + χ x*χ (x-1)*χ (x+1) := by ring
  change (∑ x : F, (1+χ x)*(1+χ (x-1))*(1+χ (x+1))) = _
  simp_rw [hex]
  simp only [sum_add_distrib, sum_const, card_univ,
    hsum, hm, hp, hpair, hpairplus, hpairouter, htriple]
  ring

/-- Every characteristic-three finite field larger than three with -1 nonsquare
contains three consecutive nonzero squares. -/
theorem exists_three_squares (hns : ¬IsSquare (-1 : F)) (hq : 3 < Fintype.card F) :
    ∃ x : F, x ≠ 0 ∧ x-1 ≠ 0 ∧ x+1 ≠ 0 ∧
      IsSquare x ∧ IsSquare (x-1) ∧ IsSquare (x+1) := by
  classical
  have hn : quadraticChar F (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hns
  have htwo : (2 : F) = -1 := by
    have h := CharP.cast_eq_zero F 3
    linear_combination h
  have hs := indicator_sum hns
  have hs0 : (∑ x : F, (1 + quadraticChar F x) * (1 + quadraticChar F (x-1)) *
      (1 + quadraticChar F (x+1))) ≠ 0 := by rw [hs]; omega
  obtain ⟨x, _, hx⟩ := exists_ne_zero_of_sum_ne_zero hs0
  have hx0 : x ≠ 0 := by
    intro h; subst x
    simp [hn] at hx
  have hxm : x-1 ≠ 0 := by
    intro h
    have he : x = 1 := sub_eq_zero.mp h
    subst x
    have hc : quadraticChar F ((1 : F)+1) = -1 := by
      rw [show (1 : F)+1 = -1 by linear_combination htwo, hn]
    simp only [sub_self, MulChar.map_one, MulChar.map_zero, hc] at hx
    norm_num at hx
  have hxp : x+1 ≠ 0 := by
    intro h
    have he : x = -1 := eq_neg_of_add_eq_zero_left h
    subst x
    simp [hn] at hx
  have h₀ : quadraticChar F x = 1 := by
    rcases quadraticChar_dichotomy hx0 with h | h
    · exact h
    · simp [h] at hx
  have h₁ : quadraticChar F (x-1) = 1 := by
    rcases quadraticChar_dichotomy hxm with h | h
    · exact h
    · simp [h] at hx
  have h₂ : quadraticChar F (x+1) = 1 := by
    rcases quadraticChar_dichotomy hxp with h | h
    · exact h
    · simp [h] at hx
  exact ⟨x, hx0, hxm, hxp, (quadraticChar_one_iff_isSquare hx0).mp h₀,
    (quadraticChar_one_iff_isSquare hxm).mp h₁,
    (quadraticChar_one_iff_isSquare hxp).mp h₂⟩

#print axioms indicator_sum
#print axioms exists_three_squares

end Erdos714ConsecutiveSquares
