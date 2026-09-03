import Submission.DivisorExplore

/-! A damped finite Alladi identity. Its maximum-colour approximation is
uniform in the number of prime factors; no arithmetic mean is asserted. -/
namespace Erdos371
open Finset

noncomputable def dampedColour (t : ℝ) (c : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  -∑ E ∈ P.powerset, t^E.card*subsetMinTerm c E

lemma dampedColour_empty (t : ℝ) (c : ℕ → ℝ) : dampedColour t c ∅=0 := by
  simp [dampedColour,subsetMinTerm]

lemma dampedColour_insert_max (t : ℝ) (c : ℕ → ℝ) (P : Finset ℕ) (p : ℕ)
    (hp : p ∉ P) (hmax : ∀ q ∈ P, q ≤ p) :
    dampedColour t c (insert p P)=t*c p+(1-t)*dampedColour t c P := by
  unfold dampedColour
  rw [sum_powerset_insert hp,← sum_add_distrib]
  have he (E : Finset ℕ) (hE : E ∈ P.powerset) :
      t^E.card*subsetMinTerm c E+t^(insert p E).card*subsetMinTerm c (insert p E)=
        (1-t)*(t^E.card*subsetMinTerm c E)-(if E=∅ then t*c p else 0) := by
    have hEP := mem_powerset.mp hE
    have hpE : p ∉ E := fun h => hp (hEP h)
    by_cases hEn : E.Nonempty
    · have hm := hmax (E.min' hEn) (hEP (E.min'_mem hEn))
      simp only [subsetMinTerm,dif_pos hEn,dif_pos (insert_nonempty p E),
        card_insert_of_notMem hpE,min'_insert p E hEn,min_eq_right hm,pow_succ,
        if_neg hEn.ne_empty,sub_zero]
      ring
    · have hEe := not_nonempty_iff_eq_empty.mp hEn
      subst E
      simp [subsetMinTerm]
  rw [sum_congr rfl he,sum_sub_distrib,← mul_sum]
  simp only [sum_ite_eq',empty_mem_powerset,ite_true]
  ring

lemma dampedColour_abs_le_one (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (c : ℕ → ℝ) (P : Finset ℕ) (hc : ∀ p ∈ P, |c p| ≤ 1) : |dampedColour t c P| ≤ 1 := by
  revert hc
  refine induction_on_max P ?_ ?_
  · intro hc
    simp only [dampedColour_empty,abs_zero]
    norm_num
  · intro p S hp ih hc
    have hpnot : p ∉ S := by intro h; exact (lt_irrefl p) (hp p h)
    rw [dampedColour_insert_max t c S p hpnot (fun q hq => (hp q hq).le)]
    have hct := hc p (mem_insert_self _ _)
    have hcs := ih (fun q hq => hc q (mem_insert_of_mem hq))
    calc
      _ ≤ |t*c p|+|(1-t)*dampedColour t c S| := abs_add_le _ _
      _ = t*|c p|+(1-t)*|dampedColour t c S| := by
        rw [abs_mul,abs_mul,abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr ht1)]
      _ ≤ t*1+(1-t)*1 := add_le_add (mul_le_mul_of_nonneg_left hct ht)
        (mul_le_mul_of_nonneg_left hcs (sub_nonneg.mpr ht1))
      _ = 1 := by ring

lemma dampedColour_max_recursion (t : ℝ) (c : ℕ → ℝ) (P : Finset ℕ) (hP : P.Nonempty) :
    dampedColour t c P=t*c (P.max' hP)+(1-t)*dampedColour t c (P.erase (P.max' hP)) := by
  have hp := P.max'_mem hP
  conv_lhs => rw [← insert_erase hp]
  exact dampedColour_insert_max t c _ _ (notMem_erase _ _)
    (fun q hq => P.le_max' q (mem_of_mem_erase hq))

/-- Keeping the largest prime has probability t, so the comparison error
is at most 2(1-t), independently of the number of smaller prime factors. -/
theorem dampedColour_max_error (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (c : ℕ → ℝ) (P : Finset ℕ) (hP : P.Nonempty) (hc : ∀ p ∈ P, |c p| ≤ 1) :
    |dampedColour t c P-c (P.max' hP)| ≤ 2*(1-t) := by
  rw [dampedColour_max_recursion t c P hP]
  have hsmall := dampedColour_abs_le_one t ht ht1 c (P.erase (P.max' hP))
    (fun p hp => hc p (mem_of_mem_erase hp))
  have htop := hc _ (P.max'_mem hP)
  have he : t*c (P.max' hP)+(1-t)*dampedColour t c (P.erase (P.max' hP))-c (P.max' hP)=
      (1-t)*(dampedColour t c (P.erase (P.max' hP))-c (P.max' hP)) := by ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1)]
  have hb := (abs_sub _ _).trans (add_le_add hsmall htop)
  nlinarith

lemma dampedColour_one (c : ℕ → ℝ) (P : Finset ℕ) (hP : P.Nonempty) :
    dampedColour 1 c P=c (P.max' hP) := by
  simp only [dampedColour_max_recursion _ _ _ hP,one_mul,sub_self,zero_mul,add_zero]

#print axioms dampedColour_insert_max
#print axioms dampedColour_max_error
end Erdos371
