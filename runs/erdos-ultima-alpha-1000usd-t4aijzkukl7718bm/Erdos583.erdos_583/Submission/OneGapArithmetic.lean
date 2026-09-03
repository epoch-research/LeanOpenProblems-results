import Submission.Work

/-! The arithmetic boundary for a cycle family with at most one missing core edge. -/
namespace Erdos583OneGapArithmeticDevelopment
set_option maxHeartbeats 200000
lemma one_gap_arithmetic (q t e d : ℕ) (h3 : 3 ≤ q) (hdense : q ≤ 2*t+2)
    (hsum : e+d=t*(q-1)) (hd : d ≤ 1) (hbound : q+e ≤ q.choose 2) :
    q=2*t+2 ∧ d=1 ∧ q+e=q.choose 2 := by
  have hsub : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hchoose : 2*q.choose 2 ≤ q*(q-1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have hq : q=2*t+2 := by
    by_contra hn
    have hlt : q ≤ 2*t+1 := by omega
    have hm := Nat.mul_le_mul_right (q-1) (show q-1 ≤ 2*t by omega)
    nlinarith
  have hc : q.choose 2=(t+1)*(q-1) := by
    rw [hq,Nat.choose_two_right]
    have he : 2*t+2=2*(t+1) := by omega
    rw [he]
    simp [Nat.mul_assoc]
  rw [hc] at hbound
  have hd1 : d=1 := by nlinarith
  exact ⟨hq,hd1,by rw [hc]; nlinarith⟩

lemma sum_one_unique {t : ℕ} (f : Fin t → ℕ) (hf : (∑ i, f i)=1) :
    ∃ j, f j=1 ∧ ∀ i, i ≠ j → f i=0 := by
  classical
  have hex : ∃ j, 0 < f j := by
    by_contra! hn
    have hz : (∑ i, f i)=0 := Finset.sum_eq_zero (fun i _ ↦ Nat.eq_zero_of_le_zero (hn i))
    omega
  obtain ⟨j,hj⟩ := hex
  have hb : f j ≤ 1 := by
    simpa only [hf] using Finset.single_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hj1 : f j=1 := by omega
  refine ⟨j,hj1,?_⟩
  intro i hij
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin t)) f (Finset.mem_univ j)
  rw [hf,hj1] at he
  have hi : i ∈ (Finset.univ : Finset (Fin t)).erase j := by simp [hij]
  have hb' := Finset.single_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) hi
  omega

end Erdos583OneGapArithmeticDevelopment
