import Submission.SixTernaryBranches
import Submission.TwelveTernaryClasses
import Submission.No9Completion

/-! Necessary ternary class counts using the interaction between five and
six exceptional labels. These do not settle the unrestricted conjecture. -/
namespace Erdos7ThirteenTernaryClasses
open Erdos7Reduction Erdos7TwelveTernaryClasses
open Erdos7FourDistinctExceptions Erdos7FiveDistinctExceptions Erdos7SixTernaryBranches
set_option autoImplicit false
set_option maxHeartbeats 4000000

lemma small_pair_no_nine {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r s : ℤ) (hrs : ¬ (3 : ℤ) ∣ r-s)
    (hr : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3)
    (hs : ∀ j, (3 : ℤ) ∣ a j-s → m j≠3)
    (hcr : (branch m a r).card ≤ 5) (hcs : (branch m a s).card ≤ 6) :
    (∀ j, (3 : ℤ) ∣ a j-r → ¬ 9 ∣ m j) ∧
    (∀ j, (3 : ℤ) ∣ a j-s → ¬ 9 ∣ m j) := by
  rw [branch_card] at hcr hcs
  exact ⟨(five_class_branch m a hc r hr hcr).1,
    six_branch_next_to_five_no_nine m a hc r s hrs hr hs hcr hcs⟩

/-- Without actual modulus three, at least eighteen labels have a factor
of three. The seventeen-label extremal distribution would be5,6,6; the
five-label branch would prevent a factor of nine in either other branch. -/
theorem eighteen_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ j, m j≠3) : 18 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  by_contra hsmall
  obtain ⟨j,hj9⟩ := Erdos7No9Certificate.arithmetic_exists_nine m a hc
  let r := a j
  have hr (s : ℤ) : ∀ k, (3 : ℤ) ∣ a k-s → m k≠3 := fun k _ => hno k
  have hs := three_branch_sum_le m a r
  have hpair := two_branch_sum m a hc (r+1) (r+2) (by omega) (hr _) (hr _)
  have h0 : (branch m a r).card ≤ 6 := by omega
  have h0low : 6 ≤ (branch m a r).card := by
    by_contra hn
    have hh := (five_class_branch m a hc r (hr _)
      (by rw [← branch_card]; omega)).1 j (by change (3 : ℤ) ∣ a j-a j; simp)
    exact hh hj9
  have hother : (branch m a (r+1)).card ≤ 5 ∨ (branch m a (r+2)).card ≤ 5 := by omega
  rcases hother with h1 | h2
  · have hh := (small_pair_no_nine m a hc (r+1) r (by omega) (hr _) (hr _) h1 h0).2
    exact hh j (by change (3 : ℤ) ∣ a j-a j; simp) hj9
  · have hh := (small_pair_no_nine m a hc (r+2) r (by omega) (hr _) (hr _) h2 h0).2
    exact hh j (by change (3 : ℤ) ∣ a j-a j; simp) hj9

/-- Every strict odd arithmetic cover has at least thirteen labels divisible
by three. No minimality or irredundance assumption is needed. -/
theorem arithmetic_thirteen_ternary {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    13 ≤ Fintype.card {j // 3 ∣ m j} := by
  classical
  by_cases hex : ∃ j, m j=3
  swap
  · have hh := eighteen_without_three m a hc (by simpa using hex)
    omega
  obtain ⟨j,hj⟩ := hex
  by_contra hsmall
  have hno (r : ℤ) (hr : ¬ (3 : ℤ) ∣ a j-r) :
      ∀ k, (3 : ℤ) ∣ a k-r → m k≠3 := by
    intro k hk hmk
    have he : k=j := hc.1 (hmk.trans hj.symm)
    subst k
    exact hr hk
  have hB := hno (a j+1) (by omega)
  have hC := hno (a j+2) (by omega)
  have hsum := three_branch_sum_le m a (a j)
  have hBC := two_branch_sum m a hc (a j+1) (a j+2) (by omega) hB hC
  have hBlow := ternary_branch_card_five m a hc (a j+1) hB
  have hClow := ternary_branch_card_five m a hc (a j+2) hC
  simp only [← branch_card] at hBlow hClow
  have hjmem : j∈branch m a (a j) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hj],by simp⟩
  have hAlow : 1 ≤ (branch m a (a j)).card := Finset.one_le_card.mpr ⟨j,hjmem⟩
  have hA : (branch m a (a j)).card ≤ 1 := by omega
  have hB6 : (branch m a (a j+1)).card ≤ 6 := by omega
  have hC6 : (branch m a (a j+2)).card ≤ 6 := by omega
  have hsmallpair : (branch m a (a j+1)).card ≤ 5 ∨ (branch m a (a j+2)).card ≤ 5 := by omega
  have hAno : ∀ k, (3 : ℤ) ∣ a k-a j → ¬ 9 ∣ m k := by
    intro k hk hk9
    have hk3 : 3 ∣ m k := (by decide : 3 ∣ 9).trans hk9
    have hkmem : k∈branch m a (a j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk3,hk⟩
    have he : k=j := Finset.card_le_one.mp hA k hkmem j hjmem
    subst k
    rw [hj] at hk9
    norm_num at hk9
  have hBCno : (∀ k, (3 : ℤ) ∣ a k-(a j+1) → ¬ 9 ∣ m k) ∧
      (∀ k, (3 : ℤ) ∣ a k-(a j+2) → ¬ 9 ∣ m k) := by
    rcases hsmallpair with hb | hc'
    · exact small_pair_no_nine m a hc (a j+1) (a j+2) (by omega) hB hC hb hC6
    · exact (small_pair_no_nine m a hc (a j+2) (a j+1) (by omega) hC hB hc' hB6).symm
  obtain ⟨k,hk9⟩ := Erdos7No9Certificate.arithmetic_exists_nine m a hc
  have hcases : (3 : ℤ) ∣ a k-a j ∨ (3 : ℤ) ∣ a k-(a j+1) ∨ (3 : ℤ) ∣ a k-(a j+2) := by omega
  rcases hcases with ha | hb | hc'
  · exact hAno k ha hk9
  · exact hBCno.1 k hb hk9
  · exact hBCno.2 k hc' hk9

theorem strict_thirteen_ternary (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i, ¬ C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    13 ≤ Fintype.card {j // 3 ∣ (C.moduli j).absNorm} := by
  letI := C.fintypeIndex
  exact arithmetic_thirteen_ternary (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms eighteen_without_three
#print axioms arithmetic_thirteen_ternary
#print axioms strict_thirteen_ternary
end Erdos7ThirteenTernaryClasses
