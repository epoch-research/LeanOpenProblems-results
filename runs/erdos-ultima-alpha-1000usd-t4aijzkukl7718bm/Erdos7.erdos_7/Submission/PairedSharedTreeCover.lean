import Submission.PairedTreeCover

/-! Conditional paired-tree certificate allowing coherent repeated leaves
within each branch as well as across the two branches. No odd witness. -/
namespace Erdos7PairedSharedTreeCover
open Erdos7SplittingTreeCover Erdos7SharedTreeCover Erdos7PairedTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem odd_cover (A B : Tree) (hA : A.Valid 3) (hB : B.Valid 3)
    (hoA : ∀ i, Odd (A.modulus i)) (hoB : ∀ i, Odd (B.modulus i))
    (c : ℤ) (hc : 3 ∣ c)
    (hiA : Consistent A 3 1) (hiB : Consistent B 3 (2+c))
    (hnA : ∀ i, A.modulus i ≠ 3) (hnB : ∀ i, B.modulus i ≠ 3)
    (hcross : ∀ i j, A.modulus i = B.modulus j →
      (A.modulus i : ℤ) ∣ A.residue 3 1 i - B.residue 3 (2+c) j) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  apply deduplicate (modulus A B) (residue A B c) ?_ ?_ (covers A B hA hB c hc)
  · intro i
    rcases i with _ | i
    · change 1 < (3:ℕ) ∧ Odd (3:ℕ)
      decide
    rcases i with i | i
    · exact ⟨A.nontrivial 3 hA i,hoA i⟩
    · exact ⟨B.nontrivial 3 hB i,hoB i⟩
  · intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    · simp [residue]
    · rcases j with j | j
      · exact False.elim (hnA j hij.symm)
      · exact False.elim (hnB j hij.symm)
    · rcases i with i | i
      · exact False.elim (hnA i hij)
      · exact False.elim (hnB i hij)
    · rcases i with i | i <;> rcases j with j | j
      · exact hiA i j hij
      · exact hcross i j hij
      · have h := hcross j i hij.symm
        have heq : A.modulus j = B.modulus i := hij.symm
        rw [heq] at h
        have hh := dvd_neg.mpr h
        simpa [residue, neg_sub] using hh
      · exact hiB i j hij

#print axioms odd_cover
end Erdos7PairedSharedTreeCover
