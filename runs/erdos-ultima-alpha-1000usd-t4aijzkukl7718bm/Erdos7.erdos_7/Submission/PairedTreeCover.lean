import Submission.SharedTreeCover

/-! A conditional certificate for two surviving ternary fibres. -/
namespace Erdos7PairedTreeCover
open Erdos7SplittingTreeCover Erdos7SharedTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Label (A B : Tree) := Option (A.Leaf ⊕ B.Leaf)
instance (A B : Tree) : Fintype (Label A B) := inferInstanceAs (Fintype (Option (A.Leaf ⊕ B.Leaf)))

def modulus (A B : Tree) : Label A B → ℕ :=
  Option.elim' 3 (Sum.elim A.modulus B.modulus)
def residue (A B : Tree) (c : ℤ) : Label A B → ℤ :=
  Option.elim' 0 (Sum.elim (A.residue 3 1) (B.residue 3 (2+c)))

lemma covers (A B : Tree) (hA : A.Valid 3) (hB : B.Valid 3)
    (c : ℤ) (hc : 3 ∣ c) (x : ℤ) :
    ∃ i : Label A B, (modulus A B i : ℤ) ∣ x-residue A B c i := by
  obtain ⟨r,hr⟩ := Erdos7DivisorRepair.split_class 1 3 (by omega) 0 x (by simp)
  fin_cases r
  · exact ⟨none, by simpa [modulus, residue] using hr⟩
  · obtain ⟨i,hi⟩ := A.covers 3 1 hA x (by simpa using hr)
    exact ⟨some (.inl i),hi⟩
  · have hh : (3:ℤ) ∣ x-(2+c) := by
      have h := dvd_sub (show (3:ℤ) ∣ x-2 by simpa using hr) hc
      convert h using 1; ring
    obtain ⟨i,hi⟩ := B.covers 3 (2+c) hB x hh
    exact ⟨some (.inr i),hi⟩

/-- No primality assumptions are needed once the actual cross-branch
congruence coherence has been checked. -/
theorem odd_cover (A B : Tree) (hA : A.Valid 3) (hB : B.Valid 3)
    (hoA : ∀ i, Odd (A.modulus i)) (hoB : ∀ i, Odd (B.modulus i))
    (hiA : Function.Injective A.modulus) (hiB : Function.Injective B.modulus)
    (hnA : ∀ i, A.modulus i ≠ 3) (hnB : ∀ i, B.modulus i ≠ 3)
    (c : ℤ) (hc : 3 ∣ c)
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
      · have h := hiA hij
        subst j
        simp [residue]
      · exact hcross i j hij
      · have h := hcross j i hij.symm
        have heq : A.modulus j = B.modulus i := hij.symm
        rw [heq] at h
        have hh := dvd_neg.mpr h
        simpa [residue, neg_sub] using hh
      · have h := hiB hij
        subst j
        simp [residue]

/-- An even positive control with a genuine shared2-class. -/
def controlA : Tree := .split 2 ![.leaf 2, .split 2 ![.leaf 4, .leaf 12]]
def controlB : Tree := .split 2 ![.leaf 6, .leaf 2]
lemma controlA_valid : controlA.Valid 3 := by decide +kernel
lemma controlB_valid : controlB.Valid 3 := by decide +kernel
lemma control_cross : ∀ i j, controlA.modulus i = controlB.modulus j →
    (controlA.modulus i : ℤ) ∣ controlA.residue 3 1 i-controlB.residue 3 (2+0) j := by
  decide +kernel
lemma control_covers : ∀ x : ℤ, ∃ i : Label controlA controlB,
    (modulus controlA controlB i : ℤ) ∣ x-residue controlA controlB 0 i :=
  covers _ _ controlA_valid controlB_valid 0 (by simp)

#print axioms covers
#print axioms odd_cover
#print axioms control_cross
#print axioms control_covers
end Erdos7PairedTreeCover
