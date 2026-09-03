import Submission.PairedTreeCover

/-! A sufficient certificate allowing an invertible affine transformation
of the second ternary fibre. Modulus reuse still requires actual coherence.
No odd witness is supplied. -/
namespace Erdos7AffinePairedTreeCover
open Erdos7SplittingTreeCover Erdos7SharedTreeCover
open Erdos7PairedTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- An inverse modulo the common period transports a fibre cover. -/
theorem affine_fiber_covers {I : Type*} (d : I → ℕ) (r : I → ℤ)
    (N : ℕ) (scale offset inverse : ℤ)
    (hperiod : ∀ i, d i ∣ N)
    (hinverse : (N : ℤ) ∣ scale*inverse-1)
    (hi3 : (3 : ℤ) ∣ inverse-1) (ho3 : (3 : ℤ) ∣ offset)
    (hc : ∀ x : ℤ, (3 : ℤ) ∣ x-2 → ∃ i, (d i : ℤ) ∣ x-r i)
    (x : ℤ) (hx : (3 : ℤ) ∣ x-2) :
    ∃ i, (d i : ℤ) ∣ x-(scale*r i+offset) := by
  let y := inverse*(x-offset)
  have hy : (3 : ℤ) ∣ y-2 := by
    have h := dvd_sub (dvd_add (dvd_mul_of_dvd_left hi3 (x-offset)) hx) ho3
    convert h using 1 <;> dsimp [y] <;> ring
  obtain ⟨i,hi⟩ := hc y hy
  refine ⟨i,?_⟩
  have hp : (d i : ℤ) ∣ N := by exact_mod_cast hperiod i
  have hunit := hp.trans hinverse
  have h := dvd_sub (dvd_mul_of_dvd_right hi scale) (dvd_mul_of_dvd_left hunit (x-offset))
  convert h using 1 <;> dsimp [y] <;> ring

def affineResidue (A B : Tree) (scale offset : ℤ) : Label A B → ℤ :=
  Option.elim' 0 (Sum.elim (A.residue 3 1)
    (fun i => scale*B.residue 3 2 i+offset))

theorem covers (A B : Tree) (hA : A.Valid 3) (hB : B.Valid 3)
    (N : ℕ) (scale offset inverse : ℤ)
    (hperiod : ∀ i, B.modulus i ∣ N)
    (hinverse : (N : ℤ) ∣ scale*inverse-1)
    (hi3 : (3 : ℤ) ∣ inverse-1) (ho3 : (3 : ℤ) ∣ offset)
    (x : ℤ) :
    ∃ i : Label A B, (modulus A B i : ℤ) ∣ x-affineResidue A B scale offset i := by
  obtain ⟨r,hr⟩ := Erdos7DivisorRepair.split_class 1 3 (by omega) 0 x (by simp)
  fin_cases r
  · exact ⟨none, by simpa [modulus,affineResidue] using hr⟩
  · obtain ⟨i,hi⟩ := A.covers 3 1 hA x (by simpa using hr)
    exact ⟨some (.inl i),hi⟩
  · obtain ⟨i,hi⟩ := affine_fiber_covers B.modulus (B.residue 3 2)
      N scale offset inverse hperiod hinverse hi3 ho3
      (fun y hy => B.covers 3 2 hB y hy) x (by simpa using hr)
    exact ⟨some (.inr i),hi⟩

/-- Actual cross-branch coherence is indispensable. Shared composite
moduli cannot be accepted merely because the resource allocation fits. -/
theorem odd_cover (A B : Tree) (hA : A.Valid 3) (hB : B.Valid 3)
    (hoA : ∀ i, Odd (A.modulus i)) (hoB : ∀ i, Odd (B.modulus i))
    (hiA : Function.Injective A.modulus) (hiB : Function.Injective B.modulus)
    (hnA : ∀ i, A.modulus i ≠ 3) (hnB : ∀ i, B.modulus i ≠ 3)
    (N : ℕ) (scale offset inverse : ℤ)
    (hperiod : ∀ i, B.modulus i ∣ N)
    (hinverse : (N : ℤ) ∣ scale*inverse-1)
    (hi3 : (3 : ℤ) ∣ inverse-1) (ho3 : (3 : ℤ) ∣ offset)
    (hcross : ∀ i j, A.modulus i = B.modulus j →
      (A.modulus i : ℤ) ∣ A.residue 3 1 i-(scale*B.residue 3 2 j+offset)) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  apply deduplicate (modulus A B) (affineResidue A B scale offset) ?_ ?_
    (covers A B hA hB N scale offset inverse hperiod hinverse hi3 ho3)
  · intro i
    rcases i with _ | i
    · change 1 < (3:ℕ) ∧ Odd (3:ℕ)
      decide
    rcases i with i | i
    · exact ⟨A.nontrivial 3 hA i,hoA i⟩
    · exact ⟨B.nontrivial 3 hB i,hoB i⟩
  · intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    · simp [affineResidue]
    · rcases j with j | j
      · exact False.elim (hnA j hij.symm)
      · exact False.elim (hnB j hij.symm)
    · rcases i with i | i
      · exact False.elim (hnA i hij)
      · exact False.elim (hnB i hij)
    · rcases i with i | i <;> rcases j with j | j
      · have h := hiA hij
        subst j
        simp [affineResidue]
      · exact hcross i j hij
      · have h := hcross j i hij.symm
        have heq : A.modulus j = B.modulus i := hij.symm
        rw [heq] at h
        have hh := dvd_neg.mpr h
        simpa [affineResidue,neg_sub] using hh
      · have h := hiB hij
        subst j
        simp [affineResidue]

/-- Even control sharing both a prime and its square, with a nontrivial
scale. This is not an odd covering system. -/
def controlA : Tree := .split 2 ![.leaf 2,.split 2 ![.leaf 4,.leaf 12]]
def controlB : Tree := .split 2 ![.leaf 2,.split 2 ![.leaf 4,.leaf 6]]
lemma controlA_valid : controlA.Valid 3 := by decide +kernel
lemma controlB_valid : controlB.Valid 3 := by decide +kernel
lemma control_period : ∀ i, controlB.modulus i ∣ 12 := by decide +kernel
lemma control_cross : ∀ i j, controlA.modulus i = controlB.modulus j →
    (controlA.modulus i : ℤ) ∣ controlA.residue 3 1 i-(7*controlB.residue 3 2 j+9) := by
  decide +kernel
lemma control_covers : ∀ x : ℤ, ∃ i : Label controlA controlB,
    (modulus controlA controlB i : ℤ) ∣ x-affineResidue controlA controlB 7 9 i :=
  covers controlA controlB controlA_valid controlB_valid 12 7 9 7 control_period
    (by norm_num) (by norm_num) (by norm_num)

/-- A small residue-alignment control: two classes modulo5 and25 can
align affinely even though no translation can align them. This asserts no
cover of the integers. -/
lemma alignment_control :
    (75 : ℤ) ∣ 28*67-1 ∧ (3 : ℤ) ∣ 67-1 ∧ (3 : ℤ) ∣ 45 ∧
      (5 : ℤ) ∣ 0-(28*0+45) ∧ (25 : ℤ) ∣ 1-(28*2+45) := by
  norm_num
lemma alignment_not_translation :
    ¬ ∃ c : ℤ, (5 : ℤ) ∣ 0-(0+c) ∧ (25 : ℤ) ∣ 1-(2+c) := by
  rintro ⟨c,⟨u,hu⟩,⟨v,hv⟩⟩
  omega

#print axioms alignment_control
#print axioms alignment_not_translation
#print axioms affine_fiber_covers
#print axioms odd_cover
#print axioms control_cross
#print axioms control_covers
end Erdos7AffinePairedTreeCover
