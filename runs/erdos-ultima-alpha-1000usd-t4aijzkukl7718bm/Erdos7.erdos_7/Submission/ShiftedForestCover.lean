import Submission.SharedTreeCover

/-! A conditional certificate for congruence-class trees with independently
shifted starting residues. No odd covering witness is asserted here. -/
namespace Erdos7ShiftedForestCover
open Erdos7SplittingTreeCover Erdos7SharedTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Label {q : ℕ} (T : Fin q → Tree) := (r : Fin q) × (T r).Leaf

def modulus {q : ℕ} (T : Fin q → Tree) (i : Label T) : ℕ :=
  (T i.1).modulus i.2

def residue {q : ℕ} (T : Fin q → Tree) (b : Fin q → ℤ)
    (i : Label T) : ℤ := (T i.1).residue q (b i.1) i.2

theorem covers {q : ℕ} (hq : 0 < q) (T : Fin q → Tree)
    (hv : ∀ r, (T r).Valid q) (b : Fin q → ℤ)
    (hb : ∀ r, (q : ℤ) ∣ b r - r.val) :
    ∀ x : ℤ, ∃ i : Label T, (modulus T i : ℤ) ∣ x - residue T b i := by
  intro x
  obtain ⟨r, hr⟩ := Erdos7DivisorRepair.split_class 1 q hq 0 x (by simp)
  have hr' : (q : ℤ) ∣ x - (r.val : ℤ) := by simpa using hr
  have hx : (q : ℤ) ∣ x - b r := by
    have h := dvd_sub hr' (hb r)
    convert h using 1 <;> ring
  obtain ⟨i, hi⟩ := (T r).covers q (b r) (hv r) x hx
  exact ⟨⟨r, i⟩, hi⟩

theorem odd_cover {q : ℕ} (hq : 0 < q) (T : Fin q → Tree)
    (hv : ∀ r, (T r).Valid q) (b : Fin q → ℤ)
    (hb : ∀ r, (q : ℤ) ∣ b r - r.val)
    (ho : ∀ i : Label T, Odd (modulus T i))
    (hc : ∀ i j : Label T, modulus T i = modulus T j →
      (modulus T i : ℤ) ∣ residue T b i - residue T b j) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  apply deduplicate (modulus T) (residue T b) ?_ hc (covers hq T hv b hb)
  intro i
  exact ⟨(T i.1).nontrivial q (hv i.1) i.2, ho i⟩

#print axioms covers
#print axioms odd_cover
end Erdos7ShiftedForestCover
