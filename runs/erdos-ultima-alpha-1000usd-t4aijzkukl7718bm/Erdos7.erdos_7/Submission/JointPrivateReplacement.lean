import Submission.PrivateReplacement

/-!
# Simultaneous private-point replacements

The exact protected region includes points covered jointly by changed classes.
A pairwise-disjoint changed family permits a simpler private-point criterion.
These are replacement criteria, not a settlement of the odd covering problem.
-/

namespace Erdos7JointPrivateReplacement
open Erdos7PrivateReplacement

def patched {I A : Type*} [DecidableEq I] (s : Finset I) (f g : I → A) (i : I) : A :=
  if i ∈ s then g i else f i

/-- Points covered by the old family and by none of its unchanged classes. -/
def Exclusive {I : Type*} (s : Finset I) (m : I → ℕ) (a : I → ℤ) (x : ℤ) : Prop :=
  (∃ i ∈ s, (m i : ℤ) ∣ x-a i) ∧
    ∀ j, j ∉ s → ¬ (m j : ℤ) ∣ x-a j

/-- The exact simultaneous replacement criterion. -/
theorem union_inclusion_iff {I : Type*} [DecidableEq I] (s : Finset I)
    (m n : I → ℕ) (a b : I → ℤ) :
    (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) →
      ∃ i, ((patched s m n i : ℕ) : ℤ) ∣ x-patched s a b i) ↔
    (∀ x : ℤ, Exclusive s m a x → ∃ i ∈ s, (n i : ℤ) ∣ x-b i) := by
  classical
  constructor
  · intro h x hx
    obtain ⟨i,hi⟩ := h x (by obtain ⟨i,_,hi⟩ := hx.1; exact ⟨i,hi⟩)
    by_cases his : i ∈ s
    · exact ⟨i,his,by simpa [patched,his] using hi⟩
    · exact False.elim (hx.2 i his (by simpa [patched,his] using hi))
  · intro h x hx
    by_cases ho : ∃ j, j ∉ s ∧ (m j : ℤ) ∣ x-a j
    · obtain ⟨j,hjs,hj⟩ := ho
      exact ⟨j,by simpa [patched,hjs] using hj⟩
    · have he : Exclusive s m a x := by
        refine ⟨?_,fun j hjs hj => ho ⟨j,hjs,hj⟩⟩
        obtain ⟨i,hi⟩ := hx
        have his : i ∈ s := by
          by_contra hn
          exact ho ⟨i,hn,hi⟩
        exact ⟨i,his,hi⟩
      obtain ⟨i,his,hi⟩ := h x he
      exact ⟨i,by simpa [patched,his] using hi⟩

/-- Original private points suffice if no point belongs to two changed classes. -/
theorem disjoint_private_replacement {I : Type*} [DecidableEq I] (s : Finset I)
    (m n : I → ℕ) (a b : I → ℤ)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x : ℤ,
      (m i : ℤ) ∣ x-a i → ¬ (m j : ℤ) ∣ x-a j)
    (hprivate : ∀ i ∈ s, ∀ x, Private m a i x → (n i : ℤ) ∣ x-b i) :
    ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) →
      ∃ i, ((patched s m n i : ℕ) : ℤ) ∣ x-patched s a b i := by
  apply (union_inclusion_iff s m n a b).mpr
  intro x hx
  obtain ⟨i,his,hi⟩ := hx.1
  refine ⟨i,his,hprivate i his x ⟨hi,?_⟩⟩
  intro j hji hj
  by_cases hjs : j ∈ s
  · exact hdis i his j hjs hji.symm x hi hj
  · exact hx.2 j hjs hj

section Control

def modulus : Fin 9 → ℕ := ![3,5,7,9,15,21,35,63,105]
def residue : Fin 9 → ℤ := ![0,0,0,7,4,2,22,1,1]
def point : Fin 9 → ℤ := ![3,5,14,16,4,2,22,253,211]
def changed : Finset (Fin 9) := {7,8}
def newModulus : Fin 9 → ℕ := ![3,5,7,9,15,21,35,45,315]
def newResidue : Fin 9 → ℤ := ![0,0,0,7,4,2,22,253,211]

lemma control_data : Function.Injective modulus ∧ Function.Injective newModulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 315) ∧
    (∀ i, 1 < newModulus i ∧ Odd (newModulus i) ∧ newModulus i ∣ 315) ∧
    (∀ i, Private modulus residue i (point i)) := by
  unfold Private
  decide +kernel

lemma control_divisors : ∀ i, ∀ d ∈ (modulus i).divisors,
    1 < d → ∃ j, modulus j = d := by
  decide +kernel

lemma private_seven (x : ℤ) (hx : Private modulus residue 7 x) :
    (315 : ℤ) ∣ x-253 := by
  have h63 := hx.1
  have h105 := hx.2 8 (by decide)
  have h15 := hx.2 4 (by decide)
  have h35 := hx.2 6 (by decide)
  have h5 := hx.2 1 (by decide)
  change (63 : ℤ) ∣ x-1 at h63
  change ¬ (105 : ℤ) ∣ x-1 at h105
  change ¬ (15 : ℤ) ∣ x-4 at h15
  change ¬ (35 : ℤ) ∣ x-22 at h35
  change ¬ (5 : ℤ) ∣ x-0 at h5
  simp only [sub_zero] at h5
  obtain ⟨k,hk⟩ := h63
  have h5' := Int.emod_add_mul_ediv k 5
  have hres : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hres with h | h | h | h | h
  · exact False.elim (h105 ⟨3*(k/5),by omega⟩)
  · exact False.elim (h15 ⟨21*(k/5)+4,by omega⟩)
  · exact False.elim (h35 ⟨9*(k/5)+3,by omega⟩)
  · exact False.elim (h5 ⟨63*(k/5)+38,by omega⟩)
  · exact ⟨k/5,by omega⟩

lemma private_eight (x : ℤ) (hx : Private modulus residue 8 x) :
    (315 : ℤ) ∣ x-211 := by
  have h105 := hx.1
  have h63 := hx.2 7 (by decide)
  have h9 := hx.2 3 (by decide)
  change (105 : ℤ) ∣ x-1 at h105
  change ¬ (63 : ℤ) ∣ x-1 at h63
  change ¬ (9 : ℤ) ∣ x-7 at h9
  obtain ⟨k,hk⟩ := h105
  have h3 := Int.emod_add_mul_ediv k 3
  have hres : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hres with h | h | h
  · exact False.elim (h63 ⟨5*(k/3),by omega⟩)
  · exact False.elim (h9 ⟨35*(k/3)+11,by omega⟩)
  · exact ⟨k/3,by omega⟩

/-- Every original private point of every changed class survives its own replacement. -/
lemma all_private_retained : ∀ i ∈ changed, ∀ x : ℤ,
    Private modulus residue i x → (newModulus i : ℤ) ∣ x-newResidue i := by
  intro i hi x hx
  simp only [changed,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact (show (45 : ℤ) ∣ 315 by norm_num).trans (private_seven x hx)
  · exact private_eight x hx

lemma patch_eq : patched changed modulus newModulus = newModulus ∧
    patched changed residue newResidue = newResidue := by
  decide +kernel

lemma lost_point : (∃ i, (modulus i : ℤ) ∣ (1 : ℤ)-residue i) ∧
    (∀ i, ¬ (newModulus i : ℤ) ∣ (1 : ℤ)-newResidue i) := by
  decide +kernel

/-- Thus the simultaneous union inclusion fails despite all original private
points being retained. The original family is partial, not an odd cover. -/
theorem private_retention_not_sufficient :
    ¬ (∀ x : ℤ, (∃ i, (modulus i : ℤ) ∣ x-residue i) →
      ∃ i, ((patched changed modulus newModulus i : ℕ) : ℤ) ∣
        x-patched changed residue newResidue i) := by
  intro h
  obtain ⟨i,hi⟩ := h 1 lost_point.1
  rw [patch_eq.1,patch_eq.2] at hi
  exact lost_point.2 i hi

lemma original_hole : ∀ i, ¬ (modulus i : ℤ) ∣ (8 : ℤ)-residue i := by
  decide +kernel

end Control

#print axioms union_inclusion_iff
#print axioms disjoint_private_replacement
#print axioms control_data
#print axioms control_divisors
#print axioms private_seven
#print axioms private_eight
#print axioms all_private_retained
#print axioms private_retention_not_sufficient
#print axioms original_hole
end Erdos7JointPrivateReplacement
