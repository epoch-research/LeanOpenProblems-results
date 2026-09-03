import FormalConjecturesUtil

/-!
A counterexample to the blanket fixed-end, exact-inversion-count criterion
for full-alphabet digit permutations. This is not a disproof of Erdős 773.
-/
namespace Erdos773.ExactInversionCarryObstacle
open Finset
set_option maxHeartbeats 1000000

/-- Digits from the constant to the leading position. -/
def word : Fin 4 → Fin 9 → Fin 9 := ![
  ![5,2,6,8,3,7,4,0,1],
  ![5,8,2,3,7,4,0,6,1],
  ![5,2,6,8,4,7,0,3,1],
  ![5,8,2,3,6,7,0,4,1]]

/-- Usual inversion count when read from the leading digit. -/
def inversions (f : Fin 9 → Fin 9) : ℕ :=
  ((univ : Finset (Fin 9 × Fin 9)).filter (fun p => p.1 < p.2 ∧ f p.1 < f p.2)).card

def evalWord (B : ℕ) (i : Fin 4) : ℕ := ∑ j : Fin 9, (word i j).val*B^j.val

theorem all_digits_once : ∀ i : Fin 4, Function.Bijective (word i) := by
  decide +kernel

theorem fixed_ends : ∀ i : Fin 4, word i 0 = 5 ∧ word i 8 = 1 := by
  decide +kernel

theorem exact_inversions : ∀ i : Fin 4, inversions (word i) = 13 := by
  decide +kernel

def root (B : ℤ) : Fin 4 → ℤ := ![
  B^8+4*B^6+7*B^5+3*B^4+8*B^3+6*B^2+2*B+5,
  B^8+6*B^7+4*B^5+7*B^4+3*B^3+2*B^2+8*B+5,
  B^8+3*B^7+7*B^5+4*B^4+8*B^3+6*B^2+2*B+5,
  B^8+4*B^7+7*B^5+6*B^4+3*B^3+2*B^2+8*B+5]

lemma eval_eq_root (B : ℕ) (i : Fin 4) : (evalWord B i : ℤ) = root B i := by
  fin_cases i <;> simp [evalWord,word,root,Fin.sum_univ_succ] <;> ring

/-- The nonzero formal norm difference vanishes on specialization to base nine. -/
theorem norm_difference (B : ℤ) :
    root B 0^2+root B 1^2-root B 2^2-root B 3^2 =
      -B^5*(B-9)*(B-1)*(2*B^8+B^7-2*B^6+5*B^5+6*B^2+4*B+2) := by
  simp [root]
  ring

theorem values :
    evalWord 9 0 = 45611852 ∧ evalWord 9 1 = 72029084 ∧
    evalWord 9 2 = 57841556 ∧ evalWord 9 3 = 62633732 := by
  decide +kernel

theorem collision :
    (evalWord 9 0)^2+(evalWord 9 1)^2 =
      (evalWord 9 2)^2+(evalWord 9 3)^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := values
  rw [h0,h1,h2,h3]
  norm_num

theorem not_sidon :
    ¬ IsSidon (((univ : Finset (Fin 4)).image (fun i => (evalWord 9 i)^2) : Finset ℕ) : Set ℕ) := by
  decide +kernel

/-- This particular exact-inversion class is not square-Sidon. -/
theorem full_alphabet_family_not_sidon :
    ¬ IsSidon {n : ℕ | ∃ f : Fin 9 → Fin 9, Function.Bijective f ∧
      f 0 = 5 ∧ f 8 = 1 ∧ inversions f = 13 ∧
      n = (∑ j : Fin 9, (f j).val*9^j.val)^2} := by
  intro h
  apply not_sidon
  apply Set.IsSidon.subset h
  intro n hn
  obtain ⟨i,hi,rfl⟩ := mem_image.mp (Finset.mem_coe.mp hn)
  exact ⟨word i,all_digits_once i,(fixed_ends i).1,(fixed_ends i).2,exact_inversions i,rfl⟩

#print axioms all_digits_once
#print axioms fixed_ends
#print axioms exact_inversions
#print axioms norm_difference
#print axioms values
#print axioms collision
#print axioms not_sidon
#print axioms full_alphabet_family_not_sidon
end Erdos773.ExactInversionCarryObstacle
