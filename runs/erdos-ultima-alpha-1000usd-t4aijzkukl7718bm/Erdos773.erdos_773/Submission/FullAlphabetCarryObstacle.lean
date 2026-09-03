import FormalConjecturesUtil

/-!
A finite obstruction to treating all full-alphabet permutation words as a
square-Sidon set. This does not exclude a large Sidon subclass, and is not a
disproof of the asymptotic conjecture in Spec.lean.
-/
namespace Erdos773.FullAlphabetCarryObstacle
open Finset
set_option maxHeartbeats 1000000

/-- Digits are listed from the constant digit to the leading digit. -/
def word : Fin 4 → Fin 8 → Fin 8 := ![
  ![3,5,7,2,6,4,0,1],
  ![3,6,4,2,7,0,5,1],
  ![3,4,7,6,2,5,0,1],
  ![3,7,6,2,4,0,5,1]]

def evalWord (B : ℕ) (i : Fin 4) : ℕ := ∑ j : Fin 8, (word i j).val*B^j.val

/-- Each word uses the entire alphabet exactly once. -/
theorem all_digits_once : ∀ i : Fin 4, Function.Bijective (word i) := by
  decide +kernel

/-- The constant and leading digits are fixed, not merely permuted. -/
theorem fixed_ends : ∀ i : Fin 4, word i 0 = 3 ∧ word i 7 = 1 := by
  decide +kernel

def root (B : ℤ) : Fin 4 → ℤ := ![
  B^7+4*B^5+6*B^4+2*B^3+7*B^2+5*B+3,
  B^7+5*B^6+7*B^4+2*B^3+4*B^2+6*B+3,
  B^7+5*B^5+2*B^4+6*B^3+7*B^2+4*B+3,
  B^7+5*B^6+4*B^4+2*B^3+6*B^2+7*B+3]

lemma eval_eq_root (B : ℕ) (i : Fin 4) : (evalWord B i : ℤ) = root B i := by
  fin_cases i <;> simp [evalWord,word,root,Fin.sum_univ_succ] <;> ring

/-- The norm difference is nonzero formally, but has a factor X-8. -/
theorem norm_difference (B : ℤ) :
    root B 0^2+root B 1^2-root B 2^2-root B 3^2 =
      -B^2*(B-8)*(B-1)*
        (2*B^8+4*B^7+7*B^6+7*B^5+6*B^4+10*B^3+10*B^2+8*B+2) := by
  simp [root]
  ring

theorem values :
    evalWord 8 0 = 2254315 ∧ evalWord 8 1 = 3437875 ∧
    evalWord 8 2 = 2272739 ∧ evalWord 8 3 = 3425723 := by
  decide +kernel

theorem collision :
    (evalWord 8 0)^2+(evalWord 8 1)^2 =
      (evalWord 8 2)^2+(evalWord 8 3)^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := values
  rw [h0,h1,h2,h3]
  norm_num

/-- The four displayed values already obstruct the blanket criterion. -/
theorem not_sidon :
    ¬ IsSidon (((univ : Finset (Fin 4)).image (fun i => (evalWord 8 i)^2) : Finset ℕ) : Set ℕ) := by
  decide +kernel

/-- All base-eight full-alphabet words with leading digit 1 and constant
digit 3 do not form a square-Sidon set. No conclusion is drawn about
special subfamilies or other alphabets. -/
theorem full_alphabet_family_not_sidon :
    ¬ IsSidon {n : ℕ | ∃ f : Fin 8 → Fin 8, Function.Bijective f ∧
      f 0 = 3 ∧ f 7 = 1 ∧ n = (∑ j : Fin 8, (f j).val*8^j.val)^2} := by
  intro h
  apply not_sidon
  apply Set.IsSidon.subset h
  intro n hn
  obtain ⟨i,hi,rfl⟩ := mem_image.mp (Finset.mem_coe.mp hn)
  exact ⟨word i,all_digits_once i,(fixed_ends i).1,(fixed_ends i).2,rfl⟩

#print axioms all_digits_once
#print axioms fixed_ends
#print axioms norm_difference
#print axioms values
#print axioms collision
#print axioms not_sidon
#print axioms full_alphabet_family_not_sidon
end Erdos773.FullAlphabetCarryObstacle
