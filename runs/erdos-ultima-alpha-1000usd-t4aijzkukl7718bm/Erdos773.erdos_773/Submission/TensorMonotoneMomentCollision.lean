import FormalConjecturesUtil

/-!
A fixed nine-digit obstruction to a digit-selection criterion.  The digits
are positive and strictly increasing, and the four words have the same digit
sum and squared-digit sum.  Their squares collide at every sufficiently
large radix.  This is NOT a disproof of Erdős 773.
-/
namespace Erdos773.TensorMonotoneMomentCollision
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The tensor-product identity underlying the four words. -/
lemma tensor_identity {R : Type*} [CommRing R] (a f d g : R) :
    ((a+f)*d+(a-f)*g)^2 + ((a-f)*d-(a+f)*g)^2 =
      ((a+f)*d-(a-f)*g)^2 + ((a-f)*d+(a+f)*g)^2 := by
  ring

/-- Digits are listed from the constant coefficient upwards. -/
def digit : Fin 4 → Fin 9 → ℕ := ![
  ![10199,10912,12219,20002,21376,23962,30399,32512,36419],
  ![9799,11092,11779,20002,22616,24042,29599,33492,35579],
  ![10001,10688,11981,20398,21824,24438,30201,32288,36181],
  ![10001,11308,12021,19598,22184,23558,29801,33708,35821]]

def word (j : Fin 4) : List ℕ := List.ofFn (digit j)

def root (B : ℕ) (j : Fin 4) : ℕ := Nat.ofDigits B (word j)

lemma digit_properties : ∀ j : Fin 4,
    StrictMono (digit j) ∧ (∀ i, 0 < digit j i ∧ digit j i < 40000) ∧
      (∑ i : Fin 9, digit j i) = 198000 ∧
      (∑ i : Fin 9, digit j i ^ 2) = 5111059036 := by
  decide +kernel

lemma word_injective : Function.Injective word := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (norm_num [word, digit, List.ofFn_succ] at h)

lemma word_digits {B : ℕ} (hB : 40000 ≤ B) (j : Fin 4) :
    ∀ x ∈ word j, x < B := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact ((digit_properties j).2.1 i).2.trans_le hB

lemma root_injective {B : ℕ} (hB : 40000 ≤ B) : Function.Injective (root B) := by
  intro i j h
  apply word_injective
  exact Nat.ofDigits_inj_of_len_eq (by omega : 1 < B)
    (by simp [word]) (word_digits hB i) (word_digits hB j) h

lemma root_positive (B : ℕ) (j : Fin 4) : 0 < root B j := by
  fin_cases j <;> simp [root, word, digit, List.ofFn_succ, Nat.ofDigits_cons]

lemma root_height {B : ℕ} (hB : 40000 ≤ B) (j : Fin 4) : root B j < B^9 := by
  have h := Nat.ofDigits_lt_base_pow_length (by omega : 1 < B) (word_digits hB j)
  simpa [root, word] using h

/-- This identity is formal; in particular it holds at every natural radix. -/
lemma square_collision (B : ℕ) :
    root B 0 ^ 2 + root B 1 ^ 2 = root B 2 ^ 2 + root B 3 ^ 2 := by
  change (Nat.ofDigits B [10199,10912,12219,20002,21376,23962,30399,32512,36419])^2 +
      (Nat.ofDigits B [9799,11092,11779,20002,22616,24042,29599,33492,35579])^2 =
    (Nat.ofDigits B [10001,10688,11981,20398,21824,24438,30201,32288,36181])^2 +
      (Nat.ofDigits B [10001,11308,12021,19598,22184,23558,29801,33708,35821])^2
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
  ring

lemma square_injective {B : ℕ} (hB : 40000 ≤ B) :
    Function.Injective (fun j : Fin 4 => root B j ^ 2) := by
  intro i j h
  apply root_injective hB
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h

private lemma image_not_sidon (f : Fin 4 → ℕ) (hf : Function.Injective f)
    (he : f 0 + f 1 = f 2 + f 3) :
    ¬ IsSidon ((univ.image f) : Set ℕ) := by
  intro h
  have hm (j : Fin 4) : f j ∈ (univ.image f : Finset ℕ) :=
    mem_image.mpr ⟨j, mem_univ j, rfl⟩
  rcases h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) he with h | h
  · exact (by decide : (0 : Fin 4) ≠ 2) (hf h.1)
  · exact (by decide : (0 : Fin 4) ≠ 3) (hf h.1)

/-- The four actual square values are not Sidon at any radix at least 40000. -/
theorem not_sidon {B : ℕ} (hB : 40000 ≤ B) :
    ¬ IsSidon ((univ.image (fun j : Fin 4 => root B j ^ 2)) : Set ℕ) :=
  image_not_sidon _ (square_injective hB) (square_collision B)

/-- The example has four distinct positive roots below the stated height. -/
theorem four_roots {B : ℕ} (hB : 40000 ≤ B) :
    (univ.image (root B)).card = 4 ∧
      ∀ j : Fin 4, 0 < root B j ∧ root B j < B^9 := by
  constructor
  · rw [card_image_of_injective _ (root_injective hB)]
    simp
  · intro j
    exact ⟨root_positive B j, root_height hB j⟩

#print axioms tensor_identity
#print axioms digit_properties
#print axioms square_collision
#print axioms not_sidon
#print axioms four_roots
end Erdos773.TensorMonotoneMomentCollision
