import Submission.BalancedTernaryBasics

/-! Exact balanced-ternary carry arithmetic for n ↦ 4n+1. No separating
barrier is constructed, and no finiteness assertion is made here. -/
namespace Erdos406Balanced

def outDigit (d : ℕ) (c : ℤ) : ℕ := ((4*((d : ℤ)-1)+c+1)%3).toNat

def nextCarry (d : ℕ) (c : ℤ) : ℤ := (4*((d : ℤ)-1)+c+1)/3

lemma outDigit_lt (d : ℕ) (c : ℤ) : outDigit d c < 3 := by
  have hn := Int.emod_nonneg (4*((d : ℤ)-1)+c+1) (by decide : (3 : ℤ) ≠ 0)
  have hl := Int.emod_lt_of_pos (4*((d : ℤ)-1)+c+1) (by decide : (0 : ℤ) < 3)
  dsimp [outDigit]
  omega

lemma carry_equation (d : ℕ) (c : ℤ) :
    4*((d : ℤ)-1)+c = (outDigit d c : ℤ)-1+3*nextCarry d c := by
  have hn := Int.emod_nonneg (4*((d : ℤ)-1)+c+1) (by decide : (3 : ℤ) ≠ 0)
  dsimp [outDigit,nextCarry]
  omega

lemma nextCarry_bounds {d : ℕ} {c : ℤ} (hd : d < 3) (hc : -2 ≤ c ∧ c ≤ 2) :
    -2 ≤ nextCarry d c ∧ nextCarry d c ≤ 2 := by
  dsimp [nextCarry]
  omega

lemma nextCarry_two {c : ℤ} (hc : -2 ≤ c ∧ c ≤ 2) :
    nextCarry 2 c = 1 ∨ nextCarry 2 c = 2 := by
  dsimp [nextCarry]
  omega

/-- Process a word, returning an output word of the same length and the final
carry. Any remaining positive carry is appended after the input word ends. -/
def transfer (c : ℤ) : List ℕ → List ℕ × ℤ
  | [] => ([],c)
  | d::w =>
    let r := transfer (nextCarry d c) w
    (outDigit d c :: r.1,r.2)

lemma transfer_length (c : ℤ) (w : List ℕ) : (transfer c w).1.length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons d w ih => simp only [transfer,List.length_cons,ih]

lemma transfer_valid (c : ℤ) (w : List ℕ) : Valid (transfer c w).1 := by
  induction w generalizing c with
  | nil => simp [transfer,Valid]
  | cons d w ih =>
    intro e he
    simp only [transfer,List.mem_cons] at he
    rcases he with rfl | he
    · exact outDigit_lt d c
    · exact ih _ _ he

lemma transfer_carry_bounds {c : ℤ} {w : List ℕ}
    (hc : -2 ≤ c ∧ c ≤ 2) (hw : Valid w) :
    -2 ≤ (transfer c w).2 ∧ (transfer c w).2 ≤ 2 := by
  induction w generalizing c with
  | nil => exact hc
  | cons d w ih =>
    exact ih (nextCarry_bounds (hw d (by simp)) hc) (valid_tail hw)

lemma transfer_final_carry {c : ℤ} {w : List ℕ}
    (hc : -2 ≤ c ∧ c ≤ 2) (hw : Valid w) (hlast : w.getLast? = some 2) :
    (transfer c w).2 = 1 ∨ (transfer c w).2 = 2 := by
  induction w generalizing c with
  | nil => simp at hlast
  | cons d w ih =>
    cases w with
    | nil =>
      have hd : d = 2 := by simpa using hlast
      simpa only [transfer,hd] using nextCarry_two hc
    | cons e w =>
      exact ih (nextCarry_bounds (hw d (by simp)) hc) (valid_tail hw)
        (by simpa only [List.getLast?_cons_cons] using hlast)

lemma transfer_value (c : ℤ) (w : List ℕ) :
    4*value w+c = value (transfer c w).1 +
      (3 : ℤ)^w.length * (transfer c w).2 := by
  induction w generalizing c with
  | nil => simp [value,transfer]
  | cons d w ih =>
    have hh := ih (nextCarry d c)
    have he := carry_equation d c
    simp only [transfer,value,List.length_cons,pow_succ]
    nlinarith

lemma transfer_digits_final_carry (n : ℕ) :
    (transfer 1 (digits n)).2 = 1 ∨ (transfer 1 (digits n)).2 = 2 := by
  by_cases hn : n = 0
  · simp [hn,transfer]
  · exact transfer_final_carry (by norm_num) (digits_lt_three n) (digits_last n (by omega))

/-- The finite carry computation, including the final carry flush, produces
exactly the canonical balanced digits of the positive affine image. -/
theorem affine_digits (n : ℕ) :
    digits (4*n+1) = (transfer 1 (digits n)).1 ++
      digits ((transfer 1 (digits n)).2.toNat) := by
  let r := transfer 1 (digits n)
  have hr : r.2 = 1 ∨ r.2 = 2 := transfer_digits_final_carry n
  have hrpos : 0 < r.2.toNat := by omega
  symm
  apply digits_unique (4*n+1)
  · intro d hd
    simp only [List.mem_append] at hd
    rcases hd with hd | hd
    · exact transfer_valid 1 (digits n) d hd
    · exact digits_lt_three _ d hd
  · right
    rw [List.getLast?_append,digits_last _ hrpos]
    rfl
  · rw [value_append,value_digits,transfer_length]
    have hh := transfer_value 1 (digits n)
    rw [value_digits] at hh
    have hc : ((r.2.toNat : ℕ) : ℤ) = r.2 := by omega
    change value r.1 + (3 : ℤ)^(digits n).length * ↑r.2.toNat = ↑(4*n+1)
    rw [hc]
    push_cast
    exact hh.symm

#print axioms transfer_value
#print axioms affine_digits
end Erdos406Balanced
