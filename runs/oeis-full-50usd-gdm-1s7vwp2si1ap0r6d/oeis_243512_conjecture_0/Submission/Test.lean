import FormalConjectures.Util.ProblemImports
open Nat ArithmeticFunction Rat
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat
noncomputable def a (n : ℕ) : ℕ := sInf {i : ℕ | 0 < i ∧ A243473_val i = n}
theorem test2 : A243473_val 120 = 2 := by
  unfold A243473_val
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  have h : sigma 1 120 = 360 := rfl
  rw [h]
  norm_num; rfl

lemma nonempty_2 : {i : ℕ | 0 < i ∧ A243473_val i = 2}.Nonempty := ⟨120, by decide, test2⟩

theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := answer(sorry)
#print axioms oeis_243512_conjecture_0
#print Nat.sInf
#check Nat.sInf_empty
#check Nat.sInf_mem

