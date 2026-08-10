import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 30000
set_option maxRecDepth 30000

open Nat ZMod

def pow10_chunk (M : ℕ) (steps : ℕ) (acc : ZMod M) : ZMod M :=
  match steps with
  | 0 => acc
  | n + 1 => pow10_chunk M n (acc ^ (10 ^ 64))

theorem pow10_chunk_eq_acc_pow (M : ℕ) (steps : ℕ) (acc : ZMod M) :
    pow10_chunk M steps acc = acc ^ ((10 ^ 64) ^ steps) := by
  induction steps generalizing acc with
  | zero => simp [pow10_chunk]
  | succ n ih =>
    rw [pow10_chunk]
    rw [ih]
    rw [← pow_mul]
    congr 1
    exact (pow_succ (10 ^ 64) n).symm

theorem lemma_13 : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
  have h : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) = pow10_chunk (10 ^ (2 ^ 13) + 1) 128 3 := by
    rw [pow10_chunk_eq_acc_pow]
    congr 1
    rw [← pow_mul]
    congr 1
    decide
  rw [h]
  decide

theorem test_13 (hp : (10 ^ (2 ^ 13) + 1).Prime) : False := by
  haveI : Fact (10 ^ (2 ^ 13) + 1).Prime := ⟨hp⟩
  have ha : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ≠ 0 := by
    intro h
    have h_cast : ((3 : ℕ) : ZMod (10 ^ (2 ^ 13) + 1)) = 0 := h
    have h_dvd : (10 ^ (2 ^ 13) + 1) ∣ 3 := by
      rwa [CharP.cast_eq_zero_iff (ZMod (10 ^ (2 ^ 13) + 1)) (10 ^ (2 ^ 13) + 1)] at h_cast
    have h_le := Nat.le_of_dvd (by decide) h_dvd
    have h_gt : 3 < 10 ^ (2 ^ 13) + 1 := by
      have h1 : 3 < 10 ^ 1 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.one_le_pow _ _ (by decide)
    omega
  have h_fermat := lemma_13
  have h_fermat_one := ZMod.pow_card_sub_one_eq_one ha
  have h_eq : (10 ^ (2 ^ 13) + 1) - 1 = 10 ^ (2 ^ 13) := by
    omega
  rw [h_eq] at h_fermat_one
  exact h_fermat h_fermat_one

