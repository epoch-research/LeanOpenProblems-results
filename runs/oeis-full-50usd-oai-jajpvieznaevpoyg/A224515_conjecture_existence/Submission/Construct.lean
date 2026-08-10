import FormalConjectures.Util.ProblemImports
open Nat
set_option linter.unusedSimpArgs false

def boolNat (b : Bool) : Nat := if b then 1 else 0

def liftMask (M t : Nat) : Nat -> Bool -> Nat
| 0, b => boolNat b
| r+1, b =>
    let x := liftMask M t r b
    let nb := M.testBit (r+1) && ((t + 2^(r+1) - x)^2).testBit (r+1)
    x + boolNat nb * 2^(r+1)

lemma boolNat_lt_two (b:Bool): boolNat b < 2 := by cases b <;> simp [boolNat]

lemma liftMask_lt (M t r b) : liftMask M t r b < 2^(r+1) := by
  induction r with
  | zero => simpa [liftMask] using boolNat_lt_two b
  | succ r ih =>
      simp [liftMask]
      by_cases h : M.testBit (r+1+1) && ((t + 2 ^ (r+1+1) - liftMask M t r b) ^ 2).testBit (r+1+1)
      · simp [boolNat, h]
        have hp : 0 < 2^(r+1+1) := by positivity
        have : liftMask M t r b + 2^(r+1+1) < 2^(r+1+1) + 2^(r+1+1) := by omega
        simpa [pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.add_assoc] using this
      · simp [boolNat, h]
        have : 2^(r+1) ≤ 2^(r+1+1) := by
          exact Nat.pow_le_pow_right (by decide) (by omega)
        omega

lemma liftMask_bit_beyond (M t r b i) (hi : r+1 ≤ i) : (liftMask M t r b).testBit i = false := by
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (liftMask_lt M t r b) (Nat.pow_le_pow_right (by decide) hi))

lemma liftMask_mod_prev (M t r b) : liftMask M t (r+1) b % 2^(r+1) = liftMask M t r b := by
  simp [liftMask]
  have hx := liftMask_lt M t r b
  have hpow : (boolNat (M.testBit (r + 1) && ((t + 2 ^ (r + 1) - liftMask M t r b) ^ 2).testBit (r + 1)) * 2 ^ (r + 1)) % 2 ^ (r + 1) = 0 := by
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
  rw [Nat.add_mod, hpow, Nat.mod_eq_of_lt hx]
  simp

lemma liftMask_testBit_low {M t r b i} (hi : i < r+1) :
    (liftMask M t (r+1) b).testBit i = (liftMask M t r b).testBit i := by
  have h := congr_arg (fun x => x.testBit i) (liftMask_mod_prev M t r b)
  -- use testBit_mod_two_pow
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h
  simp [hi] at h
  exact h

lemma liftMask_testBit_top (M t r b) :
    (liftMask M t (r+1) b).testBit (r+1) =
      (M.testBit (r+1) && ((t + 2^(r+1) - liftMask M t r b)^2).testBit (r+1)) := by
  simp [liftMask]
  have hx := liftMask_lt M t r b
  have hlow : (liftMask M t r b).testBit (r+1) = false := by
    exact Nat.testBit_eq_false_of_lt hx
  by_cases h : M.testBit (r + 1) && ((t + 2 ^ (r + 1) - liftMask M t r b) ^ 2).testBit (r + 1)
  · simp [boolNat, h, hlow]
    rw [Nat.testBit_two_pow]
    simp
  · simp [boolNat, h, hlow]
