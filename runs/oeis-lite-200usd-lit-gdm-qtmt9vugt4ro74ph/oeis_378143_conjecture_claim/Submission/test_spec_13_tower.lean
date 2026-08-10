import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000
set_option maxRecDepth 200000
open Nat ZMod

def f0 {M : ℕ} (x : ZMod M) : ZMod M := x ^ 10
def f1 {M : ℕ} (x : ZMod M) : ZMod M := f0 (f0 x)
def f2 {M : ℕ} (x : ZMod M) : ZMod M := f1 (f1 x)
def f3 {M : ℕ} (x : ZMod M) : ZMod M := f2 (f2 x)
def f4 {M : ℕ} (x : ZMod M) : ZMod M := f3 (f3 x)
def f5 {M : ℕ} (x : ZMod M) : ZMod M := f4 (f4 x)
def f6 {M : ℕ} (x : ZMod M) : ZMod M := f5 (f5 x)
def f7 {M : ℕ} (x : ZMod M) : ZMod M := f6 (f6 x)
def f8 {M : ℕ} (x : ZMod M) : ZMod M := f7 (f7 x)
def f9 {M : ℕ} (x : ZMod M) : ZMod M := f8 (f8 x)
def f10 {M : ℕ} (x : ZMod M) : ZMod M := f9 (f9 x)
def f11 {M : ℕ} (x : ZMod M) : ZMod M := f10 (f10 x)
def f12 {M : ℕ} (x : ZMod M) : ZMod M := f11 (f11 x)
def f13 {M : ℕ} (x : ZMod M) : ZMod M := f12 (f12 x)

theorem f0_eq {M : ℕ} (x : ZMod M) : f0 x = x ^ (10 ^ (2 ^ 0)) := rfl

theorem f1_eq {M : ℕ} (x : ZMod M) : f1 x = x ^ (10 ^ (2 ^ 1)) := by
  change f0 (f0 x) = _
  rw [f0_eq, f0_eq, ← pow_mul]
  congr 1

theorem f2_eq {M : ℕ} (x : ZMod M) : f2 x = x ^ (10 ^ (2 ^ 2)) := by
  change f1 (f1 x) = _
  rw [f1_eq, f1_eq, ← pow_mul]
  congr 1

theorem f3_eq {M : ℕ} (x : ZMod M) : f3 x = x ^ (10 ^ (2 ^ 3)) := by
  change f2 (f2 x) = _
  rw [f2_eq, f2_eq, ← pow_mul]
  congr 1

theorem f4_eq {M : ℕ} (x : ZMod M) : f4 x = x ^ (10 ^ (2 ^ 4)) := by
  change f3 (f3 x) = _
  rw [f3_eq, f3_eq, ← pow_mul]
  congr 1

theorem f5_eq {M : ℕ} (x : ZMod M) : f5 x = x ^ (10 ^ (2 ^ 5)) := by
  change f4 (f4 x) = _
  rw [f4_eq, f4_eq, ← pow_mul]
  congr 1

theorem f6_eq {M : ℕ} (x : ZMod M) : f6 x = x ^ (10 ^ (2 ^ 6)) := by
  change f5 (f5 x) = _
  rw [f5_eq, f5_eq, ← pow_mul]
  congr 1

theorem f7_eq {M : ℕ} (x : ZMod M) : f7 x = x ^ (10 ^ (2 ^ 7)) := by
  change f6 (f6 x) = _
  rw [f6_eq, f6_eq, ← pow_mul]
  congr 1

theorem f8_eq {M : ℕ} (x : ZMod M) : f8 x = x ^ (10 ^ (2 ^ 8)) := by
  change f7 (f7 x) = _
  rw [f7_eq, f7_eq, ← pow_mul]
  congr 1

theorem f9_eq {M : ℕ} (x : ZMod M) : f9 x = x ^ (10 ^ (2 ^ 9)) := by
  change f8 (f8 x) = _
  rw [f8_eq, f8_eq, ← pow_mul]
  congr 1

theorem f10_eq {M : ℕ} (x : ZMod M) : f10 x = x ^ (10 ^ (2 ^ 10)) := by
  change f9 (f9 x) = _
  rw [f9_eq, f9_eq, ← pow_mul]
  congr 1

theorem f11_eq {M : ℕ} (x : ZMod M) : f11 x = x ^ (10 ^ (2 ^ 11)) := by
  change f10 (f10 x) = _
  rw [f10_eq, f10_eq, ← pow_mul]
  congr 1

theorem f12_eq {M : ℕ} (x : ZMod M) : f12 x = x ^ (10 ^ (2 ^ 12)) := by
  change f11 (f11 x) = _
  rw [f11_eq, f11_eq, ← pow_mul]
  congr 1

theorem f13_eq {M : ℕ} (x : ZMod M) : f13 x = x ^ (10 ^ (2 ^ 13)) := by
  change f12 (f12 x) = _
  rw [f12_eq, f12_eq, ← pow_mul]
  congr 1

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

theorem natCast_ne_zero_of_lt {M : ℕ} (hM : 3 < M) : ((3 : ℕ) : ZMod M) ≠ 0 := by
  intro h
  have h_val := congr_arg ZMod.val h
  rw [ZMod.val_natCast M 3, ZMod.val_zero] at h_val
  rw [Nat.mod_eq_of_lt hM] at h_val
  contradiction

theorem test_13 : Nat.Prime (10 ^ (2 ^ 13) + 1) → False := by
  intro hp
  have h_gt : 3 < 10 ^ (2 ^ 13) + 1 := by
    have h1 : 3 < 10 ^ 1 + 1 := by decide
    apply lt_of_lt_of_le h1
    apply Nat.add_le_add_right
    apply Nat.pow_le_pow_right (by decide)
    decide
  have ha : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ≠ 0 := natCast_ne_zero_of_lt h_gt
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
    rw [← f13_eq]
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
