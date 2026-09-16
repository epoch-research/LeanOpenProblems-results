import FormalConjectures.Util.ProblemImports
import Submission.TestPrimality5

set_option exponentiation.threshold 1000000

namespace R

def cube {n} (x : R n) : R n := mul (mul x x) x

@[simp] theorem cube_eq_pow {n} (x : R n) : cube x = pow x 3 := by
  ext <;> simp [cube, pow]

def cube_pow {n} (x : R n) : ℕ → R n
  | 0 => x
  | k + 1 => cube (cube_pow x k)

theorem cube_pow_eq_pow {n} (x : R n) (k : ℕ) : cube_pow x k = pow x (3^k) := by
  induction k with
  | zero => simp [cube_pow, pow]
  | succ k ih =>
    rw [cube_pow, ih, cube_eq_pow]
    have h1 : 3 ^ (k + 1) = 3 ^ k * 3 := rfl
    rw [h1, pow_mul]

theorem cube_pow_add {n} (x : R n) (a b : ℕ) : cube_pow x (a + b) = cube_pow (cube_pow x a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : a + (b + 1) = a + b + 1 := by omega
    rw [h1]
    have h2 : cube_pow x (a + b + 1) = cube (cube_pow x (a + b)) := rfl
    rw [h2, ih]
    rfl

theorem cube_pow_congr {n} (x : R n) {a b : ℕ} (h : a = b) : cube_pow x a = cube_pow x b := by rw [h]

def c1 {n} (x : R n) := cube_pow x 10
def c2 {n} (x : R n) := c1 <| c1 <| c1 <| c1 <| c1 <| c1 <| c1 <| c1 <| c1 <| c1 x
def c3 {n} (x : R n) := c2 <| c2 <| c2 <| c2 <| c2 <| c2 <| c2 <| c2 <| c2 <| c2 x
def c4 {n} (x : R n) := c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 x

theorem c1_eq {n} (x : R n) : c1 x = cube_pow x 10 := rfl

theorem c2_eq {n} (x : R n) : c2 x = cube_pow x 100 := by
  dsimp [c2, c1]
  rw [←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add]

theorem c3_eq {n} (x : R n) : c3 x = cube_pow x 1000 := by
  dsimp [c3]
  simp only [c2_eq]
  rw [←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add]

theorem c4_eq {n} (x : R n) : c4 x = cube_pow x 10000 := by
  dsimp [c4]
  simp only [c3_eq]
  rw [←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add]

def do_39100 {n} (x : R n) : R n :=
  let x1 := c4 <| c4 <| c4 x
  let x2 := c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 <| c3 x1
  c2 x2

def do_39101 {n} (x : R n) : R n := cube (do_39100 x)

theorem do_39100_eq {n} (x : R n) : do_39100 x = cube_pow x 39100 := by
  dsimp [do_39100]
  simp only [c4_eq, c3_eq, c2_eq]
  rw [←cube_pow_add, ←cube_pow_add]
  rw [←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add, ←cube_pow_add]
  rw [←cube_pow_add]

theorem do_39101_eq {n} (x : R n) : do_39101 x = cube_pow x 39101 := by
  dsimp [do_39101]
  rw [do_39100_eq]
  rfl

variable {m : ℕ} (x : R (2 * 100943 * 3^m - 1))

def y_M2 : R (2 * 100943 * 3^m - 1) := pow x 100943
def y_M3 : R (2 * 100943 * 3^m - 1) := pow x (2 * 100943)
def y_Mp : R (2 * 100943 * 3^m - 1) := pow x 2

def val_M2 : R (2 * 100943 * 3^m - 1) := do_39101 (y_M2 x)
def val_M3 : R (2 * 100943 * 3^m - 1) := do_39100 (y_M3 x)
def val_Mp : R (2 * 100943 * 3^m - 1) := do_39101 (y_Mp x)
def val_M : R (2 * 100943 * 3^m - 1) := do_39101 (y_M3 x)

theorem val_M_eq : val_M x = pow x (2 * 100943 * 3^39101) := by
  dsimp [val_M, y_M3]
  rw [do_39101_eq, cube_pow_eq_pow, ←pow_mul]
  rfl

theorem val_M2_eq : val_M2 x = pow x (100943 * 3^39101) := by
  dsimp [val_M2, y_M2]
  rw [do_39101_eq, cube_pow_eq_pow, ←pow_mul]
  rfl

theorem val_M3_eq : val_M3 x = pow x (2 * 100943 * 3^39100) := by
  dsimp [val_M3, y_M3]
  rw [do_39100_eq, cube_pow_eq_pow, ←pow_mul]
  have : 2 * 100943 * 3 ^ 39100 = 2 * 100943 * 3 ^ 39100 := rfl
  rfl

theorem val_Mp_eq : val_Mp x = pow x (2 * 3^39101) := by
  dsimp [val_Mp, y_Mp]
  rw [do_39101_eq, cube_pow_eq_pow, ←pow_mul]
  have : 2 * 3 ^ 39101 = 2 * 3 ^ 39101 := rfl
  rfl

end R
