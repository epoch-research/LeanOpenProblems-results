import FormalConjectures.Util.ProblemImports

def R (n : ℕ) := ZMod n × ZMod n

namespace R

variable {n : ℕ}

@[ext] theorem ext (x y : R n) (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x; cases y; simp_all

def add (x y : R n) : R n := (x.1 + y.1, x.2 + y.2)
def sub (x y : R n) : R n := (x.1 - y.1, x.2 - y.2)
def mul (x y : R n) : R n := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def zero : R n := (0, 0)
def one : R n := (1, 0)

def pow (x : R n) : ℕ → R n
  | 0 => one
  | k + 1 => mul (pow x k) x

@[simp] theorem mul_one (x : R n) : mul x one = x := by
  ext <;> simp [mul, one]

@[simp] theorem one_mul (x : R n) : mul one x = x := by
  ext <;> simp [mul, one]

theorem mul_assoc (x y z : R n) : mul (mul x y) z = mul x (mul y z) := by
  ext <;> simp [mul] <;> ring

theorem mul_comm (x y : R n) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

theorem pow_add (x : R n) (a b : ℕ) : pow x (a + b) = mul (pow x a) (pow x b) := by
  induction b with
  | zero => simp [pow, mul_one]
  | succ b ih =>
    calc pow x (a + b + 1) = mul (pow x (a + b)) x := rfl
      _ = mul (mul (pow x a) (pow x b)) x := by rw [ih]
      _ = mul (pow x a) (mul (pow x b) x) := mul_assoc _ _ _
      _ = mul (pow x a) (pow x (b + 1)) := rfl

def cast {n p : ℕ} [NeZero p] (h : p ∣ n) (x : R n) : R p :=
  (ZMod.castHom h (ZMod p) x.1, ZMod.castHom h (ZMod p) x.2)

@[simp] theorem cast_mul {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (x y : R n) :
    cast h (mul x y) = mul (cast h x) (cast h y) := by
  ext
  · simp only [cast, mul, map_add, map_mul]
    have h3 : ZMod.castHom h (ZMod p) 3 = 3 := by
      show ZMod.castHom h (ZMod p) (3 : ℕ) = (3 : ℕ)
      rw [map_natCast]
    rw [h3]
  · simp only [cast, mul, map_add, map_mul]

@[simp] theorem cast_one {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) :
    cast h (one : R n) = (one : R p) := by
  ext <;> simp [cast, one, map_one, map_zero]

@[simp] theorem cast_zero {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) :
    cast h (zero : R n) = (zero : R p) := by
  ext <;> simp [cast, zero, map_zero]

theorem cast_pow {n p : ℕ} [NeZero n] [NeZero p] (h : p ∣ n) (x : R n) (k : ℕ) :
    cast h (pow x k) = pow (cast h x) k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih]

end R
