import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

def N : ℕ := 2 * 100943 * 3 ^ 39101 - 1

instance : NeZero N := ⟨by decide⟩
instance : Fact (1 < N) := ⟨by decide⟩


structure LucasRing (N_val : ℕ) (D_val : ZMod N_val) where
  re : ZMod N_val
  im : ZMod N_val
deriving DecidableEq

namespace LucasRing

variable {N_val : ℕ} {D_val : ZMod N_val}

def zero : LucasRing N_val D_val := ⟨0, 0⟩
def one : LucasRing N_val D_val := ⟨1, 0⟩

def add (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨-x.re, -x.im⟩
def mul (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re * y.re + D_val * x.im * y.im, x.re * y.im + x.im * y.re⟩
def sub (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re - y.re, x.im - y.im⟩

instance : Zero (LucasRing N_val D_val) := ⟨zero⟩
instance : One (LucasRing N_val D_val) := ⟨one⟩
instance : Add (LucasRing N_val D_val) := ⟨add⟩
instance : Neg (LucasRing N_val D_val) := ⟨neg⟩
instance : Mul (LucasRing N_val D_val) := ⟨mul⟩
instance : Sub (LucasRing N_val D_val) := ⟨sub⟩

@[simp] lemma add_re (x y : LucasRing N_val D_val) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : LucasRing N_val D_val) : (x + y).im = x.im + y.im := rfl
@[simp] lemma neg_re (x : LucasRing N_val D_val) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : LucasRing N_val D_val) : (-x).im = -x.im := rfl
@[simp] lemma mul_re (x y : LucasRing N_val D_val) : (x * y).re = x.re * y.re + D_val * x.im * y.im := rfl
@[simp] lemma mul_im (x y : LucasRing N_val D_val) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] lemma zero_re : (0 : LucasRing N_val D_val).re = 0 := rfl
@[simp] lemma zero_im : (0 : LucasRing N_val D_val).im = 0 := rfl
@[simp] lemma one_re : (1 : LucasRing N_val D_val).re = 1 := rfl
@[simp] lemma one_im : (1 : LucasRing N_val D_val).im = 0 := rfl
@[simp] lemma sub_re (x y : LucasRing N_val D_val) : (x - y).re = x.re - y.re := rfl
@[simp] lemma sub_im (x y : LucasRing N_val D_val) : (x - y).im = x.im - y.im := rfl

@[ext]
lemma ext {x y : LucasRing N_val D_val} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

end LucasRing

lemma nat_cast_mod_mul (p k a : ℕ) : ((a % (p * k) : ℕ) : ZMod p) = (a : ZMod p) := by
  have h_div := Nat.div_add_mod a (p * k)
  rw [← h_div]
  push_cast
  have h_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [h_zero]
  simp

lemma cast_zmod_mul (p : ℕ) (hp : p ∣ N) (x y : ZMod N) :
    ( (x * y).val : ZMod p ) = (x.val : ZMod p) * (y.val : ZMod p) := by
  have h_eq : (x * y).val = (x.val * y.val) % N := ZMod.val_mul x y
  rcases hp with ⟨k, hk⟩
  have hk_eq : N = p * k := by
    rw [hk]
    try ring
  set a := x.val
  set b := y.val
  have h_mod : a * b % N = a * b % (p * k) := by
    rw [hk_eq]
  rw [h_eq]
  change ( (a * b % N : ℕ) : ZMod p ) = (a : ZMod p) * (b : ZMod p)
  rw [h_mod]
  rw [nat_cast_mod_mul p k (a * b)]
  push_cast
  rfl

lemma cast_zmod_add (p : ℕ) (hp : p ∣ N) (x y : ZMod N) :
    ( (x + y).val : ZMod p ) = (x.val : ZMod p) + (y.val : ZMod p) := by
  have h_eq : (x + y).val = (x.val + y.val) % N := ZMod.val_add x y
  rcases hp with ⟨k, hk⟩
  have hk_eq : N = p * k := by
    rw [hk]
    try ring
  set a := x.val
  set b := y.val
  have h_mod : (a + b) % N = (a + b) % (p * k) := by
    rw [hk_eq]
  rw [h_eq]
  change ( ((a + b) % N : ℕ) : ZMod p ) = (a : ZMod p) + (b : ZMod p)
  rw [h_mod]
  rw [nat_cast_mod_mul p k (a + b)]
  push_cast
  rfl

def phi (p : ℕ) (x : LucasRing N 5) : LucasRing p 5 :=
  ⟨(x.re.val : ZMod p), (x.im.val : ZMod p)⟩

lemma phi_mul (p : ℕ) (hp : p ∣ N) (x y : LucasRing N 5) :
    phi p (x * y) = phi p x * phi p y := by
  unfold phi
  apply LucasRing.ext
  · simp only [LucasRing.mul_re, LucasRing.mul_im]
    have h_add1 := cast_zmod_add p hp (x.re * y.re) (5 * x.im * y.im)
    have h_mul1 := cast_zmod_mul p hp x.re y.re
    have h_mul2 := cast_zmod_mul p hp (5 * x.im) y.im
    have h_mul3 := cast_zmod_mul p hp 5 x.im
    rw [h_add1, h_mul1, h_mul2, h_mul3]
    have h_five : (5 : ZMod N).val = 5 := rfl
    rw [h_five]
    push_cast
    ring
  · simp only [LucasRing.mul_re, LucasRing.mul_im]
    have h_add2 := cast_zmod_add p hp (x.re * y.im) (x.im * y.re)
    have h_mul4 := cast_zmod_mul p hp x.re y.im
    have h_mul5 := cast_zmod_mul p hp x.im y.re
    rw [h_add2, h_mul4, h_mul5]

lemma phi_one (p : ℕ) : phi p 1 = 1 := by
  unfold phi
  have h_one : (1 : ZMod N).val = 1 := rfl
  have h_zero : (0 : ZMod N).val = 0 := rfl
  simp [h_one, h_zero]
  rfl

lemma cast_zmod_pow (p : ℕ) (hp : p ∣ N) (x : ZMod N) (m : ℕ) :
    ( (x ^ m).val : ZMod p ) = (x.val : ZMod p) ^ m := by
  induction m with
  | zero =>
    have h1 : x ^ 0 = 1 := rfl
    have h2 : (1 : ZMod N).val = 1 := rfl
    rw [h1, h2]
    push_cast
    simp
  | succ m ih =>
    have h1 : x ^ (m + 1) = x ^ m * x := by ring
    rw [h1]
    have h2 := cast_zmod_mul p hp (x ^ m) x
    rw [h2]
    rw [ih]
    ring

lemma phi_pow (p : ℕ) (hp : p ∣ N) (x : LucasRing N 5) (m : ℕ) :
    phi p (x ^ m) = (phi p x) ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    exact phi_one p
  | succ m ih =>
    simp only [pow_succ]
    rw [phi_mul p hp, ih]
