import Submission.RationalPolynomialModularObstruction

/-! Computable dense coefficient certificates with kernel-proved evaluation
lemmas. Coefficient lists may have trailing zeroes. -/
namespace Erdos322Research.DensePolynomialCertificate
open RationalPolynomialModularObstruction

def add : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (x : ℤ) (ys : List ℤ) : List ℤ := ys.map (x*·)

def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x::xs, ys => add (scale x ys) (0::mul xs ys)

def zero (xs : List ℤ) : Bool := xs.all (· == 0)

theorem eval_add {R : Type*} [CommRing R] (xs ys : List ℤ) (w : R) :
    evalList (add xs ys) w = evalList xs w+evalList ys w := by
  induction xs generalizing ys with
  | nil => simp [add, evalList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add, evalList]
    | cons y ys => simp [add, evalList, ih]; ring

theorem eval_scale {R : Type*} [CommRing R] (x : ℤ) (ys : List ℤ) (w : R) :
    evalList (scale x ys) w = (x : R)*evalList ys w := by
  induction ys with
  | nil => simp [scale, evalList]
  | cons y ys ih => simp only [scale, List.map_cons, evalList, Int.cast_mul] at *; rw [ih]; ring

theorem eval_mul {R : Type*} [CommRing R] (xs ys : List ℤ) (w : R) :
    evalList (mul xs ys) w = evalList xs w*evalList ys w := by
  induction xs with
  | nil => simp [mul, evalList]
  | cons x xs ih => rw [mul, eval_add, eval_scale]; simp only [evalList, Int.cast_zero, zero_add]; rw [ih]; ring

theorem eval_zero {R : Type*} [CommRing R] (xs : List ℤ) (w : R) (h : zero xs = true) :
    evalList xs w = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh : x = 0 ∧ zero xs = true := by simpa [zero] using h
    simp [evalList, hh.1, ih hh.2]

def add₂ : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => add x y::add₂ xs ys

def scale₂ (x : List ℤ) (ys : List (List ℤ)) : List (List ℤ) := ys.map (mul x)

def mul₂ : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | x::xs, ys => add₂ (scale₂ x ys) ([]::mul₂ xs ys)

def eval₂ {R : Type*} [CommRing R] : List (List ℤ) → R → R → R
  | [], _, _ => 0
  | x::xs, V, w => evalList x w+V*eval₂ xs V w

def zero₂ (xs : List (List ℤ)) : Bool := xs.all zero

theorem eval₂_add {R : Type*} [CommRing R] (xs ys : List (List ℤ)) (V w : R) :
    eval₂ (add₂ xs ys) V w = eval₂ xs V w+eval₂ ys V w := by
  induction xs generalizing ys with
  | nil => simp [add₂, eval₂]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add₂, eval₂]
    | cons y ys => simp [add₂, eval₂, eval_add, ih]; ring

theorem eval₂_scale {R : Type*} [CommRing R] (x : List ℤ) (ys : List (List ℤ)) (V w : R) :
    eval₂ (scale₂ x ys) V w = evalList x w*eval₂ ys V w := by
  induction ys with
  | nil => simp [scale₂, eval₂]
  | cons y ys ih =>
    simp only [scale₂, List.map_cons, eval₂, eval_mul] at *
    rw [ih]
    ring

theorem eval₂_mul {R : Type*} [CommRing R] (xs ys : List (List ℤ)) (V w : R) :
    eval₂ (mul₂ xs ys) V w = eval₂ xs V w*eval₂ ys V w := by
  induction xs with
  | nil => simp [mul₂, eval₂]
  | cons x xs ih =>
    rw [mul₂, eval₂_add, eval₂_scale]
    simp only [eval₂, evalList, zero_add]
    rw [ih]
    ring

theorem eval₂_zero {R : Type*} [CommRing R] (xs : List (List ℤ)) (V w : R)
    (h : zero₂ xs = true) : eval₂ xs V w = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh : zero x = true ∧ zero₂ xs = true := by simpa [zero₂] using h
    rw [eval₂, eval_zero x w hh.1, ih hh.2]
    ring

end Erdos322Research.DensePolynomialCertificate
