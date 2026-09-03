import FormalConjecturesUtil

/-!
An auxiliary test of a digit construction, not a settlement of Erdős 773.
The definitions below track rational rotations through affine digit words.
-/
namespace Erdos773.ParametricSphere

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

structure Step where
  constant : Fin 4 → ℕ
  slope : Fin 4 → ℕ
  next : ℤ × ℤ

def base (t : ℕ) : ℕ := 256 + 124160 * t

def digit (s : Step) (j : Fin 4) (t : ℕ) : ℕ :=
  2 * s.constant j + 256 * s.slope j * t

def value (ss : List Step) (j : Fin 4) (t : ℕ) : ℕ :=
  ss.foldr (fun s n => digit s j t + base t * n) 1

def ivalue (ss : List Step) (j : Fin 4) (t : ℕ) : ℤ :=
  ss.foldr (fun s n =>
    2 * (s.constant j : ℤ) + 256 * (s.slope j : ℤ) * t + (256 + 124160 * (t : ℤ)) * n) 1

lemma cast_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    (value ss j t : ℤ) = ivalue ss j t := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [value, ivalue, List.foldr_cons, digit, base, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at ih ⊢
    rw [ih]


end Erdos773.ParametricSphere
