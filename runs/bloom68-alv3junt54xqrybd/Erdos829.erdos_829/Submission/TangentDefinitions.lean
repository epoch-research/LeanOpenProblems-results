import FormalConjecturesUtil

/-!
# Integer triples on the rational cubic with value nine

The tangent transformation is represented by homogeneous integer polynomials.
The definitions in this file do not depend on either conjecture declaration.
-/

namespace Erdos829Aux.Tangent

structure Triple where
  a : ℤ
  b : ℤ
  w : ℤ
  deriving DecidableEq

def Good (p : Triple) : Prop :=
  0 < p.w ∧ IsCoprime p.a p.b ∧ p.a ^ 3 + p.b ^ 3 = 9 * p.w ^ 3

def Positive (p : Triple) : Prop := 0 < p.a ∧ 0 < p.b

def rawStep (p : Triple) : Triple :=
  { a := p.a * (p.a ^ 3 + 2 * p.b ^ 3)
    b := -p.b * (2 * p.a ^ 3 + p.b ^ 3)
    w := p.w * (p.a ^ 3 - p.b ^ 3) }

def step (p : Triple) : Triple :=
  let q := rawStep p
  if q.w < 0 then { a := -q.a, b := -q.b, w := -q.w } else q

def size (p : Triple) : ℕ := max p.a.natAbs p.b.natAbs

noncomputable def realSize (p : Triple) : ℝ :=
  max |(p.a : ℝ) / p.w| |(p.b : ℝ) / p.w|

def seed : Triple := {a := 2, b := 1, w := 1}

def orbit : ℕ → Triple
  | 0 => seed
  | k + 1 => step (orbit k)

end Erdos829Aux.Tangent
