import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation

/-! A symbolic rank-six diagnostic for the seven-point median construction.
This file proves a Pfaffian identity only. It neither constructs eight points
nor asserts a rank bound for arbitrary rational-distance configurations. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Erdos213.SignedRankSix
variable {R : Type*} [CommRing R]

def pf6 (A : Fin 8 → Fin 8 → R) (i j k l m n : Fin 8) : R :=
  A i j * (A k l * A m n - A k m * A l n + A k n * A l m) -
  A i k * (A j l * A m n - A j m * A l n + A j n * A l m) +
  A i l * (A j k * A m n - A j m * A k n + A j n * A k m) -
  A i m * (A j k * A l n - A j l * A k n + A j n * A k l) +
  A i n * (A j k * A l m - A j l * A k m + A j m * A k l)

def pf8 (A : Fin 8 → Fin 8 → R) : R :=
  A 0 1 * pf6 A 2 3 4 5 6 7 - A 0 2 * pf6 A 1 3 4 5 6 7 +
  A 0 3 * pf6 A 1 2 4 5 6 7 - A 0 4 * pf6 A 1 2 3 5 6 7 +
  A 0 5 * pf6 A 1 2 3 4 6 7 - A 0 6 * pf6 A 1 2 3 4 5 7 +
  A 0 7 * pf6 A 1 2 3 4 5 6

/-- The finite edges are signed norms in the known quadratic construction;
the final row and column represent the normalized point at infinity. -/
def medianMatrix (a b c u v w : R) : Fin 8 → Fin 8 → R :=
  !![0, -2 * b * v, -c * w, v * w, -2 * c ^ 2, 2 * a * w, c * v, 1;
     2 * b * v, 0, -a * u, -a * v, -2 * a ^ 2, 2 * c * u, -u * v, 1;
     c * w, a * u, 0, -a * w, a * c, u * w, -c * u, 1;
     -v * w, a * v, a * w, 0, a * b, -b * w, -b * v, 1;
     2 * c ^ 2, 2 * a ^ 2, -a * c, -a * b, 0, 2 * b ^ 2, -b * c, 1;
     -2 * a * w, -2 * c * u, -u * w, b * w, -2 * b ^ 2, 0, b * u, 1;
     -c * v, u * v, c * u, b * v, b * c, -b * u, 0, 1;
     -1, -1, -1, -1, -1, -1, -1, 0]

lemma median_pf8_zero (a b c u v w : R)
    (hu : u^2 = 2*a^2 + 2*b^2 - c^2)
    (hv : v^2 = 2*a^2 + 2*c^2 - b^2)
    (hw : w^2 = 2*b^2 + 2*c^2 - a^2) :
    pf8 (medianMatrix a b c u v w) = 0 := by
  simp only [pf8, pf6, medianMatrix, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (2 * a ^ 4 - 6 * a ^ 2 * b ^ 2 + 2 * b ^ 4 - 2 * a ^ 2 * c ^ 2 - 2 * b ^ 2 * c ^ 2 - 2 * a * b * v * w) * hu +
    (4 * b ^ 4 - a ^ 2 * c ^ 2 + a ^ 2 * u ^ 2 - 2 * b ^ 2 * u ^ 2 - 2 * c ^ 2 * u ^ 2 + 2 * a * c * u * w) * hv +
    (4 * a ^ 4 - b ^ 2 * c ^ 2 + 2 * b * c * u * v - u ^ 2 * v ^ 2) * hw

#print axioms median_pf8_zero
end Erdos213.SignedRankSix
