import Submission.OrdinarySquarePoints

/-!
A characteristic-three certificate defeating positive Vandermonde edge signs,
even with nonzero square weights and nonzero square point norms. This is an
obstruction to a proposed construction, not a resolution of Erdős 714.
-/

noncomputable section
open Polynomial SimpleGraph
set_option linter.unusedSimpArgs false
namespace Erdos714PositiveNorm
open Erdos714OrdinarySquarePoints (K V code z z_spec d normForm trace_d card_K parameter_irreducible)

/-- The Vandermonde product when the Artin--Schreier generator has
    relative Frobenius theta -> theta-1. The interpretation is proved in
    `Submission.PositiveNormSemantics`. -/
def orientation (v : V) : K := v 1^3-v 1*v 2^2-d*v 2^3

noncomputable def rowPoints : Fin 4 → V :=
  ![![code 1, code 26, code 5], ![code 2, code 26, code 5], ![code 22, code 21, code 7], ![code 20, code 26, code 5]]

noncomputable def columnPoints : Fin 4 → V :=
  ![![code 10, code 10, code 8], ![code 2, code 7, code 18], ![code 1, code 17, code 0], ![code 3, code 23, code 10]]

noncomputable def weights : Bool → Fin 4 → K
  | false => ![code 1, code 1, code 20, code 22]
  | true => ![code 4, code 13, code 20, code 9]

noncomputable def normRoots : Bool → Fin 4 → K
  | false => ![code 9, code 16, code 9, code 16]
  | true => ![code 13, code 16, code 14, code 3]

noncomputable def weightRoots : Bool → Fin 4 → K
  | false => ![code 1, code 1, code 12, code 11]
  | true => ![code 10, code 5, code 12, code 3]

noncomputable def orientationRoots : Fin 4 → Fin 4 → K :=
  ![![code 12, code 13, code 16, code 13], ![code 12, code 13, code 16, code 13], ![code 13, code 4, code 4, code 17], ![code 12, code 13, code 16, code 13]]

noncomputable def points : Bool → Fin 4 → V
  | false => rowPoints
  | true => columnPoints

set_option maxHeartbeats 3000000 in
theorem norm_equations (i j : Fin 4) :
    normForm d (rowPoints i + columnPoints j) = weights false i * weights true j := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  fin_cases i <;> fin_cases j <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · linear_combination (27 * z^5 + 54 * z^4 + 163 * z^3 + 140 * z^2 + 114 * z + 163) * hz + (62 * z^2 + 108 * z + 72) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 38 * z^5 + 69 * z^4 + 130 * z^3 + 181 * z^2 + 228 * z + 256) * hz + (116 * z^2 + 147 * z + 101) * h3
  · linear_combination (27 * z^5 + 109 * z^4 + 282 * z^3 + 466 * z^2 + 625 * z + 788) * hz + (337 * z^2 + 455 * z + 262) * h3
  · linear_combination (z^7 + 3 * z^6 + 73 * z^5 + 144 * z^4 + 341 * z^3 + 413 * z^2 + 599 * z + 723) * hz + (322 * z^2 + 438 * z + 241) * h3
  · linear_combination (27 * z^5 + 54 * z^4 + 163 * z^3 + 113 * z^2 + 54 * z + 85) * hz + (27 * z^2 + 76 * z + 68) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 38 * z^5 + 69 * z^4 + 118 * z^3 + 151 * z^2 + 174 * z + 169) * hz + (85 * z^2 + 98 * z + 92) * h3
  · linear_combination (27 * z^5 + 109 * z^4 + 282 * z^3 + 457 * z^2 + 586 * z + 719) * hz + (300 * z^2 + 413 * z + 248) * h3
  · linear_combination (z^7 + 3 * z^6 + 73 * z^5 + 144 * z^4 + 329 * z^3 + 392 * z^2 + 515 * z + 633) * hz + (268 * z^2 + 383 * z + 217) * h3
  · linear_combination (27 * z^5 - 17 * z^4 + 6 * z^3 - 53 * z^2 + 3 * z + 110) * hz + (46 * z^2 + 77 * z + 52) * h3
  · linear_combination (8 * z^7 + 24 * z^6 + 20 * z^5 - 18 * z^3 - 65 * z^2 - 15 * z - 31) * hz + (13 * z^2 + 7 * z + 4) * h3
  · linear_combination (27 * z^5 + 53 * z^4 + 80 * z^3 + 75 * z^2 + 94 * z + 132) * hz + (57 * z^2 + 81 * z + 46) * h3
  · linear_combination (z^7 + 6 * z^6 + 55 * z^5 + 33 * z^4 + 29 * z^3 + 15 * z + 49) * hz + (19 * z^2 + 30 * z + 18) * h3
  · linear_combination (27 * z^5 + 63 * z^3 - 19 * z^2 - 62 * z - 53) * hz + (-2 * z^2 - 9 * z + 22) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 14 * z^5 + 9 * z^4 + 34 * z^3 - 15 * z^2 + 82 * z - 92) * hz + (48 * z^2 - 20 * z + 5) * h3
  · linear_combination (27 * z^5 + 91 * z^4 + 212 * z^3 + 327 * z^2 + 420 * z + 485) * hz + (226 * z^2 + 279 * z + 170) * h3
  · linear_combination (z^7 + 3 * z^6 + 49 * z^5 + 102 * z^4 + 177 * z^3 + 232 * z^2 + 257 * z + 348) * hz + (148 * z^2 + 202 * z + 122) * h3

set_option maxHeartbeats 3000000 in
theorem orientation_equations (i j : Fin 4) :
    orientation (rowPoints i + columnPoints j) = orientationRoots i j ^ 2 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  fin_cases i <;> fin_cases j <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · linear_combination (27 * z^3 + 27 * z^2 + 8 * z - 66) * hz + (-12 * z^2 - 36 * z - 29) * h3
  · linear_combination (-8 * z^5 - 12 * z^4 - 38 * z^3 - 21 * z^2 + 5 * z + 79) * hz + (40 * z^2 + 54 * z + 31) * h3
  · linear_combination (27 * z^3 + 107 * z^2 + 269 * z + 454) * hz + (222 * z^2 + 293 * z + 167) * h3
  · linear_combination (-z^5 - 3 * z^4 + 47 * z^3 + 110 * z^2 + 269 * z + 390) * hz + (189 * z^2 + 250 * z + 139) * h3
  · linear_combination (27 * z^3 + 27 * z^2 + 8 * z - 66) * hz + (-12 * z^2 - 36 * z - 29) * h3
  · linear_combination (-8 * z^5 - 12 * z^4 - 38 * z^3 - 21 * z^2 + 5 * z + 79) * hz + (40 * z^2 + 54 * z + 31) * h3
  · linear_combination (27 * z^3 + 107 * z^2 + 269 * z + 454) * hz + (222 * z^2 + 293 * z + 167) * h3
  · linear_combination (-z^5 - 3 * z^4 + 47 * z^3 + 110 * z^2 + 269 * z + 390) * hz + (189 * z^2 + 250 * z + 139) * h3
  · linear_combination (27 * z^3 - 37 * z^2 - 130 * z - 189) * hz + (-84 * z^2 - 117 * z - 66) * h3
  · linear_combination (-8 * z^5 - 24 * z^4 - 44 * z^3 - 56 * z^2 - 64 * z - 83) * hz + (-37 * z^2 - 49 * z - 28) * h3
  · linear_combination (27 * z^3 + 73 * z^2 + 138 * z + 205) * hz + (92 * z^2 + 122 * z + 70) * h3
  · linear_combination (-z^5 - 6 * z^4 + 41 * z^3 + 39 * z^2 + 100 * z + 100) * hz + (49 * z^2 + 64 * z + 32) * h3
  · linear_combination (27 * z^3 + 27 * z^2 + 8 * z - 66) * hz + (-12 * z^2 - 36 * z - 29) * h3
  · linear_combination (-8 * z^5 - 12 * z^4 - 38 * z^3 - 21 * z^2 + 5 * z + 79) * hz + (40 * z^2 + 54 * z + 31) * h3
  · linear_combination (27 * z^3 + 107 * z^2 + 269 * z + 454) * hz + (222 * z^2 + 293 * z + 167) * h3
  · linear_combination (-z^5 - 3 * z^4 + 47 * z^3 + 110 * z^2 + 269 * z + 390) * hz + (189 * z^2 + 250 * z + 139) * h3

set_option maxHeartbeats 3000000 in
theorem point_square_equations (s : Bool) (i : Fin 4) :
    normForm d (points s i) = normRoots s i ^ 2 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  cases s <;> fin_cases i <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · linear_combination (8 * z^5 + 25 * z^4 + 60 * z^3 + 85 * z^2 + 100 * z + 127) * hz + (54 * z^2 + 75 * z + 44) * h3
  · linear_combination (8 * z^5 + 25 * z^4 + 60 * z^3 + 79 * z^2 + 78 * z + 91) * hz + (35 * z^2 + 55 * z + 38) * h3
  · linear_combination (8 * z^5 - 4 * z^4 - 18 * z^3 - 15 * z^2 - 3 * z + 11) * hz + (6 * z^2 + 8 * z + 5) * h3
  · linear_combination (8 * z^5 + 13 * z^4 + 24 * z^3 + 23 * z^2 + 24 * z + 7) * hz + (17 * z^2 + 9 * z + 10) * h3
  · linear_combination (z^5 + 2 * z^4 + 18 * z^3 + 11 * z^2 + 18 * z + 29) * hz + (11 * z^2 + 19 * z + 12) * h3
  · linear_combination (8 * z^7 + 8 * z^5 + 4 * z^3 - 8 * z^2 + 11 * z - 2) * hz + (2 * z^2 - z + 1) * h3
  · linear_combination (z^5 + 6 * z^4 + 19 * z^3 + 39 * z^2 + 59 * z + 76) * hz + (31 * z^2 + 41 * z + 23) * h3
  · linear_combination (z^7 + 10 * z^5 + 6 * z^4 + 34 * z^3 + 24 * z^2 + 60 * z + 57) * hz + (29 * z^2 + 38 * z + 19) * h3

set_option maxHeartbeats 3000000 in
theorem weight_square_equations (s : Bool) (i : Fin 4) :
    weights s i = weightRoots s i ^ 2 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  cases s <;> fin_cases i <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · ring
  · ring
  · linear_combination (-z - 2) * hz + (-z) * h3
  · linear_combination (-z) * hz + (-z^2 - 1) * h3
  · linear_combination (-z) * hz + (-z^2) * h3
  · linear_combination (-z - 1) * h3
  · linear_combination (-z - 2) * hz + (-z) * h3
  · ring

set_option maxHeartbeats 3000000 in
lemma code_nonzero (n : ℕ) (hn : n ∈ ({1, 3, 4, 5, 9, 10, 11, 12, 13, 14, 16, 17} : Finset ℕ)) : code n ≠ 0 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro h
  apply (one_ne_zero : (1 : K) ≠ 0)
  fin_cases hn <;>
    simp only [code, Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  · linear_combination (1) * h - (0) * hz - (0) * h3
  · linear_combination (z^2 + 2) * h - (1) * hz - (z) * h3
  · linear_combination (z^2 + 2 * z) * h - (1) * hz - (z^2 + z) * h3
  · linear_combination (z^2 + z) * h - (1) * hz - (z^2 + z) * h3
  · linear_combination (2 * z^2 + z + 1) * h - (2 * z + 1) * hz - (z^2 + z) * h3
  · linear_combination (2 * z^2 + 2 * z + 2) * h - (2 * z + 2) * hz - (2 * z^2 + 2 * z + 1) * h3
  · linear_combination (z) * h - (1) * hz - (z) * h3
  · linear_combination (z + 2) * h - (1) * hz - (z^2 + z) * h3
  · linear_combination (2 * z^2 + 2) * h - (2 * z + 2) * hz - (2 * z^2 + 2 * z + 1) * h3
  · linear_combination (2 * z^2 + z + 2) * h - (2 * z + 3) * hz - (3 * z^2 + 3 * z + 2) * h3
  · linear_combination (2 * z^2 + 2 * z + 1) * h - (2 * z + 6) * hz - (3 * z^2 + 4 * z + 2) * h3
  · linear_combination (2 * z^2) * h - (2 * z + 4) * hz - (2 * z^2 + 2 * z + 1) * h3

lemma roots_nonzero (s : Bool) (i : Fin 4) :
    normRoots s i ≠ 0 ∧ weightRoots s i ≠ 0 := by
  cases s <;> fin_cases i <;> constructor <;> apply code_nonzero <;> decide

lemma orientation_nonzero (i j : Fin 4) : orientationRoots i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> apply code_nonzero <;> decide

lemma rowPoints_injective : Function.Injective rowPoints := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2) * h - (0) * hz - (-1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z + 1) * h - (-2) * hz - (-z^2 - z - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z) * h - (-2) * hz - (-z - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (1) * h - (0) * hz - (0) * h3
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + 2 * z + 1) * h - (-4 * z - 6) * hz - (-2 * z^2 - 3 * z - 2) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + z + 1) * h - (-4 * z - 2) * hz - (-2 * z^2 - 2 * z - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z + 2) * h - (4) * hz - (2 * z^2 + 2 * z + 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + z + 2) * h - (2 * z + 3) * hz - (2 * z^2 + 2 * z) * h3
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + z) * h - (1) * hz - (0) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z) * h - (4) * hz - (2 * z + 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + 2 * z + 2) * h - (2 * z + 4) * hz - (2 * z^2 + 2 * z + 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + 2 * z) * h - (-2) * hz - (-1) * h3
  · rfl

lemma columnPoints_injective : Function.Injective columnPoints := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z) * h - (1) * hz - (0) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + z + 1) * h - (2 * z + 1) * hz - (z^2 + z) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + 2 * z + 1) * h - (2 * z) * hz - (z^2 + z) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z) * h - (-2) * hz - (-1) * h3
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (1) * h - (0) * hz - (0) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + z) * h - (-2) * hz - (z^2 - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + 2 * z + 2) * h - (-z - 2) * hz - (-z^2 - z - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2) * h - (0) * hz - (-1) * h3
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (2 * z^2 + 2 * z) * h - (-2) * hz - (-1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + z + 2) * h - (-z) * hz - (-z^2 - 1) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + 2 * z) * h - (1) * hz - (-z) * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, orientationRoots,
      orientation, normForm, d, code, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination (z^2 + z) * h - (1) * hz - (0) * h3
  · rfl

/-- Positive edge orientations, independent of the two square vertex restrictions. -/
def graph : SimpleGraph (Bool × (V × K)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm d (u.2.1 + v.2.1) = u.2.2 * v.2.2 ∧
    orientation (u.2.1 + v.2.1) ≠ 0 ∧ IsSquare (orientation (u.2.1 + v.2.1))
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

/-- BOTH square conditions, with zero excluded from both. -/
def allowed (v : Bool × (V × K)) : Prop :=
  v.2.2 ≠ 0 ∧ IsSquare v.2.2 ∧
    normForm d v.2.1 ≠ 0 ∧ IsSquare (normForm d v.2.1)

noncomputable def restrictedGraph : SimpleGraph {v // allowed v} := graph.induce _

lemma certificate_allowed (s : Bool) (i : Fin 4) :
    allowed (s, points s i, weights s i) := by
  obtain ⟨hn, hw⟩ := roots_nonzero s i
  change weights s i ≠ 0 ∧ IsSquare (weights s i) ∧
    normForm d (points s i) ≠ 0 ∧ IsSquare (normForm d (points s i))
  rw [weight_square_equations, point_square_equations]
  exact ⟨pow_ne_zero 2 hw, IsSquare.sq _, pow_ne_zero 2 hn, IsSquare.sq _⟩

/-- An explicit copy in the genuine square-point, square-weight restriction. -/
theorem restrictedGraph_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free restrictedGraph := by
  let L (i : Fin 4) : {v // allowed v} :=
    ⟨(false, rowPoints i, weights false i), certificate_allowed false i⟩
  let R (i : Fin 4) : {v // allowed v} :=
    ⟨(true, columnPoints i, weights true i), certificate_allowed true i⟩
  have hL : Function.Injective L := by
    intro i j h
    apply rowPoints_injective
    exact congrArg (fun v : {v // allowed v} => v.val.2.1) h
  have hR : Function.Injective R := by
    intro i j h
    apply columnPoints_injective
    exact congrArg (fun v : {v // allowed v} => v.val.2.1) h
  have hE : ∀ i j, restrictedGraph.Adj (L i) (R j) := by
    intro i j
    refine ⟨Bool.false_ne_true, norm_equations i j, ?_⟩
    change orientation (rowPoints i + columnPoints j) ≠ 0 ∧
      IsSquare (orientation (rowPoints i + columnPoints j))
    rw [orientation_equations]
    exact ⟨pow_ne_zero 2 (orientation_nonzero i j), IsSquare.sq _⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp at hxy
      | inr j => exact hE i j
    | inr i =>
      cases y with
      | inl j => exact (hE j i).symm
      | inr j => simp at hxy
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hL hxy)
      | inr j => exact False.elim (Bool.false_ne_true
          (congrArg (fun v : {v // allowed v} => v.val.1) hxy))
    | inr i =>
      cases y with
      | inl j => exact False.elim (Bool.false_ne_true
          (congrArg (fun v : {v // allowed v} => v.val.1) hxy).symm)
      | inr j => exact congrArg Sum.inr (hR hxy)

#print axioms norm_equations
#print axioms orientation_equations
#print axioms certificate_allowed
#print axioms restrictedGraph_not_free

end Erdos714PositiveNorm
