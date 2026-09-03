import FormalConjecturesUtil

/-!
A checked obstruction to simultaneously imposing square weights and square
point norms on the ordinary cubic norm graph. This does not settle Erdős 714.
The finite field and the irreducibility of the norm polynomial are part of
the certificate; no external computation is trusted by this file.
-/

open Polynomial SimpleGraph

namespace Erdos714OrdinarySquarePoints

noncomputable def basePolynomial : (ZMod 3)[X] := X^3-X-1

lemma basePolynomial_degree : basePolynomial.natDegree = 3 := by
  unfold basePolynomial
  compute_degree!

lemma basePolynomial_monic : basePolynomial.Monic := by
  unfold basePolynomial
  monicity!

lemma basePolynomial_irreducible : Irreducible basePolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [basePolynomial_degree]
    decide
  · intro x hx
    have hc : x^3 = x := by simpa using FiniteField.pow_card x
    simpa [Polynomial.IsRoot, basePolynomial, hc] using hx

instance : Fact (Irreducible basePolynomial) := ⟨basePolynomial_irreducible⟩

abbrev K := AdjoinRoot basePolynomial

instance : CharP K 3 := charP_of_injective_algebraMap (algebraMap (ZMod 3) K).injective 3

noncomputable instance : Fintype K :=
  Fintype.ofEquiv (Fin basePolynomial.natDegree → ZMod 3)
    (AdjoinRoot.powerBasis basePolynomial_monic.ne_zero).basis.equivFun.symm.toEquiv

lemma card_K : Fintype.card K = 27 := by
  have h := Fintype.card_congr
    (AdjoinRoot.powerBasis basePolynomial_monic.ne_zero).basis.equivFun.toEquiv
  simpa [basePolynomial_degree] using h

noncomputable def z : K := AdjoinRoot.root basePolynomial

lemma z_spec : z^3-z-1 = 0 := by
  have h := AdjoinRoot.eval₂_root basePolynomial
  simpa [basePolynomial, z] using h

/-- The base-three coefficient encoding used in the finite certificate. -/
noncomputable def code (n : ℕ) : K :=
  (n % 3 : ℕ) + ((n / 3) % 3 : ℕ) * z + (n / 9 : ℕ) * z^2

abbrev V := Fin 3 → K

/-- Determinant norm for θ³=θ+d. -/
def normForm {F : Type*} [CommRing F] (d : F) (v : Fin 3 → F) : F :=
  v 0^3 + 2*v 0^2*v 2 + v 0*v 2^2 - v 0*v 1^2 +
    d*v 1^3 - d*v 1*v 2^2 - 3*d*v 0*v 1*v 2 + d^2*v 2^3

theorem normForm_eq_det {F : Type*} [CommRing F] (d : F) (v : Fin 3 → F) :
    normForm d v = Matrix.det
      !![v 0, d*v 2, d*v 1;
         v 1, v 0+v 2, v 1+d*v 2;
         v 2, v 1, v 0+v 2] := by
  simp [Matrix.det_fin_three, normForm]
  ring

noncomputable def d : K := z^2

noncomputable def rowPoints : Fin 4 → V :=
  ![![code 10, code 5, code 17], ![code 11, code 5, code 17], ![code 9, code 5, code 17], ![code 17, code 3, code 17]]

noncomputable def columnPoints : Fin 4 → V :=
  ![![code 20, code 8, code 22], ![code 18, code 8, code 22], ![code 19, code 8, code 22], ![code 24, code 6, code 22]]

noncomputable def weights : Bool → Fin 4 → K
  | false => ![code 1, code 1, code 1, code 16]
  | true => ![code 9, code 9, code 9, code 20]

noncomputable def normRoots : Bool → Fin 4 → K
  | false => ![code 24, code 6, code 13, code 11]
  | true => ![code 10, code 9, code 13, code 16]

noncomputable def weightRoots : Bool → Fin 4 → K
  | false => ![code 1, code 1, code 1, code 4]
  | true => ![code 6, code 6, code 6, code 24]

noncomputable def points : Bool → Fin 4 → V
  | false => rowPoints
  | true => columnPoints

set_option maxHeartbeats 3000000 in
theorem norm_equations (i j : Fin 4) :
    normForm d (rowPoints i + columnPoints j) = weights false i * weights true j := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  fin_cases i <;> fin_cases j <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 171 * z^2 + 450 * z + 432) * hz + (272 * z^2 + 306 * z + 164) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 225 * z^2 + 432 * z + 504) * hz + (232 * z^2 + 312 * z + 168) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 198 * z^2 + 441 * z + 468) * hz + (247 * z^2 + 307 * z + 162) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 369 * z^2 + 600 * z + 812) * hz + (365 * z^2 + 488 * z + 274) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 144 * z^2 + 459 * z + 396) * hz + (307 * z^2 + 309 * z + 176) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 198 * z^2 + 441 * z + 468) * hz + (247 * z^2 + 307 * z + 162) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 171 * z^2 + 450 * z + 432) * hz + (272 * z^2 + 306 * z + 164) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 342 * z^2 + 627 * z + 854) * hz + (404 * z^2 + 533 * z + 298) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 198 * z^2 + 441 * z + 468) * hz + (247 * z^2 + 307 * z + 162) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 252 * z^2 + 423 * z + 540) * hz + (227 * z^2 + 321 * z + 180) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 261 * z^3 + 225 * z^2 + 432 * z + 504) * hz + (232 * z^2 + 312 * z + 168) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 396 * z^2 + 573 * z + 770) * hz + (336 * z^2 + 451 * z + 256) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 288 * z^2 + 680 * z + 936) * hz + (512 * z^2 + 646 * z + 372) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 342 * z^2 + 626 * z + 852) * hz + (404 * z^2 + 532 * z + 298) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 279 * z^3 + 315 * z^2 + 653 * z + 894) * hz + (453 * z^2 + 585 * z + 330) * h3
  · linear_combination (27 * z^7 + 81 * z^6 + 189 * z^5 + 189 * z^4 + 297 * z^3 + 558 * z^2 + 1003 * z + 1548) * hz + (704 * z^2 + 929 * z + 532) * h3

set_option maxHeartbeats 3000000 in
theorem point_square_equations (s : Bool) (i : Fin 4) :
    normForm d (points s i) = normRoots s i ^ 2 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  cases s <;> fin_cases i <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · linear_combination (z^7 + 6 * z^6 + 19 * z^5 + 35 * z^4 + 47 * z^3 + 50 * z^2 + 63 * z + 79) * hz + (39 * z^2 + 50 * z + 28) * h3
  · linear_combination (z^7 + 6 * z^6 + 19 * z^5 + 35 * z^4 + 47 * z^3 + 47 * z^2 + 63 * z + 78) * hz + (44 * z^2 + 55 * z + 34) * h3
  · linear_combination (z^7 + 6 * z^6 + 19 * z^5 + 35 * z^4 + 47 * z^3 + 53 * z^2 + 70 * z + 94) * hz + (40 * z^2 + 54 * z + 31) * h3
  · linear_combination (z^7 + 6 * z^6 + 19 * z^5 + 35 * z^4 + 49 * z^3 + 71 * z^2 + 130 * z + 230) * hz + (113 * z^2 + 152 * z + 86) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 26 * z^5 + z^4 + 27 * z^3 - 12 * z^2 + 64 * z + 21) * hz + (32 * z^2 + 27 * z + 10) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 26 * z^5 + z^4 + 27 * z^3 + 12 * z^2 + 36 * z + 45) * hz + (16 * z^2 + 27 * z + 15) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 26 * z^5 + z^4 + 27 * z^3 + 50 * z + 31) * hz + (20 * z^2 + 25 * z + 10) * h3
  · linear_combination (8 * z^7 + 12 * z^6 + 26 * z^5 + z^4 + 35 * z^3 + 84 * z^2 + 94 * z + 151) * hz + (62 * z^2 + 81 * z + 50) * h3

set_option maxHeartbeats 3000000 in
theorem weight_square_equations (s : Bool) (i : Fin 4) :
    weights s i = weightRoots s i ^ 2 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  cases s <;> fin_cases i <;>
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-z^2) * h3
  · linear_combination (-z^2) * h3
  · linear_combination (-z^2) * h3
  · linear_combination (-4 * z - 8) * hz + (-2 * z^2 - 4 * z - 2) * h3

set_option maxHeartbeats 3000000 in
theorem code_nonzero (n : ℕ) (hn : n ∈ ({1, 4, 6, 9, 10, 11, 13, 16, 24} : Finset ℕ)) :
    code n ≠ 0 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro h
  apply (one_ne_zero : (1 : K) ≠ 0)
  fin_cases hn <;>
    simp only [code, Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  · linear_combination (1) * h
  · linear_combination (z^2 + 2 * z) * h - (1) * hz - (z^2 + z) * h3
  · linear_combination (2 * z^2 + 1) * h - (4) * hz - (2 * z + 1) * h3
  · linear_combination (2 * z^2 + z + 1) * h - (2 * z + 1) * hz - (z^2 + z) * h3
  · linear_combination (2 * z^2 + 2 * z + 2) * h - (2 * z + 2) * hz - (2 * z^2 + 2 * z + 1) * h3
  · linear_combination (z) * h - (1) * hz - (z) * h3
  · linear_combination (2 * z^2 + 2) * h - (2 * z + 2) * hz - (2 * z^2 + 2 * z + 1) * h3
  · linear_combination (2 * z^2 + 2 * z + 1) * h - (2 * z + 6) * hz - (3 * z^2 + 4 * z + 2) * h3
  · linear_combination (2 * z + 1) * h - (4) * hz - (2 * z^2 + 2 * z + 1) * h3

theorem roots_nonzero (s : Bool) (i : Fin 4) :
    normRoots s i ≠ 0 ∧ weightRoots s i ≠ 0 := by
  cases s <;> fin_cases i <;> constructor <;>
    apply code_nonzero <;> decide

theorem rowPoints_injective : Function.Injective rowPoints := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · rfl
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · rfl
theorem columnPoints_injective : Function.Injective columnPoints := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · rfl
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h
  · have h := congrArg (fun v : V => v 0) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h
  · rfl
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · have h := congrArg (fun v : V => v 1) hij
    simp only [rowPoints, columnPoints, points, weights, normRoots, weightRoots, normForm, d, code,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Nat.reduceDiv, Nat.reduceMod, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
    exfalso
    apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination 1 * h + 1 * h3
  · rfl

lemma trace_d : d+d^3+d^9 = -1 := by
  have hz := z_spec
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  dsimp [d]
  linear_combination (z^15 + z^13 + z^12 + z^11 + 2 * z^10 + 2 * z^9 + 3 * z^8 + 4 * z^7 + 5 * z^6 + 7 * z^5 + 9 * z^4 + 13 * z^3 + 16 * z^2 + 22 * z + 29) * hz + (13 * z^2 + 17 * z + 10) * h3

theorem parameter_irreducible : Irreducible ((X^3-X-C d) : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X^3-X-C d) : K[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    have hx' : x^3-x = d := by
      simpa [Polynomial.IsRoot, sub_eq_zero] using hx
    have hx3 : x^9-x^3 = d^3 := by
      have h := congrArg (iterateFrobenius K 3 1) hx'
      simpa only [map_sub, map_pow, iterateFrobenius_def, Nat.reducePow, ← pow_mul,
        Nat.reduceMul] using h
    have hx9 : x^27-x^9 = d^9 := by
      have h := congrArg (iterateFrobenius K 3 2) hx'
      simpa only [map_sub, map_pow, iterateFrobenius_def, Nat.reducePow, ← pow_mul,
        Nat.reduceMul] using h
    have hx27 : x^27 = x := by simpa [card_K] using FiniteField.pow_card x
    have h10 : (1 : K) = 0 := by linear_combination hx' + hx3 + hx9 + trace_d - hx27
    exact one_ne_zero h10

/-- The original norm graph, with a bipartite tag and field-valued weights. -/
def graph : SimpleGraph (Bool × (V × K)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm d (u.2.1 + v.2.1) = u.2.2 * v.2.2
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
    exact ⟨Bool.false_ne_true, norm_equations i j⟩
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

#print axioms normForm_eq_det
#print axioms card_K
#print axioms parameter_irreducible
#print axioms norm_equations
#print axioms certificate_allowed
#print axioms restrictedGraph_not_free

end Erdos714OrdinarySquarePoints
