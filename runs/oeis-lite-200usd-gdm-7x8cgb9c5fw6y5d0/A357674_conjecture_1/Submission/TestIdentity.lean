import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

namespace List

def sum_prod_excl {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => L.prod + a * sum_prod_excl L

theorem prod_add_y_eq {R : Type*} [CommRing R] (y : R) (hy2 : y ^ 2 = 0) (L : List R) :
    (L.map (fun x ↦ y + x)).prod = L.prod + y * sum_prod_excl L := by
  induction L with
  | nil =>
    simp [sum_prod_excl]
  | cons a L ih =>
    simp [sum_prod_excl, ih]
    linear_combination (y + a) * (L.prod + y * sum_prod_excl L) - (L.prod * a + y * (L.prod + a * sum_prod_excl L)) + (sum_prod_excl L) * hy2

def sum_prod_excl2 {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => sum_prod_excl L + a * sum_prod_excl2 L

theorem prod_add_y_eq3 {R : Type*} [CommRing R] (y : R) (hy3 : y ^ 3 = 0) (L : List R) :
    (L.map (fun x ↦ y + x)).prod = L.prod + y * sum_prod_excl L + y ^ 2 * sum_prod_excl2 L := by
  induction L with
  | nil =>
    simp [sum_prod_excl, sum_prod_excl2]
  | cons a L ih =>
    simp [sum_prod_excl, sum_prod_excl2, ih]
    linear_combination (y + a) * (L.prod + y * sum_prod_excl L + y ^ 2 * sum_prod_excl2 L) - 
                       (L.prod * a + y * (L.prod + a * sum_prod_excl L) + y ^ 2 * (sum_prod_excl L + a * sum_prod_excl2 L)) + 
                       (sum_prod_excl2 L) * hy3


def sum_pairs {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => sum_pairs L + a * L.sum

theorem prod_one_add_y_mul_eq3 {R : Type*} [CommRing R] (y : R) (hy3 : y ^ 3 = 0) (L : List R) :
    (L.map (fun x ↦ 1 + y * x)).prod = 1 + y * L.sum + y ^ 2 * sum_pairs L := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs, ih]
    linear_combination (1 + y * a) * (1 + y * L.sum + y ^ 2 * sum_pairs L) -
                       (1 + y * (a + L.sum) + y ^ 2 * (sum_pairs L + a * L.sum)) +
                       (a * sum_pairs L) * hy3

end List
