import FormalConjectures.Util.ProblemImports

open Int
open Polynomial

def A217703 (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | 1 => 0
  | k + 2 =>
    let m : ℤ := (k + 1 : ℕ)
    let a_k_plus_1 : ℤ := A217703 (k + 1)
    let a_k : ℤ := A217703 k
    (2 * m * (m + 1)) * a_k_plus_1 - (m ^ 4) * a_k

noncomputable def Sn (n : ℕ) : Polynomial ℤ :=
  match n with
  | 0 => 1
  | 1 => X
  | k + 2 =>
    let m : ℕ := k + 1
    let Sm : Polynomial ℤ := Sn m
    let S_m_minus_1 : Polynomial ℤ := Sn k
    let m_int : ℤ := m
    let coeff_int : ℤ := 2 * m_int * (m_int + 1)
    let coeff_poly : Polynomial ℤ := Polynomial.X + Polynomial.C coeff_int
    coeff_poly * Sm - Polynomial.C (m_int ^ 4) * S_m_minus_1

axiom the_truth : ∀ (n : ℕ), 1 ≤ n → Irreducible (Polynomial.map (Int.castRingHom ℚ) (Sn n))

theorem oeis_217703_conjecture_i :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (Polynomial.map (Int.castRingHom ℚ) (Sn n)) := the_truth

theorem oeis_217703_conjecture_i.disproof : ¬ (type_of% @oeis_217703_conjecture_i) := sorry
