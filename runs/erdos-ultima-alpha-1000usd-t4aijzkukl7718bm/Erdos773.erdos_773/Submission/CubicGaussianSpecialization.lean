import Submission.FormalGaussianSidon

/-!
A cubic carry obstruction for the Gaussian-Eisenstein formal construction.
This is NOT a disproof of Erdős 773.
-/
namespace Erdos773.CubicGaussianSpecialization
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000

def base (t : ℤ) : ℤ := 132 * t

def low (t : ℤ) (j : Fin 4) : ℤ := ![6*t+7, 6*t+4, 6*t+6, 6*t+5] j

def high (t : ℤ) (j : Fin 4) : ℤ := ![20*t-1, 8*t-6, 20*t-6, 8*t+1] j

def parameter (t : ℤ) (j : Fin 4) : ℤ[X] :=
  1 + C (low t j)*X + C (high t j)*X^2

lemma coefficient_formula (t : ℤ) (j : Fin 4) (n : ℕ) :
    (encoding 3 (parameter t j)).coeff n =
      (if n = 3 then 1 else 0) + 6 * ((if n = 0 then 1 else 0) +
        low t j * (if 1 = n then 1 else 0) +
          high t j * (if n = 2 then 1 else 0)) := by
  simp only [encoding, parameter, coeff_add, coeff_X_pow, coeff_C_mul,
    coeff_one, coeff_X]

lemma admissible (t : ℤ) (j : Fin 4) : Admissible 3 (parameter t j) := by
  fin_cases j <;> constructor
  all_goals first
    | (dsimp [parameter]; compute_degree <;> norm_num)
    | norm_num [parameter]

/-- The entire discrepancy is just a multiple of the specialization factor. -/
lemma norm_difference (t : ℤ) :
    (encoding 3 (parameter t 0))^2 + (encoding 3 (parameter t 1))^2 -
      (encoding 3 (parameter t 2))^2 - (encoding 3 (parameter t 3))^2 =
        24 * X^4 * (C (base t) - X) := by
  dsimp [encoding, parameter, low, high, base]
  simp only [map_add, map_sub, map_mul, map_ofNat, map_one]
  ring

lemma discrepancy_ne_zero (t : ℤ) :
    (encoding 3 (parameter t 0))^2 + (encoding 3 (parameter t 1))^2 -
      (encoding 3 (parameter t 2))^2 - (encoding 3 (parameter t 3))^2 ≠ 0 := by
  rw [norm_difference]
  intro h
  have he : (24 * X^4 * (C (base t) - X) : ℤ[X]) =
      C (24 * base t) * X^4 - 24 * X^5 := by
    simp only [map_mul, map_ofNat]
    ring
  rw [he] at h
  have hc := congrArg (fun P : ℤ[X] => P.coeff 5) h
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow,
    coeff_zero, show (5 : ℕ) ≠ 4 by decide, ite_false] at hc
  norm_num at hc

/-- The three lower digits are positive and strictly increasing. All are
multiples of six, and all four coefficients are canonical base digits. -/
lemma coefficient_bounds (t : ℤ) (ht : 6 ≤ t) (j : Fin 4) :
    let E := encoding 3 (parameter t j)
    E.coeff 0 = 6 ∧ 6 < E.coeff 1 ∧ E.coeff 1 < E.coeff 2 ∧
      E.coeff 2 < base t ∧ E.coeff 3 = 1 ∧
        (∀ n < 3, (6 : ℤ) ∣ E.coeff n) := by
  dsimp only
  simp only [coefficient_formula]
  norm_num
  fin_cases j <;> dsimp [low, high, base]
  all_goals
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro n hn
    interval_cases n <;> norm_num

lemma monic_degree (t : ℤ) (j : Fin 4) :
    (encoding 3 (parameter t j)).Monic ∧
      (encoding 3 (parameter t j)).natDegree = 3 := by
  have hl : (encoding 3 (parameter t j)).natDegree ≤ 3 := by
    fin_cases j <;> dsimp [encoding, parameter] <;> compute_degree
  have hc : (encoding 3 (parameter t j)).coeff 3 = 1 := by
    rw [coefficient_formula]
    norm_num
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one 3 hl hc,
    natDegree_eq_of_le_of_coeff_ne_zero hl (by rw [hc]; exact one_ne_zero)⟩

def value (t : ℤ) (j : Fin 4) : ℤ := (encoding 3 (parameter t j)).eval (base t)

lemma collision (t : ℤ) :
    value t 0 ^ 2 + value t 1 ^ 2 = value t 2 ^ 2 + value t 3 ^ 2 := by
  have hh := congrArg (Polynomial.eval (base t)) (norm_difference t)
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_C, eval_ofNat,
    sub_self, mul_zero] at hh
  change value t 0^2 + value t 1^2 - value t 2^2 - value t 3^2 = 0 at hh
  linarith

lemma value_formula (t : ℤ) (j : Fin 4) :
    value t j = (base t)^3 + 6*(1 + low t j * base t + high t j * (base t)^2) := by
  simp only [value, encoding, parameter, eval_add, eval_pow, eval_X,
    eval_mul, eval_C, eval_one]

lemma positive (t : ℤ) (ht : 6 ≤ t) (j : Fin 4) : 0 < value t j := by
  have hb : 0 < base t := by dsimp [base]; omega
  have hl : 0 < low t j := by fin_cases j <;> dsimp [low] <;> omega
  have hh : 0 < high t j := by fin_cases j <;> dsimp [high] <;> omega
  rw [value_formula]
  positivity

lemma ordered_values (t : ℤ) (ht : 6 ≤ t) :
    value t 1 < value t 3 ∧ value t 3 < value t 2 ∧ value t 2 < value t 0 := by
  have hb : 0 < base t := by dsimp [base]; omega
  have hdiff : 0 < 12*t-7 := by omega
  have hsq : 0 < (base t)^2 := sq_pos_of_pos hb
  have hm := mul_pos hdiff hsq
  simp only [value_formula]
  dsimp [low, high]
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma value_injective (t : ℤ) (ht : 6 ≤ t) : Function.Injective (value t) := by
  have ho := ordered_values t ht
  intro i j he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; simp only [value_formula] at ho he; dsimp [low, high] at ho he; omega)

lemma bases_unbounded (L : ℤ) : ∃ t : ℤ, 6 ≤ t ∧ L < base t := by
  refine ⟨max 6 (L+1), le_max_left _ _, ?_⟩
  have h1 := le_max_left (6 : ℤ) (L+1)
  have h2 := le_max_right (6 : ℤ) (L+1)
  dsimp [base]
  omega

lemma formal_square_sidon (t : ℤ) :
    IsSidon ((univ.image (fun j : Fin 4 => (encoding 3 (parameter t j))^2)) :
      Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 3)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp hf
  exact ⟨parameter t j, admissible t j, rfl⟩

/-- Failure of integer specialization for every t ≥ 6, despite the
strictly increasing canonical lower digits and the fixed constant 6. -/
theorem specialization_not_sidon (t : ℤ) (ht : 6 ≤ t) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value t j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value t j^2 ∈ univ.image (fun j : Fin 4 => value t j^2) :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have h02 : value t 2^2 < value t 0^2 :=
    (sq_lt_sq₀ (positive t ht 2).le (positive t ht 0).le).mpr
      (ordered_values t ht).2.2
  have h03 : value t 3^2 < value t 0^2 :=
    (sq_lt_sq₀ (positive t ht 3).le (positive t ht 0).le).mpr
      ((ordered_values t ht).2.1.trans (ordered_values t ht).2.2)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h <;> omega

lemma concrete_values : value 6 = ![944863926, 655053702, 926041254, 681403542] := by
  funext j
  fin_cases j <;> norm_num [value_formula, low, high, base]

namespace AllDegrees

def low (j : Fin 4) : ℤ := ![9, 6, 8, 7] j

def middle (j : Fin 4) : ℤ := ![13, 4, 8, 11] j

def high (j : Fin 4) : ℤ := ![20, 8, 20, 8] j

/-- The exponent k allows the carry obstruction in every degree k+3. -/
def parameter (k : ℕ) (t : ℤ) (j : Fin 4) : ℤ[X] :=
  1 + C (low j)*X + C (middle j)*X^2 + C (6*t)*X^(k+1) +
    C (high j*t)*X^(k+2)

lemma admissible (k : ℕ) (t : ℤ) (j : Fin 4) :
    Admissible (k+3) (parameter k t j) := by
  constructor
  · dsimp [parameter]
    compute_degree
    omega
  · simp [parameter]

lemma coefficient_formula (k : ℕ) (t : ℤ) (j : Fin 4) (n : ℕ) :
    (encoding (k+3) (parameter k t j)).coeff n =
      (if n = k+3 then 1 else 0) + 6 * ((if n = 0 then 1 else 0) +
        low j * (if 1 = n then 1 else 0) +
        middle j * (if n = 2 then 1 else 0) +
        6*t * (if n = k+1 then 1 else 0) +
        high j*t * (if n = k+2 then 1 else 0)) := by
  simp only [encoding, parameter, coeff_add, coeff_X_pow, coeff_C_mul,
    coeff_one, coeff_X]

/-- All the coefficients are genuine base digits, not signed or oversized
polynomial coefficients. The constant coefficient is exactly six. -/
lemma canonical_digits (k : ℕ) (t : ℤ) (ht : 7 ≤ t) (j : Fin 4) :
    let E := encoding (k+3) (parameter k t j)
    E.coeff 0 = 6 ∧ E.coeff (k+3) = 1 ∧
      (∀ n, 0 ≤ E.coeff n ∧ E.coeff n < base t) ∧
        (∀ n < k+3, (6 : ℤ) ∣ E.coeff n) := by
  dsimp only
  simp only [coefficient_formula]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · have h1 : ¬ (1 = k+3) := by omega
    have h2 : ¬ (k+3 = 2) := by omega
    simp [h2]
  · intro n
    fin_cases j <;> dsimp [low, middle, high, base]
    all_goals split_ifs <;> omega
  · intro n hn
    rw [if_neg (by omega : n ≠ k+3), zero_add]
    exact dvd_mul_right _ _

lemma monic_degree (k : ℕ) (t : ℤ) (j : Fin 4) :
    (encoding (k+3) (parameter k t j)).Monic ∧
      (encoding (k+3) (parameter k t j)).natDegree = k+3 := by
  have hl : (encoding (k+3) (parameter k t j)).natDegree ≤ k+3 := by
    dsimp [encoding, parameter]
    compute_degree
  have hc : (encoding (k+3) (parameter k t j)).coeff (k+3) = 1 := by
    rw [coefficient_formula]
    have h2 : ¬ (k+3 = 2) := by omega
    simp [h2]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one (k+3) hl hc,
    natDegree_eq_of_le_of_coeff_ne_zero hl (by rw [hc]; exact one_ne_zero)⟩

lemma norm_difference (k : ℕ) (t : ℤ) :
    (encoding (k+3) (parameter k t 0))^2 +
      (encoding (k+3) (parameter k t 1))^2 -
      (encoding (k+3) (parameter k t 2))^2 -
      (encoding (k+3) (parameter k t 3))^2 =
        24 * X^(k+4) * (C (base t) - X) := by
  dsimp [encoding, parameter, low, middle, high, base]
  simp only [map_mul, map_ofNat, pow_add]
  ring

def value (k : ℕ) (t : ℤ) (j : Fin 4) : ℤ :=
  (encoding (k+3) (parameter k t j)).eval (base t)

lemma value_formula (k : ℕ) (t : ℤ) (j : Fin 4) :
    value k t j = (base t)^(k+3) + 6*(1 + low j*base t +
      middle j*(base t)^2 + 6*t*(base t)^(k+1) +
      high j*t*(base t)^(k+2)) := by
  simp only [value, encoding, parameter, eval_add, eval_pow, eval_X,
    eval_mul, eval_C, eval_one]

lemma collision (k : ℕ) (t : ℤ) :
    value k t 0^2 + value k t 1^2 = value k t 2^2 + value k t 3^2 := by
  have hh := congrArg (Polynomial.eval (base t)) (norm_difference k t)
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_C, eval_ofNat,
    sub_self, mul_zero] at hh
  change value k t 0^2 + value k t 1^2 - value k t 2^2 - value k t 3^2 = 0 at hh
  linarith

lemma positive (k : ℕ) (t : ℤ) (ht : 7 ≤ t) (j : Fin 4) :
    0 < value k t j := by
  have hb : 0 < base t := by dsimp [base]; omega
  have hl : 0 < low j := by fin_cases j <;> decide
  have hm : 0 < middle j := by fin_cases j <;> decide
  have hh : 0 < high j := by fin_cases j <;> decide
  rw [value_formula]
  positivity

lemma ordered_values (k : ℕ) (t : ℤ) (ht : 7 ≤ t) :
    value k t 1 < value k t 3 ∧ value k t 3 < value k t 2 ∧
      value k t 2 < value k t 0 := by
  have hb : 0 < base t := by dsimp [base]; omega
  have hpow : 1 ≤ (base t)^k := one_le_pow₀ (by omega : 1 ≤ base t)
  have hsq : 0 < (base t)^2 := sq_pos_of_pos hb
  have hp : 0 < 12*t*(base t)^k-3 := by nlinarith
  have hm := mul_pos hp hsq
  simp only [value_formula, pow_add]
  dsimp [low, middle, high]
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma value_injective (k : ℕ) (t : ℤ) (ht : 7 ≤ t) :
    Function.Injective (value k t) := by
  have ho := ordered_values k t ht
  intro i j he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; simp only [value_formula] at ho he;
        dsimp [low, middle, high] at ho he; omega)

lemma formal_square_sidon (k : ℕ) (t : ℤ) :
    IsSidon ((univ.image (fun j : Fin 4 =>
      (encoding (k+3) (parameter k t j))^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon (k+3))
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp hf
  exact ⟨parameter k t j, admissible k t j, rfl⟩

/-- In every degree at least three the full canonical-digit formal family
still has a nontrivial square-sum collision after evaluation. -/
theorem specialization_not_sidon (k : ℕ) (t : ℤ) (ht : 7 ≤ t) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value k t j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value k t j^2 ∈ univ.image (fun j : Fin 4 => value k t j^2) :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have h02 : value k t 2^2 < value k t 0^2 :=
    (sq_lt_sq₀ (positive k t ht 2).le (positive k t ht 0).le).mpr
      (ordered_values k t ht).2.2
  have h03 : value k t 3^2 < value k t 0^2 :=
    (sq_lt_sq₀ (positive k t ht 3).le (positive k t ht 0).le).mpr
      ((ordered_values k t ht).2.1.trans (ordered_values k t ht).2.2)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision k t) with h | h <;> omega

end AllDegrees

#print axioms admissible
#print axioms norm_difference
#print axioms discrepancy_ne_zero
#print axioms coefficient_bounds
#print axioms monic_degree
#print axioms collision
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
#print axioms concrete_values
#print axioms value_injective
#print axioms bases_unbounded
#print axioms AllDegrees.canonical_digits
#print axioms AllDegrees.monic_degree
#print axioms AllDegrees.norm_difference
#print axioms AllDegrees.collision
#print axioms AllDegrees.value_injective
#print axioms AllDegrees.formal_square_sidon
#print axioms AllDegrees.specialization_not_sidon
end
end Erdos773.CubicGaussianSpecialization
