import Submission.FormalGaussianSidon

/-!
A cubic obstruction at unbounded powers of the Eisenstein prime itself.
This is not a disproof of Erdős 773.
-/
namespace Erdos773.InertPrimePowerSpecialization
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def base (t : ℤ) : ℤ := (6*t+3)^2

def low (t : ℤ) (j : Fin 4) : ℤ := ![6*t+3, 6*t+5, 6*t+4, 6*t+4] j

def high (t : ℤ) (j : Fin 4) : ℤ :=
  ![3*t^2+3*t, 3*t^2+9*t+4, 3*t^2+6*t+2, 3*t^2+6*t+3] j

def parameter (t : ℤ) (j : Fin 4) : ℤ[X] :=
  1 + C (low t j)*X + C (high t j)*X^2

def E (t : ℤ) (j : Fin 4) : ℤ[X] := encoding 3 (parameter t j)

def value (t : ℤ) (j : Fin 4) : ℤ := (E t j).eval (base t)

lemma admissible (t : ℤ) (j : Fin 4) : Admissible 3 (parameter t j) := by
  constructor
  · dsimp [parameter]; compute_degree; norm_num
  · simp [parameter]

lemma coefficient_formula (t : ℤ) (j : Fin 4) (n : ℕ) :
    (E t j).coeff n = (if n = 3 then 1 else 0) + 6 *
      ((if n = 0 then 1 else 0) + low t j * (if 1 = n then 1 else 0) +
        high t j * (if n = 2 then 1 else 0)) := by
  simp [E, encoding, parameter, coeff_X_pow, coeff_one, coeff_X]

lemma canonical_digits (t : ℤ) (ht : 2 ≤ t) (j : Fin 4) :
    (E t j).coeff 0 = 6 ∧ (E t j).coeff 3 = 1 ∧
      (∀ n ≤ 3, 0 < (E t j).coeff n ∧ (E t j).coeff n < base t) ∧
      (∀ n < 3, (6 : ℤ) ∣ (E t j).coeff n) := by
  have hsq : 2*t ≤ t^2 := by nlinarith [sq_nonneg (t-2)]
  have hb : 6 < base t := by dsimp [base]; nlinarith
  have hl : 0 < 6*low t j ∧ 6*low t j < base t := by
    fin_cases j <;> dsimp [low, base] <;> constructor <;> nlinarith
  have hh : 0 < 6*high t j ∧ 6*high t j < base t := by
    fin_cases j <;> dsimp [high, base] <;> constructor <;> nlinarith
  simp only [coefficient_formula]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro n hn
    interval_cases n <;> norm_num
    all_goals first
      | (constructor <;> linarith [hl.1, hl.2, hh.1, hh.2])
      | linarith
  · intro n hn
    interval_cases n <;> norm_num

lemma monic_degree (t : ℤ) (j : Fin 4) :
    (E t j).Monic ∧ (E t j).natDegree = 3 := by
  have hl : (E t j).natDegree ≤ 3 := by
    dsimp [E, encoding, parameter]; compute_degree
  have hc : (E t j).coeff 3 = 1 := by rw [coefficient_formula]; norm_num
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one 3 hl hc,
    natDegree_eq_of_le_of_coeff_ne_zero hl (by rw [hc]; exact one_ne_zero)⟩

lemma norm_difference (t : ℤ) :
    (E t 0)^2 + (E t 1)^2 - (E t 2)^2 - (E t 3)^2 =
      12*X^4*(C (base t)-X) := by
  dsimp [E, encoding, parameter, low, high, base]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

lemma value_formula (t : ℤ) (j : Fin 4) :
    value t j = (base t)^3 + 6*(1+low t j*base t+high t j*(base t)^2) := by
  simp only [value, E, encoding, parameter, eval_add, eval_pow, eval_X,
    eval_mul, eval_C, eval_one]

lemma collision (t : ℤ) :
    value t 0^2 + value t 1^2 = value t 2^2 + value t 3^2 := by
  have h := congrArg (Polynomial.eval (base t)) (norm_difference t)
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_C,
    eval_ofNat, sub_self, mul_zero] at h
  change value t 0^2 + value t 1^2 - value t 2^2 - value t 3^2 = 0 at h
  linarith

lemma positive (t : ℤ) (ht : 2 ≤ t) (j : Fin 4) : 0 < value t j := by
  have hb : 0 < base t := by dsimp [base]; nlinarith [sq_nonneg (t-2)]
  have hl : 0 < low t j := by fin_cases j <;> dsimp [low] <;> omega
  have hh : 0 < high t j := by fin_cases j <;> dsimp [high] <;> nlinarith [sq_nonneg t]
  rw [value_formula]
  positivity

lemma ordered_values (t : ℤ) (ht : 2 ≤ t) :
    value t 0 < value t 2 ∧ value t 2 < value t 3 ∧ value t 3 < value t 1 := by
  have hb : 0 < base t := by dsimp [base]; nlinarith [sq_nonneg (t-2)]
  have hbsq : 0 < (base t)^2 := sq_pos_of_pos hb
  have hmul : 0 < t*(base t)^2 := mul_pos (by omega) hbsq
  simp only [value_formula]
  dsimp [low, high]
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma formal_square_sidon (t : ℤ) :
    IsSidon ((univ.image (fun j : Fin 4 => (E t j)^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 3)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp hf
  exact ⟨parameter t j, admissible t j, rfl⟩

lemma specialization_not_sidon (t : ℤ) (ht : 2 ≤ t) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value t j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value t j^2 ∈ univ.image (fun j : Fin 4 => value t j^2) :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have h02 : value t 0^2 < value t 2^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 2).le).mpr (ordered_values t ht).1
  have h03 : value t 0^2 < value t 3^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 3).le).mpr
      ((ordered_values t ht).1.trans (ordered_values t ht).2.1)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h <;> omega

/-- This recurrence makes 6*index(k)+3 equal to 3^(k+3). -/
def index : ℕ → ℕ
  | 0 => 4
  | k+1 => 3*index k+1

lemma index_lower (k : ℕ) : k+4 ≤ index k := by
  induction k with
  | zero => simp [index]
  | succ k ih => simp only [index]; omega

lemma index_power (k : ℕ) : 6*(index k : ℤ)+3 = (3 : ℤ)^(k+3) := by
  induction k with
  | zero => norm_num [index]
  | succ k ih =>
    simp only [index, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show k+1+3=(k+3)+1 by omega, pow_succ, ← ih]
    ring

lemma base_power (k : ℕ) : base (index k) = (3 : ℤ)^(2*k+6) := by
  dsimp [base]
  rw [index_power, ← pow_mul]
  congr 1
  omega

/-- Nontrivial specialization collisions at every even power 3^(2k+6). -/
theorem prime_power_failure (k : ℕ) :
    base (index k) = (3 : ℤ)^(2*k+6) ∧
      (∀ j : Fin 4, Admissible 3 (parameter (index k) j)) ∧
      (∀ j : Fin 4, (E (index k) j).coeff 0 = 6 ∧
        (∀ n ≤ 3, 0 < (E (index k) j).coeff n ∧
          (E (index k) j).coeff n < base (index k))) ∧
      IsSidon ((univ.image (fun j : Fin 4 => (E (index k) j)^2)) : Set ℤ[X]) ∧
      ¬IsSidon ((univ.image (fun j : Fin 4 => value (index k) j^2)) : Set ℤ) := by
  have ht : (2 : ℤ) ≤ index k := by exact_mod_cast (show 2 ≤ index k by have := index_lower k; omega)
  refine ⟨base_power k, admissible _, ?_, formal_square_sidon _, specialization_not_sidon _ ht⟩
  intro j
  have hc := canonical_digits (index k) ht j
  exact ⟨hc.1, hc.2.2.1⟩

lemma prime_power_bases_unbounded (L : ℤ) : ∃ k : ℕ, L < base (index k) := by
  refine ⟨L.toNat, ?_⟩
  have hl : L ≤ (L.toNat : ℤ) := Int.self_le_toNat L
  have hi : (L.toNat : ℤ)+4 ≤ index L.toNat := by exact_mod_cast index_lower L.toNat
  have hn : (0 : ℤ) ≤ L.toNat := Int.natCast_nonneg _
  dsimp [base]
  nlinarith [sq_nonneg (6*(index L.toNat : ℤ)+2)]

#print axioms canonical_digits
#print axioms monic_degree
#print axioms norm_difference
#print axioms collision
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
#print axioms prime_power_failure
#print axioms prime_power_bases_unbounded
end
end Erdos773.InertPrimePowerSpecialization
