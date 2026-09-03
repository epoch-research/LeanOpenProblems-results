import Submission.FormalGaussianSidon

/-!
Fixed constant, positive canonical digits, and three distinct negative real roots
still do not make evaluation preserve the formal Gaussian Sidon construction.
This is a construction obstruction, not a disproof of Erdős 773.
-/
namespace Erdos773.NegativeRootGaussianSpecialization
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma root_between {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Continuous f) (ha : f a < 0) (hb : 0 < f b) :
    ∃ x, a < x ∧ x < b ∧ f x = 0 := by
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc hab.le hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f a) (f b) from ⟨ha.le, hb.le⟩)
  refine ⟨x, ?_, ?_, he⟩
  · have hne : a ≠ x := by intro h; subst x; linarith
    exact lt_of_le_of_ne hx.1 hne
  · have hne : x ≠ b := by intro h; subst x; linarith
    exact lt_of_le_of_ne hx.2 hne

lemma cubic_factorization {A C x y z : ℝ}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hx : x^3 + A*x^2 + C*x + 6 = 0)
    (hy : y^3 + A*y^2 + C*y + 6 = 0)
    (hz : z^3 + A*z^2 + C*z + 6 = 0) :
    ∀ t : ℝ, t^3 + A*t^2 + C*t + 6 = (t-x)*(t-y)*(t-z) := by
  have h1 : x^2 + x*y + y^2 + A*(x+y) + C = 0 := by
    apply (mul_eq_zero.mp (show (x-y)*(x^2+x*y+y^2+A*(x+y)+C) = 0 by
      linear_combination hx - hy)).resolve_left
    exact sub_ne_zero.mpr hxy
  have h2 : x^2 + x*z + z^2 + A*(x+z) + C = 0 := by
    apply (mul_eq_zero.mp (show (x-z)*(x^2+x*z+z^2+A*(x+z)+C) = 0 by
      linear_combination hx - hz)).resolve_left
    exact sub_ne_zero.mpr hxz
  have hsum : x+y+z+A = 0 := by
    apply (mul_eq_zero.mp (show (y-z)*(x+y+z+A) = 0 by
      linear_combination h1 - h2)).resolve_left
    exact sub_ne_zero.mpr hyz
  have hpair : x*y+x*z+y*z-C = 0 := by
    linear_combination (x+y)*hsum - h1
  have hprod : x*y*z+6 = 0 := by
    linear_combination hx - x^2*hsum + x*hpair
  intro t
  linear_combination t^2*hsum - t*hpair + hprod

/-- A rational sign certificate gives complete real factorization, not
merely numerical approximations to three roots. -/
lemma cubic_negative_roots {A C : ℝ} (hA : 5 < A)
    (ha : (-A)^3 + A*(-A)^2 + C*(-A) + 6 < 0)
    (hb : 0 < (-5)^3 + A*(-5)^2 + C*(-5) + 6)
    (hc : (-1/5)^3 + A*(-1/5)^2 + C*(-1/5) + 6 < 0) :
    ∃ x y z : ℝ, x < y ∧ y < z ∧ z < 0 ∧
      ∀ t : ℝ, t^3 + A*t^2 + C*t + 6 = (t-x)*(t-y)*(t-z) := by
  let f : ℝ → ℝ := fun t => t^3 + A*t^2 + C*t + 6
  have hf : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨x, hx1, hx2, hx⟩ := root_between (neg_lt_neg hA) hf ha hb
  obtain ⟨y, hy1, hy2, hy⟩ := root_between (by norm_num : (-5 : ℝ) < -1/5)
    hf.neg (by dsimp [f]; linarith) (by dsimp [f]; linarith)
  obtain ⟨z, hz1, hz2, hz⟩ := root_between (by norm_num : (-1/5 : ℝ) < 0)
    hf hc (by norm_num [f])
  have hxy : x < y := hx2.trans hy1
  have hyz : y < z := hy2.trans hz1
  refine ⟨x, y, z, hxy, hyz, hz2, ?_⟩
  apply cubic_factorization hxy.ne hyz.ne (hxy.trans hyz).ne hx _ hz
  change -(f y) = 0 at hy
  dsimp only [f] at hy
  linarith

def low (j : Fin 4) : ℤ := ![33, 34, 11, 56] j

def high (j : Fin 4) : ℤ := ![9, 66, 18, 60] j

def parameter (j : Fin 4) : ℤ[X] := 1 + C (low j)*X + C (high j)*X^2

def E (j : Fin 4) : ℤ[X] := encoding 3 (parameter j)

def value (j : Fin 4) : ℤ := (E j).eval 509

lemma admissible (j : Fin 4) : Admissible 3 (parameter j) := by
  constructor
  · dsimp [parameter]; compute_degree; norm_num
  · simp [parameter]

lemma coefficient_formula (j : Fin 4) (n : ℕ) :
    (E j).coeff n = (if n = 3 then 1 else 0) + 6 *
      ((if n = 0 then 1 else 0) + low j * (if 1 = n then 1 else 0) +
        high j * (if n = 2 then 1 else 0)) := by
  simp [E, encoding, parameter, coeff_X_pow, coeff_one, coeff_X]

lemma canonical_digits (j : Fin 4) :
    (E j).coeff 0 = 6 ∧ (E j).coeff 3 = 1 ∧
      (∀ n ≤ 3, 0 < (E j).coeff n ∧ (E j).coeff n < 509) ∧
      (∀ n < 3, (6 : ℤ) ∣ (E j).coeff n) := by
  simp only [coefficient_formula]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro n hn
    interval_cases n <;> fin_cases j <;> norm_num [low, high]
  · intro n hn
    interval_cases n <;> norm_num

lemma real_factorization (j : Fin 4) :
    ∃ x y z : ℝ, x < y ∧ y < z ∧ z < 0 ∧
      ∀ t : ℝ, (E j).eval₂ (Int.castRingHom ℝ) t = (t-x)*(t-y)*(t-z) := by
  have h : ∃ x y z : ℝ, x < y ∧ y < z ∧ z < 0 ∧
      ∀ t : ℝ, t^3 + (6*high j : ℤ)*t^2 + (6*low j : ℤ)*t + 6 =
        (t-x)*(t-y)*(t-z) := by
    fin_cases j <;> apply cubic_negative_roots <;> norm_num [low, high]
  obtain ⟨x,y,z,hxy,hyz,hz,he⟩ := h
  refine ⟨x,y,z,hxy,hyz,hz,?_⟩
  intro t
  rw [← he t]
  simp only [E, encoding, parameter, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_C, eval₂_one, Int.cast_mul, Int.cast_ofNat]
  change t^3 + 6*(1+(low j : ℝ)*t+(high j : ℝ)*t^2) = _
  ring

lemma base_prime : Nat.Prime 509 := by decide

lemma norm_difference :
    (E 0)^2 + (E 1)^2 - (E 2)^2 - (E 3)^2 =
      36*X^2*(509-X)*(X^2-4*X-2) := by
  dsimp [E, encoding, parameter, low, high]
  norm_num
  ring

lemma concrete_values : value = ![145963391, 234572147, 159886577, 225312419] := by
  funext j
  fin_cases j <;> norm_num [value, E, encoding, parameter, low, high]

lemma collision : value 0^2 + value 1^2 = value 2^2 + value 3^2 := by
  rw [concrete_values]
  change (145963391 : ℤ)^2 + 234572147^2 = 159886577^2 + 225312419^2
  norm_num

lemma formal_square_sidon :
    IsSidon ((univ.image (fun j : Fin 4 => (E j)^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 3)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp hf
  exact ⟨parameter j, admissible j, rfl⟩

/-- These four admissible polynomials have three distinct negative real roots,
but their squared values at the prime base 509 are not Sidon. -/
theorem specialization_not_sidon :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value j^2 ∈ univ.image (fun j : Fin 4 => value j^2) :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have hc := hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) collision
  rw [concrete_values] at hc
  change ((145963391 : ℤ)^2 = 159886577^2 ∧ 234572147^2 = 225312419^2) ∨
    (145963391^2 = 225312419^2 ∧ 234572147^2 = 159886577^2) at hc
  norm_num at hc

#print axioms cubic_negative_roots
#print axioms canonical_digits
#print axioms real_factorization
#print axioms base_prime
#print axioms norm_difference
#print axioms collision
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
end
end Erdos773.NegativeRootGaussianSpecialization
