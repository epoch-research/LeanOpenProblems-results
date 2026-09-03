import Submission.FormalGaussianSidon

/-! An unbounded family of carry obstructions at bases congruent to 1 modulo 6.
This disproves a sufficient digit criterion, not Erdős 773. -/
namespace Erdos773.OneModSixCarry
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def base (s : ℤ) : ℤ := 2304*s^2+4704*s+2395

def low (s : ℤ) (j : Fin 3) : ℤ :=
  ![96*s^2+234*s+140, 192*s^2+428*s+238, 288*s^2+622*s+336] j

def mid (s : ℤ) (j : Fin 3) : ℤ :=
  ![138*s^2+322*s+186, 222*s^2+496*s+276, 282*s^2+622*s+342] j

def high (s : ℤ) (j : Fin 3) : ℤ := ![10*s+11, 12*s+13, 14*s+15] j

def parameter (s : ℤ) (j : Fin 3) : ℤ[X] :=
  1+C (low s j)*X+C (mid s j)*X^2+C (high s j)*X^3

def E (s : ℤ) (j : Fin 3) : ℤ[X] := encoding 4 (parameter s j)

def value (s : ℤ) (j : Fin 3) : ℤ := (E s j).eval (base s)

lemma admissible (s : ℤ) (j : Fin 3) : Admissible 4 (parameter s j) := by
  constructor
  · dsimp [parameter]; compute_degree; norm_num
  · simp [parameter]

lemma coefficient_formula (s : ℤ) (j : Fin 3) (n : ℕ) :
    (E s j).coeff n = (if n = 4 then 1 else 0)+6 *
      ((if n = 0 then 1 else 0)+low s j*(if 1 = n then 1 else 0)+
        mid s j*(if n = 2 then 1 else 0)+high s j*(if n = 3 then 1 else 0)) := by
  simp [E, encoding, parameter, coeff_X_pow, coeff_one, coeff_X]

lemma base_lower (s : ℤ) (hs : 0 ≤ s) : 6 < base s := by
  dsimp [base]; nlinarith [sq_nonneg s]

lemma canonical_digits (s : ℤ) (hs : 0 ≤ s) (j : Fin 3) :
    (E s j).coeff 0 = 6 ∧ (E s j).coeff 4 = 1 ∧
      (∀ n ≤ 4, 0 < (E s j).coeff n ∧ (E s j).coeff n < base s) ∧
      (∀ n < 4, (6 : ℤ) ∣ (E s j).coeff n) := by
  have hl : 0 < 6*low s j ∧ 6*low s j < base s := by
    fin_cases j <;> dsimp [low, base] <;> constructor <;> nlinarith [sq_nonneg s]
  have hm : 0 < 6*mid s j ∧ 6*mid s j < base s := by
    fin_cases j <;> dsimp [mid, base] <;> constructor <;> nlinarith [sq_nonneg s]
  have hh : 0 < 6*high s j ∧ 6*high s j < base s := by
    fin_cases j <;> dsimp [high, base] <;> constructor <;> nlinarith [sq_nonneg s]
  have hb := base_lower s hs
  simp only [coefficient_formula]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro n hn
    interval_cases n <;> norm_num
    all_goals first
      | (constructor <;> linarith [hl.1, hl.2, hm.1, hm.2, hh.1, hh.2])
      | linarith
  · intro n hn
    interval_cases n <;> norm_num

lemma monic_degree (s : ℤ) (j : Fin 3) :
    (E s j).Monic ∧ (E s j).natDegree = 4 := by
  have hl : (E s j).natDegree ≤ 4 := by
    dsimp [E, encoding, parameter]; compute_degree
  have hc : (E s j).coeff 4 = 1 := by rw [coefficient_formula]; norm_num
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one 4 hl hc,
    natDegree_eq_of_le_of_coeff_ne_zero hl (by rw [hc]; exact one_ne_zero)⟩

lemma norm_difference (s : ℤ) :
    (E s 0)^2+(E s 2)^2-2*(E s 1)^2 =
      C (288*(s+1)^2)*X^2*(C (base s)-X)*(X+1) := by
  dsimp [E, encoding, parameter, low, mid, high, base]
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
  ring

lemma value_formula (s : ℤ) (j : Fin 3) :
    value s j = (base s)^4 + 6*(1+low s j*base s+
      mid s j*(base s)^2+high s j*(base s)^3) := by
  simp only [value, E, encoding, parameter, eval_add, eval_pow, eval_X,
    eval_mul, eval_C, eval_one]

lemma collision (s : ℤ) : value s 0^2+value s 2^2 = value s 1^2+value s 1^2 := by
  have h := congrArg (Polynomial.eval (base s)) (norm_difference s)
  simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_C,
    eval_ofNat, sub_self, mul_zero, zero_mul] at h
  change value s 0^2+value s 2^2-2*value s 1^2 = 0 at h
  linarith

lemma positive (s : ℤ) (hs : 0 ≤ s) (j : Fin 3) : 0 < value s j := by
  have hb : 0 < base s := lt_trans (by norm_num) (base_lower s hs)
  have hl : 0 < low s j := by fin_cases j <;> dsimp [low] <;> nlinarith [sq_nonneg s]
  have hm : 0 < mid s j := by fin_cases j <;> dsimp [mid] <;> nlinarith [sq_nonneg s]
  have hh : 0 < high s j := by fin_cases j <;> dsimp [high] <;> omega
  rw [value_formula]
  positivity

lemma ordered_values (s : ℤ) (hs : 0 ≤ s) :
    value s 0 < value s 1 ∧ value s 1 < value s 2 := by
  have hb : 0 < base s := lt_trans (by norm_num) (base_lower s hs)
  have hl01 : low s 0 < low s 1 := by dsimp [low]; nlinarith [sq_nonneg s]
  have hl12 : low s 1 < low s 2 := by dsimp [low]; nlinarith [sq_nonneg s]
  have hm01 : mid s 0 < mid s 1 := by dsimp [mid]; nlinarith [sq_nonneg s]
  have hm12 : mid s 1 < mid s 2 := by dsimp [mid]; nlinarith [sq_nonneg s]
  have hh01 : high s 0 < high s 1 := by dsimp [high]; omega
  have hh12 : high s 1 < high s 2 := by dsimp [high]; omega
  have hb2 : 0 < (base s)^2 := pow_pos hb _
  have hb3 : 0 < (base s)^3 := pow_pos hb _
  constructor
  · simp only [value_formula]
    nlinarith [mul_lt_mul_of_pos_right hl01 hb, mul_lt_mul_of_pos_right hm01 hb2,
      mul_lt_mul_of_pos_right hh01 hb3]
  · simp only [value_formula]
    nlinarith [mul_lt_mul_of_pos_right hl12 hb, mul_lt_mul_of_pos_right hm12 hb2,
      mul_lt_mul_of_pos_right hh12 hb3]

lemma formal_square_sidon (s : ℤ) :
    IsSidon ((univ.image (fun j : Fin 3 => (E s j)^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 4)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp hf
  exact ⟨parameter s j, admissible s j, rfl⟩

lemma specialization_not_sidon (s : ℤ) (hs : 0 ≤ s) :
    ¬IsSidon ((univ.image (fun j : Fin 3 => value s j^2)) : Set ℤ) := by
  intro hsid
  have hm (j : Fin 3) : value s j^2 ∈ univ.image (fun j : Fin 3 => value s j^2) :=
    mem_image.mpr ⟨j, mem_univ _, rfl⟩
  have h01 : value s 0^2 < value s 1^2 :=
    (sq_lt_sq₀ (positive s hs 0).le (positive s hs 1).le).mpr (ordered_values s hs).1
  rcases hsid _ (hm 0) _ (hm 1) _ (hm 2) _ (hm 1) (collision s) with h | h <;> omega

lemma base_mod_six (s : ℤ) : base s % 6 = 1 := by
  simp [base, Int.add_emod, Int.mul_emod]

lemma bases_unbounded (L : ℤ) : ∃ s : ℤ, 0 ≤ s ∧ L < base s := by
  refine ⟨L.toNat, Int.natCast_nonneg _, ?_⟩
  have hl := Int.self_le_toNat L
  have hn := Int.natCast_nonneg L.toNat
  dsimp [base]
  nlinarith [sq_nonneg (L.toNat : ℤ)]

#print axioms canonical_digits
#print axioms norm_difference
#print axioms collision
#print axioms specialization_not_sidon
#print axioms base_mod_six
#print axioms bases_unbounded
end
end Erdos773.OneModSixCarry
