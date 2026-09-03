import Submission.FormalGaussianSidon

/-!
A quartic specialization obstruction at arbitrarily large prime bases congruent
 to one modulo 540. This refutes a sufficient digit rule, not Erdős 773.
-/
namespace Erdos773.QuarticPrimeCarry
open Polynomial Finset FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000

def base (k : ℤ) : ℤ := 540*k+1

def low (k : ℤ) : Fin 4 → ℤ := ![39*k+18,39*k+31,39*k+30,39*k+19]
def middle (k : ℤ) : Fin 4 → ℤ := ![77*k-7,5*k+22,5*k+4,77*k+23]
def high (k : ℤ) : Fin 4 → ℤ := ![4,60*k+7,60*k+7,4]

def parameter (k : ℤ) (j : Fin 4) : ℤ[X] :=
  1+C (low k j)*X+C (middle k j)*X^2+C (high k j)*X^3

def value (k : ℤ) (j : Fin 4) : ℤ :=
  (encoding 4 (parameter k j)).eval (base k)

lemma admissible (k : ℤ) (j : Fin 4) : Admissible 4 (parameter k j) := by
  fin_cases j <;> constructor
  all_goals first
    | (dsimp [parameter]; compute_degree <;> norm_num)
    | norm_num [parameter]

lemma coefficient_formula (k : ℤ) (j : Fin 4) (n : ℕ) :
    (encoding 4 (parameter k j)).coeff n =
      (if n=4 then 1 else 0)+6*((if n=0 then 1 else 0)+
        low k j*(if 1=n then 1 else 0)+middle k j*(if n=2 then 1 else 0)+
          high k j*(if n=3 then 1 else 0)) := by
  simp only [encoding,parameter,coeff_add,coeff_X_pow,coeff_C_mul,coeff_one,coeff_X]

lemma digit_bounds (k : ℤ) (hk : 2≤k) (j : Fin 4) :
    0<6*low k j ∧ 6*low k j<base k ∧
    0<6*middle k j ∧ 6*middle k j<base k ∧
    0<6*high k j ∧ 6*high k j<base k := by
  fin_cases j <;> dsimp [low,middle,high,base] <;> omega

lemma canonical_digits (k : ℤ) (hk : 2≤k) (j : Fin 4) :
    (encoding 4 (parameter k j)).coeff 0=6 ∧
    (encoding 4 (parameter k j)).coeff 4=1 ∧
    (∀ n<4, 0<(encoding 4 (parameter k j)).coeff n ∧
      (encoding 4 (parameter k j)).coeff n<base k ∧
      (6:ℤ) ∣ (encoding 4 (parameter k j)).coeff n) := by
  have hh := digit_bounds k hk j
  refine ⟨by norm_num [coefficient_formula],by norm_num [coefficient_formula],?_⟩
  intro n hn
  interval_cases n <;> simp only [coefficient_formula] <;> norm_num
  · dsimp [base]; omega
  · omega
  · omega
  · omega

lemma monic_degree (k : ℤ) (j : Fin 4) :
    (encoding 4 (parameter k j)).Monic ∧
      (encoding 4 (parameter k j)).natDegree=4 := by
  have hl : (encoding 4 (parameter k j)).natDegree≤4 := by
    fin_cases j <;> dsimp [encoding,parameter] <;> compute_degree
  have hc : (encoding 4 (parameter k j)).coeff 4=1 := by
    norm_num [coefficient_formula]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one 4 hl hc,
    natDegree_eq_of_le_of_coeff_ne_zero hl (by rw [hc]; exact one_ne_zero)⟩

lemma norm_difference (k : ℤ) :
    (encoding 4 (parameter k 0))^2+(encoding 4 (parameter k 1))^2-
      (encoding 4 (parameter k 2))^2-(encoding 4 (parameter k 3))^2 =
        72*X^3*(C (base k)-X)*(2*X^2-4*X-1) := by
  dsimp [encoding,parameter,low,middle,high,base]
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one]
  ring

lemma discrepancy_ne_zero (k : ℤ) :
    (encoding 4 (parameter k 0))^2+(encoding 4 (parameter k 1))^2-
      (encoding 4 (parameter k 2))^2-(encoding 4 (parameter k 3))^2 ≠ 0 := by
  rw [norm_difference]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (pow_ne_zero _ X_ne_zero)
    · intro h
      have hh := congrArg (fun P : ℤ[X] => P.coeff 1) h
      simp only [coeff_sub,coeff_C,coeff_X,coeff_zero] at hh
      norm_num at hh
  · intro h
    have hh := congrArg (Polynomial.eval (0 : ℤ)) h
    norm_num at hh

lemma collision (k : ℤ) : value k 0^2+value k 1^2=value k 2^2+value k 3^2 := by
  have hh := congrArg (Polynomial.eval (base k)) (norm_difference k)
  simp only [eval_sub,eval_add,eval_pow,eval_mul,eval_X,eval_C,eval_ofNat,
    sub_self,mul_zero,zero_mul] at hh
  change value k 0^2+value k 1^2-value k 2^2-value k 3^2=0 at hh
  linarith

lemma value_formula (k : ℤ) (j : Fin 4) :
    value k j=(base k)^4+6*(1+low k j*base k+
      middle k j*(base k)^2+high k j*(base k)^3) := by
  simp only [value,encoding,parameter,eval_add,eval_pow,eval_X,eval_mul,eval_C,eval_one]

lemma positive (k : ℤ) (hk : 2≤k) (j : Fin 4) : 0<value k j := by
  have hb : 0<base k := by dsimp [base]; omega
  obtain ⟨hl,_,hm,_,hh,_⟩ := digit_bounds k hk j
  have hl' : 0<low k j := by omega
  have hm' : 0 < middle k j := by omega
  have hh' : 0<high k j := by omega
  rw [value_formula]
  positivity

lemma ordered_values (k : ℤ) (hk : 2≤k) :
    value k 0<value k 3 ∧ value k 3<value k 2 ∧ value k 2<value k 1 := by
  have hb : 2≤base k := by dsimp [base]; omega
  have h03 : value k 3-value k 0=6*base k*(30*base k+1) := by
    simp only [value_formula]
    dsimp [low,middle,high]
    ring
  have h21 : value k 1-value k 2=6*base k*(18*base k+1) := by
    simp only [value_formula]
    dsimp [low,middle,high]
    ring
  have h32 : value k 2-value k 3=
      6*base k*(((60*k+3)*base k-(72*k+19))*base k+11) := by
    simp only [value_formula]
    dsimp [low,middle,high]
    ring
  have hc : 0<(60*k+3)*base k-(72*k+19) := by nlinarith
  have hp03 : 0<value k 3-value k 0 := by rw [h03]; positivity
  have hp21 : 0<value k 1-value k 2 := by rw [h21]; positivity
  have hp32 : 0<value k 2-value k 3 := by rw [h32]; positivity
  omega

lemma value_injective (k : ℤ) (hk : 2≤k) : Function.Injective (value k) := by
  have hh := ordered_values k hk
  intro i j he
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at he ⊢ <;> first | rfl | omega

lemma formal_square_sidon (k : ℤ) :
    IsSidon ((univ.image (fun j : Fin 4 => (encoding 4 (parameter k j))^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 4)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j,_,rfl⟩ := mem_image.mp hf
  exact ⟨parameter k j,admissible k j,rfl⟩

theorem specialization_not_sidon (k : ℤ) (hk : 2≤k) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value k j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value k j^2 ∈ univ.image (fun j : Fin 4 => value k j^2) :=
    mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have ho := ordered_values k hk
  have h02 : value k 0^2<value k 2^2 :=
    (sq_lt_sq₀ (positive k hk 0).le (positive k hk 2).le).mpr (ho.1.trans ho.2.1)
  have h03 : value k 0^2<value k 3^2 :=
    (sq_lt_sq₀ (positive k hk 0).le (positive k hk 3).le).mpr ho.1
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision k) with h | h <;> omega

lemma height_bounds (k : ℤ) (hk : 2≤k) (j : Fin 4) :
    (base k)^4≤value k j ∧ value k j<2*(base k)^4 := by
  have hB : 6<base k := by dsimp [base]; omega
  obtain ⟨hl,hlB,hm,hmB,hh,hhB⟩ := digit_bounds k hk j
  have h0 : 0≤base k := by omega
  have h1 := mul_nonneg (show 0≤base k-1-6*low k j by omega) h0
  have h2 := mul_nonneg (show 0≤base k-1-6*middle k j by omega) (sq_nonneg (base k))
  have h3 := mul_nonneg (show 0≤base k-1-6*high k j by omega) (pow_nonneg h0 3)
  have h4 := mul_nonneg hl.le h0
  have h5 := mul_nonneg hm.le (sq_nonneg (base k))
  have h6 := mul_nonneg hh.le (pow_nonneg h0 3)
  rw [value_formula]
  constructor <;> nlinarith

def naturalValue (k : ℤ) (j : Fin 4) : ℕ := (value k j).toNat

lemma naturalValue_cast (k : ℤ) (hk : 2≤k) (j : Fin 4) :
    (naturalValue k j : ℤ)=value k j := Int.toNat_of_nonneg (positive k hk j).le

lemma natural_collision (k : ℤ) (hk : 2≤k) :
    naturalValue k 0^2+naturalValue k 1^2=
      naturalValue k 2^2+naturalValue k 3^2 := by
  have hh := collision k
  simp only [← naturalValue_cast k hk] at hh
  exact_mod_cast hh

theorem natural_specialization_not_sidon (k : ℤ) (hk : 2≤k) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => naturalValue k j^2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : naturalValue k j^2 ∈ univ.image (fun j : Fin 4 => naturalValue k j^2) :=
    mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have ho := ordered_values k hk
  have h02 : value k 0^2<value k 2^2 :=
    (sq_lt_sq₀ (positive k hk 0).le (positive k hk 2).le).mpr (ho.1.trans ho.2.1)
  have h03 : value k 0^2<value k 3^2 :=
    (sq_lt_sq₀ (positive k hk 0).le (positive k hk 3).le).mpr ho.1
  have h02' : naturalValue k 0^2<naturalValue k 2^2 := by
    exact_mod_cast (by simpa only [naturalValue_cast k hk,Int.natCast_pow] using h02 :
      (naturalValue k 0:ℤ)^2<(naturalValue k 2:ℤ)^2)
  have h03' : naturalValue k 0^2<naturalValue k 3^2 := by
    exact_mod_cast (by simpa only [naturalValue_cast k hk,Int.natCast_pow] using h03 :
      (naturalValue k 0:ℤ)^2<(naturalValue k 3:ℤ)^2)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (natural_collision k hk) with h | h <;> omega

lemma arbitrarily_large_prime (M : ℕ) :
    ∃ k : ℕ, 2≤k ∧ M<540*k+1 ∧ Nat.Prime (540*k+1) := by
  obtain ⟨p,hp,hprime,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max M 1080) (by norm_num : (540:ℕ)≠0) (show Nat.Coprime 1 540 by norm_num)
  have hrem : p%540=1 := by simpa only [Nat.ModEq] using hmod
  have he : 540*(p/540)+1=p := by omega
  refine ⟨p/540,by omega,?_,?_⟩
  · rw [he]
    exact (le_max_left _ _).trans_lt hp
  · rwa [he]

/-- Even arbitrarily large prime bases in this coprime progression have the
quartic carry obstruction. The final property is not about the original
maximum-cardinality conjecture. -/
theorem arbitrarily_large_prime_obstruction (M : ℕ) :
    ∃ k : ℕ, 2≤k ∧ M<540*k+1 ∧ Nat.Prime (540*k+1) ∧
      ¬IsSidon ((univ.image (fun j : Fin 4 => value (k:ℤ) j^2)) : Set ℤ) := by
  obtain ⟨k,hk,hM,hp⟩ := arbitrarily_large_prime M
  exact ⟨k,hk,hM,hp,specialization_not_sidon k (by exact_mod_cast hk)⟩

#print axioms height_bounds
#print axioms natural_specialization_not_sidon
#print axioms canonical_digits
#print axioms norm_difference
#print axioms value_injective
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
#print axioms arbitrarily_large_prime_obstruction
end
end Erdos773.QuarticPrimeCarry
