import Submission.FormalGaussianSidon

/-!
An obstruction to a combined digit criterion, not a disproof of Erdős 773.
The base is 3^14, the constant digit is 24, all lower digits are divisible
by 6, and the common squared-digit norm is prime. The digit histograms
agree, but the evaluated squares have a nontrivial equal sum.
-/
namespace Erdos773.PrimePowerEnergyCarry
open Finset Polynomial
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def words (u v : ℕ) : Fin 4 → Fin 21 → ℕ := ![
  ![24,12,36,24,2*v,72,12,132,72,6*v,120,84,156,120,10*v,12*u,6*u,18*u,12*u,0,1],
  ![24,36,12,24,2*v,120,156,84,120,10*v,72,132,12,72,6*v,12*u,18*u,6*u,12*u,0,1],
  ![24,36,12,24,2*v,72,132,12,72,6*v,120,156,84,120,10*v,12*u,18*u,6*u,12*u,0,1],
  ![24,12,36,24,2*v,120,84,156,120,10*v,72,12,132,72,6*v,12*u,6*u,18*u,12*u,0,1]]

def value (u v B : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 21, words u v j i * B ^ i.val

lemma histogram (u v : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words u v j)) (List.ofFn (words u v 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [words, List.ofFn_succ, List.count_cons] <;> omega

lemma digit_sum (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 21, words u v j i) = 865 + 48*u + 18*v := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_energy (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 21, words u v j i ^ 2) = 90721 + 648*u^2 + 140*v^2 := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma value_expand_0 (u v B : ℕ) : value u v B 0 =
    (24) * B^0 +
    (12) * B^1 +
    (36) * B^2 +
    (24) * B^3 +
    (2*v) * B^4 +
    (72) * B^5 +
    (12) * B^6 +
    (132) * B^7 +
    (72) * B^8 +
    (6*v) * B^9 +
    (120) * B^10 +
    (84) * B^11 +
    (156) * B^12 +
    (120) * B^13 +
    (10*v) * B^14 +
    (12*u) * B^15 +
    (6*u) * B^16 +
    (18*u) * B^17 +
    (12*u) * B^18 +
    (0) * B^19 +
    (1) * B^20 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_1 (u v B : ℕ) : value u v B 1 =
    (24) * B^0 +
    (36) * B^1 +
    (12) * B^2 +
    (24) * B^3 +
    (2*v) * B^4 +
    (120) * B^5 +
    (156) * B^6 +
    (84) * B^7 +
    (120) * B^8 +
    (10*v) * B^9 +
    (72) * B^10 +
    (132) * B^11 +
    (12) * B^12 +
    (72) * B^13 +
    (6*v) * B^14 +
    (12*u) * B^15 +
    (18*u) * B^16 +
    (6*u) * B^17 +
    (12*u) * B^18 +
    (0) * B^19 +
    (1) * B^20 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_2 (u v B : ℕ) : value u v B 2 =
    (24) * B^0 +
    (36) * B^1 +
    (12) * B^2 +
    (24) * B^3 +
    (2*v) * B^4 +
    (72) * B^5 +
    (132) * B^6 +
    (12) * B^7 +
    (72) * B^8 +
    (6*v) * B^9 +
    (120) * B^10 +
    (156) * B^11 +
    (84) * B^12 +
    (120) * B^13 +
    (10*v) * B^14 +
    (12*u) * B^15 +
    (18*u) * B^16 +
    (6*u) * B^17 +
    (12*u) * B^18 +
    (0) * B^19 +
    (1) * B^20 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_3 (u v B : ℕ) : value u v B 3 =
    (24) * B^0 +
    (12) * B^1 +
    (36) * B^2 +
    (24) * B^3 +
    (2*v) * B^4 +
    (120) * B^5 +
    (84) * B^6 +
    (156) * B^7 +
    (120) * B^8 +
    (10*v) * B^9 +
    (72) * B^10 +
    (12) * B^11 +
    (132) * B^12 +
    (72) * B^13 +
    (6*v) * B^14 +
    (12*u) * B^15 +
    (6*u) * B^16 +
    (18*u) * B^17 +
    (12*u) * B^18 +
    (0) * B^19 +
    (1) * B^20 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma norm_difference_factor (u v B : ℕ) :
    (value u v B 0 : ℤ)^2 + (value u v B 1 : ℤ)^2 -
      (value u v B 2 : ℤ)^2 - (value u v B 3 : ℤ)^2 =
      96 * (B : ℤ)^25 * ((u : ℤ)*v-B) * ((B : ℤ)-1) * ((B : ℤ)^5-1) := by
  rw [value_expand_0, value_expand_1, value_expand_2, value_expand_3]
  push_cast
  ring

lemma collision (u v B : ℕ) (hB : B = u*v) :
    value u v B 0 ^ 2 + value u v B 1 ^ 2 =
      value u v B 2 ^ 2 + value u v B 3 ^ 2 := by
  have h := norm_difference_factor u v B
  have hB' : (B : ℤ) = (u : ℤ)*v := by exact_mod_cast hB
  rw [hB', sub_self] at h
  simp only [mul_zero, zero_mul] at h
  have hh : (value u v B 0 : ℤ)^2 + (value u v B 1 : ℤ)^2 =
      (value u v B 2 : ℤ)^2 + (value u v B 3 : ℤ)^2 := by omega
  exact_mod_cast hh

abbrev base : ℕ := 4782969
abbrev w := words 2187 2187
abbrev root := value 2187 2187 base

lemma base_is_prime_power : base = 3^14 := by norm_num

lemma energy_prime : Nat.Prime 3769070293 := by norm_num

lemma concrete_digit_conditions : ∀ j : Fin 4,
    w j 20 = 1 ∧ w j 0 = 24 ∧
      (∀ i : Fin 21, 2*w j i < base ∧ (i.val < 20 → 6 ∣ w j i)) ∧
      (∑ i : Fin 21, w j i) < base := by
  decide +kernel

lemma concrete_energy (j : Fin 4) :
    (∑ i : Fin 21, w j i ^ 2) = 3769070293 := by
  rw [digit_energy]
  norm_num

lemma roots_distinct : Function.Injective root := by
  decide +kernel

lemma roots_gcd : Nat.gcd (Nat.gcd (root 0) (root 1))
    (Nat.gcd (root 2) (root 3)) = 3 := by
  decide +kernel

lemma not_sidon : ¬ IsSidon
    (((univ : Finset (Fin 4)).image (fun j => root j ^ 2)) : Set ℕ) := by
  intro hs
  have h := hs (root 0 ^ 2) (by simp) (root 2 ^ 2) (by simp)
    (root 1 ^ 2) (by simp) (root 3 ^ 2) (by simp)
    (collision 2187 2187 base (by norm_num))
  have h02 : root 0 ^ 2 ≠ root 2 ^ 2 := by decide +kernel
  have h03 : root 0 ^ 2 ≠ root 3 ^ 2 := by decide +kernel
  rcases h with h | h
  · exact h02 h.1
  · exact h03 h.1

noncomputable def poly (j : Fin 4) : ℤ[X] :=
  ∑ i : Fin 21, C (w j i : ℤ)*X^i.val

noncomputable def parameter (j : Fin 4) : ℤ[X] :=
  ∑ i : Fin 20, C ((w j i.castSucc / 6 : ℕ) : ℤ)*X^i.val

lemma admissible (j : Fin 4) : FormalGaussianSidon.Admissible 20 (parameter j) := by
  constructor
  · fin_cases j <;> simp [parameter, words, Fin.sum_univ_succ] <;> compute_degree <;> norm_num
  · fin_cases j <;> norm_num [parameter, words, Fin.sum_univ_succ]

lemma poly_encoding (j : Fin 4) :
    poly j = FormalGaussianSidon.encoding 20 (parameter j) := by
  fin_cases j <;>
    norm_num [poly, parameter, words, FormalGaussianSidon.encoding, Fin.sum_univ_succ] <;>
    ring

lemma poly_eval (j : Fin 4) : (poly j).eval (base : ℤ) = (root j : ℤ) := by
  change (∑ i : Fin 21, C (w j i : ℤ)*X^i.val).eval (base : ℤ) =
    ((∑ i : Fin 21, w j i * base^i.val : ℕ) : ℤ)
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

lemma formal_sidon : IsSidon
    (((univ : Finset (Fin 4)).image (fun j => (poly j)^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (FormalGaussianSidon.formal_sidon 20)
  intro f hf
  obtain ⟨j, _, rfl⟩ := mem_image.mp (mem_coe.mp hf)
  exact ⟨parameter j, admissible j, by rw [poly_encoding]⟩

/-- Even this combination of digit restrictions does not justify specialization.
The theorem asserts failure of a sufficient criterion, not failure of Erdős 773. -/
theorem combined_conditions_do_not_suffice :
    ∃ B p : ℕ, ∃ f : Fin 4 → Fin 21 → ℕ,
      B = 3^14 ∧ p.Prime ∧
      (∀ j, f j 20 = 1 ∧ f j 0 = 24 ∧
        (∀ i, 2*f j i < B ∧ (i.val < 20 → 6 ∣ f j i)) ∧
        (∑ i, f j i) < B ∧ (∑ i, f j i ^ 2) = p) ∧
      (∀ j, List.Perm (List.ofFn (f j)) (List.ofFn (f 0))) ∧
      ¬ IsSidon (((univ : Finset (Fin 4)).image
        (fun j => (∑ i : Fin 21, f j i * B ^ i.val)^2)) : Set ℕ) := by
  refine ⟨base, 3769070293, w, base_is_prime_power, energy_prime, ?_, histogram _ _, not_sidon⟩
  intro j
  obtain ⟨hl, hc, hd, hs⟩ := concrete_digit_conditions j
  exact ⟨hl, hc, hd, hs, concrete_energy j⟩

#print axioms norm_difference_factor
#print axioms roots_gcd
#print axioms poly_eval
#print axioms formal_sidon
#print axioms combined_conditions_do_not_suffice
end Erdos773.PrimePowerEnergyCarry
