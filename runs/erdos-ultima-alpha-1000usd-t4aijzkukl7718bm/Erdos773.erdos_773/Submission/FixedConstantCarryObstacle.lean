import FormalConjecturesUtil

/-! Fixed constant digit 3 does not suffice for the histogram/Eisenstein
construction. This is a method obstruction, NOT a disproof of Erdos 773. -/
namespace Erdos773.FixedConstantCarry
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private def words (u v : ℕ) : Fin 4 → Fin 20 → ℕ :=
  ![![3,12,24,18,v + 3,9,30,72,60,3*v + 9,15,66,120,84,5*v + 15,3*u,9*u,15*u,3*u,1],
    ![3,18,24,12,v + 3,15,84,120,66,5*v + 15,9,60,72,30,3*v + 9,3*u,15*u,9*u,3*u,1],
    ![3,18,24,12,v + 3,9,60,72,30,3*v + 9,15,84,120,66,5*v + 15,3*u,15*u,9*u,3*u,1],
    ![3,12,24,18,v + 3,15,66,120,84,5*v + 15,9,30,72,60,3*v + 9,3*u,9*u,15*u,3*u,1]]

private def val (u v B : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 20, words u v j i * B ^ i.val

lemma leading (u v : ℕ) (j : Fin 4) : words u v j 19 = 1 := by
  fin_cases j <;> rfl

lemma constant_digit (u v : ℕ) (j : Fin 4) : words u v j 0 = 3 := by
  fin_cases j <;> rfl

lemma lower_divisible (u v : ℕ) (hv : 3 ∣ v) (j : Fin 4) (i : Fin 20)
    (hi : i.val < 19) : 3 ∣ words u v j i := by
  have hv' := Nat.mod_eq_zero_of_dvd hv
  fin_cases j <;> fin_cases i <;> simp [words] at hi ⊢ <;> omega

lemma histogram_perm (u v : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words u v j)) (List.ofFn (words u v 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [words, List.ofFn_succ, List.count_cons] <;> omega

lemma digit_sum (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 20, words u v j i) = 541 + 30 * u + 9 * v := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_norm (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 20, words u v j i ^ 2) =
      324 * u ^ 2 + 35 * v ^ 2 + 210 * v + 37171 := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_positive (u v : ℕ) (hu : 0 < u) (j : Fin 4) (i : Fin 20) :
    0 < words u v j i := by
  fin_cases j <;> fin_cases i <;> simp [words] <;> omega

lemma unique_constant (u v : ℕ) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (j : Fin 4) (i : Fin 20) (hi : 0 < i.val) (hi' : i.val < 19) :
    3 < words u v j i := by
  fin_cases j <;> fin_cases i <;> simp [words] at hi hi' ⊢ <;> omega

lemma digits_lt_of_sum (u v B : ℕ) (hs : 541 + 30 * u + 9 * v < B)
    (j : Fin 4) (i : Fin 20) : words u v j i < B := by
  have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 20))) =>
    Nat.zero_le (words u v j k)) (Finset.mem_univ i)
  rw [digit_sum] at h
  omega

lemma val_expand_0 (u v B : ℕ) : val u v B 0 =
    (3) * B ^ 0 +
      (12) * B ^ 1 +
      (24) * B ^ 2 +
      (18) * B ^ 3 +
      (v + 3) * B ^ 4 +
      (9) * B ^ 5 +
      (30) * B ^ 6 +
      (72) * B ^ 7 +
      (60) * B ^ 8 +
      (3*v + 9) * B ^ 9 +
      (15) * B ^ 10 +
      (66) * B ^ 11 +
      (120) * B ^ 12 +
      (84) * B ^ 13 +
      (5*v + 15) * B ^ 14 +
      (3*u) * B ^ 15 +
      (9*u) * B ^ 16 +
      (15*u) * B ^ 17 +
      (3*u) * B ^ 18 +
      (1) * B ^ 19 := by
  simp [val, words, Fin.sum_univ_succ, add_assoc]

lemma val_expand_1 (u v B : ℕ) : val u v B 1 =
    (3) * B ^ 0 +
      (18) * B ^ 1 +
      (24) * B ^ 2 +
      (12) * B ^ 3 +
      (v + 3) * B ^ 4 +
      (15) * B ^ 5 +
      (84) * B ^ 6 +
      (120) * B ^ 7 +
      (66) * B ^ 8 +
      (5*v + 15) * B ^ 9 +
      (9) * B ^ 10 +
      (60) * B ^ 11 +
      (72) * B ^ 12 +
      (30) * B ^ 13 +
      (3*v + 9) * B ^ 14 +
      (3*u) * B ^ 15 +
      (15*u) * B ^ 16 +
      (9*u) * B ^ 17 +
      (3*u) * B ^ 18 +
      (1) * B ^ 19 := by
  simp [val, words, Fin.sum_univ_succ, add_assoc]

lemma val_expand_2 (u v B : ℕ) : val u v B 2 =
    (3) * B ^ 0 +
      (18) * B ^ 1 +
      (24) * B ^ 2 +
      (12) * B ^ 3 +
      (v + 3) * B ^ 4 +
      (9) * B ^ 5 +
      (60) * B ^ 6 +
      (72) * B ^ 7 +
      (30) * B ^ 8 +
      (3*v + 9) * B ^ 9 +
      (15) * B ^ 10 +
      (84) * B ^ 11 +
      (120) * B ^ 12 +
      (66) * B ^ 13 +
      (5*v + 15) * B ^ 14 +
      (3*u) * B ^ 15 +
      (15*u) * B ^ 16 +
      (9*u) * B ^ 17 +
      (3*u) * B ^ 18 +
      (1) * B ^ 19 := by
  simp [val, words, Fin.sum_univ_succ, add_assoc]

lemma val_expand_3 (u v B : ℕ) : val u v B 3 =
    (3) * B ^ 0 +
      (12) * B ^ 1 +
      (24) * B ^ 2 +
      (18) * B ^ 3 +
      (v + 3) * B ^ 4 +
      (15) * B ^ 5 +
      (66) * B ^ 6 +
      (120) * B ^ 7 +
      (84) * B ^ 8 +
      (5*v + 15) * B ^ 9 +
      (9) * B ^ 10 +
      (30) * B ^ 11 +
      (72) * B ^ 12 +
      (60) * B ^ 13 +
      (3*v + 9) * B ^ 14 +
      (3*u) * B ^ 15 +
      (9*u) * B ^ 16 +
      (15*u) * B ^ 17 +
      (3*u) * B ^ 18 +
      (1) * B ^ 19 := by
  simp [val, words, Fin.sum_univ_succ, add_assoc]

lemma norm_difference_factor (u v B : ℕ) :
    (val u v B 0 : ℤ) ^ 2 + (val u v B 1 : ℤ) ^ 2 -
      (val u v B 2 : ℤ) ^ 2 - (val u v B 3 : ℤ) ^ 2 =
      24 * (B : ℤ) ^ 25 * ((u : ℤ) * v - B - 1) * ((B : ℤ) - 1) *
        ((B : ℤ) ^ 5 - 1) := by
  rw [val_expand_0, val_expand_1, val_expand_2, val_expand_3]
  push_cast
  ring

lemma collision (u v B : ℕ) (hB : B + 1 = u * v) :
    val u v B 0 ^ 2 + val u v B 1 ^ 2 = val u v B 2 ^ 2 + val u v B 3 ^ 2 := by
  have h := norm_difference_factor u v B
  have hB' : (B : ℤ) + 1 = (u : ℤ) * v := by exact_mod_cast hB
  have hz : (u : ℤ) * v - B - 1 = 0 := by omega
  rw [hz] at h
  simp only [mul_zero, zero_mul] at h
  have hh : (val u v B 0 : ℤ) ^ 2 + (val u v B 1 : ℤ) ^ 2 =
      (val u v B 2 : ℤ) ^ 2 + (val u v B 3 : ℤ) ^ 2 := by omega
  exact_mod_cast hh

private lemma digit_eval_injective {B n : ℕ} (hB : 1 < B)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < B) (hb : ∀ i, b i < B)
    (he : (∑ i, a i * B ^ i.val) = ∑ i, b i * B ^ i.val) : a = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hf (f : Fin (n+1) → ℕ) : (∑ i, f i * B ^ i.val) =
        f 0 + B * ∑ i : Fin n, f i.succ * B ^ i.val := by
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hf a, hf b] at he
    have he0 : a 0 = b 0 := by
      have hh := congrArg (· % B) he
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (ha 0),
        Nat.mod_eq_of_lt (hb 0)] using hh
    have het : (∑ i : Fin n, a i.succ * B ^ i.val) =
        ∑ i : Fin n, b i.succ * B ^ i.val := by
      rw [he0] at he
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < B) (Nat.add_left_cancel he)
    have ht := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ) het
    funext i
    refine Fin.cases he0 (fun j => congrFun ht j) i

lemma nontrivial (u v B : ℕ) (hs : 541 + 30 * u + 9 * v < B) :
    val u v B 0 ≠ val u v B 2 ∧ val u v B 0 ≠ val u v B 3 := by
  have hB : 1 < B := by omega
  have hd := digits_lt_of_sum u v B hs
  constructor <;> intro he
  · have hw := digit_eval_injective hB (words u v 0) (words u v 2) (hd 0) (hd 2) he
    have hc := congrFun hw 1
    change (12 : ℕ) = 18 at hc
    omega
  · have hw := digit_eval_injective hB (words u v 0) (words u v 3) (hd 0) (hd 3) he
    have hc := congrFun hw 5
    change (9 : ℕ) = 15 at hc
    omega

lemma not_sidon (u v B : ℕ) (hB : B + 1 = u * v)
    (hs : 541 + 30 * u + 9 * v < B) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => val u v B j ^ 2)) : Set ℕ) := by
  intro h
  have hm (j : Fin 4) : val u v B j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val u v B j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision u v B hB) with h | h
  · exact (nontrivial u v B hs).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial u v B hs).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)

lemma balanced_parameters (t : ℕ) :
    let u := 3 * (t + 20)
    let B := u ^ 2 - 1
    B + 1 = u * u ∧ 3 ∣ u ∧ 541 + 30 * u + 9 * u < B ∧
      (15 * u) ^ 2 = 225 * (B + 1) ∧
      ∀ j i, 0 < words u u j i ∧ words u u j i ≤ 15 * u ∧
        2 * words u u j i < B := by
  dsimp only
  let u := 3 * (t + 20)
  change u ^ 2 - 1 + 1 = u * u ∧ 3 ∣ u ∧
    541 + 30 * u + 9 * u < u ^ 2 - 1 ∧
    (15 * u) ^ 2 = 225 * (u ^ 2 - 1 + 1) ∧
    ∀ j i, 0 < words u u j i ∧ words u u j i ≤ 15 * u ∧
      2 * words u u j i < u ^ 2 - 1
  have hu : 60 ≤ u := by dsimp [u]; omega
  have hsq : 1 ≤ u ^ 2 := by nlinarith
  have he : u ^ 2 - 1 + 1 = u * u := by nlinarith [Nat.sub_add_cancel hsq]
  have hs : 541 + 30 * u + 9 * u < u ^ 2 - 1 := by nlinarith
  have hh : (15 * u) ^ 2 = 225 * (u ^ 2 - 1 + 1) := by rw [he]; ring
  have hhalf : 2 * (15 * u) < u ^ 2 - 1 := by nlinarith
  refine ⟨he, ⟨t + 20, rfl⟩, hs, hh, ?_⟩
  intro j i
  have hle : words u u j i ≤ 15 * u := by
    fin_cases j <;> fin_cases i <;> simp [words] <;> omega
  exact ⟨digit_positive u u (by omega) j i, hle, by omega⟩

lemma progression_parameters (B : ℕ) (hB : 3635 ≤ B) (hmod : B % 36 = 35) :
    ∃ v : ℕ, 3 ∣ v ∧ B + 1 = 12 * v ∧ 541 + 30 * 12 + 9 * v < B ∧
      ∀ j i, 0 < words 12 v j i ∧ 2 * words 12 v j i < B := by
  let t := (B + 1) / 36
  have he : B + 1 = 36 * t := by dsimp [t]; omega
  have ht : 101 ≤ t := by omega
  refine ⟨3 * t, by omega, by omega, by omega, ?_⟩
  intro j i
  refine ⟨digit_positive 12 (3 * t) (by decide) j i, ?_⟩
  fin_cases j <;> fin_cases i <;> simp [words] <;> omega

lemma counterexample_in_progression (B : ℕ) (hB : 3635 ≤ B)
    (hmod : B % 36 = 35) :
    ∃ w : Fin 4 → Fin 20 → ℕ,
      (∀ j, w j 19 = 1 ∧ w j 0 = 3 ∧
        (∀ i, i.val < 19 → 3 ∣ w j i) ∧
        (∀ i, 0 < w j i ∧ 2 * w j i < B) ∧
        (∑ i, w j i) < B ∧
        List.Perm (List.ofFn (w j)) (List.ofFn (w 0))) ∧
      ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
        (fun j => (∑ i : Fin 20, w j i * B ^ i.val) ^ 2)) : Set ℕ) := by
  obtain ⟨v, hv, he, hs, hd⟩ := progression_parameters B hB hmod
  refine ⟨words 12 v, ?_, not_sidon 12 v B he hs⟩
  intro j
  refine ⟨leading 12 v j, constant_digit 12 v j,
    fun i hi => lower_divisible 12 v hv j i hi, hd j, ?_, histogram_perm 12 v j⟩
  simpa only [digit_sum] using hs

lemma primitive_example :
    Nat.gcd (Nat.gcd (val 60 60 3599 0) (val 60 60 3599 1))
      (Nat.gcd (val 60 60 3599 2) (val 60 60 3599 3)) = 1 := by
  decide +kernel

#print axioms histogram_perm
#print axioms lower_divisible
#print axioms norm_difference_factor
#print axioms not_sidon
#print axioms balanced_parameters
#print axioms progression_parameters
#print axioms unique_constant
#print axioms primitive_example
#print axioms counterexample_in_progression
end Erdos773.FixedConstantCarry
