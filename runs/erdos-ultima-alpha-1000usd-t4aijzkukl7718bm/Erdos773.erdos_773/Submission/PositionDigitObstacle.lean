import FormalConjecturesUtil

/-!
An obstruction to adding first position-weighted digit statistics to the
base-three small-sum construction. This does NOT settle Erdős 773.
-/
namespace Erdos773.PositionDigitObstacle
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private def pattern : Fin 4 → Fin 49 → Fin 9 := ![
    ![2,0,3,0,3,0,2,0,5,0,3,0,4,0,4,0,3,0,6,0,3,0,4,0,4,0,3,0,6,0,2,0,3,0,3,0,2,0,5,7,0,8,0,8,0,7,0,0,1],
    ![4,0,3,0,3,0,4,0,6,0,3,0,2,0,2,0,3,0,5,0,3,0,2,0,2,0,3,0,5,0,4,0,3,0,3,0,4,0,6,8,0,7,0,7,0,8,0,0,1],
    ![3,0,2,0,2,0,3,0,5,0,4,0,3,0,3,0,4,0,6,0,4,0,3,0,3,0,4,0,6,0,3,0,2,0,2,0,3,0,5,8,0,7,0,7,0,8,0,0,1],
    ![3,0,4,0,4,0,3,0,6,0,2,0,3,0,3,0,2,0,5,0,2,0,3,0,3,0,2,0,5,0,3,0,4,0,4,0,3,0,6,7,0,8,0,8,0,7,0,0,1]]

private def alphabet (t : ℕ) (k : Fin 9) : ℕ :=
  match k.val with
  | 0 => 0
  | 1 => 1
  | 2 => 21
  | 3 => 219
  | 4 => 309
  | 5 => 1920
  | 6 => 4224
  | 7 => 45*(t+18)
  | _ => 99*(t+18)
private def base (t : ℕ) : ℕ := 1152*(t+18)
private def words (t : ℕ) (j : Fin 4) (i : Fin 49) : ℕ := alphabet t (pattern j i)
private def val (t : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 49, words t j i * base t ^ i.val

lemma pattern_moments : ∀ j : Fin 4, ∀ k : Fin 9, ∀ ell : Fin 2,
    (∑ i : Fin 49, if pattern j i = k then i.val ^ ell.val else 0) =
    (∑ i : Fin 49, if pattern 0 i = k then i.val ^ ell.val else 0) := by
  decide +kernel

lemma statistics (t : ℕ) (j : Fin 4) (ell : Fin 2) (f : ℕ → ℤ) :
    (∑ i : Fin 49, (i.val : ℤ) ^ ell.val * f (words t j i)) =
    (∑ i : Fin 49, (i.val : ℤ) ^ ell.val * f (words t 0 i)) := by
  have hf (j : Fin 4) :
      (∑ i : Fin 49, (i.val : ℤ) ^ ell.val * f (words t j i)) =
        ∑ k : Fin 9, (∑ i : Fin 49,
          if pattern j i = k then (i.val : ℤ) ^ ell.val else 0) * f (alphabet t k) := by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [words]
  rw [hf j, hf 0]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact_mod_cast pattern_moments j k ell

lemma leading (t : ℕ) (j : Fin 4) : words t j 48 = 1 := by
  have hp : ∀ j : Fin 4, pattern j 48 = 1 := by decide +kernel
  simp [words, hp, alphabet]

lemma constant_mod (t : ℕ) (j : Fin 4) : words t j 0 % 9 = 3 := by
  fin_cases j <;> norm_num [words, pattern, alphabet]

lemma lower_divisible (t : ℕ) (j : Fin 4) (i : Fin 49) (hi : i.val < 48) :
    3 ∣ words t j i := by
  have hpat : ∀ j : Fin 4, ∀ i : Fin 49, pattern j i = 1 → i.val = 48 := by
    decide +kernel
  have hne : pattern j i ≠ 1 := by intro h; have := hpat j i h; omega
  change 3 ∣ alphabet t (pattern j i)
  generalize pattern j i = k at hne ⊢
  have h45 : 3 ∣ 45 * (t+18) := dvd_mul_of_dvd_left (by decide) _
  have h99 : 3 ∣ 99 * (t+18) := dvd_mul_of_dvd_left (by decide) _
  fin_cases k <;> simp [alphabet, h45, h99] at hne ⊢

lemma digit_bounds (t : ℕ) (j : Fin 4) (i : Fin 49) :
    2 * words t j i < base t := by
  change 2 * alphabet t (pattern j i) < base t
  generalize pattern j i = k
  fin_cases k <;> simp [alphabet, base] <;> omega

lemma digit_sum (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 49, words t j i) = 15361 + 288 * (t+18) := by
  have hs := statistics t j 0 (fun x => (x : ℤ))
  simp only [Fin.val_zero, pow_zero, one_mul] at hs
  have h0 : (∑ i : Fin 49, words t 0 i) = 15361 + 288 * (t+18) := by
    norm_num [words, pattern, alphabet, Fin.sum_univ_succ]
    omega
  have hh : (∑ i : Fin 49, words t j i) = ∑ i : Fin 49, words t 0 i := by
    exact_mod_cast hs
  exact hh.trans h0

lemma digit_sum_lt_base (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 49, words t j i) < base t := by
  rw [digit_sum]
  dsimp [base]
  omega

lemma val_expand_0 (t : ℕ) : val t 0 =
    21 +
      219 * base t ^ 2 +
      219 * base t ^ 4 +
      21 * base t ^ 6 +
      1920 * base t ^ 8 +
      219 * base t ^ 10 +
      309 * base t ^ 12 +
      309 * base t ^ 14 +
      219 * base t ^ 16 +
      4224 * base t ^ 18 +
      219 * base t ^ 20 +
      309 * base t ^ 22 +
      309 * base t ^ 24 +
      219 * base t ^ 26 +
      4224 * base t ^ 28 +
      21 * base t ^ 30 +
      219 * base t ^ 32 +
      219 * base t ^ 34 +
      21 * base t ^ 36 +
      1920 * base t ^ 38 +
      (45*(t+18)) * base t ^ 39 +
      (99*(t+18)) * base t ^ 41 +
      (99*(t+18)) * base t ^ 43 +
      (45*(t+18)) * base t ^ 45 +
      base t ^ 48 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_1 (t : ℕ) : val t 1 =
    309 +
      219 * base t ^ 2 +
      219 * base t ^ 4 +
      309 * base t ^ 6 +
      4224 * base t ^ 8 +
      219 * base t ^ 10 +
      21 * base t ^ 12 +
      21 * base t ^ 14 +
      219 * base t ^ 16 +
      1920 * base t ^ 18 +
      219 * base t ^ 20 +
      21 * base t ^ 22 +
      21 * base t ^ 24 +
      219 * base t ^ 26 +
      1920 * base t ^ 28 +
      309 * base t ^ 30 +
      219 * base t ^ 32 +
      219 * base t ^ 34 +
      309 * base t ^ 36 +
      4224 * base t ^ 38 +
      (99*(t+18)) * base t ^ 39 +
      (45*(t+18)) * base t ^ 41 +
      (45*(t+18)) * base t ^ 43 +
      (99*(t+18)) * base t ^ 45 +
      base t ^ 48 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_2 (t : ℕ) : val t 2 =
    219 +
      21 * base t ^ 2 +
      21 * base t ^ 4 +
      219 * base t ^ 6 +
      1920 * base t ^ 8 +
      309 * base t ^ 10 +
      219 * base t ^ 12 +
      219 * base t ^ 14 +
      309 * base t ^ 16 +
      4224 * base t ^ 18 +
      309 * base t ^ 20 +
      219 * base t ^ 22 +
      219 * base t ^ 24 +
      309 * base t ^ 26 +
      4224 * base t ^ 28 +
      219 * base t ^ 30 +
      21 * base t ^ 32 +
      21 * base t ^ 34 +
      219 * base t ^ 36 +
      1920 * base t ^ 38 +
      (99*(t+18)) * base t ^ 39 +
      (45*(t+18)) * base t ^ 41 +
      (45*(t+18)) * base t ^ 43 +
      (99*(t+18)) * base t ^ 45 +
      base t ^ 48 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_3 (t : ℕ) : val t 3 =
    219 +
      309 * base t ^ 2 +
      309 * base t ^ 4 +
      219 * base t ^ 6 +
      4224 * base t ^ 8 +
      21 * base t ^ 10 +
      219 * base t ^ 12 +
      219 * base t ^ 14 +
      21 * base t ^ 16 +
      1920 * base t ^ 18 +
      21 * base t ^ 20 +
      219 * base t ^ 22 +
      219 * base t ^ 24 +
      21 * base t ^ 26 +
      1920 * base t ^ 28 +
      219 * base t ^ 30 +
      309 * base t ^ 32 +
      309 * base t ^ 34 +
      219 * base t ^ 36 +
      4224 * base t ^ 38 +
      (45*(t+18)) * base t ^ 39 +
      (99*(t+18)) * base t ^ 41 +
      (99*(t+18)) * base t ^ 43 +
      (45*(t+18)) * base t ^ 45 +
      base t ^ 48 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

attribute [local irreducible] base val

lemma norm_identity (a b c d : ℤ) :
    ((a*c-b*d)-(a*d+b*c))^2 + ((a*c-b*d)+(a*d+b*c))^2 =
      ((a*c+b*d)-(a*d-b*c))^2 + ((a*c+b*d)+(a*d-b*c))^2 := by ring

lemma collision (t : ℕ) : val t 0 ^ 2 + val t 1 ^ 2 = val t 2 ^ 2 + val t 3 ^ 2 := by
  let B : ℤ := base t
  let a := 128 * B ^ 8 + 8 * (1 + B^2 + B^4 + B^6)
  let b := 3 * (1 - B^2 - B^4 + B^6)
  let c := B^40 + 3072 * (1 + B^10 + B^20 + B^30)
  let d := 1152 * (1 - B^10 - B^20 + B^30)
  have hb : 1152 * ((t : ℤ) + 18) = (base t : ℤ) := by
    simp [base]
  have h0 : 128 * (val t 0 : ℤ) = (a*c-b*d)-(a*d+b*c) := by
    rw [val_expand_0]
    push_cast
    dsimp [a,b,c,d,B]
    linear_combination (5 * (base t : ℤ)^39 + 11 * (base t : ℤ)^41 + 11 * (base t : ℤ)^43 + 5 * (base t : ℤ)^45) * hb
  have h1 : 128 * (val t 1 : ℤ) = (a*c-b*d)+(a*d+b*c) := by
    rw [val_expand_1]
    push_cast
    dsimp [a,b,c,d,B]
    linear_combination (11 * (base t : ℤ)^39 + 5 * (base t : ℤ)^41 + 5 * (base t : ℤ)^43 + 11 * (base t : ℤ)^45) * hb
  have h2 : 128 * (val t 2 : ℤ) = (a*c+b*d)-(a*d-b*c) := by
    rw [val_expand_2]
    push_cast
    dsimp [a,b,c,d,B]
    linear_combination (11 * (base t : ℤ)^39 + 5 * (base t : ℤ)^41 + 5 * (base t : ℤ)^43 + 11 * (base t : ℤ)^45) * hb
  have h3 : 128 * (val t 3 : ℤ) = (a*c+b*d)+(a*d-b*c) := by
    rw [val_expand_3]
    push_cast
    dsimp [a,b,c,d,B]
    linear_combination (5 * (base t : ℤ)^39 + 11 * (base t : ℤ)^41 + 11 * (base t : ℤ)^43 + 5 * (base t : ℤ)^45) * hb
  have hh := norm_identity a b c d
  rw [← h0, ← h1, ← h2, ← h3] at hh
  have hz : (val t 0 : ℤ)^2 + (val t 1 : ℤ)^2 = (val t 2 : ℤ)^2 + (val t 3 : ℤ)^2 := by
    nlinarith only [hh]
  exact_mod_cast hz

lemma nontrivial (t : ℕ) : val t 0 ≠ val t 2 ∧ val t 0 ≠ val t 3 := by
  have hm (j : Fin 4) : val t j % base t = words t j 0 := by
    fin_cases j <;> simp [val, Fin.sum_univ_succ, words, pattern, alphabet,
      Nat.add_mod, Nat.mul_mod, Nat.pow_succ]
    all_goals exact Nat.mod_eq_of_lt (by simp only [base]; omega)
  constructor <;> intro h
  · have hh : val t 0 % base t = val t 2 % base t := congrArg (· % base t) h
    rw [hm 0, hm 2] at hh
    change (21 : ℕ) = 219 at hh
    omega
  · have hh : val t 0 % base t = val t 3 % base t := congrArg (· % base t) h
    rw [hm 0, hm 3] at hh
    change (21 : ℕ) = 219 at hh
    omega

lemma not_sidon (t : ℕ) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : val t j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h
  · exact (nontrivial t).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial t).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)

lemma primitive_example :
    Nat.gcd (Nat.gcd (val 1 0) (val 1 1)) (Nat.gcd (val 1 2) (val 1 3)) = 3 := by
  decide +kernel

#print axioms statistics
#print axioms leading
#print axioms constant_mod
#print axioms lower_divisible
#print axioms digit_sum_lt_base
#print axioms not_sidon
#print axioms primitive_example
end Erdos773.PositionDigitObstacle
