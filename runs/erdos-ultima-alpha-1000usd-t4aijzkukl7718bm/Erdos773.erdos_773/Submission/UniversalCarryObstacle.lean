import FormalConjecturesUtil

/-! A carry construction with a common constant digit. This is a method
obstruction, NOT a disproof of Erdos 773. -/
namespace Erdos773.UniversalCarry
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private def pattern : Fin 4 → Fin 36 → Fin 22 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,0,1,2,3,4,5,12,13,14,15,16,17,0,1,2,3,4,5,18,19,18,20,18,21],
    ![0,3,4,1,2,5,12,15,16,13,14,17,0,3,4,1,2,5,6,9,10,7,8,11,0,3,4,1,2,5,18,20,18,19,18,21],
    ![0,3,4,1,2,5,6,9,10,7,8,11,0,3,4,1,2,5,12,15,16,13,14,17,0,3,4,1,2,5,18,20,18,19,18,21],
    ![0,1,2,3,4,5,12,13,14,15,16,17,0,1,2,3,4,5,6,7,8,9,10,11,0,1,2,3,4,5,18,19,18,20,18,21]]

private def alphabet (u T : ℕ) (k : Fin 22) : ℕ :=
  match k.val with
  | 0 => 192*T
  | 1 => 120*T+192
  | 2 => 192*T+120
  | 3 => 264*T+192
  | 4 => 192*T+264
  | 5 => 8*u+192
  | 6 => 120*T
  | 7 => 21*T+120
  | 8 => 120*T+21
  | 9 => 219*T+120
  | 10 => 120*T+219
  | 11 => 5*u+120
  | 12 => 264*T
  | 13 => 219*T+264
  | 14 => 264*T+219
  | 15 => 309*T+264
  | 16 => 264*T+309
  | 17 => 11*u+264
  | 18 => 24*u
  | 19 => 15*u
  | 20 => 33*u
  | _ => 1

private def words (u T : ℕ) (j : Fin 4) (i : Fin 36) : ℕ :=
  alphabet u T (pattern j i)

private def val (u T B : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 36, words u T j i * B ^ i.val

lemma leading (u T : ℕ) (j : Fin 4) : words u T j 35 = 1 := by
  fin_cases j <;> rfl

lemma constant_digit (u T : ℕ) (j : Fin 4) : words u T j 0 = 192 * T := by
  fin_cases j <;> rfl

lemma histogram_perm (u T : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words u T j)) (List.ofFn (words u T 0)) := by
  have hp : List.Perm (List.ofFn (pattern j)) (List.ofFn (pattern 0)) := by
    fin_cases j <;> decide +kernel
  simpa [words, List.map_ofFn] using hp.map (alphabet u T)

lemma digit_sum (u T : ℕ) (j : Fin 4) :
    (∑ i : Fin 36, words u T j i) = 4801 + 4800 * T + 160 * u := by
  fin_cases j <;> simp [words, pattern, alphabet, Fin.sum_univ_succ] <;> ring

lemma digit_le_height (u T : ℕ) (j : Fin 4) (i : Fin 36) :
    words u T j i ≤ 309 * (T + 1) + 33 * u := by
  change alphabet u T (pattern j i) ≤ _
  generalize pattern j i = k
  fin_cases k <;> simp [alphabet] <;> omega

lemma val_expand_0 (u T B : ℕ) : val u T B 0 =
    (192*T) * B ^ 0 +
      (120*T+192) * B ^ 1 +
      (192*T+120) * B ^ 2 +
      (264*T+192) * B ^ 3 +
      (192*T+264) * B ^ 4 +
      (8*u+192) * B ^ 5 +
      (120*T) * B ^ 6 +
      (21*T+120) * B ^ 7 +
      (120*T+21) * B ^ 8 +
      (219*T+120) * B ^ 9 +
      (120*T+219) * B ^ 10 +
      (5*u+120) * B ^ 11 +
      (192*T) * B ^ 12 +
      (120*T+192) * B ^ 13 +
      (192*T+120) * B ^ 14 +
      (264*T+192) * B ^ 15 +
      (192*T+264) * B ^ 16 +
      (8*u+192) * B ^ 17 +
      (264*T) * B ^ 18 +
      (219*T+264) * B ^ 19 +
      (264*T+219) * B ^ 20 +
      (309*T+264) * B ^ 21 +
      (264*T+309) * B ^ 22 +
      (11*u+264) * B ^ 23 +
      (192*T) * B ^ 24 +
      (120*T+192) * B ^ 25 +
      (192*T+120) * B ^ 26 +
      (264*T+192) * B ^ 27 +
      (192*T+264) * B ^ 28 +
      (8*u+192) * B ^ 29 +
      (24*u) * B ^ 30 +
      (15*u) * B ^ 31 +
      (24*u) * B ^ 32 +
      (33*u) * B ^ 33 +
      (24*u) * B ^ 34 +
      (1) * B ^ 35 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_1 (u T B : ℕ) : val u T B 1 =
    (192*T) * B ^ 0 +
      (264*T+192) * B ^ 1 +
      (192*T+264) * B ^ 2 +
      (120*T+192) * B ^ 3 +
      (192*T+120) * B ^ 4 +
      (8*u+192) * B ^ 5 +
      (264*T) * B ^ 6 +
      (309*T+264) * B ^ 7 +
      (264*T+309) * B ^ 8 +
      (219*T+264) * B ^ 9 +
      (264*T+219) * B ^ 10 +
      (11*u+264) * B ^ 11 +
      (192*T) * B ^ 12 +
      (264*T+192) * B ^ 13 +
      (192*T+264) * B ^ 14 +
      (120*T+192) * B ^ 15 +
      (192*T+120) * B ^ 16 +
      (8*u+192) * B ^ 17 +
      (120*T) * B ^ 18 +
      (219*T+120) * B ^ 19 +
      (120*T+219) * B ^ 20 +
      (21*T+120) * B ^ 21 +
      (120*T+21) * B ^ 22 +
      (5*u+120) * B ^ 23 +
      (192*T) * B ^ 24 +
      (264*T+192) * B ^ 25 +
      (192*T+264) * B ^ 26 +
      (120*T+192) * B ^ 27 +
      (192*T+120) * B ^ 28 +
      (8*u+192) * B ^ 29 +
      (24*u) * B ^ 30 +
      (33*u) * B ^ 31 +
      (24*u) * B ^ 32 +
      (15*u) * B ^ 33 +
      (24*u) * B ^ 34 +
      (1) * B ^ 35 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_2 (u T B : ℕ) : val u T B 2 =
    (192*T) * B ^ 0 +
      (264*T+192) * B ^ 1 +
      (192*T+264) * B ^ 2 +
      (120*T+192) * B ^ 3 +
      (192*T+120) * B ^ 4 +
      (8*u+192) * B ^ 5 +
      (120*T) * B ^ 6 +
      (219*T+120) * B ^ 7 +
      (120*T+219) * B ^ 8 +
      (21*T+120) * B ^ 9 +
      (120*T+21) * B ^ 10 +
      (5*u+120) * B ^ 11 +
      (192*T) * B ^ 12 +
      (264*T+192) * B ^ 13 +
      (192*T+264) * B ^ 14 +
      (120*T+192) * B ^ 15 +
      (192*T+120) * B ^ 16 +
      (8*u+192) * B ^ 17 +
      (264*T) * B ^ 18 +
      (309*T+264) * B ^ 19 +
      (264*T+309) * B ^ 20 +
      (219*T+264) * B ^ 21 +
      (264*T+219) * B ^ 22 +
      (11*u+264) * B ^ 23 +
      (192*T) * B ^ 24 +
      (264*T+192) * B ^ 25 +
      (192*T+264) * B ^ 26 +
      (120*T+192) * B ^ 27 +
      (192*T+120) * B ^ 28 +
      (8*u+192) * B ^ 29 +
      (24*u) * B ^ 30 +
      (33*u) * B ^ 31 +
      (24*u) * B ^ 32 +
      (15*u) * B ^ 33 +
      (24*u) * B ^ 34 +
      (1) * B ^ 35 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma val_expand_3 (u T B : ℕ) : val u T B 3 =
    (192*T) * B ^ 0 +
      (120*T+192) * B ^ 1 +
      (192*T+120) * B ^ 2 +
      (264*T+192) * B ^ 3 +
      (192*T+264) * B ^ 4 +
      (8*u+192) * B ^ 5 +
      (264*T) * B ^ 6 +
      (219*T+264) * B ^ 7 +
      (264*T+219) * B ^ 8 +
      (309*T+264) * B ^ 9 +
      (264*T+309) * B ^ 10 +
      (11*u+264) * B ^ 11 +
      (192*T) * B ^ 12 +
      (120*T+192) * B ^ 13 +
      (192*T+120) * B ^ 14 +
      (264*T+192) * B ^ 15 +
      (192*T+264) * B ^ 16 +
      (8*u+192) * B ^ 17 +
      (120*T) * B ^ 18 +
      (21*T+120) * B ^ 19 +
      (120*T+21) * B ^ 20 +
      (219*T+120) * B ^ 21 +
      (120*T+219) * B ^ 22 +
      (5*u+120) * B ^ 23 +
      (192*T) * B ^ 24 +
      (120*T+192) * B ^ 25 +
      (192*T+120) * B ^ 26 +
      (264*T+192) * B ^ 27 +
      (192*T+264) * B ^ 28 +
      (8*u+192) * B ^ 29 +
      (24*u) * B ^ 30 +
      (15*u) * B ^ 31 +
      (24*u) * B ^ 32 +
      (33*u) * B ^ 33 +
      (24*u) * B ^ 34 +
      (1) * B ^ 35 := by
  simp [val, words, pattern, alphabet, Fin.sum_univ_succ, add_assoc]

lemma norm_difference_factor (u T B : ℕ) :
    (val u T B 0 : ℤ) ^ 2 + (val u T B 1 : ℤ) ^ 2 -
      (val u T B 2 : ℤ) ^ 2 - (val u T B 3 : ℤ) ^ 2 =
      216 * (B : ℤ) ^ 42 * ((u : ℤ)^2 - T - B) * ((B : ℤ) ^ 2 - 1) *
        ((B : ℤ) ^ 12 - 1) := by
  rw [val_expand_0, val_expand_1, val_expand_2, val_expand_3]
  push_cast
  ring

lemma collision (u T B : ℕ) (hB : B + T = u ^ 2) :
    val u T B 0 ^ 2 + val u T B 1 ^ 2 = val u T B 2 ^ 2 + val u T B 3 ^ 2 := by
  have h := norm_difference_factor u T B
  have hB' : (B : ℤ) + T = (u : ℤ) ^ 2 := by exact_mod_cast hB
  have hz : (u : ℤ)^2 - T - B = 0 := by omega
  rw [hz] at h
  simp only [mul_zero, zero_mul] at h
  have hh : (val u T B 0 : ℤ) ^ 2 + (val u T B 1 : ℤ) ^ 2 =
      (val u T B 2 : ℤ) ^ 2 + (val u T B 3 : ℤ) ^ 2 := by omega
  exact_mod_cast hh

lemma constant_mod (u T : ℕ) (hT : T % 3 = 1) (j : Fin 4) :
    words u T j 0 % 9 = 3 := by
  rw [constant_digit]
  omega

lemma lower_divisible (u T : ℕ) (hu : 3 ∣ u) (j : Fin 4) (i : Fin 36)
    (hi : i.val < 35) : 3 ∣ words u T j i := by
  have hp : ∀ j : Fin 4, ∀ i : Fin 36, pattern j i = 21 → i.val = 35 := by
    decide +kernel
  have hne : pattern j i ≠ 21 := by intro h; have := hp j i h; omega
  have hu' : u % 3 = 0 := Nat.mod_eq_zero_of_dvd hu
  change 3 ∣ alphabet u T (pattern j i)
  generalize pattern j i = k at hne ⊢
  fin_cases k <;> simp [alphabet] at hne ⊢ <;> omega

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

lemma nontrivial (u T B : ℕ) (hT : 0 < T)
    (hh : 309 * (T + 1) + 33 * u < B) :
    val u T B 0 ≠ val u T B 2 ∧ val u T B 0 ≠ val u T B 3 := by
  have hB : 1 < B := by omega
  have hd (j : Fin 4) (i : Fin 36) : words u T j i < B :=
    (digit_le_height u T j i).trans_lt hh
  constructor <;> intro he
  · have hw := digit_eval_injective hB (words u T 0) (words u T 2) (hd 0) (hd 2) he
    have hc := congrFun hw 1
    change 120 * T + 192 = 264 * T + 192 at hc
    omega
  · have hw := digit_eval_injective hB (words u T 0) (words u T 3) (hd 0) (hd 3) he
    have hc := congrFun hw 6
    change 120 * T = 264 * T at hc
    omega

lemma not_sidon (u T B : ℕ) (hT : 0 < T) (hB : B + T = u ^ 2)
    (hh : 309 * (T + 1) + 33 * u < B) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => val u T B j ^ 2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : val u T B j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val u T B j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision u T B hB) with h | h
  · exact (nontrivial u T B hT hh).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial u T B hT hh).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)


lemma digit_bounds_of_sum (u T B : ℕ) (hsum : 4801 + 4800 * T + 160 * u < B)
    (j : Fin 4) (i : Fin 36) : 2 * words u T j i < B := by
  have hh := digit_le_height u T j i
  omega


lemma large_base_parameters (B : ℕ) (hB : 900000000 ≤ B) (hmod : B % 3 = 2) :
    ∃ u T : ℕ, 3 ∣ u ∧ T % 3 = 1 ∧ B + T = u ^ 2 ∧
      4801 + 4800 * T + 160 * u < B ∧
      (309 * (T + 1) + 33 * u) ^ 2 ≤ 8000000 * B := by
  let s := Nat.sqrt B
  let u := 3 * (s / 3 + 1)
  have hsu : s < u := by dsimp [u]; omega
  have hus : u ≤ s + 3 := by dsimp [u]; omega
  have hdiv : 3 ∣ u := by dsimp [u]; exact dvd_mul_right 3 _
  have hsq : s ^ 2 ≤ B := Nat.sqrt_le' B
  have hsq' : B < u ^ 2 := (Nat.sqrt_lt').mp hsu
  have huB : u ^ 2 ≤ B + 6 * u := by
    have hh := Nat.mul_le_mul_right (u + s) hus
    nlinarith only [hh,hsq,hsu]
  have hslarge : 30000 ≤ s := (Nat.le_sqrt').mpr hB
  have hularge : 30000 ≤ u := by omega
  let T := u ^ 2 - B
  have hBT : B + T = u ^ 2 := by dsimp [T]; omega
  have hT6 : T ≤ 6 * u := by omega
  have hu3 : u % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsq3 : u ^ 2 % 3 = 0 := by simp [pow_two, Nat.mul_mod, hu3]
  have hTmod : T % 3 = 1 := by omega
  have hsum : 4801 + 4800 * T + 160 * u < B := by
    have hh := Nat.mul_le_mul_right u hularge
    nlinarith only [hh,hT6,hBT,hularge]
  have hH : 309 * (T + 1) + 33 * u ≤ 2000 * u := by omega
  have h2 : u ^ 2 ≤ 2 * B := by
    have hh := Nat.mul_le_mul_right u hularge
    nlinarith only [hh,huB,hularge]
  have hH2 : (309 * (T + 1) + 33 * u) ^ 2 ≤ 8000000 * B := by
    calc
      _ ≤ (2000 * u) ^ 2 := Nat.pow_le_pow_left hH _
      _ = 4000000 * u ^ 2 := by ring
      _ ≤ 8000000 * B := by omega
  exact ⟨u,T,hdiv,hTmod,hBT,hsum,hH2⟩

lemma counterexample_for_large_base (B : ℕ) (hB : 900000000 ≤ B)
    (hmod : B % 3 = 2) :
    ∃ u T : ℕ,
      (∀ j : Fin 4, words u T j 35 = 1 ∧ words u T j 0 = 192 * T ∧
        words u T j 0 % 9 = 3 ∧
        (∀ i : Fin 36, i.val < 35 → 3 ∣ words u T j i) ∧
        (∑ i : Fin 36, words u T j i) < B ∧
        List.Perm (List.ofFn (words u T j)) (List.ofFn (words u T 0))) ∧
      (∀ j : Fin 4, ∀ i : Fin 36, words u T j i ≤ 309 * (T + 1) + 33 * u) ∧
      (309 * (T + 1) + 33 * u) ^ 2 ≤ 8000000 * B ∧
      ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
        (fun j => val u T B j ^ 2)) : Set ℕ) := by
  obtain ⟨u,T,hu,hT,hBT,hsum,hH2⟩ := large_base_parameters B hB hmod
  refine ⟨u,T,?_,digit_le_height u T,hH2,?_⟩
  · intro j
    exact ⟨leading u T j, constant_digit u T j, constant_mod u T hT j,
      lower_divisible u T hu j, by rw [digit_sum]; exact hsum, histogram_perm u T j⟩
  · apply not_sidon u T B (by omega) hBT
    omega

#print axioms large_base_parameters
#print axioms counterexample_for_large_base
#print axioms digit_bounds_of_sum
#print axioms histogram_perm
#print axioms norm_difference_factor
#print axioms collision
#print axioms constant_mod
#print axioms lower_divisible
#print axioms not_sidon
end Erdos773.UniversalCarry
