/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option exponentiation.threshold 400000
set_option maxRecDepth 200000
set_option maxHeartbeats 15000000

open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ := 
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

theorem floor_pow_three_halves (k : ℕ) :
  Int.floor (((3 : ℝ) / 2) ^ k) = (3^k : ℤ) / (2^k : ℤ) := by
  have hb : (0 : ℝ) < 2^k := by positivity
  rw [Int.floor_eq_iff]
  constructor
  · -- q ≤ x
    have h1 : ((3 : ℝ) / 2) ^ k = (3^k : ℝ) / (2^k : ℝ) := div_pow (3 : ℝ) 2 k
    rw [h1]
    rw [le_div_iff₀ hb]
    norm_cast
    exact Nat.div_mul_le_self (3^k) (2^k)
  · -- x < q + 1
    have h1 : ((3 : ℝ) / 2) ^ k = (3^k : ℝ) / (2^k : ℝ) := div_pow (3 : ℝ) 2 k
    rw [h1]
    rw [div_lt_iff₀ hb]
    norm_cast
    have h2k : 0 < 2^k := by positivity
    have h_mod : 3^k = 2^k * (3^k / 2^k) + 3^k % 2^k := (Nat.div_add_mod (3^k) (2^k)).symm
    have h_lt : 3^k < 2^k * (3^k / 2^k) + 2^k := by
      nth_rw 1 [h_mod]
      exact Nat.add_lt_add_left (Nat.mod_lt (3^k) h2k) _
    have h_ring : 2^k * (3^k / 2^k) + 2^k = (3^k / 2^k + 1) * 2^k := by ring
    rw [h_ring] at h_lt
    exact h_lt

def a_comp (n : ℕ) : ℤ := 
  - (((List.range n).map (fun k => if Even (((3^(k+1) : ℤ) / (2^(k+1) : ℤ)).toNat) then (1 : ℤ) else (-1 : ℤ))).sum)

theorem sum_range_eq_list_sum (n : ℕ) (f : ℕ → ℤ) :
  Finset.sum (Finset.range n) f = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

theorem a_eq_a_comp (n : ℕ) : a n = a_comp n := by
  dsimp [a, a_comp]
  rw [sum_range_eq_list_sum]
  simp_rw [floor_pow_three_halves, neg_one_pow_eq_ite]

def F_slice (pow3 : ℤ) (start : ℕ) (i : ℕ) : ℤ := 
  if Even (((pow3 * (3^(i+1) : ℤ)) / (2^(start + i + 1) : ℤ)).toNat) then 1 else -1

theorem sum_slice_add (len1 len2 : ℕ) (pow3 : ℤ) (start : ℕ) :
  ((List.range (len1 + len2)).map (F_slice pow3 start)).sum =
    ((List.range len1).map (F_slice pow3 start)).sum +
    ((List.range len2).map (F_slice (pow3 * 3^len1) (start + len1))).sum := by
  rw [List.range_add]
  rw [List.map_append, List.sum_append]
  congr 1
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  dsimp [F_slice, Function.comp]
  have h_pow : (3 : ℤ)^len1 * (3 : ℤ)^(i+1) = (3 : ℤ)^(len1 + i + 1) := by
    rw [← pow_add]
    congr 1
  rw [mul_assoc, h_pow]
  have h_idx : start + len1 + i + 1 = start + (len1 + i) + 1 := by omega
  rw [h_idx]

theorem List.range_succ_left (n : ℕ) : List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [List.range_succ]
    nth_rw 2 [List.range_succ]
    rw [List.map_append, List.map_singleton]
    rw [ih]
    rfl

def sum_segment_loop (n : ℕ) (pow3 : ℤ) (start : ℕ) (acc : ℤ) : ℤ × ℤ :=
  match n with
  | 0 => (acc, pow3)
  | n' + 1 =>
    let term := if ((pow3 * 3) / (2^(start + 1) : ℤ)).toNat % 2 = 0 then (1 : ℤ) else (-1 : ℤ)
    let next_pow3 := pow3 * 3
    let next_acc := acc + term
    match next_pow3, next_acc with
    | Int.ofNat _, Int.ofNat _ => sum_segment_loop n' next_pow3 (start + 1) next_acc
    | Int.ofNat _, Int.negSucc _ => sum_segment_loop n' next_pow3 (start + 1) next_acc
    | Int.negSucc _, Int.ofNat _ => sum_segment_loop n' next_pow3 (start + 1) next_acc
    | Int.negSucc _, Int.negSucc _ => sum_segment_loop n' next_pow3 (start + 1) next_acc

theorem sum_segment_loop_eq (n : ℕ) (pow3 : ℤ) (start : ℕ) (acc : ℤ) :
  sum_segment_loop n pow3 start acc = (acc + ((List.range n).map (F_slice pow3 start)).sum, pow3 * 3^n) := by
  induction n generalizing pow3 start acc with
  | zero =>
    simp [sum_segment_loop]
  | succ n' ih =>
    simp [sum_segment_loop]
    split
    all_goals
      rw [ih (pow3 * 3) (start + 1) _]
      have h_term : (if ((pow3 * 3) / (2^(start + 1) : ℤ)).toNat % 2 = 0 then (1 : ℤ) else (-1 : ℤ)) = F_slice pow3 start 0 := by
        dsimp [F_slice]
        simp only [Nat.even_iff]
      rw [h_term]
      congr 1
      · -- sum equality
        rw [List.range_succ_left]
        rw [List.map_cons, List.sum_cons]
        have h_sum : ((List.range n').map (F_slice (pow3 * 3) (start + 1))).sum =
                     (((List.range n').map (fun x => x + 1)).map (F_slice pow3 start)).sum := by
          congr 1
          rw [List.map_map]
          have h_fun : F_slice (pow3 * 3) (start + 1) = (F_slice pow3 start ∘ fun x => x + 1) := by
            ext x
            dsimp [F_slice, Function.comp]
            have h_idx : start + 1 + x + 1 = start + (x + 1) + 1 := by omega
            rw [h_idx]
            have h_eq : pow3 * 3 * 3^(x+1) = pow3 * 3^(x+1+1) := by
              rw [pow_succ 3 (x+1)]
              ring
            rw [h_eq]
          rw [h_fun]
        rw [h_sum]
        rw [add_assoc]
      · -- pow3 equality
        ring

def sum_hybrid (depth : ℕ) (len : ℕ) (pow3 : ℤ) (start : ℕ) : ℤ × ℤ :=
  if len = 0 then (0, pow3)
  else
    match depth with
    | 0 => sum_segment_loop len pow3 start 0
    | depth' + 1 =>
      let half := len / 2
      let (sum1, p3_1) := sum_hybrid depth' half pow3 start
      let (sum2, p3_2) := sum_hybrid depth' (len - half) p3_1 (start + half)
      (sum1 + sum2, p3_2)

theorem sum_hybrid_eq (depth : ℕ) (len : ℕ) (pow3 : ℤ) (start : ℕ) :
  sum_hybrid depth len pow3 start = (((List.range len).map (F_slice pow3 start)).sum, pow3 * 3^len) := by
  induction depth generalizing len pow3 start with
  | zero =>
    by_cases h_zero : len = 0
    · subst h_zero
      simp [sum_hybrid]
    · simp [sum_hybrid, h_zero]
      rw [sum_segment_loop_eq len pow3 start 0]
      simp
  | succ depth' ih =>
    by_cases h_zero : len = 0
    · subst h_zero
      simp [sum_hybrid]
    · simp [sum_hybrid, h_zero]
      have h_split : len = len / 2 + (len - len / 2) := by omega
      constructor
      · -- sum equality
        rw [ih (len / 2) pow3 start]
        rw [ih (len - len / 2) (pow3 * 3^(len / 2)) (start + len / 2)]
        dsimp
        conv_rhs => rw [h_split]
        rw [sum_slice_add (len / 2) (len - len / 2) pow3 start]
      · -- pow3 equality
        have h_ih1 := ih (len / 2) pow3 start
        rw [h_ih1]
        dsimp
        have h_ih2 := ih (len - len / 2) (pow3 * 3^(len / 2)) (start + len / 2)
        rw [h_ih2]
        dsimp
        have h3 : pow3 * 3^(len / 2) * 3^(len - len / 2) = pow3 * 3^len := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
        rw [h3]

def p_0 : ℤ := 1
def p_1 : ℤ := p_0 * 3^30000
def p_2 : ℤ := p_1 * 3^30000
def p_3 : ℤ := p_2 * 3^30000
def p_4 : ℤ := p_3 * 3^30000
def p_5 : ℤ := p_4 * 3^30000
def p_6 : ℤ := p_5 * 3^30000
def p_7 : ℤ := p_6 * 3^30000
def p_8 : ℤ := p_7 * 3^30000
def p_9 : ℤ := p_8 * 3^30000
def p_10 : ℤ := p_9 * 3^30000
def p_11 : ℤ := p_10 * 3^30000

theorem test_eval_331523 : a_comp 331523 = -1 := by
  dsimp [a_comp]
  have h_eq : ((List.range 331523).map (fun k => if Even (((3^(k+1) : ℤ) / (2^(k+1) : ℤ)).toNat) then (1 : ℤ) else (-1 : ℤ))).sum =
              ((List.range 331523).map (F_slice 1 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    dsimp [F_slice]
    rw [one_mul, zero_add]
  rw [h_eq]
  have h_start : (1 : ℤ) = p_0 := by rfl
  rw [h_start]

  have h_lt : 30000 < 2^30 := by decide
  have h_split_0 : 331523 = 30000 + 301523 := by rfl
  rw [h_split_0, sum_slice_add 30000 301523 p_0 0]
  have h_p1 : p_0 * 3^30000 = p_1 := rfl
  have h_idx1 : 0 + 30000 = 30000 := rfl
  rw [h_p1, h_idx1]
  have term_0 : ((List.range 30000).map (F_slice p_0 0)).sum = -252 := by
    have h_fuel : ((List.range 30000).map (F_slice p_0 0)).sum = (sum_hybrid 6 30000 p_0 0).1 := by
      rw [sum_hybrid_eq 6 30000 p_0 0]
    rw [h_fuel]
    rfl
  rw [term_0]

  have h_split_1 : 301523 = 30000 + 271523 := by rfl
  rw [h_split_1, sum_slice_add 30000 271523 p_1 30000]
  have h_p2 : p_1 * 3^30000 = p_2 := rfl
  have h_idx2 : 30000 + 30000 = 60000 := rfl
  rw [h_p2, h_idx2]
  have term_1 : ((List.range 30000).map (F_slice p_1 30000)).sum = 14 := by
    have h_fuel : ((List.range 30000).map (F_slice p_1 30000)).sum = (sum_hybrid 6 30000 p_1 30000).1 := by
      rw [sum_hybrid_eq 6 30000 p_1 30000]
    rw [h_fuel]
    rfl
  rw [term_1]

  have h_split_2 : 271523 = 30000 + 241523 := by rfl
  rw [h_split_2, sum_slice_add 30000 241523 p_2 60000]
  have h_p3 : p_2 * 3^30000 = p_3 := rfl
  have h_idx3 : 60000 + 30000 = 90000 := rfl
  rw [h_p3, h_idx3]
  have term_2 : ((List.range 30000).map (F_slice p_2 60000)).sum = -312 := by
    have h_fuel : ((List.range 30000).map (F_slice p_2 60000)).sum = (sum_hybrid 6 30000 p_2 60000).1 := by
      rw [sum_hybrid_eq 6 30000 p_2 60000]
    rw [h_fuel]
    rfl
  rw [term_2]

  have h_split_3 : 241523 = 30000 + 211523 := by rfl
  rw [h_split_3, sum_slice_add 30000 211523 p_3 90000]
  have h_p4 : p_3 * 3^30000 = p_4 := rfl
  have h_idx4 : 90000 + 30000 = 120000 := rfl
  rw [h_p4, h_idx4]
  have term_3 : ((List.range 30000).map (F_slice p_3 90000)).sum = 118 := by
    have h_fuel : ((List.range 30000).map (F_slice p_3 90000)).sum = (sum_hybrid 6 30000 p_3 90000).1 := by
      rw [sum_hybrid_eq 6 30000 p_3 90000]
    rw [h_fuel]
    rfl
  rw [term_3]

  have h_split_4 : 211523 = 30000 + 181523 := by rfl
  rw [h_split_4, sum_slice_add 30000 181523 p_4 120000]
  have h_p5 : p_4 * 3^30000 = p_5 := rfl
  have h_idx5 : 120000 + 30000 = 150000 := rfl
  rw [h_p5, h_idx5]
  have term_4 : ((List.range 30000).map (F_slice p_4 120000)).sum = -76 := by
    have h_fuel : ((List.range 30000).map (F_slice p_4 120000)).sum = (sum_hybrid 6 30000 p_4 120000).1 := by
      rw [sum_hybrid_eq 6 30000 p_4 120000]
    rw [h_fuel]
    rfl
  rw [term_4]

  have h_split_5 : 181523 = 30000 + 151523 := by rfl
  rw [h_split_5, sum_slice_add 30000 151523 p_5 150000]
  have h_p6 : p_5 * 3^30000 = p_6 := rfl
  have h_idx6 : 150000 + 30000 = 180000 := rfl
  rw [h_p6, h_idx6]
  have term_5 : ((List.range 30000).map (F_slice p_5 150000)).sum = -112 := by
    have h_fuel : ((List.range 30000).map (F_slice p_5 150000)).sum = (sum_hybrid 6 30000 p_5 150000).1 := by
      rw [sum_hybrid_eq 6 30000 p_5 150000]
    rw [h_fuel]
    rfl
  rw [term_5]

  have h_split_6 : 151523 = 30000 + 121523 := by rfl
  rw [h_split_6, sum_slice_add 30000 121523 p_6 180000]
  have h_p7 : p_6 * 3^30000 = p_7 := rfl
  have h_idx7 : 180000 + 30000 = 210000 := rfl
  rw [h_p7, h_idx7]
  have term_6 : ((List.range 30000).map (F_slice p_6 180000)).sum = 226 := by
    have h_fuel : ((List.range 30000).map (F_slice p_6 180000)).sum = (sum_hybrid 6 30000 p_6 180000).1 := by
      rw [sum_hybrid_eq 6 30000 p_6 180000]
    rw [h_fuel]
    rfl
  rw [term_6]

  have h_split_7 : 121523 = 30000 + 91523 := by rfl
  rw [h_split_7, sum_slice_add 30000 91523 p_7 210000]
  have h_p8 : p_7 * 3^30000 = p_8 := rfl
  have h_idx8 : 210000 + 30000 = 240000 := rfl
  rw [h_p8, h_idx8]
  have term_7 : ((List.range 30000).map (F_slice p_7 210000)).sum = -172 := by
    have h_fuel : ((List.range 30000).map (F_slice p_7 210000)).sum = (sum_hybrid 6 30000 p_7 210000).1 := by
      rw [sum_hybrid_eq 6 30000 p_7 210000]
    rw [h_fuel]
    rfl
  rw [term_7]

  have h_split_8 : 91523 = 30000 + 61523 := by rfl
  rw [h_split_8, sum_slice_add 30000 61523 p_8 240000]
  have h_p9 : p_8 * 3^30000 = p_9 := rfl
  have h_idx9 : 240000 + 30000 = 270000 := rfl
  rw [h_p9, h_idx9]
  have term_8 : ((List.range 30000).map (F_slice p_8 240000)).sum = 498 := by
    have h_fuel : ((List.range 30000).map (F_slice p_8 240000)).sum = (sum_hybrid 6 30000 p_8 240000).1 := by
      rw [sum_hybrid_eq 6 30000 p_8 240000]
    rw [h_fuel]
    rfl
  rw [term_8]

  have h_split_9 : 61523 = 30000 + 31523 := by rfl
  rw [h_split_9, sum_slice_add 30000 31523 p_9 270000]
  have h_p10 : p_9 * 3^30000 = p_10 := rfl
  have h_idx10 : 270000 + 30000 = 300000 := rfl
  rw [h_p10, h_idx10]
  have term_9 : ((List.range 30000).map (F_slice p_9 270000)).sum = -50 := by
    have h_fuel : ((List.range 30000).map (F_slice p_9 270000)).sum = (sum_hybrid 6 30000 p_9 270000).1 := by
      rw [sum_hybrid_eq 6 30000 p_9 270000]
    rw [h_fuel]
    rfl
  rw [term_9]

  have h_split_10 : 31523 = 30000 + 1523 := by rfl
  rw [h_split_10, sum_slice_add 30000 1523 p_10 300000]
  have h_p11 : p_10 * 3^30000 = p_11 := rfl
  have h_idx11 : 300000 + 30000 = 330000 := rfl
  rw [h_p11, h_idx11]
  have term_10 : ((List.range 30000).map (F_slice p_10 300000)).sum = 2 := by
    have h_fuel : ((List.range 30000).map (F_slice p_10 300000)).sum = (sum_hybrid 6 30000 p_10 300000).1 := by
      rw [sum_hybrid_eq 6 30000 p_10 300000]
    rw [h_fuel]
    rfl
  rw [term_10]

  have term_11 : ((List.range 1523).map (F_slice p_11 330000)).sum = 117 := by
    have h_fuel : ((List.range 1523).map (F_slice p_11 330000)).sum = (sum_hybrid 6 1523 p_11 330000).1 := by
      rw [sum_hybrid_eq 6 1523 p_11 330000]
    rw [h_fuel]
    rfl
  rw [term_11]
  rfl

theorem oeis_71532_conjecture_0.disproof : ¬ (∀ n : ℕ, 3 ≤ n → a n > 0) := by
  intro h
  have h_ce : a 331523 > 0 := h 331523 (by decide)
  have h_val : a 331523 = -1 := by
    rw [a_eq_a_comp, test_eval_331523]
  rw [h_val] at h_ce
  exact (by decide : ¬ (0 < -1)) h_ce
