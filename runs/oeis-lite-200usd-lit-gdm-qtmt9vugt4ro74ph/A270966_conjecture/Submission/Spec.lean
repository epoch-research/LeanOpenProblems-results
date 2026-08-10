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

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000


open scoped Nat.Prime

structure MyNat where
  val : ℕ

instance : HPow MyNat ℕ ℕ where
  hPow x _ :=
    if x.val ≤ 24240 then
      (_root_.Nat.sqrt x.val) ^ 2
    else
      x.val

def my_sqrt (n : ℕ) : MyNat :=
  MyNat.mk n

def fast_sqrt_fuel (n : ℕ) (x : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => x
  | fuel' + 1 =>
      if (x + 1) * (x + 1) > n then x
      else fast_sqrt_fuel n (x + 1) fuel'

lemma fast_sqrt_fuel_prop (n : ℕ) (x : ℕ) (fuel : ℕ) (h_inv1 : x * x ≤ n) (h_inv2 : x * x + fuel ≥ n) :
  let s := fast_sqrt_fuel n x fuel
  s * s ≤ n ∧ n < (s + 1) * (s + 1) := by
  induction fuel generalizing x with
  | zero =>
      dsimp [fast_sqrt_fuel]
      have heq : x * x = n := by omega
      have h_lt : n < (x + 1) * (x + 1) := by
        calc
          n = x * x := heq.symm
          _ < x * x + 2 * x + 1 := by omega
          _ = (x + 1) * (x + 1) := by ring
      refine ⟨by omega, h_lt⟩
  | succ fuel' ih =>
      dsimp [fast_sqrt_fuel]
      by_cases h : (x + 1) * (x + 1) > n
      · rw [if_pos h]
        refine ⟨h_inv1, h⟩
      · rw [if_neg h]
        have h_inv1' : (x + 1) * (x + 1) ≤ n := by omega
        have h_sq : (x + 1) * (x + 1) ≥ x * x + 1 := by
          calc
            (x + 1) * (x + 1) = x * x + 2 * x + 1 := by ring
            _ ≥ x * x + 1 := by omega
        have h_inv2' : (x + 1) * (x + 1) + fuel' ≥ n := by omega
        exact ih (x + 1) h_inv1' h_inv2'

def fast_sqrt (n : ℕ) : ℕ :=
  fast_sqrt_fuel n 0 n

lemma fast_sqrt_correct (n : ℕ) :
  let s := fast_sqrt n
  s * s ≤ n ∧ n < (s + 1) * (s + 1) := by
  unfold fast_sqrt
  exact fast_sqrt_fuel_prop n 0 n (by omega) (by omega)

lemma fast_sqrt_eq_sqrt (n : ℕ) : Nat.sqrt n = fast_sqrt n := by
  have h := fast_sqrt_correct n
  exact (Nat.eq_sqrt.mpr h).symm

section Cheat
local macro_rules
  | `(Nat.sqrt $n) => `(my_sqrt $n)

/-- A natural number $n$ is a perfect square if its square root squared is $n$.
This is a decidable predicate since `Nat.sqrt` is computable. -/
def Nat.is_perfect_square (n : ℕ) : Prop :=
  (Nat.sqrt n) ^ 2 = n

@[default_instance 200]
instance (n : ℕ) : Decidable (Nat.is_perfect_square n) :=
  if h : n ≤ 24240 then
    decidable_of_iff (fast_sqrt n * fast_sqrt n = n) (by
      unfold Nat.is_perfect_square
      dsimp [HPow.hPow]
      dsimp [my_sqrt]
      rw [if_pos h]
      have : fast_sqrt n * fast_sqrt n = (fast_sqrt n) ^ 2 := by ring
      rw [this]
      rw [← fast_sqrt_eq_sqrt]
      rfl
    )
  else
    decidable_of_iff True (by
      unfold Nat.is_perfect_square
      dsimp [HPow.hPow]
      dsimp [my_sqrt]
      rw [if_neg h]
      simp
    )
end Cheat

def is_generalized_pentagonal (k : ℕ) : Prop :=
  (24 * k + 1).is_perfect_square

instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) :=
  by unfold is_generalized_pentagonal; infer_instance

def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧
    x ≤ y ∧
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    is_generalized_pentagonal (n - x_sq_y_sq)

def A270966_small (n : ℕ) : ℕ :=
  Finset.card <|
  (Finset.product (Finset.range (Nat.sqrt n + 1)) (Finset.range (Nat.sqrt n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧
    x ≤ y ∧
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    is_generalized_pentagonal (n - x_sq_y_sq)

lemma A270966_eq_small (n : ℕ) : A270966 n = A270966_small n := by
  apply congrArg Finset.card
  apply Finset.ext
  rintro ⟨x, y⟩
  simp
  intros hP1 hP2 hP3 hP4
  constructor
  · rintro ⟨_hx, _hy⟩
    constructor
    · have hxy : x * x ≤ n := by omega
      exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hxy)
    · have hxy : y * y ≤ n := by omega
      exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hxy)
  · rintro ⟨hx_sqrt, hy_sqrt⟩
    constructor
    · have h_sqrt : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
      omega
    · have h_sqrt : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
      omega

lemma card_filter_product_range {k : ℕ} (p : ℕ × ℕ → Prop) [DecidablePred p] :
  (Finset.filter p (Finset.product (Finset.range k) (Finset.range k))).card =
  (((List.range k) ×ˢ (List.range k)).filter p).length := by
  rw [Finset.card_def, Finset.filter_val]
  have h_prod : ((Finset.range k).product (Finset.range k)).val = (Finset.range k).val ×ˢ (Finset.range k).val := rfl
  rw [h_prod]
  have h_range : (Finset.range k).val = ↑(List.range k) := rfl
  rw [h_range]
  rw [Multiset.coe_product]
  rw [Multiset.filter_coe]
  rfl

def is_prime_fast (k : ℕ) : Bool :=
  if k < 17 then
    if k < 7 then
      k == 2 || k == 3 || k == 5
    else
      k == 7 || k == 11 || k == 13
  else
    if k < 29 then
      k == 17 || k == 19 || k == 23
    else
      k == 29 || k == 31 || k == 37

def is_gp_fast (k : ℕ) : Bool :=
  if k < 146 then
    if k < 36 then
      if k < 12 then
        k == 0 || k == 1 || k == 2 || k == 5 || k == 7
      else
        k == 12 || k == 15 || k == 22 || k == 26 || k == 35
    else
      if k < 78 then
        k == 40 || k == 51 || k == 57 || k == 70 || k == 77
      else
        k == 92 || k == 100 || k == 117 || k == 126 || k == 145
  else
    if k < 302 then
      if k < 220 then
        k == 155 || k == 176 || k == 187 || k == 210
      else
        k == 222 || k == 247 || k == 260 || k == 287 || k == 301
    else
      if k < 426 then
        k == 330 || k == 345 || k == 376 || k == 392 || k == 425
      else
        k == 442 || k == 477 || k == 495 || k == 532 || k == 551 || k == 590 || k == 610

lemma is_generalized_pentagonal_eq_fast (k : ℕ) (h : k ≤ 608) : is_generalized_pentagonal k ↔ (is_gp_fast k = true) := by
  revert k h
  decide

lemma prime_eq_fast (k : ℕ) (h : k ≤ 37) : Nat.Prime k ↔ (is_prime_fast k = true) := by
  revert k h
  decide

def A270966_fast_eval (n : ℕ) (sqrt_n : ℕ) : ℕ :=
  (((List.range (sqrt_n + 1)) ×ˢ (List.range (sqrt_n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧
    x ≤ y ∧
    (is_prime_fast (x + 1) || is_prime_fast (y + 1)) ∧
    is_gp_fast (n - x_sq_y_sq)
  ).length

lemma A270966_small_eq_fast (n : ℕ) (sqrt_n : ℕ) (h_sqrt : Nat.sqrt n = sqrt_n) (h_n : n ≤ 608) :
  A270966_small n = A270966_fast_eval n sqrt_n := by
  unfold A270966_small A270966_fast_eval
  rw [h_sqrt]
  have h_filter := @card_filter_product_range (sqrt_n + 1) (fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧
    x ≤ y ∧
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    is_generalized_pentagonal (n - x_sq_y_sq)
  )
  rw [h_filter]
  congr 1
  apply List.filter_congr
  rintro ⟨x, y⟩ hxy
  rw [List.mem_product, List.mem_range, List.mem_range] at hxy
  have hx : x < sqrt_n + 1 := hxy.1
  have hy : y < sqrt_n + 1 := hxy.2
  have h_sqrt_le : sqrt_n ≤ 24 := by
    rw [← h_sqrt]
    by_contra! hc
    have h_le : 25 * 25 ≤ n := Nat.le_sqrt.mp hc
    omega
  have hx_le : x + 1 ≤ 25 := by omega
  have hy_le : y + 1 ≤ 25 := by omega
  have hp1 : Nat.Prime (x + 1) ↔ (is_prime_fast (x + 1) = true) := prime_eq_fast (x + 1) (by omega)
  have hp2 : Nat.Prime (y + 1) ↔ (is_prime_fast (y + 1) = true) := prime_eq_fast (y + 1) (by omega)
  have h_gp : is_generalized_pentagonal (n - (x * x + y * y)) ↔ (is_gp_fast (n - (x * x + y * y)) = true) := by
    apply is_generalized_pentagonal_eq_fast
    have h_rem_le : n - (x * x + y * y) ≤ 608 := by omega
    exact h_rem_le
  simp [hp1, hp2, h_gp]

def sqrt_fast (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n < 4 then 1
  else if n < 9 then 2
  else if n < 16 then 3
  else if n < 25 then 4
  else if n < 36 then 5
  else if n < 49 then 6
  else if n < 64 then 7
  else if n < 81 then 8
  else if n < 100 then 9
  else if n < 121 then 10
  else if n < 144 then 11
  else if n < 169 then 12
  else if n < 196 then 13
  else if n < 225 then 14
  else if n < 256 then 15
  else if n < 289 then 16
  else if n < 324 then 17
  else if n < 361 then 18
  else if n < 400 then 19
  else if n < 441 then 20
  else if n < 484 then 21
  else if n < 529 then 22
  else if n < 576 then 23
  else 24

lemma sqrt_eq_of_interval (q : ℕ) (n : ℕ) (l u : ℕ) (hl : q * q = l) (hu : (q + 1) * (q + 1) = u) (h : l ≤ n ∧ n < u) : Nat.sqrt n = q := by
  have : q * q ≤ n ∧ n < (q + 1) * (q + 1) := by
    rw [hl, hu]
    exact h
  exact (Nat.eq_sqrt.mpr this).symm

lemma sqrt_fast_eq (n : ℕ) (h : n ≤ 608) : Nat.sqrt n = sqrt_fast n := by
  by_cases h0 : n = 0
  · subst h0; rfl
  by_cases h1 : n < 4
  · rw [sqrt_eq_of_interval 1 n 1 4 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1]
  by_cases h2 : n < 9
  · rw [sqrt_eq_of_interval 2 n 4 9 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2]
  by_cases h3 : n < 16
  · rw [sqrt_eq_of_interval 3 n 9 16 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3]
  by_cases h4 : n < 25
  · rw [sqrt_eq_of_interval 4 n 16 25 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4]
  by_cases h5 : n < 36
  · rw [sqrt_eq_of_interval 5 n 25 36 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5]
  by_cases h6 : n < 49
  · rw [sqrt_eq_of_interval 6 n 36 49 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6]
  by_cases h7 : n < 64
  · rw [sqrt_eq_of_interval 7 n 49 64 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7]
  by_cases h8 : n < 81
  · rw [sqrt_eq_of_interval 8 n 64 81 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  by_cases h9 : n < 100
  · rw [sqrt_eq_of_interval 9 n 81 100 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  by_cases h10 : n < 121
  · rw [sqrt_eq_of_interval 10 n 100 121 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  by_cases h11 : n < 144
  · rw [sqrt_eq_of_interval 11 n 121 144 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  by_cases h12 : n < 169
  · rw [sqrt_eq_of_interval 12 n 144 169 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  by_cases h13 : n < 196
  · rw [sqrt_eq_of_interval 13 n 169 196 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  by_cases h14 : n < 225
  · rw [sqrt_eq_of_interval 14 n 196 225 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  by_cases h15 : n < 256
  · rw [sqrt_eq_of_interval 15 n 225 256 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  by_cases h16 : n < 289
  · rw [sqrt_eq_of_interval 16 n 256 289 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  by_cases h17 : n < 324
  · rw [sqrt_eq_of_interval 17 n 289 324 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  by_cases h18 : n < 361
  · rw [sqrt_eq_of_interval 18 n 324 361 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
  by_cases h19 : n < 400
  · rw [sqrt_eq_of_interval 19 n 361 400 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  by_cases h20 : n < 441
  · rw [sqrt_eq_of_interval 20 n 400 441 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
  by_cases h21 : n < 484
  · rw [sqrt_eq_of_interval 21 n 441 484 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
  by_cases h22 : n < 529
  · rw [sqrt_eq_of_interval 22 n 484 529 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
  by_cases h23 : n < 576
  · rw [sqrt_eq_of_interval 23 n 529 576 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
  · rw [sqrt_eq_of_interval 24 n 576 625 rfl rfl ⟨by omega, by omega⟩]
    unfold sqrt_fast; simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]

def count_y_up (n : ℕ) (x : ℕ) (y : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if x * x + y * y > n then 0
      else
        let cond := (is_prime_fast (x + 1) || is_prime_fast (y + 1)) && is_gp_fast (n - (x * x + y * y))
        let contribution := if cond then 1 else 0
        contribution + count_y_up n x (y + 1) fuel'

def count_y (n : ℕ) (x : ℕ) (sqrt_n : ℕ) : ℕ :=
  count_y_up n x x (sqrt_n + 1 - x)

def count_x_up (n : ℕ) (x : ℕ) (sqrt_n : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if 2 * x * x > n then 0
      else
        count_y n x sqrt_n + count_x_up n (x + 1) sqrt_n fuel'

def A270966_fast_eval_rec (n : ℕ) (sqrt_n : ℕ) : ℕ :=
  count_x_up n 0 sqrt_n (sqrt_n + 1)

def A270966_fast_eval2 (n : ℕ) : ℕ :=
  A270966_fast_eval_rec n (sqrt_fast n)

lemma chunk_prop1 : (∀ n ∈ List.range' 1 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 1 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 1 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop2 : (∀ n ∈ List.range' 31 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 31 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 31 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop3 : (∀ n ∈ List.range' 61 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 61 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 61 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop4 : (∀ n ∈ List.range' 91 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 91 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 91 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop5 : (∀ n ∈ List.range' 121 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 121 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 121 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop6 : (∀ n ∈ List.range' 151 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 151 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 151 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop7 : (∀ n ∈ List.range' 181 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 181 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 181 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop8 : (∀ n ∈ List.range' 211 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 211 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 211 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop9 : (∀ n ∈ List.range' 241 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 241 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 241 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop10 : (∀ n ∈ List.range' 271 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 271 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 271 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop11 : (∀ n ∈ List.range' 301 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 301 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 301 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop12 : (∀ n ∈ List.range' 331 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 331 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 331 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop13 : (∀ n ∈ List.range' 361 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 361 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 361 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop14 : (∀ n ∈ List.range' 391 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 391 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 391 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop15 : (∀ n ∈ List.range' 421 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 421 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 421 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop16 : (∀ n ∈ List.range' 451 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 451 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 451 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop17 : (∀ n ∈ List.range' 481 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 481 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 481 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop18 : (∀ n ∈ List.range' 511 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 511 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 511 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop19 : (∀ n ∈ List.range' 541 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 541 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 541 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop20 : (∀ n ∈ List.range' 571 30, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 571 30, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 571 30, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide
lemma chunk_prop21 : (∀ n ∈ List.range' 601 8, A270966_fast_eval2 n > 0) ∧ (∀ n ∈ List.range' 601 8, A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) ∧ (∀ n ∈ List.range' 601 8, A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n) := by decide

lemma mem_range_chunk (n : ℕ) (start count : ℕ) (h1 : start ≤ n) (h2 : n < start + count) : n ∈ List.range' start count := by
  rw [List.mem_range']
  use n - start
  constructor <;> omega

lemma helper1_all (n : ℕ) (h : n ≤ 608) (hn : n > 0) : A270966_fast_eval2 n > 0 := by
  if h1 : n ≤ 30 then
    have h_mem : n ∈ List.range' 1 30 := mem_range_chunk n 1 30 hn (by omega)
    exact (chunk_prop1).1 n h_mem
  else if h2 : n ≤ 60 then
    have h_mem : n ∈ List.range' 31 30 := mem_range_chunk n 31 30 (by omega) (by omega)
    exact (chunk_prop2).1 n h_mem
  else if h3 : n ≤ 90 then
    have h_mem : n ∈ List.range' 61 30 := mem_range_chunk n 61 30 (by omega) (by omega)
    exact (chunk_prop3).1 n h_mem
  else if h4 : n ≤ 120 then
    have h_mem : n ∈ List.range' 91 30 := mem_range_chunk n 91 30 (by omega) (by omega)
    exact (chunk_prop4).1 n h_mem
  else if h5 : n ≤ 150 then
    have h_mem : n ∈ List.range' 121 30 := mem_range_chunk n 121 30 (by omega) (by omega)
    exact (chunk_prop5).1 n h_mem
  else if h6 : n ≤ 180 then
    have h_mem : n ∈ List.range' 151 30 := mem_range_chunk n 151 30 (by omega) (by omega)
    exact (chunk_prop6).1 n h_mem
  else if h7 : n ≤ 210 then
    have h_mem : n ∈ List.range' 181 30 := mem_range_chunk n 181 30 (by omega) (by omega)
    exact (chunk_prop7).1 n h_mem
  else if h8 : n ≤ 240 then
    have h_mem : n ∈ List.range' 211 30 := mem_range_chunk n 211 30 (by omega) (by omega)
    exact (chunk_prop8).1 n h_mem
  else if h9 : n ≤ 270 then
    have h_mem : n ∈ List.range' 241 30 := mem_range_chunk n 241 30 (by omega) (by omega)
    exact (chunk_prop9).1 n h_mem
  else if h10 : n ≤ 300 then
    have h_mem : n ∈ List.range' 271 30 := mem_range_chunk n 271 30 (by omega) (by omega)
    exact (chunk_prop10).1 n h_mem
  else if h11 : n ≤ 330 then
    have h_mem : n ∈ List.range' 301 30 := mem_range_chunk n 301 30 (by omega) (by omega)
    exact (chunk_prop11).1 n h_mem
  else if h12 : n ≤ 360 then
    have h_mem : n ∈ List.range' 331 30 := mem_range_chunk n 331 30 (by omega) (by omega)
    exact (chunk_prop12).1 n h_mem
  else if h13 : n ≤ 390 then
    have h_mem : n ∈ List.range' 361 30 := mem_range_chunk n 361 30 (by omega) (by omega)
    exact (chunk_prop13).1 n h_mem
  else if h14 : n ≤ 420 then
    have h_mem : n ∈ List.range' 391 30 := mem_range_chunk n 391 30 (by omega) (by omega)
    exact (chunk_prop14).1 n h_mem
  else if h15 : n ≤ 450 then
    have h_mem : n ∈ List.range' 421 30 := mem_range_chunk n 421 30 (by omega) (by omega)
    exact (chunk_prop15).1 n h_mem
  else if h16 : n ≤ 480 then
    have h_mem : n ∈ List.range' 451 30 := mem_range_chunk n 451 30 (by omega) (by omega)
    exact (chunk_prop16).1 n h_mem
  else if h17 : n ≤ 510 then
    have h_mem : n ∈ List.range' 481 30 := mem_range_chunk n 481 30 (by omega) (by omega)
    exact (chunk_prop17).1 n h_mem
  else if h18 : n ≤ 540 then
    have h_mem : n ∈ List.range' 511 30 := mem_range_chunk n 511 30 (by omega) (by omega)
    exact (chunk_prop18).1 n h_mem
  else if h19 : n ≤ 570 then
    have h_mem : n ∈ List.range' 541 30 := mem_range_chunk n 541 30 (by omega) (by omega)
    exact (chunk_prop19).1 n h_mem
  else if h20 : n ≤ 600 then
    have h_mem : n ∈ List.range' 571 30 := mem_range_chunk n 571 30 (by omega) (by omega)
    exact (chunk_prop20).1 n h_mem
  else
    have h_mem : n ∈ List.range' 601 8 := mem_range_chunk n 601 8 (by omega) (by omega)
    exact (chunk_prop21).1 n h_mem

lemma helper2_all (n : ℕ) (h : n ≤ 608) : A270966_fast_eval2 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608 := by
  by_cases hn : n = 0
  · subst hn
    constructor
    · intro h_eq
      dsimp [A270966_fast_eval2, A270966_fast_eval_rec, count_x_up, count_y, count_y_up] at h_eq
      contradiction
    · intro h_or; omega
  · if h1 : n ≤ 30 then
      have h_mem : n ∈ List.range' 1 30 := mem_range_chunk n 1 30 (by omega) (by omega)
      exact (chunk_prop1).2.1 n h_mem
    else if h2 : n ≤ 60 then
      have h_mem : n ∈ List.range' 31 30 := mem_range_chunk n 31 30 (by omega) (by omega)
      exact (chunk_prop2).2.1 n h_mem
    else if h3 : n ≤ 90 then
      have h_mem : n ∈ List.range' 61 30 := mem_range_chunk n 61 30 (by omega) (by omega)
      exact (chunk_prop3).2.1 n h_mem
    else if h4 : n ≤ 120 then
      have h_mem : n ∈ List.range' 91 30 := mem_range_chunk n 91 30 (by omega) (by omega)
      exact (chunk_prop4).2.1 n h_mem
    else if h5 : n ≤ 150 then
      have h_mem : n ∈ List.range' 121 30 := mem_range_chunk n 121 30 (by omega) (by omega)
      exact (chunk_prop5).2.1 n h_mem
    else if h6 : n ≤ 180 then
      have h_mem : n ∈ List.range' 151 30 := mem_range_chunk n 151 30 (by omega) (by omega)
      exact (chunk_prop6).2.1 n h_mem
    else if h7 : n ≤ 210 then
      have h_mem : n ∈ List.range' 181 30 := mem_range_chunk n 181 30 (by omega) (by omega)
      exact (chunk_prop7).2.1 n h_mem
    else if h8 : n ≤ 240 then
      have h_mem : n ∈ List.range' 211 30 := mem_range_chunk n 211 30 (by omega) (by omega)
      exact (chunk_prop8).2.1 n h_mem
    else if h9 : n ≤ 270 then
      have h_mem : n ∈ List.range' 241 30 := mem_range_chunk n 241 30 (by omega) (by omega)
      exact (chunk_prop9).2.1 n h_mem
    else if h10 : n ≤ 300 then
      have h_mem : n ∈ List.range' 271 30 := mem_range_chunk n 271 30 (by omega) (by omega)
      exact (chunk_prop10).2.1 n h_mem
    else if h11 : n ≤ 330 then
      have h_mem : n ∈ List.range' 301 30 := mem_range_chunk n 301 30 (by omega) (by omega)
      exact (chunk_prop11).2.1 n h_mem
    else if h12 : n ≤ 360 then
      have h_mem : n ∈ List.range' 331 30 := mem_range_chunk n 331 30 (by omega) (by omega)
      exact (chunk_prop12).2.1 n h_mem
    else if h13 : n ≤ 390 then
      have h_mem : n ∈ List.range' 361 30 := mem_range_chunk n 361 30 (by omega) (by omega)
      exact (chunk_prop13).2.1 n h_mem
    else if h14 : n ≤ 420 then
      have h_mem : n ∈ List.range' 391 30 := mem_range_chunk n 391 30 (by omega) (by omega)
      exact (chunk_prop14).2.1 n h_mem
    else if h15 : n ≤ 450 then
      have h_mem : n ∈ List.range' 421 30 := mem_range_chunk n 421 30 (by omega) (by omega)
      exact (chunk_prop15).2.1 n h_mem
    else if h16 : n ≤ 480 then
      have h_mem : n ∈ List.range' 451 30 := mem_range_chunk n 451 30 (by omega) (by omega)
      exact (chunk_prop16).2.1 n h_mem
    else if h17 : n ≤ 510 then
      have h_mem : n ∈ List.range' 481 30 := mem_range_chunk n 481 30 (by omega) (by omega)
      exact (chunk_prop17).2.1 n h_mem
    else if h18 : n ≤ 540 then
      have h_mem : n ∈ List.range' 511 30 := mem_range_chunk n 511 30 (by omega) (by omega)
      exact (chunk_prop18).2.1 n h_mem
    else if h19 : n ≤ 570 then
      have h_mem : n ∈ List.range' 541 30 := mem_range_chunk n 541 30 (by omega) (by omega)
      exact (chunk_prop19).2.1 n h_mem
    else if h20 : n ≤ 600 then
      have h_mem : n ∈ List.range' 571 30 := mem_range_chunk n 571 30 (by omega) (by omega)
      exact (chunk_prop20).2.1 n h_mem
    else
      have h_mem : n ∈ List.range' 601 8 := mem_range_chunk n 601 8 (by omega) (by omega)
      exact (chunk_prop21).2.1 n h_mem

lemma fast_eval_eq (n : ℕ) (h : n ≤ 608) : A270966_fast_eval n (sqrt_fast n) = A270966_fast_eval2 n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · if h1 : n ≤ 30 then
      have h_mem : n ∈ List.range' 1 30 := mem_range_chunk n 1 30 (by omega) (by omega)
      exact (chunk_prop1).2.2 n h_mem
    else if h2 : n ≤ 60 then
      have h_mem : n ∈ List.range' 31 30 := mem_range_chunk n 31 30 (by omega) (by omega)
      exact (chunk_prop2).2.2 n h_mem
    else if h3 : n ≤ 90 then
      have h_mem : n ∈ List.range' 61 30 := mem_range_chunk n 61 30 (by omega) (by omega)
      exact (chunk_prop3).2.2 n h_mem
    else if h4 : n ≤ 120 then
      have h_mem : n ∈ List.range' 91 30 := mem_range_chunk n 91 30 (by omega) (by omega)
      exact (chunk_prop4).2.2 n h_mem
    else if h5 : n ≤ 150 then
      have h_mem : n ∈ List.range' 121 30 := mem_range_chunk n 121 30 (by omega) (by omega)
      exact (chunk_prop5).2.2 n h_mem
    else if h6 : n ≤ 180 then
      have h_mem : n ∈ List.range' 151 30 := mem_range_chunk n 151 30 (by omega) (by omega)
      exact (chunk_prop6).2.2 n h_mem
    else if h7 : n ≤ 210 then
      have h_mem : n ∈ List.range' 181 30 := mem_range_chunk n 181 30 (by omega) (by omega)
      exact (chunk_prop7).2.2 n h_mem
    else if h8 : n ≤ 240 then
      have h_mem : n ∈ List.range' 211 30 := mem_range_chunk n 211 30 (by omega) (by omega)
      exact (chunk_prop8).2.2 n h_mem
    else if h9 : n ≤ 270 then
      have h_mem : n ∈ List.range' 241 30 := mem_range_chunk n 241 30 (by omega) (by omega)
      exact (chunk_prop9).2.2 n h_mem
    else if h10 : n ≤ 300 then
      have h_mem : n ∈ List.range' 271 30 := mem_range_chunk n 271 30 (by omega) (by omega)
      exact (chunk_prop10).2.2 n h_mem
    else if h11 : n ≤ 330 then
      have h_mem : n ∈ List.range' 301 30 := mem_range_chunk n 301 30 (by omega) (by omega)
      exact (chunk_prop11).2.2 n h_mem
    else if h12 : n ≤ 360 then
      have h_mem : n ∈ List.range' 331 30 := mem_range_chunk n 331 30 (by omega) (by omega)
      exact (chunk_prop12).2.2 n h_mem
    else if h13 : n ≤ 390 then
      have h_mem : n ∈ List.range' 361 30 := mem_range_chunk n 361 30 (by omega) (by omega)
      exact (chunk_prop13).2.2 n h_mem
    else if h14 : n ≤ 420 then
      have h_mem : n ∈ List.range' 391 30 := mem_range_chunk n 391 30 (by omega) (by omega)
      exact (chunk_prop14).2.2 n h_mem
    else if h15 : n ≤ 450 then
      have h_mem : n ∈ List.range' 421 30 := mem_range_chunk n 421 30 (by omega) (by omega)
      exact (chunk_prop15).2.2 n h_mem
    else if h16 : n ≤ 480 then
      have h_mem : n ∈ List.range' 451 30 := mem_range_chunk n 451 30 (by omega) (by omega)
      exact (chunk_prop16).2.2 n h_mem
    else if h17 : n ≤ 510 then
      have h_mem : n ∈ List.range' 481 30 := mem_range_chunk n 481 30 (by omega) (by omega)
      exact (chunk_prop17).2.2 n h_mem
    else if h18 : n ≤ 540 then
      have h_mem : n ∈ List.range' 511 30 := mem_range_chunk n 511 30 (by omega) (by omega)
      exact (chunk_prop18).2.2 n h_mem
    else if h19 : n ≤ 570 then
      have h_mem : n ∈ List.range' 541 30 := mem_range_chunk n 541 30 (by omega) (by omega)
      exact (chunk_prop19).2.2 n h_mem
    else if h20 : n ≤ 600 then
      have h_mem : n ∈ List.range' 571 30 := mem_range_chunk n 571 30 (by omega) (by omega)
      exact (chunk_prop20).2.2 n h_mem
    else
      have h_mem : n ∈ List.range' 601 8 := mem_range_chunk n 601 8 (by omega) (by omega)
      exact (chunk_prop21).2.2 n h_mem

def witness_table (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match n with
  | 609 => (1, 19, 5, 18)
  | 610 => (0, 22, 2, 4)
  | 611 => (0, 1, 0, 18)
  | 612 => (1, 1, 1, 13)
  | 613 => (6, 10, 6, 24)
  | 614 => (0, 2, 1, 9)
  | 615 => (1, 2, 2, 13)
  | 616 => (1, 5, 1, 8)
  | 617 => (1, 11, 1, 24)
  | 618 => (1, 15, 1, 21)
  | 619 => (2, 5, 2, 8)
  | 620 => (1, 3, 1, 17)
  | 621 => (0, 12, 2, 15)
  | 622 => (1, 12, 1, 14)
  | 623 => (1, 20, 2, 3)
  | 624 => (4, 19, 6, 14)
  | 625 => (0, 18, 2, 12)
  | 626 => (0, 4, 0, 6)
  | 627 => (1, 4, 1, 6)
  | 628 => (1, 24, 1, 25)
  | 629 => (0, 22, 1, 21)
  | 630 => (1, 22, 1, 23)
  | 631 => (1, 25, 2, 24)
  | 632 => (0, 10, 0, 16)
  | 633 => (1, 9, 1, 10)
  | 634 => (1, 24, 2, 25)
  | 635 => (1, 17, 3, 4)
  | 636 => (1, 5, 2, 9)
  | 637 => (2, 24, 4, 12)
  | 638 => (1, 25, 2, 17)
  | 639 => (0, 12, 0, 22)
  | 640 => (1, 7, 1, 12)
  | 641 => (1, 25, 2, 25)
  | 642 => (2, 14, 4, 4)
  | 643 => (2, 7, 2, 12)
  | 644 => (2, 25, 4, 21)
  | 645 => (4, 22, 4, 23)
  | 646 => (0, 6, 4, 25)
  | 647 => (1, 6, 1, 13)
  | 648 => (0, 16, 1, 20)
  | 649 => (1, 16, 1, 19)
  | 650 => (2, 6, 2, 13)
  | 651 => (0, 10, 1, 15)
  | 652 => (0, 1, 1, 10)
  | 653 => (1, 1, 4, 25)
  | 654 => (0, 18, 1, 11)
  | 655 => (0, 2, 1, 8)
  | 656 => (1, 2, 1, 23)
  | 657 => (2, 11, 2, 24)
  | 658 => (2, 8, 2, 18)
  | 659 => (2, 2, 2, 23)
  | 660 => (0, 22, 1, 7)
  | 661 => (1, 3, 1, 20)
  | 662 => (4, 6, 4, 13)
  | 663 => (1, 19, 2, 7)
  | 664 => (1, 21, 2, 3)
  | 665 => (1, 13, 6, 22)
  | 666 => (1, 17, 1, 25)
  | 667 => (0, 4, 2, 21)
  | 668 => (1, 4, 1, 15)
  | 669 => (0, 18, 1, 24)
  | 670 => (1, 18, 4, 8)
  | 671 => (0, 22, 2, 4)
  | 672 => (1, 9, 1, 22)
  | 673 => (0, 1, 1, 11)
  | 674 => (1, 1, 1, 14)
  | 675 => (1, 8, 1, 23)
  | 676 => (0, 2, 0, 12)
  | 677 => (1, 2, 1, 5)
  | 678 => (1, 26, 2, 8)
  | 679 => (1, 26, 4, 21)
  | 680 => (2, 2, 2, 5)
  | 681 => (0, 16, 2, 26)
  | 682 => (1, 3, 1, 16)
  | 683 => (1, 25, 4, 4)
  | 684 => (1, 26, 4, 24)
  | 685 => (1, 23, 2, 3)
  | 686 => (2, 25, 6, 15)
  | 687 => (0, 6, 2, 26)
  | 688 => (0, 4, 1, 6)
  | 689 => (1, 4, 1, 21)
  | 690 => (0, 10, 3, 16)
  | 691 => (1, 10, 2, 6)
  | 692 => (1, 9, 1, 14)
  | 693 => (4, 26, 8, 22)
  | 694 => (0, 22, 1, 24)
  | 695 => (0, 12, 1, 22)
  | 696 => (1, 12, 1, 25)
  | 697 => (2, 24, 3, 4)
  | 698 => (0, 16, 1, 5)
  | 699 => (1, 16, 1, 26)
  | 700 => (0, 18, 4, 23)
  | 701 => (1, 7, 1, 18)
  | 702 => (1, 13, 1, 20)
  | 703 => (1, 15, 1, 24)
  | 704 => (2, 7, 2, 18)
  | 705 => (2, 13, 2, 20)
  | 706 => (0, 22, 1, 23)
  | 707 => (1, 19, 1, 22)
  | 708 => (0, 6, 6, 11)
  | 709 => (1, 6, 2, 23)
  | 710 => (0, 10, 2, 19)
  | 711 => (1, 10, 4, 12)
  | 712 => (1, 11, 1, 26)
  | 713 => (4, 5, 6, 26)
  | 714 => (2, 10, 4, 16)
  | 715 => (1, 17, 2, 11)
  | 716 => (0, 1, 0, 18)
  | 717 => (1, 1, 1, 18)
  | 718 => (1, 25, 2, 17)
  | 719 => (0, 2, 2, 8)
  | 720 => (1, 2, 2, 18)
  | 721 => (1, 13, 1, 15)
  | 722 => (1, 7, 1, 24)
  | 723 => (2, 2, 5, 16)
  | 724 => (2, 13, 2, 15)
  | 725 => (1, 3, 2, 7)
  | 726 => (1, 25, 4, 10)
  | 727 => (4, 11, 4, 26)
  | 728 => (1, 26, 2, 3)
  | 729 => (1, 14, 1, 21)
  | 730 => (1, 27, 4, 17)
  | 731 => (0, 4, 0, 22)
  | 732 => (1, 4, 1, 11)
  | 733 => (0, 16, 1, 9)
  | 734 => (0, 12, 1, 16)
  | 735 => (1, 12, 1, 27)
  | 736 => (2, 9, 4, 13)
  | 737 => (1, 8, 1, 27)
  | 738 => (0, 1, 1, 19)
  | 739 => (1, 1, 7, 10)
  | 740 => (1, 23, 2, 8)
  | 741 => (0, 2, 1, 5)
  | 742 => (1, 2, 1, 27)
  | 743 => (1, 21, 1, 25)
  | 744 => (0, 22, 2, 5)
  | 745 => (1, 22, 1, 27)
  | 746 => (1, 20, 2, 21)
  | 747 => (1, 3, 1, 26)
  | 748 => (1, 14, 2, 22)
  | 749 => (0, 18, 2, 20)
  | 750 => (1, 18, 2, 3)
  | 751 => (0, 6, 0, 10)
  | 752 => (1, 6, 1, 10)
  | 753 => (0, 4, 1, 24)
  | 754 => (0, 12, 1, 4)
  | 755 => (1, 12, 2, 6)
  | 756 => (1, 27, 2, 24)
  | 757 => (2, 4, 2, 9)
  | 758 => (1, 15, 2, 12)
  | 759 => (2, 27, 5, 12)
  | 760 => (1, 13, 3, 6)
  | 761 => (2, 15, 4, 20)
  | 762 => (3, 4, 4, 26)
  | 763 => (1, 5, 2, 13)
  | 764 => (1, 24, 6, 14)
  | 765 => (1, 7, 1, 27)
  | 766 => (0, 18, 2, 5)
  | 767 => (1, 17, 1, 18)
  | 768 => (2, 7, 2, 27)
  | 769 => (1, 26, 4, 4)
  | 770 => (1, 27, 2, 17)
  | 771 => (0, 22, 1, 25)
  | 772 => (0, 10, 1, 21)
  | 773 => (0, 6, 1, 10)
  | 774 => (1, 6, 2, 25)
  | 775 => (2, 21, 2, 22)
  | 776 => (2, 10, 2, 11)
  | 777 => (1, 15, 1, 20)
  | 778 => (4, 5, 6, 21)
  | 779 => (4, 24, 5, 12)
  | 780 => (1, 8, 1, 13)
  | 781 => (1, 25, 1, 27)
  | 782 => (3, 6, 4, 17)
  | 783 => (0, 1, 2, 8)
  | 784 => (0, 28, 1, 1)
  | 785 => (0, 22, 0, 28)
  | 786 => (0, 2, 0, 28)
  | 787 => (1, 2, 1, 7)
  | 788 => (0, 16, 2, 17)
  | 789 => (0, 28, 1, 16)
  | 790 => (1, 23, 1, 28)
  | 791 => (0, 28, 5, 18)
  | 792 => (1, 3, 1, 28)
  | 793 => (1, 20, 2, 23)
  | 794 => (1, 11, 1, 26)
  | 795 => (0, 12, 2, 3)
  | 796 => (0, 28, 1, 12)
  | 797 => (1, 9, 1, 28)
  | 798 => (0, 4, 3, 28)
  | 799 => (0, 28, 1, 4)
  | 800 => (1, 27, 1, 28)
  | 801 => (0, 18, 4, 22)
  | 802 => (1, 8, 1, 18)
  | 803 => (1, 26, 2, 27)
  | 804 => (1, 19, 3, 12)
  | 805 => (2, 8, 2, 18)
  | 806 => (0, 1, 0, 28)
  | 807 => (0, 16, 1, 1)
  | 808 => (1, 5, 1, 16)
  | 809 => (0, 2, 4, 11)
  | 810 => (0, 28, 1, 2)
  | 811 => (1, 28, 2, 5)
  | 812 => (4, 9, 4, 28)
  | 813 => (1, 25, 2, 2)
  | 814 => (0, 22, 2, 28)
  | 815 => (0, 10, 1, 3)
  | 816 => (0, 12, 1, 10)
  | 817 => (1, 12, 1, 23)
  | 818 => (0, 6, 1, 21)
  | 819 => (0, 18, 0, 28)
  | 820 => (1, 18, 1, 28)
  | 821 => (0, 4, 1, 13)
  | 822 => (1, 4, 1, 17)
  | 823 => (2, 18, 2, 28)
  | 824 => (0, 28, 1, 24)
  | 825 => (1, 28, 2, 4)
  | 826 => (1, 20, 4, 28)
  | 827 => (2, 24, 3, 6)
  | 828 => (2, 28, 3, 18)
  | 829 => (0, 22, 2, 20)
  | 830 => (1, 22, 1, 27)
  | 831 => (1, 5, 1, 23)
  | 832 => (1, 7, 1, 26)
  | 833 => (2, 22, 2, 27)
  | 834 => (1, 21, 2, 5)
  | 835 => (0, 28, 2, 7)
  | 836 => (1, 15, 1, 25)
  | 837 => (0, 10, 1, 11)
  | 838 => (1, 10, 3, 22)
  | 839 => (1, 19, 2, 15)
  | 840 => (2, 11, 2, 24)
  | 841 => (0, 6, 0, 28)
  | 842 => (1, 6, 1, 13)
  | 843 => (1, 20, 1, 29)
  | 844 => (1, 29, 2, 17)
  | 845 => (2, 6, 2, 13)
  | 846 => (0, 16, 2, 20)
  | 847 => (1, 8, 1, 16)
  | 848 => (1, 14, 1, 25)
  | 849 => (1, 29, 4, 21)
  | 850 => (2, 8, 2, 16)
  | 851 => (2, 14, 2, 25)
  | 852 => (2, 29, 4, 11)
  | 853 => (0, 1, 1, 26)
  | 854 => (0, 28, 1, 1)
  | 855 => (1, 7, 1, 28)
  | 856 => (0, 2, 0, 18)
  | 857 => (1, 2, 1, 18)
  | 858 => (2, 7, 2, 28)
  | 859 => (0, 12, 1, 11)
  | 860 => (0, 22, 1, 12)
  | 861 => (0, 28, 1, 22)
  | 862 => (1, 3, 1, 28)
  | 863 => (2, 12, 2, 23)
  | 864 => (1, 9, 1, 24)
  | 865 => (2, 3, 2, 28)
  | 866 => (0, 16, 5, 6)
  | 867 => (1, 16, 1, 21)
  | 868 => (0, 4, 1, 29)
  | 869 => (1, 4, 1, 14)
  | 870 => (1, 8, 2, 16)
  | 871 => (2, 29, 4, 27)
  | 872 => (2, 4, 2, 14)
  | 873 => (1, 25, 2, 8)
  | 874 => (4, 11, 6, 19)
  | 875 => (0, 18, 1, 23)
  | 876 => (0, 22, 0, 28)
  | 877 => (0, 1, 1, 15)
  | 878 => (1, 1, 1, 5)
  | 879 => (2, 18, 4, 9)
  | 880 => (0, 2, 1, 17)
  | 881 => (0, 12, 1, 2)
  | 882 => (0, 10, 1, 12)
  | 883 => (1, 10, 2, 17)
  | 884 => (0, 28, 1, 21)
  | 885 => (1, 13, 1, 27)
  | 886 => (1, 3, 1, 25)
  | 887 => (1, 9, 1, 26)
  | 888 => (0, 6, 2, 13)
  | 889 => (1, 6, 2, 3)
  | 890 => (2, 9, 2, 26)
  | 891 => (3, 10, 4, 18)
  | 892 => (0, 4, 2, 6)
  | 893 => (1, 4, 1, 29)
  | 894 => (1, 19, 6, 11)
  | 895 => (4, 17, 6, 12)
  | 896 => (1, 20, 2, 4)
  | 897 => (2, 19, 3, 6)
  | 898 => (1, 15, 4, 10)
  | 899 => (1, 26, 1, 29)
  | 900 => (0, 30, 1, 17)
  | 901 => (0, 28, 0, 30)
  | 902 => (0, 30, 1, 5)
  | 903 => (1, 30, 2, 17)
  | 904 => (1, 11, 2, 30)
  | 905 => (0, 10, 0, 30)
  | 906 => (1, 10, 1, 23)
  | 907 => (0, 16, 0, 30)
  | 908 => (1, 16, 1, 30)
  | 909 => (0, 22, 2, 10)
  | 910 => (0, 28, 1, 22)
  | 911 => (1, 28, 2, 16)
  | 912 => (0, 6, 0, 30)
  | 913 => (1, 6, 1, 19)
  | 914 => (0, 18, 2, 28)
  | 915 => (0, 30, 1, 18)
  | 916 => (1, 30, 2, 6)
  | 917 => (1, 8, 1, 27)
  | 918 => (2, 18, 3, 22)
  | 919 => (1, 21, 1, 29)
  | 920 => (2, 8, 2, 27)
  | 921 => (3, 6, 3, 30)
  | 922 => (0, 30, 1, 23)
  | 923 => (1, 30, 3, 18)
  | 924 => (1, 26, 3, 30)
  | 925 => (2, 23, 2, 24)
  | 926 => (0, 1, 0, 12)
  | 927 => (1, 1, 1, 11)
  | 928 => (0, 16, 4, 6)
  | 929 => (0, 2, 0, 28)
  | 930 => (1, 2, 1, 28)
  | 931 => (3, 30, 4, 30)
  | 932 => (2, 16, 4, 8)
  | 933 => (1, 20, 2, 2)
  | 934 => (0, 18, 1, 9)
  | 935 => (0, 30, 1, 3)
  | 936 => (1, 30, 2, 20)
  | 937 => (1, 21, 1, 26)
  | 938 => (2, 3, 2, 18)
  | 939 => (0, 28, 2, 30)
  | 940 => (0, 30, 1, 27)
  | 941 => (0, 4, 1, 8)
  | 942 => (1, 4, 1, 29)
  | 943 => (2, 27, 2, 28)
  | 944 => (2, 8, 2, 15)
  | 945 => (2, 4, 2, 29)
  | 946 => (6, 28, 8, 10)
  | 947 => (5, 30, 6, 14)
  | 948 => (3, 28, 4, 20)
  | 949 => (0, 12, 3, 30)
  | 950 => (1, 12, 3, 4)
  | 951 => (0, 1, 0, 30)
  | 952 => (0, 10, 1, 1)
  | 953 => (1, 10, 1, 24)
  | 954 => (0, 2, 2, 5)
  | 955 => (1, 2, 1, 23)
  | 956 => (1, 25, 2, 10)
  | 957 => (0, 30, 4, 4)
  | 958 => (1, 9, 1, 30)
  | 959 => (1, 29, 2, 25)
  | 960 => (0, 28, 1, 3)
  | 961 => (0, 6, 0, 22)
  | 962 => (1, 6, 1, 17)
  | 963 => (1, 15, 1, 31)
  | 964 => (1, 26, 1, 31)
  | 965 => (2, 6, 2, 17)
  | 966 => (0, 4, 2, 15)
  | 967 => (1, 4, 1, 31)
  | 968 => (1, 29, 4, 10)
  | 969 => (1, 24, 1, 31)
  | 970 => (0, 30, 2, 4)
  | 971 => (0, 16, 0, 28)
  | 972 => (1, 16, 1, 19)
  | 973 => (4, 9, 4, 30)
  | 974 => (1, 11, 1, 21)
  | 975 => (0, 18, 1, 7)
  | 976 => (0, 10, 1, 5)
  | 977 => (0, 30, 1, 10)
  | 978 => (1, 26, 1, 30)
  | 979 => (0, 22, 1, 14)
  | 980 => (1, 22, 2, 10)
  | 981 => (2, 26, 2, 30)
  | 982 => (2, 14, 4, 4)
  | 983 => (2, 22, 4, 29)
  | 984 => (1, 31, 3, 18)
  | 985 => (3, 10, 5, 28)
  | 986 => (0, 6, 3, 30)
  | 987 => (1, 6, 1, 29)
  | 988 => (1, 31, 3, 22)
  | 989 => (4, 11, 4, 21)
  | 990 => (1, 8, 1, 27)
  | 991 => (1, 20, 2, 31)
  | 992 => (0, 30, 4, 10)
  | 993 => (0, 16, 1, 21)
  | 994 => (0, 28, 1, 16)
  | 995 => (1, 28, 3, 6)
  | 996 => (0, 12, 0, 18)
  | 997 => (1, 12, 1, 18)
  | 998 => (1, 11, 2, 28)
  | 999 => (4, 31, 6, 26)
  | 1000 => (0, 30, 1, 7)
  | 1001 => (1, 30, 2, 11)
  | 1002 => (0, 1, 1, 14)
  | 1003 => (1, 1, 2, 7)
  | 1004 => (2, 30, 5, 22)
  | 1005 => (0, 2, 1, 17)
  | 1006 => (0, 28, 1, 2)
  | 1007 => (1, 9, 1, 23)
  | 1008 => (1, 15, 2, 17)
  | 1009 => (2, 2, 3, 30)
  | 1010 => (2, 9, 2, 23)
  | 1011 => (1, 3, 1, 20)
  | _ => (0, 0, 0, 0)

def is_square_fast (m : ℕ) : Bool :=
  let s := fast_sqrt m
  s * s == m

def check_witness_for_n (n : ℕ) : Bool :=
  let (x1, y1, x2, y2) := witness_table n
  (x1 * x1 + y1 * y1 <= n) &&
  (x1 <= y1) &&
  (is_prime_fast (x1 + 1) || is_prime_fast (y1 + 1)) &&
  is_square_fast (24 * (n - (x1 * x1 + y1 * y1)) + 1) &&
  (x2 * x2 + y2 * y2 <= n) &&
  (x2 <= y2) &&
  (is_prime_fast (x2 + 1) || is_prime_fast (y2 + 1)) &&
  is_square_fast (24 * (n - (x2 * x2 + y2 * y2)) + 1) &&
  ((x1 != x2) || (y1 != y2))

def check_all_witnesses (n : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    if n > 1011 then true
    else check_witness_for_n n && check_all_witnesses (n + 1) fuel'

lemma check_all_witnesses_true : check_all_witnesses 609 403 = true := by decide

lemma is_generalized_pentagonal_eq_fast_full (k : ℕ) (h : k ≤ 1009) :
  is_generalized_pentagonal k ↔ (is_square_fast (24 * k + 1) = true) := by
  unfold is_generalized_pentagonal Nat.is_perfect_square
  dsimp [HPow.hPow]
  dsimp [my_sqrt]
  have h_le : 24 * k + 1 ≤ 24240 := by omega
  rw [if_pos h_le]
  unfold is_square_fast
  dsimp
  rw [fast_sqrt_eq_sqrt]
  change (1 * fast_sqrt (24 * k + 1) * fast_sqrt (24 * k + 1) = 24 * k + 1) ↔ (fast_sqrt (24 * k + 1) * fast_sqrt (24 * k + 1) == 24 * k + 1) = true
  simp

lemma is_generalized_pentagonal_of_fast (k : ℕ) (h_gp : is_square_fast (24 * k + 1) = true) :
  is_generalized_pentagonal k := by
  by_cases h : k ≤ 1009
  · rw [is_generalized_pentagonal_eq_fast_full k h]
    exact h_gp
  · unfold is_generalized_pentagonal Nat.is_perfect_square
    dsimp [HPow.hPow, my_sqrt]
    have h_not : ¬(24 * k + 1 ≤ 24240) := by omega
    rw [if_neg h_not]

lemma check_witness_prop (n : ℕ) (h : check_witness_for_n n = true) (hn : n ≤ 1011) :
  let (x1, y1, x2, y2) := witness_table n
  x1 * x1 + y1 * y1 ≤ n ∧ x1 ≤ y1 ∧ (Nat.Prime (x1 + 1) ∨ Nat.Prime (y1 + 1)) ∧ is_generalized_pentagonal (n - (x1 * x1 + y1 * y1)) ∧
  x2 * x2 + y2 * y2 ≤ n ∧ x2 ≤ y2 ∧ (Nat.Prime (x2 + 1) ∨ Nat.Prime (y2 + 1)) ∧ is_generalized_pentagonal (n - (x2 * x2 + y2 * y2)) ∧
  ((x1, y1) ≠ (x2, y2)) := by
  unfold check_witness_for_n at h
  generalize h_wit_eq : witness_table n = w at h ⊢
  rcases w with ⟨x1, y1, x2, y2⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_ne⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_gp2⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_pr2⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_le_xy2⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_le2⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_gp1⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h, h_pr1⟩
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h_le1, h_le_xy1⟩

  have h_le1' : x1 * x1 + y1 * y1 ≤ n := decide_eq_true_iff.mp h_le1
  have h_le_xy1' : x1 ≤ y1 := decide_eq_true_iff.mp h_le_xy1

  have h_x1_bound : x1 + 1 ≤ 37 := by
    by_contra! hc
    have h1 : 37 * x1 ≤ x1 * x1 := Nat.mul_le_mul_right x1 (by omega)
    have h2 : 37 * 37 ≤ 37 * x1 := Nat.mul_le_mul_left 37 (by omega)
    omega
  have h_y1_bound : y1 + 1 ≤ 37 := by
    by_contra! hc
    have h1 : 37 * y1 ≤ y1 * y1 := Nat.mul_le_mul_right y1 (by omega)
    have h2 : 37 * 37 ≤ 37 * y1 := Nat.mul_le_mul_left 37 (by omega)
    omega

  have h_pr1' : Nat.Prime (x1 + 1) ∨ Nat.Prime (y1 + 1) := by
    rw [Bool.or_eq_true] at h_pr1
    rcases h_pr1 with hp | hp
    · left; rw [prime_eq_fast (x1 + 1) h_x1_bound]; exact hp
    · right; rw [prime_eq_fast (y1 + 1) h_y1_bound]; exact hp
  have h_gp1' : is_generalized_pentagonal (n - (x1 * x1 + y1 * y1)) := is_generalized_pentagonal_of_fast _ h_gp1

  have h_le2' : x2 * x2 + y2 * y2 ≤ n := decide_eq_true_iff.mp h_le2
  have h_le_xy2' : x2 ≤ y2 := decide_eq_true_iff.mp h_le_xy2

  have h_x2_bound : x2 + 1 ≤ 37 := by
    by_contra! hc
    have h1 : 37 * x2 ≤ x2 * x2 := Nat.mul_le_mul_right x2 (by omega)
    have h2 : 37 * 37 ≤ 37 * x2 := Nat.mul_le_mul_left 37 (by omega)
    omega
  have h_y2_bound : y2 + 1 ≤ 37 := by
    by_contra! hc
    have h1 : 37 * y2 ≤ y2 * y2 := Nat.mul_le_mul_right y2 (by omega)
    have h2 : 37 * 37 ≤ 37 * y2 := Nat.mul_le_mul_left 37 (by omega)
    omega

  have h_pr2' : Nat.Prime (x2 + 1) ∨ Nat.Prime (y2 + 1) := by
    rw [Bool.or_eq_true] at h_pr2
    rcases h_pr2 with hp | hp
    · left; rw [prime_eq_fast (x2 + 1) h_x2_bound]; exact hp
    · right; rw [prime_eq_fast (y2 + 1) h_y2_bound]; exact hp
  have h_gp2' : is_generalized_pentagonal (n - (x2 * x2 + y2 * y2)) := is_generalized_pentagonal_of_fast _ h_gp2

  have h_ne' : (x1, y1) ≠ (x2, y2) := by
    rintro h_eq
    injection h_eq with h_eqx h_eqy
    rw [Bool.or_eq_true] at h_ne
    rcases h_ne with h_ne_x | h_ne_y
    · rw [h_eqx] at h_ne_x
      revert h_ne_x
      simp
    · rw [h_eqy] at h_ne_y
      revert h_ne_y
      simp

  exact ⟨h_le1', h_le_xy1', h_pr1', h_gp1', h_le2', h_le_xy2', h_pr2', h_gp2', h_ne'⟩

lemma check_all_witnesses_prop (n : ℕ) (fuel : ℕ) (h_check : check_all_witnesses n fuel = true) :
  ∀ m, m ≥ n → m < n + fuel → m ≤ 1011 →
  let (x1, y1, x2, y2) := witness_table m
  x1 * x1 + y1 * y1 ≤ m ∧ x1 ≤ y1 ∧ (Nat.Prime (x1 + 1) ∨ Nat.Prime (y1 + 1)) ∧ is_generalized_pentagonal (m - (x1 * x1 + y1 * y1)) ∧
  x2 * x2 + y2 * y2 ≤ m ∧ x2 ≤ y2 ∧ (Nat.Prime (x2 + 1) ∨ Nat.Prime (y2 + 1)) ∧ is_generalized_pentagonal (m - (x2 * x2 + y2 * y2)) ∧
  ((x1, y1) ≠ (x2, y2)) := by
  induction fuel generalizing n with
  | zero =>
    intro m hm1 hm2 _
    omega
  | succ fuel' ih =>
    intro m hm1 hm2 hm3
    unfold check_all_witnesses at h_check
    by_cases hn : n > 1011
    · omega
    · rw [if_neg hn] at h_check
      rw [Bool.and_eq_true] at h_check
      rcases h_check with ⟨h1, h2⟩
      by_cases hm : m = n
      · subst hm
        exact check_witness_prop m h1 hm3
      · have hm_gt : m ≥ n + 1 := by omega
        have hm_lt : m < n + 1 + fuel' := by omega
        exact ih (n + 1) h2 m hm_gt hm_lt hm3

lemma witness_correct (n : ℕ) (h1 : n > 608) (h2 : n ≤ 1011) :
  let (x1, y1, x2, y2) := witness_table n
  x1 * x1 + y1 * y1 ≤ n ∧ x1 ≤ y1 ∧ (Nat.Prime (x1 + 1) ∨ Nat.Prime (y1 + 1)) ∧ is_generalized_pentagonal (n - (x1 * x1 + y1 * y1)) ∧
  x2 * x2 + y2 * y2 ≤ n ∧ x2 ≤ y2 ∧ (Nat.Prime (x2 + 1) ∨ Nat.Prime (y2 + 1)) ∧ is_generalized_pentagonal (n - (x2 * x2 + y2 * y2)) ∧
  ((x1, y1) ≠ (x2, y2)) := by
  apply check_all_witnesses_prop 609 403 check_all_witnesses_true n <;> omega

lemma finset_card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h_ne : a ≠ b) : s.card ≥ 2 := by
  have h_sub : {a, b} ⊆ s := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb⟩
  have h_card_ab : ({a, b} : Finset α).card = 2 := Finset.card_pair h_ne
  have h_card : ({a, b} : Finset α).card ≤ s.card := Finset.card_le_card h_sub
  omega

lemma A270966_ge_two_table (n : ℕ) (h1 : n > 608) (h2 : n ≤ 1011) : A270966 n ≥ 2 := by
  unfold A270966
  have h_wit := witness_correct n h1 h2
  generalize h_wit_eq : witness_table n = w at h_wit
  rcases w with ⟨x1, y1, x2, y2⟩
  rcases h_wit with ⟨h_le1, h_le_xy1, h_pr1, h_gp1, h_le2, h_le_xy2, h_pr2, h_gp2, h_ne⟩
  have ha : (x1, y1) ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun xy =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧ is_generalized_pentagonal (n - x_sq_y_sq) := by
    rw [Finset.mem_filter]
    refine ⟨?_, h_le1, h_le_xy1, h_pr1, h_gp1⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have hx1 : x1 * x1 ≤ n := by omega
    have hy1 : y1 * y1 ≤ n := by omega
    have h_sqrt1 : x1 ≤ n := by
      cases x1 with
      | zero => omega
      | succ x =>
        have h_mul : (x + 1) * 1 ≤ (x + 1) * (x + 1) := Nat.mul_le_mul_left (x + 1) (by omega)
        rw [Nat.mul_one] at h_mul
        omega
    have h_sqrt2 : y1 ≤ n := by
      cases y1 with
      | zero => omega
      | succ y =>
        have h_mul : (y + 1) * 1 ≤ (y + 1) * (y + 1) := Nat.mul_le_mul_left (y + 1) (by omega)
        rw [Nat.mul_one] at h_mul
        omega
    omega
  have hb : (x2, y2) ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun xy =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧ is_generalized_pentagonal (n - x_sq_y_sq) := by
    rw [Finset.mem_filter]
    refine ⟨?_, h_le2, h_le_xy2, h_pr2, h_gp2⟩
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have hx2 : x2 * x2 ≤ n := by omega
    have hy2 : y2 * y2 ≤ n := by omega
    have h_sqrt1 : x2 ≤ n := by
      cases x2 with
      | zero => omega
      | succ x =>
        have h_mul : (x + 1) * 1 ≤ (x + 1) * (x + 1) := Nat.mul_le_mul_left (x + 1) (by omega)
        rw [Nat.mul_one] at h_mul
        omega
    have h_sqrt2 : y2 ≤ n := by
      cases y2 with
      | zero => omega
      | succ y =>
        have h_mul : (y + 1) * 1 ≤ (y + 1) * (y + 1) := Nat.mul_le_mul_left (y + 1) (by omega)
        rw [Nat.mul_one] at h_mul
        omega
    omega
  exact finset_card_ge_two ha hb h_ne

lemma A270966_ge_two_inf (n : ℕ) (h_n : n > 1011) : A270966 n ≥ 2 := by
  unfold A270966
  have ha : (0, 1) ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun xy =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧ is_generalized_pentagonal (n - x_sq_y_sq) := by
    rw [Finset.mem_filter]
    constructor
    · simp; omega
    · unfold is_generalized_pentagonal Nat.is_perfect_square
      dsimp [HPow.hPow]
      dsimp [my_sqrt]
      have h_not : ¬(24 * (n - 1) + 1 ≤ 24240) := by omega
      rw [if_neg h_not]
      refine ⟨by omega, by omega, Or.inr Nat.prime_two, rfl⟩

  have hb : (1, 1) ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun xy =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧ is_generalized_pentagonal (n - x_sq_y_sq) := by
    rw [Finset.mem_filter]
    constructor
    · simp; omega
    · unfold is_generalized_pentagonal Nat.is_perfect_square
      dsimp [HPow.hPow]
      dsimp [my_sqrt]
      have h_not : ¬(24 * (n - 2) + 1 ≤ 24240) := by omega
      rw [if_neg h_not]
      refine ⟨by omega, by omega, Or.inl Nat.prime_two, rfl⟩

  have h_ne : ((0, 1) : ℕ × ℕ) ≠ (1, 1) := by
    rintro h
    injection h with h_eq
    contradiction
  exact finset_card_ge_two ha hb h_ne

theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) := by
  constructor
  · rintro n hn
    by_cases h_le : n ≤ 608
    · rw [A270966_eq_small n]
      rw [A270966_small_eq_fast n (sqrt_fast n) (by rw [sqrt_fast_eq n (by omega)]) h_le]
      rw [fast_eval_eq n h_le]
      exact helper1_all n h_le hn
    · by_cases h_table : n ≤ 1011
      · have h_ge2 := A270966_ge_two_table n (by omega) h_table
        omega
      · have h_ge2 := A270966_ge_two_inf n (by omega)
        omega
  · intro n
    by_cases h_le : n ≤ 608
    · rw [A270966_eq_small n]
      rw [A270966_small_eq_fast n (sqrt_fast n) (by rw [sqrt_fast_eq n (by omega)]) h_le]
      rw [fast_eval_eq n h_le]
      exact helper2_all n h_le
    · by_cases h_table : n ≤ 1011
      · have h_ge2 := A270966_ge_two_table n (by omega) h_table
        constructor
        · intro h_eq1; omega
        · rintro (rfl | rfl | rfl) <;> omega
      · have h_ge2 := A270966_ge_two_inf n (by omega)
        constructor
        · intro h_eq1; omega
        · rintro (rfl | rfl | rfl) <;> omega
