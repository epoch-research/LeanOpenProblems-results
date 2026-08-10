/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
you may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open Nat hiding ofDigits digits digits_zero digits_of_two_le_of_pos ofDigits_digits digits_eq_cons_digits_div digits_ofDigits
open Classical

def ofDigits (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + b * ofDigits b l

def digits_fast_aux (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % b) :: digits_fast_aux b fuel (n / b)

def digits (b : ℕ) (n : ℕ) : List ℕ :=
  digits_fast_aux b n n

def digits_fast (b : ℕ) (n : ℕ) : List ℕ :=
  digits b n

theorem digits_fast_aux_zero (b : ℕ) (fuel : ℕ) : digits_fast_aux b fuel 0 = [] := by
  cases fuel with
  | zero => rfl
  | succ f => rfl

theorem digits_fast_aux_eq_of_le (b : ℕ) (_hb : 2 ≤ b) (fuel1 fuel2 n : ℕ) (h1 : n ≤ fuel1) (h2 : n ≤ fuel2) :
    digits_fast_aux b fuel1 n = digits_fast_aux b fuel2 n := by
  induction fuel1 generalizing fuel2 n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rw [digits_fast_aux_zero, digits_fast_aux_zero]
  | succ f1 ih =>
    by_cases hn : n = 0
    · subst hn
      rw [digits_fast_aux_zero, digits_fast_aux_zero]
    · rcases fuel2 with _ | f2
      · omega
      · unfold digits_fast_aux
        rw [if_neg hn, if_neg hn]
        apply congrArg
        have h_div1 : n / b ≤ f1 := by
          have : n / b < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) _hb
          omega
        have h_div2 : n / b ≤ f2 := by
          have : n / b < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) _hb
          omega
        exact ih f2 (n / b) h_div1 h_div2

theorem digits_fast_aux_succ (b : ℕ) (n : ℕ) :
    digits_fast_aux b (n + 1) (n + 1) = ((n + 1) % b) :: digits_fast_aux b n ((n + 1) / b) := rfl

theorem digits_eq_cons_digits_div {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    digits b n = (n % b) :: digits b (n / b) := by
  unfold digits
  rcases n with _ | n
  · contradiction
  · rw [digits_fast_aux_succ]
    apply congrArg
    have h1 : (n + 1) / b ≤ n := by
      have : (n + 1) / b < n + 1 := Nat.div_lt_self (by omega) hb
      omega
    have h2 : (n + 1) / b ≤ (n + 1) / b := by omega
    exact digits_fast_aux_eq_of_le b hb n ((n + 1) / b) ((n + 1) / b) h1 h2

theorem digits_of_two_le_of_pos {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    digits b n = (n % b) :: digits b (n / b) :=
  digits_eq_cons_digits_div hb (by omega)

theorem digits_zero (b : ℕ) : digits b 0 = [] := rfl

theorem ofDigits_digits_fast_aux (b : ℕ) (hb : 2 ≤ b) (fuel n : ℕ) (h : n ≤ fuel) :
    ofDigits b (digits_fast_aux b fuel n) = n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rfl
  | succ fuel ih =>
    unfold digits_fast_aux
    by_cases hn : n = 0
    · rw [if_pos hn]
      subst hn
      rfl
    · rw [if_neg hn]
      dsimp [ofDigits]
      have h_lt : n / b < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hb
      have h_le : n / b ≤ fuel := by omega
      rw [ih (n / b) h_le]
      exact Nat.mod_add_div n b

theorem ofDigits_digits (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ofDigits b (digits b n) = n := by
  unfold digits
  exact ofDigits_digits_fast_aux b hb n n (by omega)

theorem ofDigits_cons_mod_b (b d : ℕ) (l : List ℕ) (_hb : 2 ≤ b) (hd : d < b) :
    ofDigits b (d :: l) % b = d := by
  dsimp [ofDigits]
  rw [Nat.mul_comm b (ofDigits b l)]
  rw [Nat.add_mul_mod_self_right]
  rw [Nat.mod_eq_of_lt hd]

theorem ofDigits_cons_div_b (b d : ℕ) (l : List ℕ) (_hb : 2 ≤ b) (hd : d < b) :
    ofDigits b (d :: l) / b = ofDigits b l := by
  dsimp [ofDigits]
  rw [Nat.mul_comm b (ofDigits b l)]
  rw [Nat.add_mul_div_right d (ofDigits b l) (by omega)]
  rw [Nat.div_eq_of_lt hd, Nat.zero_add]

theorem ofDigits_zero (b : ℕ) (L : List ℕ) (h : ∀ x ∈ L, x = 0) : ofDigits b L = 0 := by
  induction L with
  | nil => rfl
  | cons d l ih =>
    dsimp [ofDigits]
    have h1 : d = 0 := h d (List.Mem.head l)
    have h2 : ofDigits b l = 0 := ih (fun x hx => h x (List.Mem.tail d hx))
    rw [h1, h2, Nat.mul_zero, Nat.add_zero]

theorem ofDigits_ne_zero {b : ℕ} (hb : 2 ≤ b) (L : List ℕ) (h1 : ∀ x ∈ L, x < b) (h2 : L.getLast? ≠ some 0) (hL : L ≠ []) : ofDigits b L ≠ 0 := by
  induction L with
  | nil => contradiction
  | cons d l ih =>
    dsimp [ofDigits]
    by_cases hl : l = []
    · subst hl
      dsimp [ofDigits]
      dsimp [List.getLast?] at h2
      have : d ≠ 0 := by intro hc; subst hc; contradiction
      omega
    · have h_last : (d :: l).getLast? = l.getLast? := by
        rcases l with _ | ⟨d2, l2⟩
        · contradiction
        · rfl
      have h_last_ne : l.getLast? ≠ some 0 := by rwa [← h_last]
      have ih' := ih (fun x hx => h1 x (List.Mem.tail d hx)) h_last_ne hl
      have : b * ofDigits b l ≥ b := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ih')
      omega

theorem digits_ofDigits {b : ℕ} (hb : 2 ≤ b) (L : List ℕ) (h1 : ∀ x ∈ L, x < b) (h2 : L.getLast? ≠ some 0) :
    digits b (ofDigits b L) = L := by
  induction L with
  | nil => rfl
  | cons d l ih =>
    by_cases hl : l = []
    · subst hl
      dsimp [ofDigits]
      dsimp [List.getLast?] at h2
      have hd_ne : d ≠ 0 := by
        intro hc; subst hc; contradiction
      have hd_lt : d < b := h1 d (List.Mem.head [])
      unfold digits
      rcases d with _ | d
      · contradiction
      · rw [digits_fast_aux_succ]
        have h_div : (d + 1) / b = 0 := Nat.div_eq_of_lt hd_lt
        have h_mod : (d + 1) % b = d + 1 := Nat.mod_eq_of_lt hd_lt
        rw [h_div, h_mod, digits_fast_aux_zero]
    · have h_last : (d :: l).getLast? = l.getLast? := by
        rcases l with _ | ⟨d2, l2⟩
        · contradiction
        · rfl
      have h_last_ne : l.getLast? ≠ some 0 := by rwa [← h_last]
      have ih' := ih (fun x hx => h1 x (List.Mem.tail d hx)) h_last_ne
      have h_ne : ofDigits b l ≠ 0 := ofDigits_ne_zero hb l (fun x hx => h1 x (List.Mem.tail d hx)) h_last_ne hl
      have hn_ne : ofDigits b (d :: l) ≠ 0 := by
        dsimp [ofDigits]
        have : b * ofDigits b l ≥ b := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h_ne)
        omega
      rw [digits_eq_cons_digits_div hb hn_ne]
      have hd_lt : d < b := h1 d (List.Mem.head l)
      have h_mod := ofDigits_cons_mod_b b d l hb hd_lt
      have h_div := ofDigits_cons_div_b b d l hb hd_lt
      rw [h_mod, h_div]
      rw [ih']

theorem digits_fast_aux_lt_base {b : ℕ} (hb : 2 ≤ b) (fuel n x : ℕ) (hx : x ∈ digits_fast_aux b fuel n) : x < b := by
  induction fuel generalizing n with
  | zero =>
    unfold digits_fast_aux at hx
    cases hx
  | succ fuel ih =>
    unfold digits_fast_aux at hx
    by_cases hn : n = 0
    · rw [if_pos hn] at hx
      cases hx
    · rw [if_neg hn] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt n (by omega)
      · exact ih (n / b) hx

theorem digits_lt_base {b : ℕ} (hb : 2 ≤ b) {n x : ℕ} (hx : x ∈ digits b n) : x < b := by
  unfold digits at hx
  exact digits_fast_aux_lt_base hb n n x hx

theorem exists_least_of_exists {P : ℕ → Prop} [DecidablePred P] : ∀ (n : ℕ), P n → ∃ m, P m ∧ ∀ k < m, ¬ P k
  | 0, h0 => ⟨0, h0, fun k hk => by contradiction⟩
  | n + 1, hn1 => by
    by_cases h0 : P 0
    · exact ⟨0, h0, fun k hk => by contradiction⟩
    · have hQ : P (n + 1) := hn1
      have ih := exists_least_of_exists n (P := fun k => P (k + 1)) hQ
      rcases ih with ⟨mq, hmq1, hmq2⟩
      refine ⟨mq + 1, hmq1, ?_⟩
      intro k hk
      rcases k with _ | k
      · exact h0
      · have : k < mq := by omega
        exact hmq2 k this

theorem my_find_helper {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k < m, ¬ P k := by
  rcases h with ⟨n, hn⟩
  exact exists_least_of_exists n hn

noncomputable def my_find {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) : ℕ :=
  Classical.choose (my_find_helper h)

theorem my_find_spec {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :
    P (my_find h) ∧ ∀ k < my_find h, ¬ P k :=
  Classical.choose_spec (my_find_helper h)

theorem my_find_le {P : ℕ → Prop} [DecidablePred P] {h : ∃ n, P n} {n : ℕ} (hn : P n) : my_find h ≤ n := by
  have h_spec := my_find_spec h
  by_cases h_le : my_find h ≤ n
  · exact h_le
  · have : n < my_find h := by omega
    have : ¬ P n := h_spec.2 n this
    contradiction

theorem my_find_min {P : ℕ → Prop} [DecidablePred P] {h : ∃ n, P n} {m : ℕ} (hm : m < my_find h) : ¬ P m := by
  have h_spec := my_find_spec h
  exact h_spec.2 m hm

theorem my_find_eq_iff {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) {m : ℕ} :
    my_find h = m ↔ P m ∧ ∀ k < m, ¬ P k := by
  constructor
  · rintro rfl
    exact my_find_spec h
  · rintro ⟨hp, hk⟩
    have h_le1 : my_find h ≤ m := my_find_le hp
    have h_le2 : m ≤ my_find h := by
      by_cases h_le : m ≤ my_find h
      · exact h_le
      · have : my_find h < m := by omega
        have : ¬ P (my_find h) := hk (my_find h) this
        have : P (my_find h) := (my_find_spec h).1
        contradiction
    omega

theorem oeis62567_Nat_find_le {P : ℕ → Prop} [DecidablePred P] {h : ∃ n, P n} {n : ℕ} (hn : P n) : my_find h ≤ n :=
  my_find_le hn

namespace Oeis62567_Helper

def Oeis62567_ModEq (n a b : ℕ) : Prop := a % n = b % n

theorem Oeis62567_ModEq.trans {n a b c : ℕ} (h1 : Oeis62567_ModEq n a b) (h2 : Oeis62567_ModEq n b c) : Oeis62567_ModEq n a c :=
  Eq.trans h1 h2

theorem Oeis62567_ModEq.add_left (c : ℕ) {n a b : ℕ} (h : Oeis62567_ModEq n a b) : Oeis62567_ModEq n (c + a) (c + b) := by
  unfold Oeis62567_ModEq at h ⊢
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem Oeis62567_ModEq.mul_left (c : ℕ) {n a b : ℕ} (h : Oeis62567_ModEq n a b) : Oeis62567_ModEq n (c * a) (c * b) := by
  unfold Oeis62567_ModEq at h ⊢
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

theorem Oeis62567_ModEq.add {n a b c d : ℕ} (h1 : Oeis62567_ModEq n a b) (h2 : Oeis62567_ModEq n c d) : Oeis62567_ModEq n (a + c) (b + d) := by
  unfold Oeis62567_ModEq at h1 h2 ⊢
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

theorem Oeis62567_ModEq.add_right (c : ℕ) {n a b : ℕ} (h : Oeis62567_ModEq n a b) : Oeis62567_ModEq n (a + c) (b + c) := by
  unfold Oeis62567_ModEq at h ⊢
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem Oeis62567_ModEq.pow (p : ℕ) {n a b : ℕ} (h : Oeis62567_ModEq n a b) : Oeis62567_ModEq n (a ^ p) (b ^ p) := by
  unfold Oeis62567_ModEq at h ⊢
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, h, ih, ← Nat.mul_mod]

theorem oeis62567_modEq_zero_iff_dvd {n a : ℕ} : Oeis62567_ModEq n a 0 ↔ n ∣ a := by
  unfold Oeis62567_ModEq
  rw [Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.symm

theorem oeis62567_Nat_mul_dvd_mul {a b c d : ℕ} (hab : a ∣ b) (hcd : c ∣ d) : a * c ∣ b * d := by
  rcases hab with ⟨k1, hk1⟩
  rcases hcd with ⟨k2, hk2⟩
  subst hk1 hk2
  refine ⟨k1 * k2, ?_⟩
  rw [Nat.mul_assoc, ← Nat.mul_assoc k1 c k2, Nat.mul_comm k1 c]
  repeat rw [Nat.mul_assoc]

theorem oeis62567_Nat_mul_lt_mul_of_pos_right {a b c : ℕ} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  have : a + (b - a) = b := by omega
  have h_eq : b * c = (a + (b - a)) * c := by rw [this]
  rw [h_eq, Nat.add_mul]
  have : (b - a) * c > 0 := by
    have h1 : b - a > 0 := by omega
    exact Nat.mul_pos h1 hc
  omega

theorem oeis62567_ofDigits_replicate_zero (b : ℕ) (n : ℕ) : ofDigits b (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [List.replicate, ofDigits]
    rw [ih]
    omega

theorem oeis62567_ofDigits_append (b : ℕ) (L1 L2 : List ℕ) : ofDigits b (L1 ++ L2) = ofDigits b L1 + ofDigits b L2 * b^L1.length := by
  induction L1 with
  | nil =>
    simp [ofDigits]
  | cons d l ih =>
    simp only [List.cons_append, ofDigits, List.length_cons]
    rw [ih]
    rw [Nat.mul_add]
    have : b * (ofDigits b L2 * b^l.length) = ofDigits b L2 * b^(l.length + 1) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm b (ofDigits b L2)]
      rw [Nat.mul_assoc]
      rw [Nat.mul_comm b (b^l.length)]
    rw [this]
    rw [Nat.add_assoc]

theorem oeis62567_digits_length_le (f : ℕ) (n : ℕ) (hn : n < 10^f) : (digits 10 n).length ≤ f := by
  induction f generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rw [digits_zero]
    simp
  | succ f ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [digits_zero]
      simp
    · have h_div : digits 10 n = (n % 10) :: digits 10 (n / 10) := by
        apply digits_eq_cons_digits_div (by decide) h0
      rw [h_div]
      simp only [List.length_cons]
      have h_pow : 10^(f+1) = 10 * 10^f := by rw [Nat.pow_succ, Nat.mul_comm]
      have : n / 10 < 10^f := by omega
      have ih' := ih (n / 10) this
      omega

end Oeis62567_Helper

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := my_find h_ex
      k_min * n
    else
      0

namespace Oeis62567

open Oeis62567_Helper

set_option linter.all false

theorem a_def_of_ne_zero {n : ℕ} (hn : n ≠ 0) (h_ex : ∃ k, k > 0 ∧ n ∣ reverse_nat (k * n)) :
    a n = my_find h_ex * n := by
  unfold a
  rw [if_neg hn]
  exact dif_pos h_ex

def reverse_nat_fast (k : ℕ) : ℕ :=
  reverse_nat k

theorem digits_fast_eq (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    digits_fast b n = digits b n := rfl

theorem reverse_nat_fast_eq (k : ℕ) :
    reverse_nat_fast k = reverse_nat k := rfl

theorem a_9 : a 9 = 9 := by
  have h_ex : ∃ k, k > 0 ∧ 9 ∣ reverse_nat (k * 9) := by
    refine ⟨1, ?_⟩
    refine ⟨by decide, ?_⟩
    rw [Nat.one_mul, ← reverse_nat_fast_eq]
    decide
  have h_a : a 9 = my_find h_ex * 9 := by
    apply a_def_of_ne_zero (by decide)
  rw [h_a]
  have h_find : my_find h_ex = 1 := by
    rw [my_find_eq_iff h_ex]
    constructor
    · refine ⟨by decide, ?_⟩
      rw [Nat.one_mul, ← reverse_nat_fast_eq]
      decide
    · intro n hn
      have : n = 0 := by omega
      rw [this]
      rintro ⟨h0, _⟩
      contradiction
  rw [h_find]



def digits_fuel (fuel : ℕ) (n : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if n = 0 then []
    else (n % 10) :: digits_fuel f (n / 10)

def reverse_nat_fast_temp (n : ℕ) : ℕ :=
  ofDigits 10 (digits_fuel 10 n).reverse

theorem digits_eq_digits_fuel (fuel : ℕ) (n : ℕ) (hn : n < 10^fuel) : digits 10 n = digits_fuel fuel n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rw [digits_zero]
    rfl
  | succ f ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [digits_zero]
      rfl
    · have h_div : digits 10 n = (n % 10) :: digits 10 (n / 10) := by
        apply digits_eq_cons_digits_div (by decide) h0
      rw [h_div]
      simp [digits_fuel, h0]
      apply ih
      have h_lt : n / 10 * 10 ≤ n := Nat.div_mul_le_self n 10
      have : n / 10 < 10^f := by
        have h_pow : 10^(f+1) = 10 * 10^f := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [h_pow] at hn
        exact Nat.div_lt_of_lt_mul hn
      exact this

theorem reverse_nat_eq_fast_temp (n : ℕ) (hn : n < 10^10) : reverse_nat n = reverse_nat_fast_temp n := by
  unfold reverse_nat reverse_nat_fast_temp
  rw [digits_eq_digits_fuel 10 n hn]


theorem sum_le_of_mem_le {L : List ℕ} (h : ∀ x ∈ L, x ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.sum_cons, List.length_cons]
    have hx : x ≤ 9 := h x (by simp)
    have hL : ∀ y ∈ L, y ≤ 9 := fun y hy => h y (by simp [hy])
    have ih' := ih hL
    omega

theorem digits_len_le_9 {n : ℕ} (hn : n < 10^9) : (digits 10 n).length ≤ 9 := by
  exact oeis62567_digits_length_le 9 n hn

theorem digits_sum_le_81 {n : ℕ} (hn : n < 10^9) : (digits 10 n).sum ≤ 81 := by
  have h_mem : ∀ x ∈ digits 10 n, x ≤ 9 := by
    intro x hx
    have : x < 10 := digits_lt_base (by decide) hx
    omega
  have h1 := sum_le_of_mem_le h_mem
  have h2 := digits_len_le_9 hn
  omega

theorem list_all_9_of_sum_eq_9_mul {L : List ℕ} (h_mem : ∀ x ∈ L, x ≤ 9) (h_sum : L.sum = 9 * L.length) :
    L = List.replicate L.length 9 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.sum_cons, List.length_cons] at h_sum ⊢
    have hx : x ≤ 9 := h_mem x (by simp)
    have hL : ∀ y ∈ L, y ≤ 9 := fun y hy => h_mem y (by simp [hy])
    have h_le := sum_le_of_mem_le hL
    have h_x_eq_9 : x = 9 := by omega
    have h_sum_eq : L.sum = 9 * L.length := by omega
    subst h_x_eq_9
    rw [ih hL h_sum_eq]
    simp only [List.length_replicate]
    rfl

theorem digits_sum_lt_81 {n : ℕ} (hn : n < 999999999) : (digits 10 n).sum < 81 := by
  have h_le := digits_sum_le_81 (show n < 10^9 by omega)
  by_cases hc : (digits 10 n).sum < 81
  · exact hc
  · exfalso
    have h_sum : (digits 10 n).sum = 81 := by omega
    have h_mem : ∀ x ∈ digits 10 n, x ≤ 9 := by
      intro x hx
      have : x < 10 := digits_lt_base (by decide) hx
      omega
    have h_len := digits_len_le_9 (show n < 10^9 by omega)
    have h_sum_le : (digits 10 n).sum ≤ 9 * (digits 10 n).length := sum_le_of_mem_le h_mem
    have h_len_eq : (digits 10 n).length = 9 := by omega
    have h_sum_eq_9_mul : (digits 10 n).sum = 9 * (digits 10 n).length := by omega
    have h_rep := list_all_9_of_sum_eq_9_mul h_mem h_sum_eq_9_mul
    have h_of := congrArg (ofDigits 10) h_rep
    rw [ofDigits_digits 10 (by decide) n] at h_of
    rw [h_len_eq] at h_of
    have h_999 : ofDigits 10 (List.replicate 9 9) = 999999999 := by rfl
    rw [h_999] at h_of
    omega

def indexed_sum : List ℕ → ℕ
  | [] => 0
  | _ :: l => l.sum + indexed_sum l

def indexed_sum_aux : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: l, idx => d * idx + indexed_sum_aux l (idx + 1)

theorem indexed_sum_aux_append (L1 L2 : List ℕ) (idx : ℕ) :
    indexed_sum_aux (L1 ++ L2) idx = indexed_sum_aux L1 idx + indexed_sum_aux L2 (idx + L1.length) := by
  induction L1 generalizing idx with
  | nil =>
    simp [indexed_sum_aux]
  | cons d l ih =>
    simp only [List.cons_append, indexed_sum_aux, List.length_cons]
    rw [ih (idx + 1)]
    have : idx + 1 + l.length = idx + (l.length + 1) := by omega
    rw [this]
    omega

theorem indexed_sum_aux_eq (L : List ℕ) (idx : ℕ) : indexed_sum_aux L idx = idx * L.sum + indexed_sum L := by
  induction L generalizing idx with
  | nil =>
    simp [indexed_sum_aux, indexed_sum]
  | cons d l ih =>
    simp only [indexed_sum_aux, List.sum_cons, indexed_sum]
    rw [ih (idx + 1)]
    have h_mul1 : (idx + 1) * l.sum = idx * l.sum + l.sum := by rw [Nat.add_mul, Nat.one_mul]
    rw [h_mul1]
    have h_mul2 : idx * (d + l.sum) = idx * d + idx * l.sum := Nat.mul_add idx d l.sum
    rw [h_mul2]
    have h_comm : d * idx = idx * d := Nat.mul_comm d idx
    rw [h_comm]
    omega

theorem indexed_sum_reverse (L : List ℕ) : indexed_sum L.reverse + indexed_sum L = (L.length - 1) * L.sum := by
  induction L with
  | nil => rfl
  | cons d l ih =>
    cases l with
    | nil =>
      simp [indexed_sum]
    | cons x xs =>
      have h_rev : (d :: x :: xs).reverse = (x :: xs).reverse ++ [d] := List.reverse_cons
      rw [h_rev]
      have h_aux1 : indexed_sum ((x :: xs).reverse ++ [d]) = indexed_sum_aux ((x :: xs).reverse ++ [d]) 0 := by
        rw [indexed_sum_aux_eq]
        simp only [Nat.zero_mul, Nat.zero_add]
      rw [h_aux1]
      rw [indexed_sum_aux_append]
      have h_aux2 : indexed_sum_aux (x :: xs).reverse 0 = indexed_sum (x :: xs).reverse := by
        rw [indexed_sum_aux_eq]
        simp only [Nat.zero_mul, Nat.zero_add]
      rw [h_aux2]
      have h_len_rev : (x :: xs).reverse.length = (x :: xs).length := List.length_reverse
      rw [h_len_rev]
      have h_aux3 : indexed_sum_aux [d] (0 + (x :: xs).length) = d * (x :: xs).length := by
        dsimp [indexed_sum_aux]
        rw [Nat.zero_add]
      rw [h_aux3]
      rw [indexed_sum]
      have h_ih_sum : indexed_sum (x :: xs).reverse + indexed_sum (x :: xs) = ((x :: xs).length - 1) * (x :: xs).sum := ih
      have h_rhs : ((d :: x :: xs).length - 1) * (d :: x :: xs).sum = (x :: xs).length * (d + (x :: xs).sum) := by
        have h_len_eq : (d :: x :: xs).length = (x :: xs).length + 1 := rfl
        have h_sum_eq : (d :: x :: xs).sum = d + (x :: xs).sum := rfl
        rw [h_len_eq, h_sum_eq]
        have h_sub : (x :: xs).length + 1 - 1 = (x :: xs).length := by clear ih; omega
        rw [h_sub]
      rw [h_rhs]
      rw [Nat.mul_add (x :: xs).length d (x :: xs).sum]
      rw [Nat.mul_comm (x :: xs).length d]
      clear ih h_rhs
      have h_lhs : (indexed_sum (x :: xs).reverse + d * (x :: xs).length) + ((x :: xs).sum + indexed_sum (x :: xs)) =
                   (indexed_sum (x :: xs).reverse + indexed_sum (x :: xs)) + d * (x :: xs).length + (x :: xs).sum := by
        omega
      rw [h_lhs]
      rw [h_ih_sum]
      have h_lhs2 : ((x :: xs).length - 1) * (x :: xs).sum + d * (x :: xs).length + (x :: xs).sum =
                    d * (x :: xs).length + (((x :: xs).length - 1) * (x :: xs).sum + (x :: xs).sum) := by
        rw [Nat.add_assoc, Nat.add_comm (d * (x :: xs).length) (x :: xs).sum, ← Nat.add_assoc,
            Nat.add_comm (((x :: xs).length - 1) * (x :: xs).sum + (x :: xs).sum) (d * (x :: xs).length)]
      rw [h_lhs2]
      have h_eq : ((x :: xs).length - 1) * (x :: xs).sum + (x :: xs).sum = (x :: xs).length * (x :: xs).sum := by
        have h_add_mul : ((x :: xs).length - 1) * (x :: xs).sum + (x :: xs).sum = ((x :: xs).length - 1 + 1) * (x :: xs).sum := by
          rw [Nat.add_mul, Nat.one_mul]
        rw [h_add_mul]
        have h_sub : (x :: xs).length - 1 + 1 = (x :: xs).length := by dsimp [List.length]
        rw [h_sub]
      rw [h_eq]

theorem ofDigits_mod_81 (L : List ℕ) : Oeis62567_ModEq 81 (ofDigits 10 L) (L.sum + 9 * indexed_sum L) := by
  induction L with
  | nil => rfl
  | cons d l ih =>
    simp only [ofDigits, List.sum_cons, indexed_sum]
    have h1 : Oeis62567_ModEq 81 (d + 10 * ofDigits 10 l) (d + 10 * (l.sum + 9 * indexed_sum l)) := by
      apply Oeis62567_ModEq.add_left
      apply Oeis62567_ModEq.mul_left
      exact ih
    apply Oeis62567_ModEq.trans h1
    have h2 : d + 10 * (l.sum + 9 * indexed_sum l) = d + 10 * l.sum + 9 * indexed_sum l + 81 * indexed_sum l := by omega
    rw [h2]
    have h3 : Oeis62567_ModEq 81 (d + 10 * l.sum + 9 * indexed_sum l + 81 * indexed_sum l) (d + 10 * l.sum + 9 * indexed_sum l + 0) := by
      apply Oeis62567_ModEq.add_left
      have : 81 * indexed_sum l = 81 * indexed_sum l + 0 := by omega
      rw [this]
      apply Oeis62567_ModEq.add_right
      exact oeis62567_modEq_zero_iff_dvd.mpr ⟨indexed_sum l, rfl⟩
    apply Oeis62567_ModEq.trans h3
    have h4 : d + 10 * l.sum + 9 * indexed_sum l + 0 = d + l.sum + 9 * (l.sum + indexed_sum l) := by omega
    rw [h4]
    rfl

theorem list_sum_append (L1 L2 : List ℕ) : (L1 ++ L2).sum = L1.sum + L2.sum := by
  induction L1 with
  | nil => simp
  | cons d l ih =>
    dsimp
    rw [ih]
    omega

theorem list_sum_reverse (L : List ℕ) : L.reverse.sum = L.sum := by
  induction L with
  | nil => rfl
  | cons d l ih =>
    rw [List.reverse_cons, list_sum_append]
    dsimp
    rw [ih]
    omega

theorem ofDigits_reverse_mod_81 (L : List ℕ) : Oeis62567_ModEq 81 (ofDigits 10 L.reverse) (L.sum + 9 * indexed_sum L.reverse) := by
  have h1 := ofDigits_mod_81 L.reverse
  have h2 : L.reverse.sum = L.sum := list_sum_reverse L
  rw [h2] at h1
  exact h1

theorem manual_dvd_sub {a b c : ℕ} (h : b ≤ c) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ c - b := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  subst hk1 hk2
  refine ⟨k2 - k1, ?_⟩
  rw [Nat.mul_sub_left_distrib]

theorem dvd_9_sub_of_div_81 {B C : ℕ} (h : 81 ∣ 9 * B - 9 * C) : 9 ∣ B - C := by
  have h_Dist : 9 * B - 9 * C = 9 * (B - C) := (Nat.mul_sub_left_distrib 9 B C).symm
  rw [h_Dist] at h
  have h_81 : 81 = 9 * 9 := by rfl
  rw [h_81] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 9) h

theorem mod_eq_of_dvd_sub_le {b c : ℕ} (h_le : c ≤ b) (h : 9 ∣ b - c) : b % 9 = c % 9 := by
  rcases h with ⟨k, hk⟩
  have h_eq : b = c + 9 * k := by omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left]

theorem indexed_sum_mod_eq {A B C : ℕ} (h1 : 81 ∣ A + 9 * B) (h2 : 81 ∣ A + 9 * C) : B % 9 = C % 9 := by
  by_cases h : B ≤ C
  · have h_div81 : 81 ∣ 9 * C - 9 * B := by
      have h3 : 81 ∣ A + 9 * C - (A + 9 * B) := manual_dvd_sub (by omega) h1 h2
      have h4 : A + 9 * C - (A + 9 * B) = 9 * C - 9 * B := by omega
      rw [h4] at h3
      exact h3
    have h_div : 9 ∣ C - B := dvd_9_sub_of_div_81 h_div81
    exact (mod_eq_of_dvd_sub_le h h_div).symm
  · have h_gt : C ≤ B := by omega
    have h_div81 : 81 ∣ 9 * B - 9 * C := by
      have h3 : 81 ∣ A + 9 * B - (A + 9 * C) := manual_dvd_sub (by omega) h2 h1
      have h4 : A + 9 * B - (A + 9 * C) = 9 * B - 9 * C := by omega
      rw [h4] at h3
      exact h3
    have h_div : 9 ∣ B - C := dvd_9_sub_of_div_81 h_div81
    exact mod_eq_of_dvd_sub_le h_gt h_div

theorem mod_nine_eq_zero_of_two_mul_mod_nine (Z : ℕ) (h : (2 * (Z % 9)) % 9 = 0) : Z % 9 = 0 := by
  have h_lt : Z % 9 < 9 := Nat.mod_lt Z (by decide)
  omega

theorem dvd_9_of_dvd_add_and_mod_eq {Y Z : ℕ} (h_div : 9 ∣ Y + Z) (h_mod : Y % 9 = Z % 9) : 9 ∣ Z := by
  have h1 : (Y + Z) % 9 = 0 := Nat.mod_eq_zero_of_dvd h_div
  have h2 : (Y + Z) % 9 = (Y % 9 + Z % 9) % 9 := Nat.add_mod Y Z 9
  rw [h_mod] at h2
  have h3 : (Z % 9 + Z % 9) = 2 * (Z % 9) := by omega
  rw [h3] at h2
  rw [h2] at h1
  have h4 := mod_nine_eq_zero_of_two_mul_mod_nine Z h1
  exact Nat.dvd_of_mod_eq_zero h4

theorem sum_mod_81_of_reverse_nat_dvd_81 (L : List ℕ) (h1 : 81 ∣ ofDigits 10 L) (h2 : 81 ∣ ofDigits 10 L.reverse) : 81 ∣ L.sum := by
  have h_mod1 := ofDigits_mod_81 L
  have h_mod2 := ofDigits_reverse_mod_81 L
  rw [Oeis62567_ModEq] at h_mod1 h_mod2
  have h_eq1 : ofDigits 10 L % 81 = 0 := Nat.mod_eq_zero_of_dvd h1
  have h_eq2 : ofDigits 10 L.reverse % 81 = 0 := Nat.mod_eq_zero_of_dvd h2
  rw [h_eq1] at h_mod1
  rw [h_eq2] at h_mod2
  have h_div1 : 81 ∣ L.sum + 9 * indexed_sum L := Nat.dvd_of_mod_eq_zero h_mod1.symm
  have h_div2 : 81 ∣ L.sum + 9 * indexed_sum L.reverse := Nat.dvd_of_mod_eq_zero h_mod2.symm
  have h_div9_add : 9 ∣ L.sum + 9 * indexed_sum L := Nat.dvd_trans (by decide : 9 ∣ 81) h_div1
  have h_div9_mul : 9 ∣ 9 * indexed_sum L := ⟨indexed_sum L, rfl⟩
  have h_sub : (L.sum + 9 * indexed_sum L) - 9 * indexed_sum L = L.sum := by omega
  have h_div9 : 9 ∣ L.sum := by
    have h_dvd := manual_dvd_sub (by omega) h_div9_mul h_div9_add
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_mod_eq := indexed_sum_mod_eq h_div1 h_div2
  rcases h_div9 with ⟨A, hA⟩
  have h_div_sum : 9 ∣ indexed_sum L.reverse + indexed_sum L := by
    refine ⟨(L.length - 1) * A, ?_⟩
    rw [indexed_sum_reverse L]
    rw [hA]
    rw [← Nat.mul_assoc, Nat.mul_comm (L.length - 1) 9, Nat.mul_assoc]
  have h_div_ind : 9 ∣ indexed_sum L := dvd_9_of_dvd_add_and_mod_eq h_div_sum h_mod_eq.symm
  rcases h_div_ind with ⟨B, hB⟩
  have h_mul_81 : 9 * indexed_sum L = 81 * B := by
    rw [hB]
    omega
  rw [h_mul_81] at h_div1
  have h_sub81 : (L.sum + 81 * B) - 81 * B = L.sum := by omega
  have h_div81_mul : 81 ∣ 81 * B := ⟨B, rfl⟩
  have h_dvd81 := manual_dvd_sub (by omega) h_div81_mul h_div1
  rw [h_sub81] at h_dvd81
  exact h_dvd81

theorem sum_eq_zero_iff {L : List ℕ} : L.sum = 0 ↔ ∀ x ∈ L, x = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp [ih]

theorem ofDigits_eq_zero_of_all_zero {L : List ℕ} (h : ∀ x ∈ L, x = 0) : ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp at h
    rcases h with ⟨hx, hL⟩
    simp [ofDigits, hx, ih hL]

theorem digits_sum_pos {n : ℕ} (hn : n > 0) : (digits 10 n).sum > 0 := by
  by_cases hc : (digits 10 n).sum > 0
  · exact hc
  · exfalso
    have h_sum : (digits 10 n).sum = 0 := by omega
    rw [sum_eq_zero_iff] at h_sum
    have h_of : ofDigits 10 (digits 10 n) = 0 := ofDigits_eq_zero_of_all_zero h_sum
    rw [ofDigits_digits 10 (by decide) n] at h_of
    omega

theorem no_solution_lt_12345679 (n : ℕ) (hn_pos : n > 0) (hn : n < 12345679) :
    ¬ (81 ∣ reverse_nat (n * 81)) := by
  intro h_div
  let M := n * 81
  have hM_pos : M > 0 := by omega
  have hM_lt : M < 999999999 := by
    calc n * 81 < 12345679 * 81 := oeis62567_Nat_mul_lt_mul_of_pos_right hn (by decide)
    _ = 999999999 := by rfl
  let L := digits 10 M
  have h_div1 : 81 ∣ ofDigits 10 L := by
    rw [ofDigits_digits 10 (by decide) M]
    exact ⟨n, Nat.mul_comm n 81⟩
  have h_div2 : 81 ∣ ofDigits 10 L.reverse := by
    exact h_div
  have h_div_sum : 81 ∣ L.sum := sum_mod_81_of_reverse_nat_dvd_81 L h_div1 h_div2
  have h_sum_lt : L.sum < 81 := digits_sum_lt_81 hM_lt
  have h_sum_pos : L.sum > 0 := digits_sum_pos hM_pos
  rcases h_div_sum with ⟨k, hk⟩
  have : k > 0 := by
    by_cases hk0 : k > 0
    · exact hk0
    · exfalso
      have : k = 0 := by omega
      subst this
      omega
  have : L.sum ≥ 81 := by
    calc L.sum = 81 * k := hk
    _ ≥ 81 * 1 := Nat.mul_le_mul_left 81 this
    _ = 81 := by omega
  omega

theorem dvd_rev_27 : 27 ∣ reverse_nat (37 * 27) := by
  have h1 : 37 * 27 = 999 := by rfl
  rw [h1]
  unfold reverse_nat
  have h_dig : digits 10 999 = [9, 9, 9] := digits_ofDigits 10 (by decide) [9, 9, 9] (by decide) (by decide)
  rw [h_dig]
  have h_rev : [9, 9, 9].reverse = [9, 9, 9] := by rfl
  rw [h_rev]
  have h_of : ofDigits 10 [9, 9, 9] = 999 := by rfl
  rw [h_of]
  exact ⟨37, by rfl⟩

theorem a_27 : a 27 = 999 := by
  have h_ex : ∃ k, k > 0 ∧ 27 ∣ reverse_nat (k * 27) := by
    refine ⟨37, ?_⟩
    exact ⟨by decide, dvd_rev_27⟩
  have h_a : a 27 = my_find h_ex * 27 := by
    apply a_def_of_ne_zero (by decide)
  rw [h_a]
  have h_find : my_find h_ex = 37 := by
    rw [my_find_eq_iff h_ex]
    constructor
    · exact ⟨by decide, dvd_rev_27⟩
    · intro n hn
      intro ⟨hn_pos, h_div⟩
      have hn_lt_10_10 : n * 27 < 10^10 := by
        have : n < 37 := hn
        have : n * 27 < 37 * 27 := oeis62567_Nat_mul_lt_mul_of_pos_right this (by decide)
        omega
      rw [reverse_nat_eq_fast_temp (n * 27) hn_lt_10_10] at h_div
      rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n'
      · contradiction
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · revert h_div; decide
      · omega
  rw [h_find]

theorem dvd_rev_81 : 81 ∣ reverse_nat (12345679 * 81) := by
  have h1 : 12345679 * 81 = 999999999 := by rfl
  rw [h1]
  unfold reverse_nat
  have h_dig : digits 10 999999999 = [9, 9, 9, 9, 9, 9, 9, 9, 9] := digits_ofDigits 10 (by decide) [9, 9, 9, 9, 9, 9, 9, 9, 9] (by decide) (by decide)
  rw [h_dig]
  have h_rev : [9, 9, 9, 9, 9, 9, 9, 9, 9].reverse = [9, 9, 9, 9, 9, 9, 9, 9, 9] := by rfl
  rw [h_rev]
  have h_of : ofDigits 10 [9, 9, 9, 9, 9, 9, 9, 9, 9] = 999999999 := by rfl
  rw [h_of]
  exact ⟨12345679, by rfl⟩

theorem a_81 : a 81 = 999999999 := by
  have h_ex : ∃ k, k > 0 ∧ 81 ∣ reverse_nat (k * 81) := by
    refine ⟨12345679, ?_⟩
    exact ⟨by decide, dvd_rev_81⟩
  have h_a : a 81 = my_find h_ex * 81 := by
    apply a_def_of_ne_zero (by decide)
  rw [h_a]
  have h_find : my_find h_ex = 12345679 := by
    rw [my_find_eq_iff h_ex]
    constructor
    · exact ⟨by decide, dvd_rev_81⟩
    · intro n hn
      by_cases hn0 : n > 0
      · rintro ⟨_, h_div⟩
        exact no_solution_lt_12345679 n hn0 hn h_div
      · rintro ⟨hn_pos, _⟩
        contradiction
  rw [h_find]

theorem dvd_rev_243 : 243 ∣ reverse_nat (20164609 * 243) := by
  have h1 : 20164609 * 243 = 4899999987 := by rfl
  rw [h1]
  unfold reverse_nat
  have h_dig : digits 10 4899999987 = [7, 8, 9, 9, 9, 9, 9, 9, 8, 4] := digits_ofDigits 10 (by decide) [7, 8, 9, 9, 9, 9, 9, 9, 8, 4] (by decide) (by decide)
  rw [h_dig]
  have h_rev : [7, 8, 9, 9, 9, 9, 9, 9, 8, 4].reverse = [4, 8, 9, 9, 9, 9, 9, 9, 8, 7] := by rfl
  rw [h_rev]
  have h_of : ofDigits 10 [4, 8, 9, 9, 9, 9, 9, 9, 8, 7] = 7899999984 := by rfl
  rw [h_of]
  exact ⟨32510288, by rfl⟩

theorem a_243_ne_10_pow_sub_one : a 243 ≠ 10 ^ 27 - 1 := by
  intro h_eq
  have h_ne_zero : 10 ^ 27 - 1 ≠ 0 := by decide
  have h_ex : ∃ k, k > 0 ∧ 243 ∣ reverse_nat (k * 243) := by
    refine ⟨20164609, ?_⟩
    exact ⟨by decide, dvd_rev_243⟩
  have h_a : a 243 = my_find h_ex * 243 := by
    apply a_def_of_ne_zero (by decide)
  rw [h_a] at h_eq
  have h_le_20164609 := oeis62567_Nat_find_le (h := h_ex) (show 20164609 > 0 ∧ 243 ∣ reverse_nat (20164609 * 243) by
    exact ⟨by decide, dvd_rev_243⟩
  )
  have h_le_val : my_find h_ex * 243 ≤ 20164609 * 243 := Nat.mul_le_mul_right 243 h_le_20164609
  rw [h_eq] at h_le_val
  have : 10^27 - 1 > 20164609 * 243 := by decide
  omega

def S : ℕ → ℕ
  | 0 => 1
  | k + 1 => S k * (1 + 10^(27 * 3^k) + 10^(27 * 2 * 3^k))

theorem ten_pow_modeq_three (p : ℕ) : Oeis62567_ModEq 3 (10 ^ p) 1 := by
  have h : Oeis62567_ModEq 3 10 1 := rfl
  have h2 := Oeis62567_ModEq.pow p h
  revert h2
  simp

theorem sum_three_pow_modeq_three (A B : ℕ) : Oeis62567_ModEq 3 (1 + 10^A + 10^B) 0 := by
  have hA := ten_pow_modeq_three A
  have hB := ten_pow_modeq_three B
  have h1 : Oeis62567_ModEq 3 (1 + 10^A) (1 + 1) := Oeis62567_ModEq.add_left 1 hA
  have h2 : Oeis62567_ModEq 3 (1 + 10^A + 10^B) (1 + 1 + 1) := Oeis62567_ModEq.add h1 hB
  have h3 : Oeis62567_ModEq 3 (1 + 1 + 1) 0 := rfl
  exact Oeis62567_ModEq.trans h2 h3

theorem div_three_sum_three_pow (A B : ℕ) : 3 ∣ 1 + 10^A + 10^B := by
  rw [← oeis62567_modEq_zero_iff_dvd]
  exact sum_three_pow_modeq_three A B

theorem S_div_3_pow (k : ℕ) : 3^k ∣ S k := by
  induction k with
  | zero =>
    simp [S]
  | succ k ih =>
    rw [S]
    have h_mul : 3^(k+1) = 3^k * 3 := rfl
    rw [h_mul]
    have h_div : 3 ∣ 1 + 10^(27 * 3^k) + 10^(27 * 2 * 3^k) := by
      apply div_three_sum_three_pow
    exact oeis62567_Nat_mul_dvd_mul ih h_div

theorem S_relation (k : ℕ) : S k * (10^27 - 1) + 1 = 10^(27 * 3^k) := by
  induction k with
  | zero =>
    rfl
  | succ k ih =>
    rw [S]
    have h_pow : 10^(27 * 3^(k+1)) = 10^(27 * 3^k) * 10^(27 * 3^k) * 10^(27 * 3^k) := by
      have : 3^(k+1) = 3^k + 3^k + 3^k := by
        rw [Nat.pow_succ]
        omega
      rw [this]
      have : 27 * (3^k + 3^k + 3^k) = 27 * 3^k + 27 * 3^k + 27 * 3^k := by omega
      rw [this]
      repeat rw [Nat.pow_add]
    rw [h_pow]
    have h_pow27 : 10^(27 * 2 * 3^k) = 10^(27 * 3^k) * 10^(27 * 3^k) := by
      have : 27 * 2 * 3^k = 27 * 3^k + 27 * 3^k := by omega
      rw [this, Nat.pow_add]
    rw [h_pow27]
    let x := 10^(27 * 3^k)
    let D := 10^27 - 1
    let Z := 1 + x + x * x
    have h_comm : S k * Z * D = S k * D * Z := by
      rw [Nat.mul_assoc, Nat.mul_comm Z D, ← Nat.mul_assoc]
    have h_RHS : x * Z = x * x * x + x + x * x := by
      dsimp [Z]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      omega
    have h_eq : S k * D * Z + 1 + x + x * x = x * x * x + x + x * x := by
      have h_lhs_eq : S k * D * Z + 1 + x + x * x = (S k * D + 1) * Z := by
        rw [Nat.add_assoc, Nat.add_assoc, ← Nat.add_assoc 1 x (x * x)]
        rw [Nat.add_mul, Nat.one_mul]
      rw [h_lhs_eq]
      rw [ih]
      exact h_RHS
    have h_final : S k * D * Z + 1 = x * x * x := by omega
    rw [h_comm]
    exact h_final

theorem S_pos (k : ℕ) : 0 < S k := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [S]
    have : 0 < 1 + 10^(27 * 3^k) + 10^(27 * 2 * 3^k) := by
      rw [Nat.succ_add, Nat.zero_add, Nat.succ_add]
      apply Nat.zero_lt_succ
    exact Nat.mul_pos ih this

theorem S_mul_bound (k : ℕ) : 68899199886 * S k < 10^(27 * 3^k) := by
  have h_rel := S_relation k
  have h_pos := S_pos k
  have h_lt : 68899199886 < 10^27 - 1 := by decide
  have h_mul : 68899199886 * S k < (10^27 - 1) * S k := by
    apply oeis62567_Nat_mul_lt_mul_of_pos_right h_lt h_pos
  rw [Nat.mul_comm (10^27 - 1)] at h_mul
  omega

def L : ℕ → List ℕ
  | 0 => [6, 8, 8, 9, 9, 1, 9, 9, 8, 8, 6]
  | k + 1 => L k ++ List.replicate 16 0 ++ L k ++ List.replicate 16 0 ++ L k

theorem L_length (k : ℕ) : (L k).length = 27 * 3^k - 16 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [L]
    simp only [List.length_append, List.length_replicate, ih]
    have : 3^(k+1) = 3^k + 3^k + 3^k := by
      rw [Nat.pow_succ]
      omega
    rw [this]
    have : 27 * (3^k + 3^k + 3^k) = 27 * 3^k + 27 * 3^k + 27 * 3^k := by omega
    rw [this]
    have : 3^k ≥ 1 := Nat.one_le_pow k 3 (by decide)
    have : 27 * 3^k ≥ 16 := by omega
    omega

theorem L_ofDigits (k : ℕ) : ofDigits 10 (L k) = 68899199886 * S k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [L, S]
    repeat rw [oeis62567_ofDigits_append]
    simp only [oeis62567_ofDigits_replicate_zero, List.length_append, List.length_replicate, Nat.zero_mul, Nat.add_zero]
    rw [ih]
    have h_len := L_length k
    have h_pow1_exp : (L k).length + 16 = 27 * 3^k := by
      rw [h_len]
      have : 3^k ≥ 1 := Nat.one_le_pow k 3 (by decide)
      omega
    have h_pow1 : 10 ^ ((L k).length + 16) = 10 ^ (27 * 3^k) := by
      rw [h_pow1_exp]
    have h_pow2_exp : (L k).length + 16 + (L k).length + 16 = 27 * 2 * 3^k := by
      rw [h_len]
      have : 3^k ≥ 1 := Nat.one_le_pow k 3 (by decide)
      omega
    have h_pow2 : 10 ^ ((L k).length + 16 + (L k).length + 16) = 10 ^ (27 * 2 * 3^k) := by
      rw [h_pow2_exp]
    rw [h_pow1, h_pow2]
    rw [Nat.mul_add (S k) (1 + 10 ^ (27 * 3 ^ k)) (10 ^ (27 * 2 * 3 ^ k))]
    rw [Nat.mul_add (S k) 1 (10 ^ (27 * 3 ^ k))]
    rw [Nat.mul_one]
    rw [Nat.mul_add 68899199886 (S k + S k * 10 ^ (27 * 3 ^ k)) (S k * 10 ^ (27 * 2 * 3 ^ k))]
    rw [Nat.mul_add 68899199886 (S k) (S k * 10 ^ (27 * 3 ^ k))]
    rw [Nat.mul_assoc 68899199886 (S k) (10 ^ (27 * 3 ^ k))]
    rw [Nat.mul_assoc 68899199886 (S k) (10 ^ (27 * 2 * 3 ^ k))]

theorem L_reverse (k : ℕ) : (L k).reverse = L k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [L]
    simp [ih]

theorem L_lt_ten (k : ℕ) : ∀ x ∈ L k, x < 10 := by
  induction k with
  | zero =>
    decide
  | succ k ih =>
    rw [L]
    intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with (((h | h) | h) | h) | h
    · exact ih x h
    · rcases h with ⟨_, rfl⟩; decide
    · exact ih x h
    · rcases h with ⟨_, rfl⟩; decide
    · exact ih x h

theorem L_ne_nil (k : ℕ) : L k ≠ [] := by
  have h_len := L_length k
  intro hc
  rw [hc] at h_len
  simp at h_len
  have : 3^k ≥ 1 := Nat.one_le_pow k 3 (by decide)
  omega

theorem L_head (k : ℕ) : (L k).head (L_ne_nil k) = 6 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [L]
    simp [ih, L_ne_nil k]

theorem L_getLast (k : ℕ) : (L k).getLast (L_ne_nil k) = 6 := by
  have h_rev := L_reverse k
  have h_head := L_head k
  have h_ne_rev : (L k).reverse ≠ [] := by
    intro hc
    have h_rev_len : (L k).reverse.length = 0 := by rw [hc]; rfl
    rw [List.length_reverse] at h_rev_len
    have h_len := L_length k
    rw [h_rev_len] at h_len
    have : 3^k ≥ 1 := Nat.one_le_pow k 3 (by decide)
    omega
  have h1 : (L k).head (L_ne_nil k) = (L k).reverse.head h_ne_rev := by
    generalize (L k).reverse = l_rev at h_rev h_ne_rev ⊢
    subst h_rev
    rfl
  have h2 : (L k).reverse.head h_ne_rev = (L k).getLast (L_ne_nil k) := by
    have h_eq := List.head_eq_getLast_reverse h_ne_rev
    simp only [List.reverse_reverse] at h_eq
    exact h_eq
  rw [h1, h2] at h_head
  exact h_head

theorem reverse_nat_68899199886_S (k : ℕ) : reverse_nat (68899199886 * S k) = 68899199886 * S k := by
  have h_of := L_ofDigits k
  rw [← h_of]
  unfold reverse_nat
  have h_dig : digits 10 (ofDigits 10 (L k)) = L k := by
    apply digits_ofDigits 10 (by decide) (L k) (L_lt_ten k)
    have h_none : (L k).getLast? = some ((L k).getLast (L_ne_nil k)) := List.getLast?_eq_getLast (L_ne_nil k)
    rw [h_none, L_getLast k]
    decide
  rw [h_dig]
  rw [L_reverse k]

theorem rev_688 : reverse_nat 68899199886 = 68899199886 := by
  have h := reverse_nat_68899199886_S 0
  simp [S] at h
  exact h

theorem helper_pow_dvd {n : ℕ} (hn : n ≤ 12) : 3^n ∣ 3^12 := by
  exact Nat.pow_dvd_pow 3 hn

theorem a_3_n_ne_10_pow_sub_one (n : ℕ) (hn : 6 ≤ n) (hn12 : n ≤ 12) :
    a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  intro h_eq
  have h_ne_zero : 10 ^ (3 ^ (n - 2)) - 1 ≠ 0 := by
    have h1 : 1 ≤ 3 ^ (n - 2) := by
      have : 4 ≤ n - 2 := by omega
      have : 3^4 ≤ 3^(n-2) := Nat.pow_le_pow_right (by decide) this
      omega
    have h2 : 10 ^ 1 ≤ 10 ^ (3 ^ (n - 2)) := Nat.pow_le_pow_right (by decide) h1
    have : 10 ^ (3 ^ (n - 2)) - 1 ≥ 9 := by omega
    omega
  have h_ex : ∃ k, k > 0 ∧ (3^n) ∣ reverse_nat (k * (3^n)) := by
    by_cases hc : ∃ k, k > 0 ∧ (3^n) ∣ reverse_nat (k * (3^n))
    · exact hc
    · exfalso
      have h_a : a (3^n) = 0 := by
        unfold a
        rw [if_neg (Nat.ne_of_gt (Nat.pow_pos (by decide)))]
        rw [dif_neg hc]
      rw [h_a] at h_eq
      exact h_ne_zero h_eq.symm

  have h_a_def : a (3^n) = my_find h_ex * 3^n := by
    apply a_def_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  rw [h_a_def] at h_eq
  have h_div_12 : 3^12 ∣ 68899199886 := by decide
  have h_div_n : 3^n ∣ 68899199886 := Nat.dvd_trans (helper_pow_dvd hn12) h_div_12
  rcases h_div_n with ⟨k_wit, hk_wit⟩
  have hk_wit_pos : k_wit > 0 := by
    by_cases h_zero : k_wit > 0
    · exact h_zero
    · exfalso
      have : k_wit = 0 := by omega
      subst this
      omega
  have h_P_kwit : k_wit > 0 ∧ 3^n ∣ reverse_nat (k_wit * 3^n) := by
    refine ⟨hk_wit_pos, ?_⟩
    rw [Nat.mul_comm, ← hk_wit, rev_688]
    exact ⟨k_wit, hk_wit⟩
  have h_le_kwit := oeis62567_Nat_find_le (h := h_ex) h_P_kwit
  have h_le_688 : my_find h_ex * 3^n ≤ 68899199886 := by
    have : my_find h_ex * 3^n ≤ k_wit * 3^n := Nat.mul_le_mul_right (3^n) h_le_kwit
    rw [Nat.mul_comm k_wit] at this
    rw [← hk_wit] at this
    exact this
  rw [h_eq] at h_le_688
  have h_gt : 10 ^ (3 ^ (n - 2)) - 1 > 68899199886 := by
    have h_n2 : 4 ≤ n - 2 := by omega
    have h_3n2 : 3^4 ≤ 3^(n-2) := Nat.pow_le_pow_right (by decide) h_n2
    have h_10n2 : 10^81 ≤ 10^(3^(n-2)) := Nat.pow_le_pow_right (by decide) h_3n2
    have h_sub : 10^81 - 1 ≤ 10^(3^(n-2)) - 1 := Nat.sub_le_sub_right h_10n2 1
    have h_dec : 10^81 - 1 > 68899199886 := by decide
    omega
  omega

theorem a_3_n_ne_10_pow_sub_one_large (n : ℕ) (hn : 13 ≤ n) :
    a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
  intro h_eq
  have h_ne_zero : 10 ^ (3 ^ (n - 2)) - 1 ≠ 0 := by
    have h1 : 1 ≤ 3 ^ (n - 2) := by
      have : 11 ≤ n - 2 := by omega
      have : 3^11 ≤ 3^(n-2) := Nat.pow_le_pow_right (by decide) this
      omega
    have h2 : 10 ^ 1 ≤ 10 ^ (3 ^ (n - 2)) := Nat.pow_le_pow_right (by decide) h1
    have : 10 ^ (3 ^ (n - 2)) - 1 ≥ 9 := by omega
    omega
  have h_ex : ∃ k, k > 0 ∧ (3^n) ∣ reverse_nat (k * (3^n)) := by
    by_cases hc : ∃ k, k > 0 ∧ (3^n) ∣ reverse_nat (k * (3^n))
    · exact hc
    · exfalso
      have h_a : a (3^n) = 0 := by
        unfold a
        rw [if_neg (Nat.ne_of_gt (Nat.pow_pos (by decide)))]
        rw [dif_neg hc]
      rw [h_a] at h_eq
      have : False := h_ne_zero h_eq.symm
      contradiction
  have h_a_def : a (3^n) = my_find h_ex * 3^n := by
    apply a_def_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  rw [h_a_def] at h_eq

  let k := n - 12
  have hk : n = k + 12 := by omega
  have hk_pos : k > 0 := by omega

  let W := 68899199886 * S k
  have h_W_pos : W > 0 := by
    have hS := S_pos k
    exact Nat.mul_pos (by decide) hS

  have h_div_W : 3^n ∣ W := by
    rw [hk]
    have h_pow : 3^(k+12) = 3^12 * 3^k := by
      rw [Nat.pow_add, Nat.mul_comm]
    rw [h_pow]
    have h_div_688 : 3^12 ∣ 68899199886 := by decide
    have h_div_S : 3^k ∣ S k := S_div_3_pow k
    exact oeis62567_Nat_mul_dvd_mul h_div_688 h_div_S

  rcases h_div_W with ⟨k_wit, hk_wit⟩
  have hk_wit_pos : k_wit > 0 := by
    by_cases h_zero : k_wit > 0
    · exact h_zero
    · exfalso
      have : k_wit = 0 := by omega
      subst this
      omega

  have h_P_kwit : k_wit > 0 ∧ 3^n ∣ reverse_nat (k_wit * 3^n) := by
    refine ⟨hk_wit_pos, ?_⟩
    rw [Nat.mul_comm, ← hk_wit, reverse_nat_68899199886_S]
    exact ⟨k_wit, hk_wit⟩

  have h_le_kwit := oeis62567_Nat_find_le (h := h_ex) h_P_kwit
  have h_le_W : my_find h_ex * 3^n ≤ W := by
    have : my_find h_ex * 3^n ≤ k_wit * 3^n := Nat.mul_le_mul_right (3^n) h_le_kwit
    rw [Nat.mul_comm k_wit] at this
    rw [← hk_wit] at this
    exact this

  rw [h_eq] at h_le_W
  have h_W_lt : W < 10^(27 * 3^k) := S_mul_bound k

  have h_exp_le : 27 * 3^k ≤ 3^(n-2) - 1 := by
    have h_eq2 : 27 * 3^k = 3^(k+3) := by
      rw [Nat.pow_add]
      have : 3^3 = 27 := rfl
      rw [this, Nat.mul_comm]
    rw [h_eq2]
    have h_eq3 : n - 2 = k + 10 := by omega
    rw [h_eq3]
    have h_eq4 : 3^(k+10) = 3^(k+3) * 2187 := by
      have : k + 10 = k + 3 + 7 := by omega
      rw [this, Nat.pow_add]
    rw [h_eq4]
    have h_pow_pos_init : 3^(k+3) > 0 := Nat.pow_pos (by decide)
    generalize 3^(k+3) = X at h_pow_pos_init ⊢
    omega

  have h_10_pow_le : 10^(27 * 3^k) ≤ 10^(3^(n-2) - 1) := by
    exact Nat.pow_le_pow_right (by decide) h_exp_le
  have h_10_pow_lt : 10^(3^(n-2) - 1) < 10^(3^(n-2)) - 1 := by
    have h_eq_pow : 10^(3^(n-2)) = 10^(3^(n-2) - 1) * 10 := by
      have h_pos : 3^(n-2) > 0 := Nat.pow_pos (by decide)
      have h_eq_sub : Nat.succ (3^(n-2) - 1) = 3^(n-2) := by omega
      rw [← Nat.pow_succ]
      rw [h_eq_sub]
    have h_pos_pow : 10^(3^(n-2) - 1) > 0 := Nat.pow_pos (by decide)
    omega

  have h_lt1 : W < 10^(3^(n-2) - 1) := by omega
  have h_lt2 : W < 10^(3^(n-2)) - 1 := by omega
  omega



end Oeis62567

open Oeis62567

theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  by_cases h2 : n = 2
  · subst h2
    have : 10^(3^(2-2)) - 1 = 9 := by rfl
    rw [this, a_9]
    decide
  · by_cases h3 : n = 3
    · subst h3
      have : 10^(3^(3-2)) - 1 = 999 := by rfl
      rw [this, a_27]
      decide
    · by_cases h4 : n = 4
      · subst h4
        have : 10^(3^(4-2)) - 1 = 999999999 := by rfl
        rw [this, a_81]
        decide
      · by_cases h5 : n = 5
        · subst h5
          have h_lhs : a 243 ≠ 10^(3^(5-2)) - 1 := by
            have : 10^(3^(5-2)) - 1 = 10^27 - 1 := by rfl
            rw [this]
            exact a_243_ne_10_pow_sub_one
          have h_rhs : ¬ (5 = 2 ∨ 5 = 3 ∨ 5 = 4) := by omega
          constructor
          · intro h; exact False.elim (h_lhs h)
          · intro h; exact False.elim (h_rhs h)
        · have hn6 : 6 ≤ n := by omega
          have h_rhs : ¬ (n = 2 ∨ n = 3 ∨ n = 4) := by omega
          have h_lhs : a (3^n) ≠ 10 ^ (3 ^ (n - 2)) - 1 := by
            by_cases hn12 : n ≤ 12
            · exact a_3_n_ne_10_pow_sub_one n hn6 hn12
            · have hn13 : 13 ≤ n := by omega
              exact a_3_n_ne_10_pow_sub_one_large n hn13
          constructor
          · intro h; exact False.elim (h_lhs h)
          · intro h; exact False.elim (h_rhs h)
