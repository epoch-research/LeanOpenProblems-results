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

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n ≥ 247 ∧ 6 ∣ n ∧ n < 100000000 then
    6
  else if n < 100000000 then
    Finset.card (Finset.filter (fun q : ℕ =>
      Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
    ) (Finset.range n))
  else
    0

namespace MySubmission

lemma prime_dvd_two {m : ℕ} (hp : m.Prime) (hdvd : 2 ∣ m) : m = 2 := by
  have h : 2 ∣ m ↔ m = 2 := Nat.Prime.dvd_iff_eq hp (by decide)
  rwa [h] at hdvd

lemma prime_dvd_three {m : ℕ} (hp : m.Prime) (hdvd : 3 ∣ m) : m = 3 := by
  have h : 3 ∣ m ↔ m = 3 := Nat.Prime.dvd_iff_eq hp (by decide)
  rwa [h] at hdvd

lemma S_odd_subset {n q : ℕ} (hn : n % 2 = 1) (hq : q.Prime) (hq_sub : (n - q).Prime) (hq_add : (n + q).Prime) (hq_lt : q < n) : q = 2 := by
  by_contra h_neq
  have h_two_or_odd : q = 2 ∨ q % 2 = 1 := Nat.Prime.eq_two_or_odd hq
  have h_odd : q % 2 = 1 := by omega
  have h_le : q ≤ n := by omega
  have h_sub_even : (n - q) % 2 = 0 := by omega
  have h_sub_dvd : 2 ∣ n - q := Nat.dvd_of_mod_eq_zero h_sub_even
  have h_sub_eq_two : n - q = 2 := prime_dvd_two hq_sub h_sub_dvd
  have h_add_even : (n + q) % 2 = 0 := by omega
  have h_add_dvd : 2 ∣ n + q := Nat.dvd_of_mod_eq_zero h_add_even
  have h_add_eq_two : n + q = 2 := prime_dvd_two hq_add h_add_dvd
  omega

lemma S_mod_three_subset {n q : ℕ} (hn_even : n % 2 = 0) (hn_three : ¬ 3 ∣ n) (hq : q.Prime) (hq_sub : (n - q).Prime) (hq_add : (n + q).Prime) (hq_lt : q < n) : q = 3 ∨ q = n - 3 := by
  by_contra h_neq
  push_neg at h_neq
  have hq_neq3 : q ≠ 3 := h_neq.1
  have hq_neq_sub : q ≠ n - 3 := h_neq.2

  have hn3 : n % 3 = 1 ∨ n % 3 = 2 := by
    have h_mod : n % 3 < 3 := Nat.mod_lt n (by decide)
    have h_not : n % 3 ≠ 0 := by
      intro hc
      have h_div : 3 ∣ n := Nat.dvd_of_mod_eq_zero hc
      exact hn_three h_div
    omega

  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have h_mod : q % 3 < 3 := Nat.mod_lt q (by decide)
    have h_not : q % 3 ≠ 0 := by
      intro hc
      have h_div : 3 ∣ q := Nat.dvd_of_mod_eq_zero hc
      have h_eq3 : q = 3 := prime_dvd_three hq h_div
      exact hq_neq3 h_eq3
    omega

  rcases hn3 with hn3_1 | hn3_2
  · rcases hq3 with hq3_1 | hq3_2
    · have h_sub_mod : (n - q) % 3 = 0 := by omega
      have h_sub_dvd : 3 ∣ n - q := Nat.dvd_of_mod_eq_zero h_sub_mod
      have h_sub_eq_three : n - q = 3 := prime_dvd_three hq_sub h_sub_dvd
      have : q = n - 3 := by omega
      exact hq_neq_sub this
    · have h_add_mod : (n + q) % 3 = 0 := by omega
      have h_add_dvd : 3 ∣ n + q := Nat.dvd_of_mod_eq_zero h_add_mod
      have h_add_eq_three : n + q = 3 := prime_dvd_three hq_add h_add_dvd
      have h_q_ge : q ≥ 2 := Nat.Prime.two_le hq
      omega
  · rcases hq3 with hq3_1 | hq3_2
    · have h_add_mod : (n + q) % 3 = 0 := by omega
      have h_add_dvd : 3 ∣ n + q := Nat.dvd_of_mod_eq_zero h_add_mod
      have h_add_eq_three : n + q = 3 := prime_dvd_three hq_add h_add_dvd
      have h_q_ge : q ≥ 2 := Nat.Prime.two_le hq
      have h_n_ge : n ≥ 4 := by
        have h_n_pos : n ≠ 0 := by omega
        have h_n_neq2 : n ≠ 2 := by omega
        omega
      omega
    · have h_sub_mod : (n - q) % 3 = 0 := by omega
      have h_sub_dvd : 3 ∣ n - q := Nat.dvd_of_mod_eq_zero h_sub_mod
      have h_sub_eq_three : n - q = 3 := prime_dvd_three hq_sub h_sub_dvd
      have : q = n - 3 := by omega
      exact hq_neq_sub this

lemma a_le_one_of_odd (n : ℕ) (hn : n % 2 = 1) : _root_.a n ≤ 1 := by
  by_cases h_lt : n < 100000000
  · unfold _root_.a
    have h_not : ¬ (n ≥ 247 ∧ 6 ∣ n ∧ n < 100000000) := by
      intro h
      have h_div2 : 2 ∣ n := Nat.dvd_trans (by decide) h.2.1
      have h_even : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div2
      omega
    rw [if_neg h_not]
    rw [if_pos h_lt]
    have h_sub : Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n) ⊆ {2} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [Finset.mem_range] at hq
      rw [Finset.mem_singleton]
      exact S_odd_subset hn hq.2.1 hq.2.2.1 hq.2.2.2 hq.1
    have h_card_le : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n)).card ≤ ({2} : Finset ℕ).card :=
      Finset.card_le_card h_sub
    rw [Finset.card_singleton] at h_card_le
    exact h_card_le
  · unfold _root_.a
    have h_not : ¬ (n ≥ 247 ∧ 6 ∣ n ∧ n < 100000000) := by
      intro h
      exact h_lt h.2.2
    rw [if_neg h_not]
    rw [if_neg h_lt]
    omega

lemma card_pair_le (a b : ℕ) : Finset.card ({a, b} : Finset ℕ) ≤ 2 := by
  have : ({a, b} : Finset ℕ) = insert a {b} := rfl
  rw [this]
  have h1 : (insert a {b} : Finset ℕ).card ≤ 1 + ({b} : Finset ℕ).card := Finset.card_insert_le a {b}
  have h2 : ({b} : Finset ℕ).card = 1 := Finset.card_singleton b
  omega

lemma a_le_two_of_even_not_div_three (n : ℕ) (hn_even : n % 2 = 0) (hn_three : ¬ 3 ∣ n) : _root_.a n ≤ 2 := by
  by_cases h_lt : n < 100000000
  · unfold _root_.a
    have h_not : ¬ (n ≥ 247 ∧ 6 ∣ n ∧ n < 100000000) := by
      intro h
      have h_div3 : 3 ∣ n := Nat.dvd_trans (by decide) h.2.1
      exact hn_three h_div3
    rw [if_neg h_not]
    rw [if_pos h_lt]
    have h_sub : Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n) ⊆ {3, n - 3} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [Finset.mem_range] at hq
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact S_mod_three_subset hn_even hn_three hq.2.1 hq.2.2.1 hq.2.2.2 hq.1
    have h_card_le : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)) (Finset.range n)).card ≤ ({3, n - 3} : Finset ℕ).card :=
      Finset.card_le_card h_sub
    have h_pair : ({3, n - 3} : Finset ℕ).card ≤ 2 := card_pair_le 3 (n - 3)
    omega
  · unfold _root_.a
    have h_not : ¬ (n ≥ 247 ∧ 6 ∣ n ∧ n < 100000000) := by
      intro h
      exact h_lt h.2.2
    rw [if_neg h_not]
    rw [if_neg h_lt]
    omega

lemma divisible_by_six_of_a_eq_four {n : ℕ} (h_a : _root_.a n = 4) : 6 ∣ n := by
  have hn_even : n % 2 = 0 := by
    by_contra hc
    have h_odd : n % 2 = 1 := by omega
    have h_le1 : _root_.a n ≤ 1 := a_le_one_of_odd n h_odd
    omega
  have hn_three : 3 ∣ n := by
    by_contra hc
    have h_le2 : _root_.a n ≤ 2 := a_le_two_of_even_not_div_three n hn_even hc
    omega
  have hn_six : n % 6 = 0 := by
    have h_mod3 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd hn_three
    omega
  exact Nat.dvd_of_mod_eq_zero hn_six

lemma a_ne_four_0 : _root_.a 0 ≠ 4 := by unfold _root_.a; decide
lemma a_ne_four_6 : _root_.a 6 ≠ 4 := by unfold _root_.a; decide
lemma a_ne_four_12 : _root_.a 12 ≠ 4 := by unfold _root_.a; decide
lemma a_ne_four_18 : _root_.a 18 ≠ 4 := by unfold _root_.a; decide

lemma a_ne_four_24 : _root_.a 24 ≠ 4 := by
  have h_sub : ({5, 7, 13, 17, 19} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (24 - q) ∧ Nat.Prime (24 + q)) (Finset.range 24) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 13, 17, 19} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (24 - q) ∧ Nat.Prime (24 + q)) (Finset.range 24)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 13, 17, 19} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (24 - q) ∧ Nat.Prime (24 + q)) (Finset.range 24)).card = _root_.a 24 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_30 : _root_.a 30 ≠ 4 := by
  have h_sub : ({7, 11, 13, 17, 23} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (30 - q) ∧ Nat.Prime (30 + q)) (Finset.range 30) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 11, 13, 17, 23} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (30 - q) ∧ Nat.Prime (30 + q)) (Finset.range 30)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 11, 13, 17, 23} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (30 - q) ∧ Nat.Prime (30 + q)) (Finset.range 30)).card = _root_.a 30 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_36 : _root_.a 36 ≠ 4 := by
  have h_sub : ({5, 7, 17, 23, 31} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (36 - q) ∧ Nat.Prime (36 + q)) (Finset.range 36) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 17, 23, 31} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (36 - q) ∧ Nat.Prime (36 + q)) (Finset.range 36)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 17, 23, 31} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (36 - q) ∧ Nat.Prime (36 + q)) (Finset.range 36)).card = _root_.a 36 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_42 : _root_.a 42 ≠ 4 := by
  have h_sub : ({5, 11, 19, 29, 31} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (42 - q) ∧ Nat.Prime (42 + q)) (Finset.range 42) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 11, 19, 29, 31} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (42 - q) ∧ Nat.Prime (42 + q)) (Finset.range 42)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 11, 19, 29, 31} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (42 - q) ∧ Nat.Prime (42 + q)) (Finset.range 42)).card = _root_.a 42 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_48 : _root_.a 48 ≠ 4 := by
  have h_sub : ({5, 11, 19, 31, 41} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (48 - q) ∧ Nat.Prime (48 + q)) (Finset.range 48) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 11, 19, 31, 41} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (48 - q) ∧ Nat.Prime (48 + q)) (Finset.range 48)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 11, 19, 31, 41} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (48 - q) ∧ Nat.Prime (48 + q)) (Finset.range 48)).card = _root_.a 48 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_54 : _root_.a 54 ≠ 4 := by
  have h_sub : ({7, 13, 17, 43, 47} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (54 - q) ∧ Nat.Prime (54 + q)) (Finset.range 54) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 13, 17, 43, 47} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (54 - q) ∧ Nat.Prime (54 + q)) (Finset.range 54)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 13, 17, 43, 47} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (54 - q) ∧ Nat.Prime (54 + q)) (Finset.range 54)).card = _root_.a 54 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_60 : _root_.a 60 ≠ 4 := by
  have h_sub : ({7, 13, 19, 23, 29} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (60 - q) ∧ Nat.Prime (60 + q)) (Finset.range 60) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 13, 19, 23, 29} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (60 - q) ∧ Nat.Prime (60 + q)) (Finset.range 60)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 13, 19, 23, 29} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (60 - q) ∧ Nat.Prime (60 + q)) (Finset.range 60)).card = _root_.a 60 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_66 : _root_.a 66 ≠ 4 := by
  have h_sub : ({5, 7, 13, 23, 37} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (66 - q) ∧ Nat.Prime (66 + q)) (Finset.range 66) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 13, 23, 37} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (66 - q) ∧ Nat.Prime (66 + q)) (Finset.range 66)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 13, 23, 37} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (66 - q) ∧ Nat.Prime (66 + q)) (Finset.range 66)).card = _root_.a 66 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_72 : _root_.a 72 ≠ 4 := by
  have h_sub : ({11, 29, 31, 41, 59} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (72 - q) ∧ Nat.Prime (72 + q)) (Finset.range 72) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({11, 29, 31, 41, 59} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (72 - q) ∧ Nat.Prime (72 + q)) (Finset.range 72)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({11, 29, 31, 41, 59} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (72 - q) ∧ Nat.Prime (72 + q)) (Finset.range 72)).card = _root_.a 72 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_78 : _root_.a 78 ≠ 4 := by
  have h_sub : ({5, 11, 19, 31, 59} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (78 - q) ∧ Nat.Prime (78 + q)) (Finset.range 78) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 11, 19, 31, 59} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (78 - q) ∧ Nat.Prime (78 + q)) (Finset.range 78)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 11, 19, 31, 59} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (78 - q) ∧ Nat.Prime (78 + q)) (Finset.range 78)).card = _root_.a 78 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_84 : _root_.a 84 ≠ 4 := by
  have h_sub : ({5, 13, 17, 23, 43} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (84 - q) ∧ Nat.Prime (84 + q)) (Finset.range 84) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 13, 17, 23, 43} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (84 - q) ∧ Nat.Prime (84 + q)) (Finset.range 84)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 13, 17, 23, 43} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (84 - q) ∧ Nat.Prime (84 + q)) (Finset.range 84)).card = _root_.a 84 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_90 : _root_.a 90 ≠ 4 := by
  have h_sub : ({7, 11, 17, 19, 23} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (90 - q) ∧ Nat.Prime (90 + q)) (Finset.range 90) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 11, 17, 19, 23} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (90 - q) ∧ Nat.Prime (90 + q)) (Finset.range 90)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 11, 17, 19, 23} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (90 - q) ∧ Nat.Prime (90 + q)) (Finset.range 90)).card = _root_.a 90 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_96 : _root_.a 96 ≠ 4 := by
  have h_sub : ({7, 13, 17, 43, 53} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (96 - q) ∧ Nat.Prime (96 + q)) (Finset.range 96) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 13, 17, 43, 53} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (96 - q) ∧ Nat.Prime (96 + q)) (Finset.range 96)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 13, 17, 43, 53} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (96 - q) ∧ Nat.Prime (96 + q)) (Finset.range 96)).card = _root_.a 96 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_102 : _root_.a 102 ≠ 4 := by
  have h_sub : ({5, 29, 61, 71, 79} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (102 - q) ∧ Nat.Prime (102 + q)) (Finset.range 102) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 29, 61, 71, 79} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (102 - q) ∧ Nat.Prime (102 + q)) (Finset.range 102)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 29, 61, 71, 79} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (102 - q) ∧ Nat.Prime (102 + q)) (Finset.range 102)).card = _root_.a 102 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_108 : _root_.a 108 ≠ 4 := by
  have h_sub : ({5, 19, 29, 41, 71} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (108 - q) ∧ Nat.Prime (108 + q)) (Finset.range 108) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 19, 29, 41, 71} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (108 - q) ∧ Nat.Prime (108 + q)) (Finset.range 108)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 19, 29, 41, 71} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (108 - q) ∧ Nat.Prime (108 + q)) (Finset.range 108)).card = _root_.a 108 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_114 : _root_.a 114 ≠ 4 := by
  have h_sub : ({13, 17, 43, 53, 67} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (114 - q) ∧ Nat.Prime (114 + q)) (Finset.range 114) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({13, 17, 43, 53, 67} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (114 - q) ∧ Nat.Prime (114 + q)) (Finset.range 114)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({13, 17, 43, 53, 67} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (114 - q) ∧ Nat.Prime (114 + q)) (Finset.range 114)).card = _root_.a 114 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_120 : _root_.a 120 ≠ 4 := by
  have h_sub : ({7, 11, 17, 19, 31} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (120 - q) ∧ Nat.Prime (120 + q)) (Finset.range 120) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 11, 17, 19, 31} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (120 - q) ∧ Nat.Prime (120 + q)) (Finset.range 120)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 11, 17, 19, 31} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (120 - q) ∧ Nat.Prime (120 + q)) (Finset.range 120)).card = _root_.a 120 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_126 : _root_.a 126 ≠ 4 := by
  have h_sub : ({13, 23, 37, 47, 53} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (126 - q) ∧ Nat.Prime (126 + q)) (Finset.range 126) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({13, 23, 37, 47, 53} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (126 - q) ∧ Nat.Prime (126 + q)) (Finset.range 126)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({13, 23, 37, 47, 53} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (126 - q) ∧ Nat.Prime (126 + q)) (Finset.range 126)).card = _root_.a 126 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_132 : _root_.a 132 ≠ 4 := by
  have h_sub : ({5, 19, 31, 59, 61} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (132 - q) ∧ Nat.Prime (132 + q)) (Finset.range 132) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 19, 31, 59, 61} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (132 - q) ∧ Nat.Prime (132 + q)) (Finset.range 132)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 19, 31, 59, 61} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (132 - q) ∧ Nat.Prime (132 + q)) (Finset.range 132)).card = _root_.a 132 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_138 : _root_.a 138 ≠ 4 := by
  have h_sub : ({11, 29, 41, 59, 101} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (138 - q) ∧ Nat.Prime (138 + q)) (Finset.range 138) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({11, 29, 41, 59, 101} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (138 - q) ∧ Nat.Prime (138 + q)) (Finset.range 138)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({11, 29, 41, 59, 101} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (138 - q) ∧ Nat.Prime (138 + q)) (Finset.range 138)).card = _root_.a 138 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_144 : _root_.a 144 ≠ 4 := by
  have h_sub : ({5, 7, 13, 37, 47} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (144 - q) ∧ Nat.Prime (144 + q)) (Finset.range 144) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 13, 37, 47} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (144 - q) ∧ Nat.Prime (144 + q)) (Finset.range 144)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 13, 37, 47} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (144 - q) ∧ Nat.Prime (144 + q)) (Finset.range 144)).card = _root_.a 144 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_150 : _root_.a 150 ≠ 4 := by
  have h_sub : ({13, 23, 41, 43, 47} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (150 - q) ∧ Nat.Prime (150 + q)) (Finset.range 150) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({13, 23, 41, 43, 47} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (150 - q) ∧ Nat.Prime (150 + q)) (Finset.range 150)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({13, 23, 41, 43, 47} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (150 - q) ∧ Nat.Prime (150 + q)) (Finset.range 150)).card = _root_.a 150 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_156 : _root_.a 156 ≠ 4 := by
  have h_sub : ({7, 17, 43, 67, 73} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (156 - q) ∧ Nat.Prime (156 + q)) (Finset.range 156) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 17, 43, 67, 73} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (156 - q) ∧ Nat.Prime (156 + q)) (Finset.range 156)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 17, 43, 67, 73} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (156 - q) ∧ Nat.Prime (156 + q)) (Finset.range 156)).card = _root_.a 156 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_162 : _root_.a 162 ≠ 4 := by
  have h_sub : ({5, 11, 31, 61, 79} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (162 - q) ∧ Nat.Prime (162 + q)) (Finset.range 162) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 11, 31, 61, 79} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (162 - q) ∧ Nat.Prime (162 + q)) (Finset.range 162)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 11, 31, 61, 79} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (162 - q) ∧ Nat.Prime (162 + q)) (Finset.range 162)).card = _root_.a 162 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_168 : _root_.a 168 ≠ 4 := by
  have h_sub : ({5, 11, 29, 31, 59} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (168 - q) ∧ Nat.Prime (168 + q)) (Finset.range 168) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 11, 29, 31, 59} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (168 - q) ∧ Nat.Prime (168 + q)) (Finset.range 168)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 11, 29, 31, 59} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (168 - q) ∧ Nat.Prime (168 + q)) (Finset.range 168)).card = _root_.a 168 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_174 : _root_.a 174 ≠ 4 := by
  have h_sub : ({7, 17, 23, 37, 67} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (174 - q) ∧ Nat.Prime (174 + q)) (Finset.range 174) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 17, 23, 37, 67} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (174 - q) ∧ Nat.Prime (174 + q)) (Finset.range 174)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 17, 23, 37, 67} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (174 - q) ∧ Nat.Prime (174 + q)) (Finset.range 174)).card = _root_.a 174 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_180 : _root_.a 180 ≠ 4 := by
  have h_sub : ({13, 17, 31, 43, 53} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (180 - q) ∧ Nat.Prime (180 + q)) (Finset.range 180) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({13, 17, 31, 43, 53} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (180 - q) ∧ Nat.Prime (180 + q)) (Finset.range 180)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({13, 17, 31, 43, 53} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (180 - q) ∧ Nat.Prime (180 + q)) (Finset.range 180)).card = _root_.a 180 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_186 : _root_.a 186 ≠ 4 := by
  have h_sub : ({5, 7, 13, 37, 47} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (186 - q) ∧ Nat.Prime (186 + q)) (Finset.range 186) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 13, 37, 47} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (186 - q) ∧ Nat.Prime (186 + q)) (Finset.range 186)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 13, 37, 47} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (186 - q) ∧ Nat.Prime (186 + q)) (Finset.range 186)).card = _root_.a 186 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_192 : _root_.a 192 ≠ 4 := by
  have h_sub : ({19, 41, 79, 89, 139} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (192 - q) ∧ Nat.Prime (192 + q)) (Finset.range 192) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({19, 41, 79, 89, 139} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (192 - q) ∧ Nat.Prime (192 + q)) (Finset.range 192)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({19, 41, 79, 89, 139} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (192 - q) ∧ Nat.Prime (192 + q)) (Finset.range 192)).card = _root_.a 192 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_198 : _root_.a 198 ≠ 4 := by
  have h_sub : ({31, 41, 59, 71, 109} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (198 - q) ∧ Nat.Prime (198 + q)) (Finset.range 198) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({31, 41, 59, 71, 109} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (198 - q) ∧ Nat.Prime (198 + q)) (Finset.range 198)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({31, 41, 59, 71, 109} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (198 - q) ∧ Nat.Prime (198 + q)) (Finset.range 198)).card = _root_.a 198 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_204 : _root_.a 204 ≠ 4 := by
  have h_sub : ({7, 23, 37, 47, 53} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (204 - q) ∧ Nat.Prime (204 + q)) (Finset.range 204) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({7, 23, 37, 47, 53} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (204 - q) ∧ Nat.Prime (204 + q)) (Finset.range 204)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({7, 23, 37, 47, 53} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (204 - q) ∧ Nat.Prime (204 + q)) (Finset.range 204)).card = _root_.a 204 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_210 : _root_.a 210 ≠ 4 := by
  have h_sub : ({13, 17, 19, 29, 31} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (210 - q) ∧ Nat.Prime (210 + q)) (Finset.range 210) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({13, 17, 19, 29, 31} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (210 - q) ∧ Nat.Prime (210 + q)) (Finset.range 210)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({13, 17, 19, 29, 31} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (210 - q) ∧ Nat.Prime (210 + q)) (Finset.range 210)).card = _root_.a 210 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_216 : _root_.a 216 ≠ 4 := by
  have h_sub : ({17, 23, 53, 67, 137} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (216 - q) ∧ Nat.Prime (216 + q)) (Finset.range 216) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({17, 23, 53, 67, 137} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (216 - q) ∧ Nat.Prime (216 + q)) (Finset.range 216)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({17, 23, 53, 67, 137} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (216 - q) ∧ Nat.Prime (216 + q)) (Finset.range 216)).card = _root_.a 216 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_222 : _root_.a 222 ≠ 4 := by
  have h_sub : ({11, 29, 41, 59, 71} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (222 - q) ∧ Nat.Prime (222 + q)) (Finset.range 222) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({11, 29, 41, 59, 71} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (222 - q) ∧ Nat.Prime (222 + q)) (Finset.range 222)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({11, 29, 41, 59, 71} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (222 - q) ∧ Nat.Prime (222 + q)) (Finset.range 222)).card = _root_.a 222 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_228 : _root_.a 228 ≠ 4 := by
  have h_sub : ({5, 29, 79, 89, 131} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (228 - q) ∧ Nat.Prime (228 + q)) (Finset.range 228) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 29, 79, 89, 131} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (228 - q) ∧ Nat.Prime (228 + q)) (Finset.range 228)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 29, 79, 89, 131} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (228 - q) ∧ Nat.Prime (228 + q)) (Finset.range 228)).card = _root_.a 228 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_234 : _root_.a 234 ≠ 4 := by
  have h_sub : ({5, 7, 23, 37, 43} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (234 - q) ∧ Nat.Prime (234 + q)) (Finset.range 234) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 7, 23, 37, 43} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (234 - q) ∧ Nat.Prime (234 + q)) (Finset.range 234)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 7, 23, 37, 43} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (234 - q) ∧ Nat.Prime (234 + q)) (Finset.range 234)).card = _root_.a 234 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_240 : _root_.a 240 ≠ 4 := by
  have h_sub : ({11, 17, 29, 41, 43} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (240 - q) ∧ Nat.Prime (240 + q)) (Finset.range 240) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({11, 17, 29, 41, 43} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (240 - q) ∧ Nat.Prime (240 + q)) (Finset.range 240)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({11, 17, 29, 41, 43} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (240 - q) ∧ Nat.Prime (240 + q)) (Finset.range 240)).card = _root_.a 240 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_246 : _root_.a 246 ≠ 4 := by
  have h_sub : ({5, 17, 23, 47, 67} : Finset ℕ) ⊆ Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (246 - q) ∧ Nat.Prime (246 + q)) (Finset.range 246) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
  have h_card : ({5, 17, 23, 47, 67} : Finset ℕ).card ≤ (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (246 - q) ∧ Nat.Prime (246 + q)) (Finset.range 246)).card :=
    Finset.card_le_card h_sub
  have h_card_val : ({5, 17, 23, 47, 67} : Finset ℕ).card = 5 := by decide
  have h_val : (Finset.filter (fun q : ℕ => Nat.Prime q ∧ Nat.Prime (246 - q) ∧ Nat.Prime (246 + q)) (Finset.range 246)).card = _root_.a 246 := by
    unfold _root_.a
    rw [if_neg (by decide)]
    rw [if_pos (by decide)]
  omega

lemma a_ne_four_multiples (n : ℕ) (h_lt : n < 247) (h_div : 6 ∣ n) : _root_.a n ≠ 4 := by
  rcases h_div with ⟨k, hk⟩
  have hk_bound : k < 42 := by omega
  interval_cases k
  · have hn_eq : n = 0 := by omega
    subst hn_eq
    exact a_ne_four_0
  · have hn_eq : n = 6 := by omega
    subst hn_eq
    exact a_ne_four_6
  · have hn_eq : n = 12 := by omega
    subst hn_eq
    exact a_ne_four_12
  · have hn_eq : n = 18 := by omega
    subst hn_eq
    exact a_ne_four_18
  · have hn_eq : n = 24 := by omega
    subst hn_eq
    exact a_ne_four_24
  · have hn_eq : n = 30 := by omega
    subst hn_eq
    exact a_ne_four_30
  · have hn_eq : n = 36 := by omega
    subst hn_eq
    exact a_ne_four_36
  · have hn_eq : n = 42 := by omega
    subst hn_eq
    exact a_ne_four_42
  · have hn_eq : n = 48 := by omega
    subst hn_eq
    exact a_ne_four_48
  · have hn_eq : n = 54 := by omega
    subst hn_eq
    exact a_ne_four_54
  · have hn_eq : n = 60 := by omega
    subst hn_eq
    exact a_ne_four_60
  · have hn_eq : n = 66 := by omega
    subst hn_eq
    exact a_ne_four_66
  · have hn_eq : n = 72 := by omega
    subst hn_eq
    exact a_ne_four_72
  · have hn_eq : n = 78 := by omega
    subst hn_eq
    exact a_ne_four_78
  · have hn_eq : n = 84 := by omega
    subst hn_eq
    exact a_ne_four_84
  · have hn_eq : n = 90 := by omega
    subst hn_eq
    exact a_ne_four_90
  · have hn_eq : n = 96 := by omega
    subst hn_eq
    exact a_ne_four_96
  · have hn_eq : n = 102 := by omega
    subst hn_eq
    exact a_ne_four_102
  · have hn_eq : n = 108 := by omega
    subst hn_eq
    exact a_ne_four_108
  · have hn_eq : n = 114 := by omega
    subst hn_eq
    exact a_ne_four_114
  · have hn_eq : n = 120 := by omega
    subst hn_eq
    exact a_ne_four_120
  · have hn_eq : n = 126 := by omega
    subst hn_eq
    exact a_ne_four_126
  · have hn_eq : n = 132 := by omega
    subst hn_eq
    exact a_ne_four_132
  · have hn_eq : n = 138 := by omega
    subst hn_eq
    exact a_ne_four_138
  · have hn_eq : n = 144 := by omega
    subst hn_eq
    exact a_ne_four_144
  · have hn_eq : n = 150 := by omega
    subst hn_eq
    exact a_ne_four_150
  · have hn_eq : n = 156 := by omega
    subst hn_eq
    exact a_ne_four_156
  · have hn_eq : n = 162 := by omega
    subst hn_eq
    exact a_ne_four_162
  · have hn_eq : n = 168 := by omega
    subst hn_eq
    exact a_ne_four_168
  · have hn_eq : n = 174 := by omega
    subst hn_eq
    exact a_ne_four_174
  · have hn_eq : n = 180 := by omega
    subst hn_eq
    exact a_ne_four_180
  · have hn_eq : n = 186 := by omega
    subst hn_eq
    exact a_ne_four_186
  · have hn_eq : n = 192 := by omega
    subst hn_eq
    exact a_ne_four_192
  · have hn_eq : n = 198 := by omega
    subst hn_eq
    exact a_ne_four_198
  · have hn_eq : n = 204 := by omega
    subst hn_eq
    exact a_ne_four_204
  · have hn_eq : n = 210 := by omega
    subst hn_eq
    exact a_ne_four_210
  · have hn_eq : n = 216 := by omega
    subst hn_eq
    exact a_ne_four_216
  · have hn_eq : n = 222 := by omega
    subst hn_eq
    exact a_ne_four_222
  · have hn_eq : n = 228 := by omega
    subst hn_eq
    exact a_ne_four_228
  · have hn_eq : n = 234 := by omega
    subst hn_eq
    exact a_ne_four_234
  · have hn_eq : n = 240 := by omega
    subst hn_eq
    exact a_ne_four_240
  · have hn_eq : n = 246 := by omega
    subst hn_eq
    exact a_ne_four_246

lemma oeis_275768_conjecture_0_proof : ¬ ∃ n : ℕ, _root_.a n = 4 := by
  intro ⟨n, hn⟩
  by_cases h_lt : n < 247
  · by_cases h_div : 6 ∣ n
    · exact a_ne_four_multiples n h_lt h_div hn
    · have : 6 ∣ n := divisible_by_six_of_a_eq_four hn
      exact h_div this
  · have h_ge : n ≥ 247 := by omega
    by_cases h_bound : n < 100000000
    · by_cases h_div : 6 ∣ n
      · have h_eq : _root_.a n = 6 := by
          unfold _root_.a
          rw [if_pos ⟨h_ge, h_div, h_bound⟩]
        omega
      · have : 6 ∣ n := divisible_by_six_of_a_eq_four hn
        exact h_div this
    · have h_eq : _root_.a n = 0 := by
        unfold _root_.a
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
      omega

end MySubmission

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 :=
  MySubmission.oeis_275768_conjecture_0_proof
