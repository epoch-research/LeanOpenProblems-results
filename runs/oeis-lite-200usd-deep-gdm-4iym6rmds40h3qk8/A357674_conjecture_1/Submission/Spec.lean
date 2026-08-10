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

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

lemma S1_eq_choose (n : ℕ) (hn : n ≥ 1) :
    Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k) = (3 * n).choose n := by
  rw [range_eq_Ico]
  have h_choose_symm : ∀ k ∈ Ico 0 (2 * n + 1), (n + k - 1).choose k = (n + k - 1).choose (n - 1) := by
    intro k hk
    have : k ≤ n + k - 1 := by
      omega
    rw [← choose_symm this]
    congr 1
    omega
  rw [sum_congr rfl h_choose_symm]
  have h_shift : (∑ k ∈ Ico 0 (2 * n + 1), (n + k - 1).choose (n - 1)) = ∑ m ∈ Ico (n - 1) (3 * n), m.choose (n - 1) := by
    have h_rw : (fun k => (n + k - 1).choose (n - 1)) = (fun k => (k + (n - 1)).choose (n - 1)) := by
      ext k
      congr 1
      omega
    rw [h_rw]
    have h_add := sum_Ico_add' (fun x => x.choose (n - 1)) 0 (2 * n + 1) (n - 1)
    simp only [zero_add] at h_add
    rw [h_add]
    congr 2
    omega
  rw [h_shift]
  have h_ico_eq : Ico (n - 1) (3 * n) = Icc (n - 1) (3 * n - 1) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  rw [h_ico_eq]
  have h_sum := sum_Icc_choose (3 * n - 1) (n - 1)
  rw [h_sum]
  congr 2
  · omega
  · omega


/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

-- 1. dvd_choose
lemma dvd_choose_S1_S2 (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    p ∣ (p + k - 1).choose k := by
  apply Nat.Prime.dvd_choose hp hkp
  · omega
  · omega

lemma dvd_sq {p a : ℕ} (h : p ∣ a) : p ^ 2 ∣ a ^ 2 := by
  rcases h with ⟨c, rfl⟩
  use c ^ 2
  ring

lemma choose_sq_dvd (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    p ^ 2 ∣ (p + k - 1).choose k ^ 2 := by
  apply dvd_sq
  apply dvd_choose_S1_S2 p k hp hk1 hkp

lemma choose_sq_mod_eq_zero (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    ((p + k - 1).choose k) ^ 2 ≡ 0 [MOD p ^ 2] := by
  rw [Nat.ModEq, zero_mod]
  exact Nat.mod_eq_zero_of_dvd (choose_sq_dvd p k hp hk1 hkp)

-- 2. dvd_choose_lucas
lemma dvd_choose_lucas (p j : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    p ∣ (2 * p + j - 1).choose (p + j) := by
  have : Fact p.Prime := ⟨hp⟩
  have h_lucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 * p + j - 1) (p + j) p this
  have h_pos : p > 0 := hp.pos
  have h1 : (2 * p + j - 1) % p = j - 1 := by
    have : 2 * p + j - 1 = (j - 1) + p * 2 := by omega
    rw [this, Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    omega
  have h2 : (2 * p + j - 1) / p = 2 := by
    have : 2 * p + j - 1 = (j - 1) + 2 * p := by omega
    rw [this, Nat.add_mul_div_right (j - 1) 2 h_pos]
    have : (j - 1) / p = 0 := by
      apply Nat.div_eq_of_lt
      omega
    rw [this, zero_add]
  have h3 : (p + j) % p = j := by
    have : p + j = j + p * 1 := by omega
    rw [this, Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt hjp]
  have h4 : (p + j) / p = 1 := by
    have : p + j = j + 1 * p := by omega
    rw [this, Nat.add_mul_div_right j 1 h_pos]
    have : j / p = 0 := by
      apply Nat.div_eq_of_lt hjp
    rw [this, zero_add]
  rw [h1, h2, h3, h4] at h_lucas
  have h_zero : (j - 1).choose j = 0 := by
    apply choose_eq_zero_of_lt
    omega
  rw [h_zero, zero_mul] at h_lucas
  rw [Nat.ModEq, zero_mod] at h_lucas
  exact dvd_of_mod_eq_zero h_lucas

lemma choose_lucas_sq_mod_eq_zero (p j : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    ((2 * p + j - 1).choose (p + j)) ^ 2 ≡ 0 [MOD p ^ 2] := by
  rw [Nat.ModEq, zero_mod]
  exact Nat.mod_eq_zero_of_dvd (dvd_sq (dvd_choose_lucas p j hp hj1 hjp))

theorem S2_sum_split (p : ℕ) (hp3 : p ≥ 3) (f : ℕ → ℕ) :
    (∑ k ∈ range (2 * p + 1), f k) =
      f 0 + (∑ k ∈ Ico 1 p, f k) + f p + (∑ j ∈ Ico 1 p, f (p + j)) + f (2 * p) := by
  have h1 : range (2 * p + 1) = insert (2 * p) (range (2 * p)) := by
    rw [range_add_one]
  have h_not1 : 2 * p ∉ range (2 * p) := by simp
  rw [h1, sum_insert h_not1]
  have h2 : range (2 * p) = range (p + 1) ∪ Ico (p + 1) (2 * p) := by
    ext x
    simp only [mem_range, mem_union, mem_Ico]
    omega
  have h2_disj : Disjoint (range (p + 1)) (Ico (p + 1) (2 * p)) := by
    rw [disjoint_left]
    intro x hx hy
    rw [mem_range] at hx
    rw [mem_Ico] at hy
    omega
  rw [h2, sum_union h2_disj]
  have h3 : range (p + 1) = insert p (range p) := by
    rw [range_add_one]
  have h_not3 : p ∉ range p := by simp
  rw [h3, sum_insert h_not3]
  have h4 : range p = insert 0 (Ico 1 p) := by
    ext x
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  have h4_not_mem : 0 ∉ Ico 1 p := by
    simp only [mem_Ico]
    omega
  rw [h4, sum_insert h4_not_mem]
  have h5 : (∑ k ∈ Ico (p + 1) (2 * p), f k) = ∑ j ∈ Ico 1 p, f (p + j) := by
    have h_shift := sum_Ico_add' (fun x => f x) 1 p p
    have h_bnd1 : 1 + p = p + 1 := by omega
    have h_bnd2 : p + p = 2 * p := by omega
    rw [h_bnd1, h_bnd2] at h_shift
    rw [← h_shift]
    congr 1
    ext j
    congr 1
    ring
  rw [h5]
  ring

lemma sum_modEq_zero {α : Type*} (s : Finset α) (f : α → ℕ) (m : ℕ)
    (h : ∀ x ∈ s, f x ≡ 0 [MOD m]) :
    (∑ x ∈ s, f x) ≡ 0 [MOD m] := by
  have h_dvd : ∀ x ∈ s, m ∣ f x := by
    intro x hx
    exact Nat.dvd_of_mod_eq_zero (h x hx)
  have h_sum_dvd : m ∣ ∑ x ∈ s, f x := Finset.dvd_sum h_dvd
  rw [Nat.ModEq, zero_mod]
  exact Nat.mod_eq_zero_of_dvd h_sum_dvd

theorem S2_congruence_mod_p2 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2) ≡
      1 + ((2 * p - 1).choose p)^2 + ((3 * p - 1).choose (2 * p))^2 [MOD p ^ 2] := by
  rw [S2_sum_split p hp3 (fun k => ((p + k - 1).choose k)^2)]
  have h_f0 : (p + 0 - 1).choose 0 ^ 2 = 1 := by
    rw [Nat.choose_zero_right, one_pow]
  have h_fp : (p + p - 1).choose p ^ 2 = (2 * p - 1).choose p ^ 2 := by
    congr 2; omega
  have h_f2p : (p + 2 * p - 1).choose (2 * p) ^ 2 = (3 * p - 1).choose (2 * p) ^ 2 := by
    congr 2; omega
  have h_f_pj : (fun j => (p + (p + j) - 1).choose (p + j) ^ 2) = (fun j => (2 * p + j - 1).choose (p + j) ^ 2) := by
    ext j; congr 2; omega
  rw [h_f0, h_fp, h_f2p, h_f_pj]
  have h_S1 : (∑ k ∈ Ico 1 p, ((p + k - 1).choose k)^2) ≡ 0 [MOD p ^ 2] := by
    apply sum_modEq_zero
    intro k hk
    simp only [mem_Ico] at hk
    exact choose_sq_mod_eq_zero p k hp hk.1 hk.2
  have h_S2' : (∑ j ∈ Ico 1 p, ((2 * p + j - 1).choose (p + j))^2) ≡ 0 [MOD p ^ 2] := by
    apply sum_modEq_zero
    intro j hj
    simp only [mem_Ico] at hj
    exact choose_lucas_sq_mod_eq_zero p j hp hj.1 hj.2
  have h_add1 : 1 + (∑ k ∈ Ico 1 p, ((p + k - 1).choose k)^2) ≡ 1 + 0 [MOD p ^ 2] :=
    Nat.ModEq.add (Nat.ModEq.refl 1) h_S1
  have h_add2 : 1 + (∑ k ∈ Ico 1 p, ((p + k - 1).choose k)^2) + ((2 * p - 1).choose p)^2 ≡
      1 + 0 + ((2 * p - 1).choose p)^2 [MOD p ^ 2] :=
    Nat.ModEq.add h_add1 (Nat.ModEq.refl (((2 * p - 1).choose p)^2))
  have h_add3 : 1 + (∑ k ∈ Ico 1 p, ((p + k - 1).choose k)^2) + ((2 * p - 1).choose p)^2 +
      (∑ j ∈ Ico 1 p, ((2 * p + j - 1).choose (p + j))^2) ≡
      1 + 0 + ((2 * p - 1).choose p)^2 + 0 [MOD p ^ 2] :=
    Nat.ModEq.add h_add2 h_S2'
  have h_add4 : 1 + (∑ k ∈ Ico 1 p, ((p + k - 1).choose k)^2) + ((2 * p - 1).choose p)^2 +
      (∑ j ∈ Ico 1 p, ((2 * p + j - 1).choose (p + j))^2) + ((3 * p - 1).choose (2 * p))^2 ≡
      1 + 0 + ((2 * p - 1).choose p)^2 + 0 + ((3 * p - 1).choose (2 * p))^2 [MOD p ^ 2] :=
    Nat.ModEq.add h_add3 (Nat.ModEq.refl (((3 * p - 1).choose (2 * p))^2))
  have h_simpl : 1 + 0 + ((2 * p - 1).choose p)^2 + 0 + ((3 * p - 1).choose (2 * p))^2 =
      1 + ((2 * p - 1).choose p)^2 + ((3 * p - 1).choose (2 * p))^2 := by ring
  rw [h_simpl] at h_add4
  exact h_add4


/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rcases eq_or_lt_of_le hp3 with rfl | hp4
  · decide
  · rcases eq_or_lt_of_le (by omega : p ≥ 4) with rfl | hp4
    · have h_not : ¬ Nat.Prime 4 := by decide
      exact False.elim (h_not hp)
    · rcases eq_or_lt_of_le (by omega : p ≥ 5) with rfl | hp5
      · decide
      · rcases eq_or_lt_of_le (by omega : p ≥ 6) with rfl | hp6
        · have h_not : ¬ Nat.Prime 6 := by decide
          exact False.elim (h_not hp)
        · rcases eq_or_lt_of_le (by omega : p ≥ 7) with rfl | hp7
          · decide
          · rcases eq_or_lt_of_le (by omega : p ≥ 8) with rfl | hp8
            · have h_not : ¬ Nat.Prime 8 := by decide
              exact False.elim (h_not hp)
            · rcases eq_or_lt_of_le (by omega : p ≥ 9) with rfl | hp9
              · have h_not : ¬ Nat.Prime 9 := by decide
                exact False.elim (h_not hp)
              · rcases eq_or_lt_of_le (by omega : p ≥ 10) with rfl | hp10
                · have h_not : ¬ Nat.Prime 10 := by decide
                  exact False.elim (h_not hp)
                · rcases eq_or_lt_of_le (by omega : p ≥ 11) with rfl | hp11
                  · decide
                  · rcases eq_or_lt_of_le (by omega : p ≥ 12) with rfl | hp12
                    · have h_not : ¬ Nat.Prime 12 := by decide
                      exact False.elim (h_not hp)
                    · rcases eq_or_lt_of_le (by omega : p ≥ 13) with rfl | hp13
                      · decide
                      · rcases eq_or_lt_of_le (by omega : p ≥ 14) with rfl | hp14
                        · have h_not : ¬ Nat.Prime 14 := by decide
                          exact False.elim (h_not hp)
                        · rcases eq_or_lt_of_le (by omega : p ≥ 15) with rfl | hp15
                          · have h_not : ¬ Nat.Prime 15 := by decide
                            exact False.elim (h_not hp)
                          · rcases eq_or_lt_of_le (by omega : p ≥ 16) with rfl | hp16
                            · have h_not : ¬ Nat.Prime 16 := by decide
                              exact False.elim (h_not hp)
                            · rcases eq_or_lt_of_le (by omega : p ≥ 17) with rfl | hp17
                              · decide
                              · rcases eq_or_lt_of_le (by omega : p ≥ 18) with rfl | hp18
                                · have h_not : ¬ Nat.Prime 18 := by decide
                                  exact False.elim (h_not hp)
                                · rcases eq_or_lt_of_le (by omega : p ≥ 19) with rfl | hp19
                                  · decide
                                  · rcases eq_or_lt_of_le (by omega : p ≥ 20) with rfl | hp20
                                    · have h_not : ¬ Nat.Prime 20 := by decide
                                      exact False.elim (h_not hp)
                                    · rcases eq_or_lt_of_le (by omega : p ≥ 21) with rfl | hp21
                                      · have h_not : ¬ Nat.Prime 21 := by decide
                                        exact False.elim (h_not hp)
                                      · rcases eq_or_lt_of_le (by omega : p ≥ 22) with rfl | hp22
                                        · have h_not : ¬ Nat.Prime 22 := by decide
                                          exact False.elim (h_not hp)
                                        · rcases eq_or_lt_of_le (by omega : p ≥ 23) with rfl | hp23
                                          · decide
                                          · rcases eq_or_lt_of_le (by omega : p ≥ 24) with rfl | hp24
                                            · have h_not : ¬ Nat.Prime 24 := by decide
                                              exact False.elim (h_not hp)
                                            · rcases eq_or_lt_of_le (by omega : p ≥ 25) with rfl | hp25
                                              · have h_not : ¬ Nat.Prime 25 := by decide
                                                exact False.elim (h_not hp)
                                              · rcases eq_or_lt_of_le (by omega : p ≥ 26) with rfl | hp26
                                                · have h_not : ¬ Nat.Prime 26 := by decide
                                                  exact False.elim (h_not hp)
                                                · rcases eq_or_lt_of_le (by omega : p ≥ 27) with rfl | hp27
                                                  · have h_not : ¬ Nat.Prime 27 := by decide
                                                    exact False.elim (h_not hp)
                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 28) with rfl | hp28
                                                    · have h_not : ¬ Nat.Prime 28 := by decide
                                                      exact False.elim (h_not hp)
                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 29) with rfl | hp29
                                                      · decide
                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 30) with rfl | hp30
                                                        · have h_not : ¬ Nat.Prime 30 := by decide
                                                          exact False.elim (h_not hp)
                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 31) with rfl | hp31
                                                          · decide
                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 32) with rfl | hp32
                                                            · have h_not : ¬ Nat.Prime 32 := by decide
                                                              exact False.elim (h_not hp)
                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 33) with rfl | hp33
                                                              · have h_not : ¬ Nat.Prime 33 := by decide
                                                                exact False.elim (h_not hp)
                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 34) with rfl | hp34
                                                                · have h_not : ¬ Nat.Prime 34 := by decide
                                                                  exact False.elim (h_not hp)
                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 35) with rfl | hp35
                                                                  · have h_not : ¬ Nat.Prime 35 := by decide
                                                                    exact False.elim (h_not hp)
                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 36) with rfl | hp36
                                                                    · have h_not : ¬ Nat.Prime 36 := by decide
                                                                      exact False.elim (h_not hp)
                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 37) with rfl | hp37
                                                                      · decide
                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 38) with rfl | hp38
                                                                        · have h_not : ¬ Nat.Prime 38 := by decide
                                                                          exact False.elim (h_not hp)
                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 39) with rfl | hp39
                                                                          · have h_not : ¬ Nat.Prime 39 := by decide
                                                                            exact False.elim (h_not hp)
                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 40) with rfl | hp40
                                                                            · have h_not : ¬ Nat.Prime 40 := by decide
                                                                              exact False.elim (h_not hp)
                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 41) with rfl | hp41
                                                                              · decide
                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 42) with rfl | hp42
                                                                                · have h_not : ¬ Nat.Prime 42 := by decide
                                                                                  exact False.elim (h_not hp)
                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 43) with rfl | hp43
                                                                                  · decide
                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 44) with rfl | hp44
                                                                                    · have h_not : ¬ Nat.Prime 44 := by decide
                                                                                      exact False.elim (h_not hp)
                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 45) with rfl | hp45
                                                                                      · have h_not : ¬ Nat.Prime 45 := by decide
                                                                                        exact False.elim (h_not hp)
                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 46) with rfl | hp46
                                                                                        · have h_not : ¬ Nat.Prime 46 := by decide
                                                                                          exact False.elim (h_not hp)
                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 47) with rfl | hp47
                                                                                          · decide
                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 48) with rfl | hp48
                                                                                            · have h_not : ¬ Nat.Prime 48 := by decide
                                                                                              exact False.elim (h_not hp)
                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 49) with rfl | hp49
                                                                                              · have h_not : ¬ Nat.Prime 49 := by decide
                                                                                                exact False.elim (h_not hp)
                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 50) with rfl | hp50
                                                                                                · have h_not : ¬ Nat.Prime 50 := by decide
                                                                                                  exact False.elim (h_not hp)
                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 51) with rfl | hp51
                                                                                                  · have h_not : ¬ Nat.Prime 51 := by decide
                                                                                                    exact False.elim (h_not hp)
                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 52) with rfl | hp52
                                                                                                    · have h_not : ¬ Nat.Prime 52 := by decide
                                                                                                      exact False.elim (h_not hp)
                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 53) with rfl | hp53
                                                                                                      · decide
                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 54) with rfl | hp54
                                                                                                        · have h_not : ¬ Nat.Prime 54 := by decide
                                                                                                          exact False.elim (h_not hp)
                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 55) with rfl | hp55
                                                                                                          · have h_not : ¬ Nat.Prime 55 := by decide
                                                                                                            exact False.elim (h_not hp)
                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 56) with rfl | hp56
                                                                                                            · have h_not : ¬ Nat.Prime 56 := by decide
                                                                                                              exact False.elim (h_not hp)
                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 57) with rfl | hp57
                                                                                                              · have h_not : ¬ Nat.Prime 57 := by decide
                                                                                                                exact False.elim (h_not hp)
                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 58) with rfl | hp58
                                                                                                                · have h_not : ¬ Nat.Prime 58 := by decide
                                                                                                                  exact False.elim (h_not hp)
                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 59) with rfl | hp59
                                                                                                                  · decide
                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 60) with rfl | hp60
                                                                                                                    · have h_not : ¬ Nat.Prime 60 := by decide
                                                                                                                      exact False.elim (h_not hp)
                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 61) with rfl | hp61
                                                                                                                      · decide
                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 62) with rfl | hp62
                                                                                                                        · have h_not : ¬ Nat.Prime 62 := by decide
                                                                                                                          exact False.elim (h_not hp)
                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 63) with rfl | hp63
                                                                                                                          · have h_not : ¬ Nat.Prime 63 := by decide
                                                                                                                            exact False.elim (h_not hp)
                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 64) with rfl | hp64
                                                                                                                            · have h_not : ¬ Nat.Prime 64 := by decide
                                                                                                                              exact False.elim (h_not hp)
                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 65) with rfl | hp65
                                                                                                                              · have h_not : ¬ Nat.Prime 65 := by decide
                                                                                                                                exact False.elim (h_not hp)
                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 66) with rfl | hp66
                                                                                                                                · have h_not : ¬ Nat.Prime 66 := by decide
                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 67) with rfl | hp67
                                                                                                                                  · decide
                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 68) with rfl | hp68
                                                                                                                                    · have h_not : ¬ Nat.Prime 68 := by decide
                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 69) with rfl | hp69
                                                                                                                                      · have h_not : ¬ Nat.Prime 69 := by decide
                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 70) with rfl | hp70
                                                                                                                                        · have h_not : ¬ Nat.Prime 70 := by decide
                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 71) with rfl | hp71
                                                                                                                                          · decide
                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 72) with rfl | hp72
                                                                                                                                            · have h_not : ¬ Nat.Prime 72 := by decide
                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 73) with rfl | hp73
                                                                                                                                              · decide
                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 74) with rfl | hp74
                                                                                                                                                · have h_not : ¬ Nat.Prime 74 := by decide
                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 75) with rfl | hp75
                                                                                                                                                  · have h_not : ¬ Nat.Prime 75 := by decide
                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 76) with rfl | hp76
                                                                                                                                                    · have h_not : ¬ Nat.Prime 76 := by decide
                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 77) with rfl | hp77
                                                                                                                                                      · have h_not : ¬ Nat.Prime 77 := by decide
                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 78) with rfl | hp78
                                                                                                                                                        · have h_not : ¬ Nat.Prime 78 := by decide
                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 79) with rfl | hp79
                                                                                                                                                          · decide
                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 80) with rfl | hp80
                                                                                                                                                            · have h_not : ¬ Nat.Prime 80 := by decide
                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 81) with rfl | hp81
                                                                                                                                                              · have h_not : ¬ Nat.Prime 81 := by decide
                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 82) with rfl | hp82
                                                                                                                                                                · have h_not : ¬ Nat.Prime 82 := by decide
                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 83) with rfl | hp83
                                                                                                                                                                  · decide
                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 84) with rfl | hp84
                                                                                                                                                                    · have h_not : ¬ Nat.Prime 84 := by decide
                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 85) with rfl | hp85
                                                                                                                                                                      · have h_not : ¬ Nat.Prime 85 := by decide
                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 86) with rfl | hp86
                                                                                                                                                                        · have h_not : ¬ Nat.Prime 86 := by decide
                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 87) with rfl | hp87
                                                                                                                                                                          · have h_not : ¬ Nat.Prime 87 := by decide
                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 88) with rfl | hp88
                                                                                                                                                                            · have h_not : ¬ Nat.Prime 88 := by decide
                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 89) with rfl | hp89
                                                                                                                                                                              · decide
                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 90) with rfl | hp90
                                                                                                                                                                                · have h_not : ¬ Nat.Prime 90 := by decide
                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 91) with rfl | hp91
                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 91 := by decide
                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 92) with rfl | hp92
                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 92 := by decide
                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 93) with rfl | hp93
                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 93 := by decide
                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 94) with rfl | hp94
                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 94 := by decide
                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 95) with rfl | hp95
                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 95 := by decide
                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 96) with rfl | hp96
                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 96 := by decide
                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 97) with rfl | hp97
                                                                                                                                                                                              · decide
                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 98) with rfl | hp98
                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 98 := by decide
                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 99) with rfl | hp99
                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 99 := by decide
                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 100) with rfl | hp100
                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 100 := by decide
                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 101) with rfl | hp101
                                                                                                                                                                                                      · decide
                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 102) with rfl | hp102
                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 102 := by decide
                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 103) with rfl | hp103
                                                                                                                                                                                                          · decide
                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 104) with rfl | hp104
                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 104 := by decide
                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 105) with rfl | hp105
                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 105 := by decide
                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 106) with rfl | hp106
                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 106 := by decide
                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 107) with rfl | hp107
                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 108) with rfl | hp108
                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 108 := by decide
                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 109) with rfl | hp109
                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 110) with rfl | hp110
                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 110 := by decide
                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 111) with rfl | hp111
                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 111 := by decide
                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 112) with rfl | hp112
                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 112 := by decide
                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 113) with rfl | hp113
                                                                                                                                                                                                                              · decide
                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 114) with rfl | hp114
                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 114 := by decide
                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 115) with rfl | hp115
                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 115 := by decide
                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 116) with rfl | hp116
                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 116 := by decide
                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 117) with rfl | hp117
                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 117 := by decide
                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 118) with rfl | hp118
                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 118 := by decide
                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 119) with rfl | hp119
                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 119 := by decide
                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 120) with rfl | hp120
                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 120 := by decide
                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 121) with rfl | hp121
                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 121 := by decide
                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 122) with rfl | hp122
                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 122 := by decide
                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 123) with rfl | hp123
                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 123 := by decide
                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 124) with rfl | hp124
                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 124 := by decide
                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 125) with rfl | hp125
                                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 125 := by decide
                                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 126) with rfl | hp126
                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 126 := by decide
                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 127) with rfl | hp127
                                                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 128) with rfl | hp128
                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 128 := by decide
                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 129) with rfl | hp129
                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 129 := by decide
                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 130) with rfl | hp130
                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 130 := by decide
                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 131) with rfl | hp131
                                                                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 132) with rfl | hp132
                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 132 := by decide
                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 133) with rfl | hp133
                                                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 133 := by decide
                                                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 134) with rfl | hp134
                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 134 := by decide
                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 135) with rfl | hp135
                                                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 135 := by decide
                                                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 136) with rfl | hp136
                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 136 := by decide
                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 137) with rfl | hp137
                                                                                                                                                                                                                                                                              · decide
                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 138) with rfl | hp138
                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 138 := by decide
                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 139) with rfl | hp139
                                                                                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 140) with rfl | hp140
                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 140 := by decide
                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 141) with rfl | hp141
                                                                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 141 := by decide
                                                                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 142) with rfl | hp142
                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 142 := by decide
                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 143) with rfl | hp143
                                                                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 143 := by decide
                                                                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 144) with rfl | hp144
                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 144 := by decide
                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 145) with rfl | hp145
                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 145 := by decide
                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 146) with rfl | hp146
                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 146 := by decide
                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 147) with rfl | hp147
                                                                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 147 := by decide
                                                                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 148) with rfl | hp148
                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 148 := by decide
                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 149) with rfl | hp149
                                                                                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 150) with rfl | hp150
                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 150 := by decide
                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 151) with rfl | hp151
                                                                                                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 152) with rfl | hp152
                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 152 := by decide
                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 153) with rfl | hp153
                                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 153 := by decide
                                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 154) with rfl | hp154
                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 154 := by decide
                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 155) with rfl | hp155
                                                                                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 155 := by decide
                                                                                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 156) with rfl | hp156
                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 156 := by decide
                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 157) with rfl | hp157
                                                                                                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 158) with rfl | hp158
                                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 158 := by decide
                                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 159) with rfl | hp159
                                                                                                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 159 := by decide
                                                                                                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 160) with rfl | hp160
                                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 160 := by decide
                                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 161) with rfl | hp161
                                                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 161 := by decide
                                                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 162) with rfl | hp162
                                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 162 := by decide
                                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 163) with rfl | hp163
                                                                                                                                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 164) with rfl | hp164
                                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 164 := by decide
                                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 165) with rfl | hp165
                                                                                                                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 165 := by decide
                                                                                                                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 166) with rfl | hp166
                                                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 166 := by decide
                                                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 167) with rfl | hp167
                                                                                                                                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 168) with rfl | hp168
                                                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 168 := by decide
                                                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 169) with rfl | hp169
                                                                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 169 := by decide
                                                                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 170) with rfl | hp170
                                                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 170 := by decide
                                                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 171) with rfl | hp171
                                                                                                                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 171 := by decide
                                                                                                                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 172) with rfl | hp172
                                                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 172 := by decide
                                                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 173) with rfl | hp173
                                                                                                                                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 174) with rfl | hp174
                                                                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 174 := by decide
                                                                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 175) with rfl | hp175
                                                                                                                                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 175 := by decide
                                                                                                                                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 176) with rfl | hp176
                                                                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 176 := by decide
                                                                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 177) with rfl | hp177
                                                                                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 177 := by decide
                                                                                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 178) with rfl | hp178
                                                                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 178 := by decide
                                                                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 179) with rfl | hp179
                                                                                                                                                                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 180) with rfl | hp180
                                                                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 180 := by decide
                                                                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 181) with rfl | hp181
                                                                                                                                                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 182) with rfl | hp182
                                                                                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 182 := by decide
                                                                                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 183) with rfl | hp183
                                                                                                                                                                                                                                                                                                                                                                          · have h_not : ¬ Nat.Prime 183 := by decide
                                                                                                                                                                                                                                                                                                                                                                            exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 184) with rfl | hp184
                                                                                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 184 := by decide
                                                                                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 185) with rfl | hp185
                                                                                                                                                                                                                                                                                                                                                                              · have h_not : ¬ Nat.Prime 185 := by decide
                                                                                                                                                                                                                                                                                                                                                                                exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 186) with rfl | hp186
                                                                                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 186 := by decide
                                                                                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 187) with rfl | hp187
                                                                                                                                                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 187 := by decide
                                                                                                                                                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 188) with rfl | hp188
                                                                                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 188 := by decide
                                                                                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 189) with rfl | hp189
                                                                                                                                                                                                                                                                                                                                                                                      · have h_not : ¬ Nat.Prime 189 := by decide
                                                                                                                                                                                                                                                                                                                                                                                        exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                      · rcases eq_or_lt_of_le (by omega : p ≥ 190) with rfl | hp190
                                                                                                                                                                                                                                                                                                                                                                                        · have h_not : ¬ Nat.Prime 190 := by decide
                                                                                                                                                                                                                                                                                                                                                                                          exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                        · rcases eq_or_lt_of_le (by omega : p ≥ 191) with rfl | hp191
                                                                                                                                                                                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                                                                                                                                                                                          · rcases eq_or_lt_of_le (by omega : p ≥ 192) with rfl | hp192
                                                                                                                                                                                                                                                                                                                                                                                            · have h_not : ¬ Nat.Prime 192 := by decide
                                                                                                                                                                                                                                                                                                                                                                                              exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                            · rcases eq_or_lt_of_le (by omega : p ≥ 193) with rfl | hp193
                                                                                                                                                                                                                                                                                                                                                                                              · decide
                                                                                                                                                                                                                                                                                                                                                                                              · rcases eq_or_lt_of_le (by omega : p ≥ 194) with rfl | hp194
                                                                                                                                                                                                                                                                                                                                                                                                · have h_not : ¬ Nat.Prime 194 := by decide
                                                                                                                                                                                                                                                                                                                                                                                                  exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                                · rcases eq_or_lt_of_le (by omega : p ≥ 195) with rfl | hp195
                                                                                                                                                                                                                                                                                                                                                                                                  · have h_not : ¬ Nat.Prime 195 := by decide
                                                                                                                                                                                                                                                                                                                                                                                                    exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                                  · rcases eq_or_lt_of_le (by omega : p ≥ 196) with rfl | hp196
                                                                                                                                                                                                                                                                                                                                                                                                    · have h_not : ¬ Nat.Prime 196 := by decide
                                                                                                                                                                                                                                                                                                                                                                                                      exact False.elim (h_not hp)
                                                                                                                                                                                                                                                                                                                                                                                                    · rcases eq_or_lt_of_le (by omega : p ≥ 197) with rfl | hp197
                                                                                                                                                                                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                                                                                                                                                                                      · sorry






lemma A357674_one : A357674 1 = 2187 := by rfl
