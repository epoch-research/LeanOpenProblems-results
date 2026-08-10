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

namespace OEIS272479

open Nat
open Classical

private theorem digits_ten_mul (n : ℕ) (hn : 0 < n) : digits 10 (10 * n) = 0 :: digits 10 n := by
  have h_append := digits_append_zeroes_append_digits (b := 10) (k := 1) (m := n) (n := 0) (by omega) hn
  simp only [digits_zero, List.nil_append, List.replicate, List.length_nil, zero_add, pow_one, zero_add] at h_append
  exact h_append.symm

private theorem dsum_ten_mul (n : ℕ) (hn : 0 < n) : (digits 10 (10 * n)).sum = (digits 10 n).sum := by
  rw [digits_ten_mul n hn]
  simp

private theorem partners_nonempty_of_harshad (n : ℕ) (hn : n > 0) (hdvd : (digits 10 n).sum ∣ n) :
    ( {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ ).Nonempty := by
  use 10 * n
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have h1 : (digits 10 n).sum ∣ n := hdvd
    have h2 : n ∣ 10 * n := dvd_mul_left n 10
    exact dvd_trans h1 h2
  · rw [dsum_ten_mul n hn]
    exact hdvd


private theorem modeq_9_sub_eq_mul (x y : ℕ) (h_eq : x % 9 = y % 9) (h_le : y ≤ x) : ∃ w, x = y + 9 * w := by
  use (x - y) / 9
  omega

private theorem dsum_le (n : ℕ) : (digits 10 n).sum ≤ n := by
  have h_le := Nat.sum_le_ofDigits (p := 10) (digits 10 n) (by decide)
  rw [Nat.ofDigits_digits] at h_le
  exact h_le

private theorem dsum_add_nine_le_self (n : ℕ) (hn : 10 ≤ n) : (digits 10 n).sum + 9 ≤ n := by
  have h_pos : n ≠ 0 := by omega
  have h_digits : digits 10 n = n % 10 :: digits 10 (n / 10) := Nat.digits_eq_cons_digits_div (by decide) h_pos
  have h_sum : (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum := by
    rw [h_digits]
    simp
  have h_le := dsum_le (n / 10)
  have h_a_ge : n / 10 ≥ 1 := by omega
  rw [h_sum]
  omega


private theorem two_dsum_le_self_add_nine (n : ℕ) (hn : 10 ≤ n) : 2 * (digits 10 n).sum ≤ n + 9 := by
  have h_pos : n ≠ 0 := by omega
  have h_digits : digits 10 n = n % 10 :: digits 10 (n / 10) := Nat.digits_eq_cons_digits_div (by decide) h_pos
  have h_sum : (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum := by
    rw [h_digits]
    simp
  have h_le := dsum_le (n / 10)
  have h_mod_lt : n % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [h_sum]
  omega

private theorem nine_mul_lt_ten_pow (w : ℕ) (hw : w ≥ 1) : 9 * w < 10^w := by
  induction w with
  | zero => omega
  | succ w ih =>
    by_cases hw0 : w = 0
    · subst hw0; simp
    · have hw_ge1 : w ≥ 1 := by omega
      have ih' := ih hw_ge1
      have h_pow : 10^(w+1) = 10^w * 10 := rfl
      generalize hW : 10^w = W at ih' h_pow ⊢
      have hW_ge : W ≥ 10 := by
        rw [← hW]
        have : 10^1 ≤ 10^w := Nat.pow_le_pow_right (by decide) hw_ge1
        exact this
      rw [h_pow]
      have h_mul : 9 * (w + 1) = 9 * w + 9 := by omega
      rw [h_mul]
      omega

private theorem M_lt_pow (M w : ℕ) (hw : w ≥ 1) (h_le : M ≤ 9 * w) : M < 10^w := by
  have := nine_mul_lt_ten_pow w hw
  omega

private theorem non_harshad_ge_ten (n : ℕ) (hn : n > 0) (h_nh : ¬ (digits 10 n).sum ∣ n) : n ≥ 10 := by
  by_contra h_lt
  have h_lt : n < 10 := by omega
  have h_eq : digits 10 n = [n] := by
    exact digits_of_lt 10 n (by omega) h_lt
  have h_sum : (digits 10 n).sum = n := by
    rw [h_eq]
    simp
  apply h_nh
  rw [h_sum]

private theorem exists_w_of_non_harshad (n : ℕ) (hn : n > 0) (h_nh : ¬ (digits 10 n).sum ∣ n) :
    ∃ w ≥ 1, 10^w > (digits 10 n).sum ∧ (digits 10 (digits 10 n).sum).sum + 9 * w = n := by
  have h_ge10 := non_harshad_ge_ten n hn h_nh
  set M := (digits 10 n).sum
  set DM := (digits 10 M).sum
  have h_leM : DM ≤ M := dsum_le M
  have h_leN : M + 9 ≤ n := dsum_add_nine_le_self n h_ge10
  have h_le : DM + 9 ≤ n := by omega
  have h_le_DM : DM ≤ n := by omega
  have h_mod1 : n ≡ M [MOD 9] := Nat.modEq_digits_sum 9 10 (by rfl) n
  have h_mod2 : M ≡ DM [MOD 9] := Nat.modEq_digits_sum 9 10 (by rfl) M
  have h_mod : n ≡ DM [MOD 9] := Nat.ModEq.trans h_mod1 h_mod2
  have h_ex := modeq_9_sub_eq_mul n DM h_mod h_le_DM
  rcases h_ex with ⟨w, hw_eq⟩
  have hw_ge1 : w ≥ 1 := by
    by_contra h_lt
    have : w = 0 := by omega
    subst this
    omega
  use w
  refine ⟨hw_ge1, ?_, ?_⟩
  · have h_le_w : M ≤ 9 * w := by
      by_cases h_M_lt : M < 10
      · have : M ≤ 9 := by omega
        omega
      · have h_M_ge : 10 ≤ M := by omega
        have h_DM_le := dsum_add_nine_le_self M h_M_ge
        have h_two_M := two_dsum_le_self_add_nine n h_ge10
        omega
    exact M_lt_pow M w hw_ge1 h_le_w
  · omega



private theorem dsum_append_zeroes_append_digits (b k m n : ℕ) (hb : 1 < b) (hm : 0 < m) :
    (digits b (n + b ^ ((digits b n).length + k) * m)).sum = (digits b n).sum + (digits b m).sum := by
  have h := digits_append_zeroes_append_digits hb hm (k := k) (n := n)
  rw [← h]
  simp

private theorem dsum_nine_complement (k : ℕ) : ∀ X, X < 10^k → (digits 10 (10^k - 1 - X)).sum + (digits 10 X).sum = 9 * k := by
  induction k with
  | zero =>
    intro X hX
    have : X = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro X hX
    have h_div_mod : X = X % 10^k + 10^k * (X / 10^k) := (Nat.mod_add_div X (10^k)).symm
    have h_d_lt_raw : X / 10^k < 10 := Nat.div_lt_of_lt_mul hX
    have h_R_lt_raw : X % 10^k < 10^k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    generalize hR : X % 10^k = R
    generalize hd : X / 10^k = d
    rw [hR] at h_R_lt_raw h_div_mod
    rw [hd] at h_d_lt_raw h_div_mod
    have h_pow : 10^(k+1) = 10^k * 10 := rfl
    have h_comp_lt : 10^k - 1 - R < 10^k := by
      clear hd hR h_div_mod h_pow h_d_lt_raw
      omega
    have h_len_comp : (digits 10 (10^k - 1 - R)).length ≤ k := by
      rw [digits_length_le_iff (by decide)]
      exact h_comp_lt
    have h_len_R : (digits 10 R).length ≤ k := by
      rw [digits_length_le_iff (by decide)]
      exact h_R_lt_raw
    have h_le : 10^k * d ≤ 10^k * 9 := Nat.mul_le_mul_left (10^k) (by omega)
    have h_eq_comp : 10^(k+1) - 1 - X = (10^k - 1 - R) + 10^k * (9 - d) := by
      rw [h_pow, h_div_mod, Nat.mul_sub_left_distrib]
      have hW_pos : 0 < 10^k := Nat.pow_pos (by decide)
      generalize hY : 10^k * d = Y at h_le ⊢
      generalize hW : 10^k = W at h_le h_R_lt_raw hW_pos ⊢
      clear ih h_len_comp hY hd hR h_div_mod hX h_pow h_len_R
      omega
    by_cases hd0 : d = 0
    · have h_eq : X = R := by
        rw [hd0] at h_div_mod
        simp at h_div_mod
        exact h_div_mod
      have h_comp_eq : 10^(k+1) - 1 - X = (10^k - 1 - R) + 10^k * 9 := by
        rw [h_pow, h_eq]
        generalize hW : 10^k = W at h_comp_lt h_len_comp h_R_lt_raw ⊢
        clear ih h_len_comp h_eq_comp h_len_R hd0 hd hR h_div_mod h_pow hX h_le h_comp_lt
        omega
      rw [h_comp_eq, h_eq]
      have h_pos : 0 < 9 := by decide
      have h_dsum := dsum_append_zeroes_append_digits 10 (k - (digits 10 (10^k - 1 - R)).length) 9 (10^k - 1 - R) (by decide) h_pos
      have h_add : (digits 10 (10^k - 1 - R)).length + (k - (digits 10 (10^k - 1 - R)).length) = k := add_tsub_cancel_of_le h_len_comp
      rw [h_add] at h_dsum
      rw [h_dsum]
      have h_nine : (digits 10 9).sum = 9 := by
        rw [digits_of_lt 10 9 (by decide) (by decide)]
        rfl
      rw [h_nine]
      have h_ih := ih R h_R_lt_raw
      omega
    · by_cases hd9 : d = 9
      · have h_eq_comp' : 10^(k+1) - 1 - X = 10^k - 1 - R := by
          rw [h_pow, h_div_mod, hd9]
          generalize hW : 10^k = W at h_R_lt_raw ⊢
          clear ih h_len_comp h_eq_comp h_len_R hd0 hd9 hd hR h_div_mod h_pow hX h_le
          omega
        rw [h_eq_comp', h_div_mod, hd9]
        have h_pos : 0 < 9 := by decide
        have h_dsum := dsum_append_zeroes_append_digits 10 (k - (digits 10 R).length) 9 R (by decide) h_pos
        have h_add : (digits 10 R).length + (k - (digits 10 R).length) = k := add_tsub_cancel_of_le h_len_R
        rw [h_add] at h_dsum
        rw [h_dsum]
        have h_nine : (digits 10 9).sum = 9 := by
          rw [digits_of_lt 10 9 (by decide) (by decide)]
          rfl
        rw [h_nine]
        have h_ih := ih R h_R_lt_raw
        omega
      · -- Case d ≠ 0 and d ≠ 9
        have hd_pos : 0 < d := by omega
        have hd9_pos : 0 < 9 - d := by omega
        rw [h_eq_comp, h_div_mod]
        have h_dsum1 := dsum_append_zeroes_append_digits 10 (k - (digits 10 (10^k - 1 - R)).length) (9 - d) (10^k - 1 - R) (by decide) hd9_pos
        have h_add1 : (digits 10 (10^k - 1 - R)).length + (k - (digits 10 (10^k - 1 - R)).length) = k := add_tsub_cancel_of_le h_len_comp
        rw [h_add1] at h_dsum1
        rw [h_dsum1]
        have h_dsum2 := dsum_append_zeroes_append_digits 10 (k - (digits 10 R).length) d R (by decide) hd_pos
        have h_add2 : (digits 10 R).length + (k - (digits 10 R).length) = k := add_tsub_cancel_of_le h_len_R
        rw [h_add2] at h_dsum2
        rw [h_dsum2]
        have h_sing1 : (digits 10 (9 - d)).sum = 9 - d := by
          have : 9 - d < 10 := by omega
          rw [digits_of_lt 10 (9 - d) (by omega) this]
          simp
        have h_sing2 : (digits 10 d).sum = d := by
          rw [digits_of_lt 10 d (by omega) h_d_lt_raw]
          simp
        rw [h_sing1, h_sing2]
        have h_ih := ih R h_R_lt_raw
        omega


private theorem dsum_mul_ten_pow_sub_one (w M : ℕ) (h_lt : M < 10^w) (hM_ge2 : 2 ≤ M) :
    (digits 10 (M * (10^w - 1))).sum = 9 * w := by
  have h_m_pos : 0 < M - 1 := by omega
  have h_le_comp : (digits 10 (10^w - 1 - (M - 1))).length ≤ w := by
    rw [digits_length_le_iff (by decide)]
    omega
  have h_dsum := dsum_append_zeroes_append_digits 10 (w - (digits 10 (10^w - 1 - (M - 1))).length) (M - 1) (10^w - 1 - (M - 1)) (by decide) h_m_pos
  have h_add : (digits 10 (10^w - 1 - (M - 1))).length + (w - (digits 10 (10^w - 1 - (M - 1))).length) = w := add_tsub_cancel_of_le h_le_comp
  rw [h_add] at h_dsum
  have h_eq : 10^w - 1 - (M - 1) + 10^w * (M - 1) = M * (10^w - 1) := by
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_comm M (10^w)]
    generalize hW : 10^w = W at h_lt h_le_comp h_dsum h_add ⊢
    generalize hWM : W * M = WM at h_lt h_le_comp h_dsum h_add ⊢
    have h_le_WM : W ≤ WM := by
      rw [← hWM]
      exact Nat.le_mul_of_pos_right W (by omega)
    omega
  rw [h_eq] at h_dsum
  rw [h_dsum]
  exact dsum_nine_complement w (M - 1) (by omega)


private theorem dsum_zero_iff (n : ℕ) : (digits 10 n).sum = 0 ↔ n = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    constructor
    · intro h_sum
      by_cases hn0 : n = 0
      · exact hn0
      · have h_pos : n ≠ 0 := hn0
        have h_digits : digits 10 n = n % 10 :: digits 10 (n / 10) := Nat.digits_eq_cons_digits_div (by decide) h_pos
        have h_sum2 : (digits 10 n).sum = n % 10 + (digits 10 (n / 10)).sum := by
          rw [h_digits]
          simp
        rw [h_sum2] at h_sum
        have h_mod : n % 10 = 0 := by omega
        have h_div_sum : (digits 10 (n / 10)).sum = 0 := by omega
        have h_div_lt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
        have ih' := (ih (n / 10) h_div_lt).mp h_div_sum
        omega
    · intro h
      subst h
      simp

private theorem partners_nonempty_of_non_harshad (n : ℕ) (hn : n > 0) (h_nh : ¬ (digits 10 n).sum ∣ n) :
    ( {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ ).Nonempty := by
  set M := (digits 10 n).sum
  have hM_pos : 0 < M := by
    by_contra h_zero
    have : (digits 10 n).sum = 0 := by omega
    have : n = 0 := (dsum_zero_iff n).mp this
    omega
  have hM_ge2 : 2 ≤ M := by
    by_contra h_lt
    have : M = 1 := by omega
    have h_dvd : M ∣ n := by rw [this]; exact Nat.one_dvd n
    contradiction
  have h_ex := exists_w_of_non_harshad n hn h_nh
  rcases h_ex with ⟨w, hw_ge1, hw_lt, hw_eq⟩
  set k := M * 10^(2 * w) + M * (10^w - 1)
  use k
  have hk_pos : 0 < k := by
    have : 0 < M * 10^(2 * w) := Nat.mul_pos hM_pos (Nat.pow_pos (by decide))
    omega
  have hk_comm : k = M * (10^(2 * w) + 10^w - 1) := by
    have h_assoc : 10^(2 * w) + 10^w - 1 = 10^(2 * w) + (10^w - 1) := by
      generalize hP : 10^(2 * w) = P
      generalize hQ : 10^w = Q
      have : Q ≥ 1 := by
        subst hQ
        exact Nat.one_le_pow w 10 (by decide)
      omega
    rw [h_assoc, Nat.mul_add]
  have hdvd1 : M ∣ k := by
    rw [hk_comm]
    exact dvd_mul_right M _
  have h_le_len : (digits 10 (M * (10^w - 1))).length ≤ 2 * w := by
    rw [digits_length_le_iff (by decide)]
    have h_mul_lt : M * (10^w - 1) < 10^w * 10^w := by
      have : 10^w - 1 < 10^w := by omega
      have : M * (10^w - 1) < M * 10^w := Nat.mul_lt_mul_of_pos_left this hM_pos
      have : M * 10^w < 10^w * 10^w := Nat.mul_lt_mul_of_pos_right hw_lt (Nat.pow_pos (by decide))
      omega
    have h_pow_add : 10^w * 10^w = 10^(2 * w) := by
      rw [← Nat.pow_add]
      have : w + w = 2 * w := by omega
      rw [this]
    omega
  have h_dsum := dsum_append_zeroes_append_digits 10 (2 * w - (digits 10 (M * (10^w - 1))).length) M (M * (10^w - 1)) (by decide) hM_pos
  have h_add : (digits 10 (M * (10^w - 1))).length + (2 * w - (digits 10 (M * (10^w - 1))).length) = 2 * w := add_tsub_cancel_of_le h_le_len
  rw [h_add] at h_dsum
  have hk_eq : k = M * (10^w - 1) + 10^(2 * w) * M := by
    rw [Nat.add_comm, Nat.mul_comm (10^(2 * w)) M]
  have hk_sum : (digits 10 k).sum = n := by
    rw [hk_eq]
    rw [h_dsum]
    have h_mul : (digits 10 (M * (10^w - 1))).sum = 9 * w := dsum_mul_ten_pow_sub_one w M hw_lt hM_ge2
    rw [h_mul]
    dsimp only [M] at *
    clear hk_pos hdvd1 hk_comm h_le_len h_add h_dsum hk_eq k
    omega
  have hdvd2 : (digits 10 k).sum ∣ n := by
    rw [hk_sum]
  have hk_ge : k ≥ 10^(2 * w) := by
    have : M * 10^(2 * w) ≥ 10^(2 * w) := Nat.le_mul_of_pos_left (10^(2 * w)) hM_pos
    omega
  have hn_lt : n < 10^(2 * w) := by
    have h_DM_le : (digits 10 M).sum ≤ M := dsum_le M
    dsimp only [M] at *
    have : n < 10^w + 9 * w := by omega
    have h_pow2 : 10^(2 * w) = 10^w * 10^w := by
      rw [← Nat.pow_add]
      have : w + w = 2 * w := by omega
      rw [this]
    have h_pow_ge : 10^w ≥ 10 := by
      have : 10^1 ≤ 10^w := Nat.pow_le_pow_right (by decide) hw_ge1
      exact this
    have : 9 * w < 10^w := nine_mul_lt_ten_pow w hw_ge1
    rw [h_pow2]
    clear hk_pos hdvd1 hk_comm h_le_len h_dsum hk_eq hk_sum hdvd2 hk_ge k
    generalize hW : 10^w = W at h_pow_ge this hw_lt h_DM_le ⊢
    have h_pow_le : 2 * W ≤ W * W := by
      have : 2 ≤ W := by omega
      exact Nat.mul_le_mul_right W this
    generalize hWW : W * W = WW at h_pow_le ⊢
    omega
  have h_neq : k ≠ n := by
    have : k > n := by omega
    omega
  refine ⟨hk_pos, h_neq, hdvd1, hdvd2⟩

end OEIS272479

open OEIS272479

open Nat
open Classical
open ProblemAttributes


/--
A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.
Let $D(n)$ be the sum of digits of $n$.
$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.
For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dsum (m : ℕ) : ℕ := (digits 10 m).sum

  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}

  -- The set of partners is bounded below by 1. If it is non-empty, `sInf`
  -- correctly returns the smallest element. If empty, we return 0 as per the OEIS comment.
  if partners.Nonempty then
    sInf partners
  else
    0

/-- A272479 Conjecture: the sequence contains no zeros. -/
@[category research solved, formal_proof using formal_conjectures at "Submission/Spec.lean", AMS 11]
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp only
  split_ifs with h
  · have h_mem := Nat.sInf_mem h
    rcases h_mem with ⟨h_pos, _, _, _⟩
    omega
  · exfalso
    apply h
    by_cases h_harshad : (digits 10 n).sum ∣ n
    · exact partners_nonempty_of_harshad n hn h_harshad
    · exact partners_nonempty_of_non_harshad n hn h_harshad
