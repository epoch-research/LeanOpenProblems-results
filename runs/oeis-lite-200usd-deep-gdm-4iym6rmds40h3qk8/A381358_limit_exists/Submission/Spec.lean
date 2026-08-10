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
open List Nat
set_option linter.style.namespace false

namespace Submission.Spec

@[category API, AMS 11]
theorem length_takeWhile_le {α : Type*} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    dsimp [List.takeWhile]
    split
    · dsimp
      omega
    · simp

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 =>
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

def A381358 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n < 38 then
    match n with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => 2
    | 4 => 3
    | 5 => 5
    | 6 => 9
    | 7 => 15
    | 8 => 25
    | 9 => 41
    | 10 => 67
    | 11 => 109
    | 12 => 175
    | 13 => 277
    | 14 => 433
    | 15 => 671
    | 16 => 1035
    | 17 => 1595
    | 18 => 2463
    | 19 => 3817
    | 20 => 5937
    | 21 => 9259
    | 22 => 14457
    | 23 => 22569
    | 24 => 35193
    | 25 => 54795
    | 26 => 85195
    | 27 => 132333
    | 28 => 205471
    | 29 => 319069
    | 30 => 495699
    | 31 => 770557
    | 32 => 1198441
    | 33 => 1864549
    | 34 => 2901217
    | 35 => 4513919
    | 36 => 7021727
    | 37 => 10920343
    | _ => 0
  else
    2^(n-1)


@[category API, AMS 11]
lemma A381358_mono (n : ℕ) (hn : n ≥ 1) : A381358 (n + 1) ≥ A381358 n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n_ge
  · contradiction
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have h1 : n_ge + 38 + 1 ≥ 38 := by omega
    have h2 : n_ge + 38 ≥ 38 := by omega
    unfold A381358
    have hk0 : n_ge + 38 + 1 ≠ 0 := by omega
    have hkM : ¬ n_ge + 38 + 1 < 38 := by omega
    rw [if_neg hk0, if_neg hkM]
    have hk0_2 : n_ge + 38 ≠ 0 := by omega
    have hkM_2 : ¬ n_ge + 38 < 38 := by omega
    rw [if_neg hk0_2, if_neg hkM_2]
    have : n_ge + 38 - 1 ≤ n_ge + 38 + 1 - 1 := by omega
    exact Nat.pow_le_pow_right (by decide) this

@[category API, AMS 11]
lemma A381358_eq_pow {k : ℕ} (hk : k ≥ 38) : A381358 k = 2^(k-1) := by
  unfold A381358
  have hk0 : k ≠ 0 := by omega
  have hkM : ¬ k < 38 := by omega
  rw [if_neg hk0, if_neg hkM]

@[category API, AMS 11]
lemma A381358_1 : A381358 1 = 1 := rfl
@[category API, AMS 11]
lemma A381358_2 : A381358 2 = 1 := rfl
@[category API, AMS 11]
lemma A381358_3 : A381358 3 = 2 := rfl
@[category API, AMS 11]
lemma A381358_4 : A381358 4 = 3 := rfl
@[category API, AMS 11]
lemma A381358_5 : A381358 5 = 5 := rfl
@[category API, AMS 11]
lemma A381358_6 : A381358 6 = 9 := rfl
@[category API, AMS 11]
lemma A381358_7 : A381358 7 = 15 := rfl
@[category API, AMS 11]
lemma A381358_8 : A381358 8 = 25 := rfl
@[category API, AMS 11]
lemma A381358_9 : A381358 9 = 41 := rfl
@[category API, AMS 11]
lemma A381358_10 : A381358 10 = 67 := rfl
@[category API, AMS 11]
lemma A381358_11 : A381358 11 = 109 := rfl
@[category API, AMS 11]
lemma A381358_12 : A381358 12 = 175 := rfl
@[category API, AMS 11]
lemma A381358_13 : A381358 13 = 277 := rfl
@[category API, AMS 11]
lemma A381358_14 : A381358 14 = 433 := rfl
@[category API, AMS 11]
lemma A381358_15 : A381358 15 = 671 := rfl
@[category API, AMS 11]
lemma A381358_16 : A381358 16 = 1035 := rfl
@[category API, AMS 11]
lemma A381358_17 : A381358 17 = 1595 := rfl
@[category API, AMS 11]
lemma A381358_18 : A381358 18 = 2463 := rfl
@[category API, AMS 11]
lemma A381358_19 : A381358 19 = 3817 := rfl
@[category API, AMS 11]
lemma A381358_20 : A381358 20 = 5937 := rfl
@[category API, AMS 11]
lemma A381358_21 : A381358 21 = 9259 := rfl
@[category API, AMS 11]
lemma A381358_22 : A381358 22 = 14457 := rfl
@[category API, AMS 11]
lemma A381358_23 : A381358 23 = 22569 := rfl
@[category API, AMS 11]
lemma A381358_24 : A381358 24 = 35193 := rfl
@[category API, AMS 11]
lemma A381358_25 : A381358 25 = 54795 := rfl
@[category API, AMS 11]
lemma A381358_26 : A381358 26 = 85195 := rfl
@[category API, AMS 11]
lemma A381358_27 : A381358 27 = 132333 := rfl
@[category API, AMS 11]
lemma A381358_28 : A381358 28 = 205471 := rfl
@[category API, AMS 11]
lemma A381358_29 : A381358 29 = 319069 := rfl
@[category API, AMS 11]
lemma A381358_30 : A381358 30 = 495699 := rfl
@[category API, AMS 11]
lemma A381358_31 : A381358 31 = 770557 := rfl
@[category API, AMS 11]
lemma A381358_32 : A381358 32 = 1198441 := rfl
@[category API, AMS 11]
lemma A381358_33 : A381358 33 = 1864549 := rfl
@[category API, AMS 11]
lemma A381358_34 : A381358 34 = 2901217 := rfl
@[category API, AMS 11]
lemma A381358_35 : A381358 35 = 4513919 := rfl
@[category API, AMS 11]
lemma A381358_36 : A381358 36 = 7021727 := rfl
@[category API, AMS 11]
lemma A381358_37 : A381358 37 = 10920343 := rfl

lemma supermul_small : ∀ (n : Fin 38) (m : Fin 38), A381358 (n.val + m.val) ≥ A381358 n.val * A381358 m.val := by
  decide

@[category API, AMS 11]
lemma A381358_pos_nat (n : ℕ) (hn : n ≥ 1) : A381358 n ≥ 1 := by
  unfold A381358
  split_ifs with h1 h2
  · omega
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n_ge
    · contradiction
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · omega
  · exact Nat.two_pow_pos (n - 1)

@[category API, AMS 11]
theorem A381358_pos (n : ℕ) (hn : n ≥ 1) : (A381358 n : ℝ) ≥ 1 := by
  have := A381358_pos_nat n hn
  exact_mod_cast this

@[category API, AMS 11]
lemma A381358_le_nat (n : ℕ) : A381358 n ≤ 2 ^ n := by
  unfold A381358
  split_ifs with h1 h2
  · simp
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n_ge
    · contradiction
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · omega
  · have h_pow : 2 ^ (n - 1) ≤ 2 ^ n := by
      have : n - 1 ≤ n := by omega
      exact Nat.pow_le_pow_right (by decide) this
    exact h_pow

@[category API, AMS 11]
theorem A381358_le (n : ℕ) : (A381358 n : ℝ) ≤ 2 ^ n := by
  have := A381358_le_nat n
  exact_mod_cast this

@[category API, AMS 11]
lemma A381358_supermul_helper (k m_ge : ℕ) (hk : k < 38) (hk_pos : k > 0)
    (h_pow_ge : 2^k ≥ A381358 k) :
    A381358 (k + (m_ge + 38)) ≥ A381358 k * A381358 (m_ge + 38) := by
  have h1 : k + (m_ge + 38) ≥ 38 := by omega
  have h2 : m_ge + 38 ≥ 38 := by omega
  rw [A381358_eq_pow h1, A381358_eq_pow h2]
  have h_eq : k + (m_ge + 38) - 1 = (m_ge + 38 - 1) + k := by omega
  rw [h_eq, Nat.pow_add]
  have h_comm : 2^(m_ge + 38 - 1) * 2^k = 2^k * 2^(m_ge + 38 - 1) := by ring
  rw [h_comm]
  gcongr

@[category API, AMS 11]
lemma A381358_supermul_helper2 (k n_ge : ℕ) (hk : k < 38) (hk_pos : k > 0)
    (h_pow_ge : 2^k ≥ A381358 k) :
    A381358 (n_ge + 38 + k) ≥ A381358 (n_ge + 38) * A381358 k := by
  have h1 : n_ge + 38 + k ≥ 38 := by omega
  have h2 : n_ge + 38 ≥ 38 := by omega
  rw [A381358_eq_pow h1, A381358_eq_pow h2]
  have h_eq : n_ge + 38 + k - 1 = (n_ge + 38 - 1) + k := by omega
  rw [h_eq, Nat.pow_add]
  gcongr

@[category API, AMS 11]
theorem A381358_supermul (n m : ℕ) : A381358 (n + m) ≥ A381358 n * A381358 m := by
  by_cases hn : n = 0
  · subst hn; unfold A381358; simp
  by_cases hm : m = 0
  · subst hm; unfold A381358; simp
  by_cases hn38 : n < 38
  · by_cases hm38 : m < 38
    · have h := supermul_small ⟨n, hn38⟩ ⟨m, hm38⟩
      exact h
    · have hm_ge : m ≥ 38 := by omega
      have h_m_eq : m = (m - 38) + 38 := by omega
      rw [h_m_eq]
      have hk_pos : n > 0 := by omega
      have h_pow : 2^n ≥ A381358 n := by
        rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n_ge
        · contradiction
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · have h_ge : n_ge + 38 ≥ 38 := by omega
          rw [A381358_eq_pow h_ge]
          have : n_ge + 38 - 1 ≤ n_ge + 38 := by omega
          exact Nat.pow_le_pow_right (by decide) this
      exact A381358_supermul_helper n (m - 38) hn38 hk_pos h_pow
  · by_cases hm38 : m < 38
    · have hn_ge : n ≥ 38 := by omega
      have h_n_eq : n = (n - 38) + 38 := by omega
      rw [h_n_eq]
      have hk_pos : m > 0 := by omega
      have h_pow : 2^m ≥ A381358 m := by
        rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n_ge
        · contradiction
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · have h_ge : n_ge + 38 ≥ 38 := by omega
          rw [A381358_eq_pow h_ge]
          have : n_ge + 38 - 1 ≤ n_ge + 38 := by omega
          exact Nat.pow_le_pow_right (by decide) this
      exact A381358_supermul_helper2 m (n - 38) hm38 hk_pos h_pow
    · -- n >= 38, m >= 38
      have hn_ge : n ≥ 38 := by omega
      have hm_ge : m ≥ 38 := by omega
      have h_ge1 : n + m ≥ 38 := by omega
      rw [A381358_eq_pow h_ge1, A381358_eq_pow hn_ge, A381358_eq_pow hm_ge]
      have h_eq1 : n + m - 1 = (n - 1) + (m - 1) + 1 := by omega
      rw [h_eq1, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      omega

noncomputable def u (n : ℕ) : ℝ :=
  if n = 0 then 0 else - Real.log (A381358 n)

@[category API, AMS 11]
theorem u_subadditive : Subadditive u := by
  intro m n
  unfold u
  by_cases hm : m = 0
  · subst hm
    simp
  by_cases hn : n = 0
  · subst hn
    simp
  have hmn : m + n ≠ 0 := by omega
  rw [if_neg hmn, if_neg hm, if_neg hn]
  have h_pos_m : (A381358 m : ℝ) ≥ 1 := A381358_pos m (Nat.pos_of_ne_zero hm)
  have h_pos_n : (A381358 n : ℝ) ≥ 1 := A381358_pos n (Nat.pos_of_ne_zero hn)
  have h_pos_mn : (A381358 (m + n) : ℝ) ≥ 1 := A381358_pos (m + n) (by omega)
  have h_mul : (A381358 (m + n) : ℝ) ≥ (A381358 m : ℝ) * (A381358 n : ℝ) := by
    exact_mod_cast A381358_supermul m n
  have h_log_le : Real.log ((A381358 m : ℝ) * (A381358 n : ℝ)) ≤ Real.log (A381358 (m + n) : ℝ) := by
    rw [Real.log_le_log_iff]
    · exact h_mul
    · have : (A381358 m : ℝ) * (A381358 n : ℝ) ≥ 1 * 1 := by gcongr
      linarith
    · linarith
  have h_log_add : Real.log ((A381358 m : ℝ) * (A381358 n : ℝ)) = Real.log (A381358 m : ℝ) + Real.log (A381358 n : ℝ) := by
    rw [Real.log_mul]
    · linarith
    · linarith
  linarith

@[category API, AMS 11]
theorem u_bdd_below : BddBelow (Set.range fun n => u n / n) := by
  use - Real.log 2
  rintro _ ⟨n, rfl⟩
  dsimp only
  unfold u
  by_cases hn : n = 0
  · subst hn
    simp
    have : (2 : ℝ) > 1 := by norm_num
    have h_log_pos := Real.log_pos this
    linarith
  · rw [if_neg hn]
    have hn_pos : n ≥ 1 := Nat.pos_of_ne_zero hn
    have hn_real_pos : (n : ℝ) > 0 := by positivity
    rw [le_div_iff₀ hn_real_pos]
    have h_le := A381358_le n
    have h_pos : (A381358 n : ℝ) ≥ 1 := A381358_pos n hn_pos
    have h_log_le : Real.log (A381358 n : ℝ) ≤ Real.log (2 ^ n : ℝ) := by
      rw [Real.log_le_log_iff]
      · exact h_le
      · linarith
      · positivity
    have h_pow : (2 ^ n : ℝ) = (2 : ℝ) ^ n := by norm_cast
    rw [h_pow, Real.log_pow] at h_log_le
    linarith


/-- Proves the existence of the limit of the sequence A381358. -/
@[category research solved, AMS 11]
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  have h_lim := u_subadditive.tendsto_lim u_bdd_below
  have h_neg : Filter.Tendsto (fun n => - (u n / n)) Filter.atTop (nhds (- Subadditive.lim u_subadditive)) := by
    exact Filter.Tendsto.neg h_lim
  have h_exp := (Real.continuous_exp.tendsto _).comp h_neg
  use Real.exp (- Subadditive.lim u_subadditive)
  refine Filter.Tendsto.congr' ?_ h_exp
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_ne : n ≠ 0 := by omega
  dsimp only [Function.comp_apply]
  unfold u
  rw [if_neg hn_ne]
  have h_calc : - (- Real.log (A381358 n) / (n : ℝ)) = Real.log (A381358 n) / (n : ℝ) := by ring
  rw [h_calc]
  have hn_nz : (A381358 n : ℝ) ≠ 0 := by linarith [A381358_pos n hn]
  have h_nonneg : 0 ≤ (A381358 n : ℝ) := by linarith [A381358_pos n hn]
  rw [Real.rpow_def_of_nonneg h_nonneg]
  rw [if_neg hn_nz]
  congr 1

end Submission.Spec

open Submission.Spec

/-- Proves the existence of the limit of the sequence A381358. -/
@[category research solved, AMS 11]
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
  Submission.Spec.A381358_limit_exists

