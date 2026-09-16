import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds

open Nat Filter Topology

/--
A386660: $a(n) = \sum_{k=1}^n \binom{n}{k} \pmod{2^k}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)

def M (n : ℕ) : ℕ := (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))

lemma M_eq (n : ℕ) : ∃ k ≤ n, M n = min (n.choose k) (2 ^ k) := by
  have h : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (succ_pos n)⟩
  rcases Finset.exists_mem_eq_sup (Finset.range (n + 1)) h (fun k => min (n.choose k) (2 ^ k)) with ⟨k, hk, hM⟩
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hM⟩

lemma M_ge_one (n : ℕ) : 1 ≤ M n := by
  have : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (succ_pos n)
  have H := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) 0 this
  simp only [choose_zero_right, pow_zero, min_self] at H
  exact H

lemma M_pos (n : ℕ) : 0 < (M n : ℝ) := Nat.cast_pos.mpr (M_ge_one n)

lemma M_le_two_pow (n : ℕ) : M n ≤ 2 ^ n := by
  apply Finset.sup_le
  intro k hk
  have h_min : min (n.choose k) (2 ^ k) ≤ 2 ^ k := min_le_right _ _
  have h_pow : 2 ^ k ≤ 2 ^ n := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact le_trans h_min h_pow

lemma choose_mul_choose_le (n m k j : ℕ) : n.choose k * m.choose j ≤ (n + m).choose (k + j) := by
  rw [Nat.add_choose_eq n m (k + j)]
  have h : (k, j) ∈ Finset.antidiagonal (k + j) := Finset.mem_antidiagonal.mpr rfl
  exact @Finset.single_le_sum (ℕ × ℕ) ℕ _ _ (fun ij => n.choose ij.1 * m.choose ij.2) (Finset.antidiagonal (k + j)) _ (fun _ _ => Nat.zero_le _) _ h

lemma min_mul_min_le_min_mul_mul (A B C D : ℕ) : min A B * min C D ≤ min (A * C) (B * D) := by
  apply le_min
  · exact Nat.mul_le_mul (min_le_left A B) (min_le_left C D)
  · exact Nat.mul_le_mul (min_le_right A B) (min_le_right C D)

lemma M_le_sup (n : ℕ) (k : ℕ) (hk : k ≤ n) : min (n.choose k) (2 ^ k) ≤ M n := by
  have : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  exact @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) k this

lemma M_super (n m : ℕ) : M n * M m ≤ M (n + m) := by
  rcases M_eq n with ⟨k, hk, hn⟩
  rcases M_eq m with ⟨j, hj, hm⟩
  rw [hn, hm]
  have H1 : min (n.choose k) (2 ^ k) * min (m.choose j) (2 ^ j) ≤ min (n.choose k * m.choose j) (2 ^ (k + j)) := by
    rw [pow_add]
    exact min_mul_min_le_min_mul_mul _ _ _ _
  have H2 : min (n.choose k * m.choose j) (2 ^ (k + j)) ≤ min ((n + m).choose (k + j)) (2 ^ (k + j)) := by
    apply min_le_min _ le_rfl
    exact choose_mul_choose_le n m k j
  have H3 : min ((n + m).choose (k + j)) (2 ^ (k + j)) ≤ M (n + m) := by
    exact M_le_sup (n + m) (k + j) (Nat.add_le_add hk hj)
  exact le_trans H1 (le_trans H2 H3)

noncomputable def u (n : ℕ) : ℝ := - Real.log (M n)

lemma u_subadditive : Subadditive u := by
  intro n m
  dsimp [u]
  have p1 := M_pos n
  have p2 := M_pos m
  rw [← neg_add, neg_le_neg_iff, ← Real.log_mul p1.ne' p2.ne']
  apply Real.log_le_log (mul_pos p1 p2)
  norm_cast
  exact M_super n m

lemma u_div_bdd : BddBelow (Set.range fun n => u n / n) := by
  use - Real.log 2
  rintro _ ⟨n, rfl⟩
  dsimp [u]
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, div_zero]
    have : 0 ≤ Real.log 2 := by positivity
    linarith
  have p1 := M_pos n
  have p2 : (M n : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (M n : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast M_le_two_pow n
         _ = (2 : ℝ) ^ n := by norm_cast
  have p3 : Real.log (M n) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log p1 p2
  have p4 : Real.log (M n) ≤ n * Real.log 2 := by
    calc Real.log (M n) ≤ Real.log ((2 : ℝ) ^ n) := p3
         _ = n * Real.log 2 := by simp [Real.log_pow]
  have p5 : - Real.log (M n) ≥ - (n * Real.log 2) := neg_le_neg p4
  have p6 : (- Real.log (M n)) / n ≥ - Real.log 2 := by
    calc (- Real.log (M n)) / n ≥ (- (n * Real.log 2)) / n := div_le_div_of_nonneg_right p5 (Nat.cast_nonneg n)
         _ = - Real.log 2 := by
           rw [neg_div, mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn)]
  exact p6

lemma M_tendsto : Tendsto (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (Real.exp (- Subadditive.lim u_subadditive))) := by
  have h1 : Tendsto (fun n => u n / n) atTop (𝓝 (Subadditive.lim u_subadditive)) :=
    Subadditive.tendsto_lim u_subadditive u_div_bdd
  have h2 : Tendsto (fun n => - (u n / n)) atTop (𝓝 (- Subadditive.lim u_subadditive)) :=
    Tendsto.neg h1
  have h3 : Tendsto (fun n => Real.exp (- (u n / n))) atTop (𝓝 (Real.exp (- Subadditive.lim u_subadditive))) :=
    (Continuous.tendsto Real.continuous_exp _).comp h2
  have h_eq : (fun n => Real.exp (- (u n / n))) = (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) := by
    ext n
    by_cases hn : n = 0
    · simp [hn, u]
    have p1 := M_pos n
    dsimp [u]
    have h_rw : - (- Real.log (M n) / n) = Real.log (M n) / (n : ℝ) := by ring
    rw [h_rw]
    rw [Real.rpow_def_of_pos p1]
    congr 1
    ring
  rwa [h_eq] at h3

lemma mod_le_min (A B : ℕ) (hB : 0 < B) : A % B ≤ min A B := by
  apply le_min
  · exact Nat.mod_le A B
  · exact le_of_lt (Nat.mod_lt A hB)

lemma a_le_M (n : ℕ) : a n ≤ n * M n := by
  dsimp [a, M]
  calc
    _ ≤ (Finset.Icc 1 n).sum (fun k => min (n.choose k) (2 ^ k)) := by
      apply Finset.sum_le_sum
      intro k _
      apply mod_le_min
      positivity
    _ ≤ (Finset.Icc 1 n).sum (fun _ => (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.le_sup (f := fun k => min (n.choose k) (2 ^ k))
      have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk_le)
    _ = n * (Finset.range (n + 1)).sup (fun k => min (n.choose k) (2 ^ k)) := by
      rw [Finset.sum_const]
      have : (Finset.Icc 1 n).card = n := by
        cases n <;> simp
      rw [this, smul_eq_mul]

lemma a_ge_term (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) : (n.choose k) % (2 ^ k) ≤ a n := by
  dsimp [a]
  have hk : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
  rw [← Finset.add_sum_erase _ _ hk]
  exact Nat.le_add_right _ _

lemma M_le_n_mul_a (n : ℕ) (hn : 1 ≤ n) : M n ≤ n * a n := by
  by_cases hn1 : n = 1
  · subst hn1
    have hM1 : M 1 = 1 := rfl
    have ha1 : a 1 = 1 := rfl
    rw [hM1, ha1]
  have hn2 : 2 ≤ n := by omega
  rcases M_eq n with ⟨k, hkn, hM⟩
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    rw [hk0, choose_zero_right, pow_zero, min_self] at hM
    have H : 2 ≤ M n := by
      have : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
      have H1 := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) 1 this
      simp only [choose_one_right, pow_one] at H1
      calc 2 ≤ min n 2 := le_min hn2 (by decide)
           _ ≤ M n := H1
    linarith
  by_cases h_case : n.choose k < 2 ^ k
  · have h1 : M n = n.choose k := by rw [hM, min_eq_left (le_of_lt h_case)]
    have h2 : (n.choose k) % (2 ^ k) = n.choose k := Nat.mod_eq_of_lt h_case
    have h3 : n.choose k ≤ a n := by
      calc n.choose k = (n.choose k) % (2 ^ k) := h2.symm
           _ ≤ a n := a_ge_term n k hk1 hkn
    have Hfinal1 : M n = n.choose k := h1
    have Hfinal2 : n.choose k ≤ a n := h3
    have Hfinal3 : a n ≤ n * a n := Nat.le_mul_of_pos_left _ hn
    exact le_trans (le_of_eq Hfinal1) (le_trans Hfinal2 Hfinal3)
  · have h_case' := not_lt.mp h_case
    have h1 : M n = 2 ^ k := by rw [hM, min_eq_right h_case']
    have hkn_strict : k < n := by
      by_contra hc
      have hk_eq_n : k = n := le_antisymm hkn (not_lt.mp hc)
      rw [hk_eq_n, choose_self] at h_case'
      have h_pow : 2 ^ n ≤ 1 := h_case'
      have h_pow2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by simp
             _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
      linarith
    have hk_plus_1 : k + 1 ≤ n := hkn_strict
    have h_case2 : n.choose (k + 1) < 2 ^ (k + 1) := by
      by_contra hc2
      have hc2' := not_lt.mp hc2
      have H : 2 ^ (k + 1) ≤ M n := by
        have : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk_plus_1)
        have H1 := @Finset.le_sup _ ℕ _ _ (Finset.range (n + 1)) (fun k => min (n.choose k) (2 ^ k)) (k + 1) this
        calc 2 ^ (k + 1) ≤ min (n.choose (k + 1)) (2 ^ (k + 1)) := le_min hc2' le_rfl
             _ ≤ M n := H1
      rw [h1, pow_succ, mul_two] at H
      have hp : 0 < 2 ^ k := by positivity
      linarith
    have h2 : (n.choose (k + 1)) % (2 ^ (k + 1)) = n.choose (k + 1) := Nat.mod_eq_of_lt h_case2
    have h3 : n.choose (k + 1) ≤ a n := by
      calc n.choose (k + 1) = (n.choose (k + 1)) % (2 ^ (k + 1)) := h2.symm
           _ ≤ a n := a_ge_term n (k + 1) (by omega) hk_plus_1
    have h4 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := by
      rw [← choose_succ_right_eq, mul_comm]
    have h5 : M n * 1 ≤ n.choose k * (n - k) := by
      calc M n * 1 = 2 ^ k * 1 := by rw [h1]
           _ ≤ 2 ^ k * (n - k) := Nat.mul_le_mul_left _ (by omega)
           _ ≤ n.choose k * (n - k) := Nat.mul_le_mul_right _ h_case'
    rw [mul_one, ← h4] at h5
    have Hfinal1 : M n ≤ n.choose (k + 1) * (k + 1) := h5
    have Hfinal2 : n.choose (k + 1) * (k + 1) ≤ a n * n := Nat.mul_le_mul h3 hk_plus_1
    have Hfinal3 : M n ≤ a n * n := le_trans Hfinal1 Hfinal2
    exact le_trans Hfinal3 (le_of_eq (mul_comm (a n) n))

lemma tendsto_root_n : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
  have : Tendsto (fun x : ℝ => x ^ (1 / x)) atTop (𝓝 1) := tendsto_rpow_div
  exact this.comp tendsto_natCast_atTop_atTop

lemma a_sandwich (L : ℝ)
    (ha_pos : ∀ n, 1 ≤ n → 0 < (a n : ℝ)) (hM_pos : ∀ n, 1 ≤ n → 0 < (M n : ℝ))
    (h_upper : ∀ n, 1 ≤ n → (a n : ℝ) ≤ (n : ℝ) * (M n : ℝ))
    (h_lower : ∀ n, 1 ≤ n → (M n : ℝ) ≤ (n : ℝ) * (a n : ℝ))
    (hL : Tendsto (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 L)) :
    Tendsto (fun n => (a n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 L) := by
  have H_upper : ∀ᶠ n in atTop, (a n : ℝ) ^ (1 / (n : ℝ)) ≤ (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (a n : ℝ) ≤ (n : ℝ) * (M n : ℝ) := h_upper n hn
    have h2 : (a n : ℝ) ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * (M n : ℝ)) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (le_of_lt (ha_pos n hn)) h1 (by positivity)
    have h3 : ((n : ℝ) * (M n : ℝ)) ^ (1 / (n : ℝ)) = (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ)) := by
      apply Real.mul_rpow (by positivity) (le_of_lt (hM_pos n hn))
    rwa [h3] at h2
  have H_lower : ∀ᶠ n in atTop, (M n : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ)) ≤ (a n : ℝ) ^ (1 / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (M n : ℝ) ≤ (n : ℝ) * (a n : ℝ) := h_lower n hn
    have h2 : (M n : ℝ) ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * (a n : ℝ)) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow (le_of_lt (hM_pos n hn)) h1 (by positivity)
    have h3 : ((n : ℝ) * (a n : ℝ)) ^ (1 / (n : ℝ)) = (n : ℝ) ^ (1 / (n : ℝ)) * (a n : ℝ) ^ (1 / (n : ℝ)) := by
      apply Real.mul_rpow (by positivity) (le_of_lt (ha_pos n hn))
    rw [h3] at h2
    have hp : 0 < (n : ℝ) ^ (1 / (n : ℝ)) := by positivity
    rw [div_le_iff₀ hp, mul_comm]
    exact h2
  have h_lim_upper : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (1 * L)) :=
    Tendsto.mul tendsto_root_n hL
  rw [one_mul] at h_lim_upper
  have h_lim_lower : Tendsto (fun n : ℕ => (M n : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (L / 1)) :=
    Tendsto.div hL tendsto_root_n one_ne_zero
  rw [div_one] at h_lim_lower
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim_lower h_lim_upper H_lower H_upper

theorem oeis_386660_conjecture_0 :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  use Real.exp (- Subadditive.lim u_subadditive)
  have ha_pos : ∀ n, 1 ≤ n → 0 < (a n : ℝ) := by
    intro n hn
    have h1 : 1 ≤ M n := M_ge_one n
    have h2 : M n ≤ n * a n := M_le_n_mul_a n hn
    have h3 : 1 ≤ n * a n := le_trans h1 h2
    have h4 : 0 < a n := by
      by_contra hc
      have : a n = 0 := Nat.le_zero.mp (not_lt.mp hc)
      rw [this, mul_zero] at h3
      contradiction
    exact Nat.cast_pos.mpr h4
  have hM_pos : ∀ n, 1 ≤ n → 0 < (M n : ℝ) := by
    intro n _
    exact M_pos n
  have h_upper : ∀ n, 1 ≤ n → (a n : ℝ) ≤ (n : ℝ) * (M n : ℝ) := by
    intro n _
    exact_mod_cast a_le_M n
  have h_lower : ∀ n, 1 ≤ n → (M n : ℝ) ≤ (n : ℝ) * (a n : ℝ) := by
    intro n hn
    exact_mod_cast M_le_n_mul_a n hn
  exact a_sandwich (Real.exp (- Subadditive.lim u_subadditive)) ha_pos hM_pos h_upper h_lower M_tendsto

theorem oeis_386660_conjecture_0.disproof : ¬ (type_of% @oeis_386660_conjecture_0) := sorry
