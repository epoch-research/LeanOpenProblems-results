import FormalConjectures.Util.ProblemImports

open Nat

/--
A386660: $a(n) = \sum_{k=1}^n \binom{n}{k} \pmod{2^k}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)


namespace Oeis386660

lemma a_le_sum (n : ℕ) : a n ≤ (Finset.Icc 1 n).sum (fun k => 2 ^ k) := by
  dsimp [a]
  apply Finset.sum_le_sum
  intro k hk
  have h2k : 2 ^ k > 0 := Nat.two_pow_pos k
  have h_mod := Nat.mod_lt (n.choose k) h2k
  exact Nat.le_of_lt h_mod

lemma sum_two_pow_eq (n : ℕ) : (Finset.Icc 1 n).sum (fun k => 2 ^ k) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- induction step
    have h_split : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h_split]
    have h_not_mem : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    rw [Finset.sum_insert h_not_mem]
    rw [ih]
    -- The goal is: 2 ^ (n + 1) + (2 ^ (n + 1) - 2) = 2 ^ (n + 1 + 1) - 2
    rw [pow_succ 2 (n + 1)]
    have h2 : 2 ≤ 2 ^ (n + 1) := by
      have h3 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      have h4 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      omega
    omega

lemma a_le (n : ℕ) : a n < 2 ^ (n + 1) := by
  have h1 := a_le_sum n
  have h2 := sum_two_pow_eq n
  have h3 : 2 ^ (n + 1) - 2 < 2 ^ (n + 1) := by
    have h4 : 2 ≤ 2 ^ (n + 1) := by
      have h5 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      have h6 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      omega
    omega
  omega


lemma a_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a n := by
  dsimp [a]
  have h_mem : n ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    exact ⟨hn, le_refl n⟩
  have h_pos : n.choose n % (2 ^ n) = 1 := by
    have h2n : 2 ^ n > 1 := by
      have : 1 < 2 ^ 1 := by norm_num
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) hn)
    rw [choose_self, Nat.mod_eq_of_lt h2n]
  -- Now we can show that the sum is >= the term at n
  have h_sum := Finset.single_le_sum (fun k _ => Nat.zero_le ((n.choose k) % (2 ^ k))) h_mem
  rw [h_pos] at h_sum
  exact h_sum

lemma a_lt_four_pow (n : ℕ) (hn : 1 ≤ n) : a n < 4 ^ n := by
  have h1 := a_le n
  have h2 : 2 ^ (n + 1) ≤ 4 ^ n := by
    have h3 : n + 1 ≤ 2 * n := by omega
    have h4 : 2 ^ (n + 1) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) h3
    have h5 : 2 ^ (2 * n) = 4 ^ n := by
      rw [pow_mul]
      rfl
    omega
  omega

lemma choose_mul_choose_le_add_choose (n m k j : ℕ) :
    n.choose k * m.choose j ≤ (n + m).choose (k + j) := by
  rw [Nat.add_choose_eq n m (k + j)]
  have h_mem : (k, j) ∈ Finset.antidiagonal (k + j) := by
    simp [Finset.mem_antidiagonal]
  apply Finset.single_le_sum (fun x _ => Nat.zero_le (n.choose x.1 * m.choose x.2)) h_mem

lemma min_mul_min_le (A B C D X Y : ℕ) (hAC : A * C ≤ X) (hBD : B * D ≤ Y) :
    min A B * min C D ≤ min X Y := by
  have h1 : min A B ≤ A := min_le_left A B
  have h2 : min C D ≤ C := min_le_left C D
  have h3 : min A B * min C D ≤ A * C := Nat.mul_le_mul h1 h2
  have h4 : min A B ≤ B := min_le_right A B
  have h5 : min C D ≤ D := min_le_right C D
  have h6 : min A B * min C D ≤ B * D := Nat.mul_le_mul h4 h5
  apply le_min
  · exact le_trans h3 hAC
  · exact le_trans h6 hBD

def M (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (fun k => min (2 ^ k) (n.choose k))

lemma M_mul_le (n m : ℕ) : M n * M m ≤ M (n + m) := by
  by_cases hn : n = 0
  · subst hn
    simp [M]
  by_cases hm : m = 0
  · subst hm
    simp [M]
  have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
  have h2 : 1 ≤ m := Nat.pos_of_ne_zero hm
  dsimp [M]
  rw [Finset.sup_mul₀]
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_Icc] at hk
  rw [mul_comm]
  rw [Finset.sup_mul₀]
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_Icc] at hj
  rw [mul_comm]
  have h_min := min_mul_min_le (2 ^ k) (n.choose k) (2 ^ j) (m.choose j) (2 ^ (k + j)) ((n + m).choose (k + j))
    (by rw [← pow_add]) (choose_mul_choose_le_add_choose n m k j)
  have h_mem : k + j ∈ Finset.Icc 1 (n + m) := by
    simp only [Finset.mem_Icc]
    omega
  have h_le := Finset.le_sup (f := fun x => min (2 ^ x) ((n + m).choose x)) h_mem
  exact le_trans h_min h_le

lemma M_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ M n := by
  dsimp [M]
  have h_mem : 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    exact ⟨by decide, hn⟩
  have h_le := Finset.le_sup (f := fun x => min (2 ^ x) (n.choose x)) h_mem
  have h_min : 1 ≤ min (2 ^ 1) (n.choose 1) := by
    rw [pow_one, choose_one_right]
    apply le_min
    · decide
    · exact hn
  exact le_trans h_min h_le

noncomputable def u (n : ℕ) : ℝ :=
  if n = 0 then 0 else - Real.log (M n : ℝ)

lemma u_subadditive : Subadditive u := by
  intro n m
  by_cases hn : n = 0
  · subst hn; simp [u]
  by_cases hm : m = 0
  · subst hm; simp [u]
  have hnm : n + m ≠ 0 := by omega
  dsimp [u]
  rw [if_neg hn, if_neg hm, if_neg hnm]
  rw [← neg_add, neg_le_neg_iff]
  have hM_pos (x : ℕ) (hx : x ≠ 0) : 0 < (M x : ℝ) := by
    have h_ge := M_ge_one x (Nat.pos_of_ne_zero hx)
    exact_mod_cast h_ge
  rw [← Real.log_mul (ne_of_gt (hM_pos n hn)) (ne_of_gt (hM_pos m hm))]
  have h_mul : (M n : ℝ) * (M m : ℝ) ≤ (M (n + m) : ℝ) := by
    have := M_mul_le n m
    exact_mod_cast this
  apply Real.log_le_log
  · exact mul_pos (hM_pos n hn) (hM_pos m hm)
  · exact h_mul

lemma M_le_two_pow (n : ℕ) : M n ≤ 2 ^ n := by
  dsimp [M]
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have h1 : min (2 ^ k) (n.choose k) ≤ 2 ^ k := min_le_left _ _
  have h2 : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hk.2
  exact le_trans h1 h2

lemma u_div_bdd_below : BddBelow (Set.range (fun n => u n / (n : ℝ))) := by
  use - Real.log 2
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    simp [u]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
    dsimp [u]
    rw [if_neg hn]
    have h2 : (M n : ℝ) ≤ (2 ^ n : ℝ) := by
      have := M_le_two_pow n
      exact_mod_cast this
    have h3 : (2 ^ n : ℝ) = (2 : ℝ) ^ (n : ℝ) := by
      rw [← Real.rpow_natCast]
    rw [h3] at h2
    have hM_pos : 0 < (M n : ℝ) := by
      have := M_ge_one n h1
      exact_mod_cast this
    have h4 : Real.log (M n : ℝ) ≤ Real.log ((2 : ℝ) ^ (n : ℝ)) := by
      apply Real.log_le_log hM_pos h2
    rw [Real.log_rpow (by norm_num)] at h4
    have h5 : - Real.log (M n : ℝ) ≥ - ((n : ℝ) * Real.log 2) := by
      linarith
    have h_pos : 0 < (n : ℝ) := by positivity
    have h_div : ((n : ℝ) * Real.log 2) / (n : ℝ) = Real.log 2 := by
      exact mul_div_cancel_left₀ (Real.log 2) (ne_of_gt h_pos)
    have h6 : - ((n : ℝ) * Real.log 2) / (n : ℝ) ≤ - Real.log (M n : ℝ) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right h5 (by positivity)
    have h7 : - ((n : ℝ) * Real.log 2) / (n : ℝ) = - Real.log 2 := by
      rw [neg_div, h_div]
    rw [h7] at h6
    exact h6

lemma M_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (M n : ℝ) := by
  have := M_ge_one n hn
  exact_mod_cast this

lemma M_rpow_eq_exp_log_div (n : ℕ) (hn : 1 ≤ n) :
    (M n : ℝ) ^ (1 / (n : ℝ)) = Real.exp (Real.log (M n : ℝ) / (n : ℝ)) := by
  rw [Real.rpow_def_of_pos (M_pos n hn)]
  congr 1
  ring

theorem M_tendsto : ∃ L : ℝ, Filter.Tendsto (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds L) := by
  use Real.exp (- u_subadditive.lim)
  have h1 := u_subadditive.tendsto_lim u_div_bdd_below
  have h2 : Filter.Tendsto (fun n => - (u n / (n : ℝ))) Filter.atTop (nhds (- u_subadditive.lim)) := by
    exact Filter.Tendsto.neg h1
  have h3 : Filter.Tendsto (fun n => Real.exp (- (u n / (n : ℝ)))) Filter.atTop (nhds (Real.exp (- u_subadditive.lim))) := by
    exact (Continuous.tendsto Real.continuous_exp (- u_subadditive.lim)).comp h2
  -- Now we show that (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) is eventually equal to (fun n => Real.exp (- (u n / (n : ℝ))))
  have h4 : ∀ n ≥ 1, (M n : ℝ) ^ (1 / (n : ℝ)) = Real.exp (- (u n / (n : ℝ))) := by
    intro n hn
    rw [M_rpow_eq_exp_log_div n hn]
    congr 1
    dsimp [u]
    have hn0 : n ≠ 0 := by omega
    rw [if_neg hn0]
    ring
  have h_congr : (fun n => (M n : ℝ) ^ (1 / (n : ℝ))) =ᶠ[Filter.atTop] (fun n => Real.exp (- (u n / (n : ℝ)))) := by
    filter_upwards [Filter.eventually_ge_atTop 1]
    exact h4
  exact Filter.Tendsto.congr' h_congr.symm h3

lemma a_le_n_mul_M (n : ℕ) (hn : 1 ≤ n) : a n ≤ n * M n := by
  dsimp [a]
  have h_sum : (Finset.Icc 1 n).sum (fun k => (n.choose k) % (2 ^ k)) ≤ (Finset.Icc 1 n).sum (fun _ => M n) := by
    apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have h_mod : (n.choose k) % (2 ^ k) < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have h_mod_le : (n.choose k) % (2 ^ k) ≤ 2 ^ k := Nat.le_of_lt h_mod
    have h_mod_le2 : (n.choose k) % (2 ^ k) ≤ n.choose k := Nat.mod_le _ _
    have h_min : (n.choose k) % (2 ^ k) ≤ min (2 ^ k) (n.choose k) := le_min h_mod_le h_mod_le2
    have h_sup : min (2 ^ k) (n.choose k) ≤ M n := by
      dsimp [M]
      have h_mem : k ∈ Finset.Icc 1 n := by
        simp only [Finset.mem_Icc]
        exact hk
      exact Finset.le_sup (f := fun x => min (2 ^ x) (n.choose x)) h_mem
    exact le_trans h_min h_sup
  rw [Finset.sum_const] at h_sum
  rw [Nat.card_Icc] at h_sum
  have h_card : n + 1 - 1 = n := by omega
  rw [h_card] at h_sum
  exact h_sum

lemma choose_le_n_mul_choose_succ (n k : ℕ) (hk : k < n) : n.choose k ≤ n * n.choose (k + 1) := by
  have h1 : 1 ≤ n - k := by omega
  have h2 : n.choose k ≤ n.choose k * (n - k) := by
    have h_le : 1 ≤ n - k := by omega
    have := Nat.mul_le_mul_left (n.choose k) h_le
    rw [mul_one] at this
    exact this
  rw [← Nat.choose_succ_right_eq] at h2
  have h3 : n.choose (k + 1) * (k + 1) ≤ n.choose (k + 1) * n := by
    apply Nat.mul_le_mul_left
    omega
  have h4 : n.choose (k + 1) * n = n * n.choose (k + 1) := by ring
  rw [h4] at h3
  exact le_trans h2 h3

lemma a_term_le_a (n k : ℕ) (hk : k ∈ Finset.Icc 1 n) : (n.choose k) % (2 ^ k) ≤ a n := by
  dsimp [a]
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk

lemma min_le_n_mul_a_of_delta (n d : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (hd : n - k = d) :
    min (2 ^ k) (n.choose k) ≤ n * a n := by
  induction d generalizing k with
  | zero =>
    -- d = 0
    have hk_eq : k = n := by omega
    rw [hk_eq]
    have h_choose : n.choose n = 1 := choose_self n
    rw [h_choose]
    have h_min : min (2 ^ n) 1 = 1 := by
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
      exact min_eq_right this
    rw [h_min]
    have h_a_ge_one : 1 ≤ a n := a_ge_one n hn
    have h_n_ge_one : 1 ≤ n := hn
    have : 1 * 1 ≤ n * a n := Nat.mul_le_mul h_n_ge_one h_a_ge_one
    rw [one_mul] at this
    exact this
  | succ d ih =>
    -- induction step
    have hk_lt : k < n := by omega
    have hk_succ_le : k + 1 ≤ n := by omega
    have hk_succ_ge1 : 1 ≤ k + 1 := by omega
    have hd_succ : n - (k + 1) = d := by omega
    have h_ih := ih (k + 1) hk_succ_ge1 hk_succ_le hd_succ
    by_cases h_pow : 2 ^ k > n.choose k
    · have h_min : min (2 ^ k) (n.choose k) = n.choose k := min_eq_right (le_of_lt h_pow)
      rw [h_min]
      have h_mem : k ∈ Finset.Icc 1 n := by
        simp only [Finset.mem_Icc]
        exact ⟨hk1, hk2⟩
      have h_term := a_term_le_a n k h_mem
      have h_mod : (n.choose k) % (2 ^ k) = n.choose k := Nat.mod_eq_of_lt h_pow
      rw [h_mod] at h_term
      have h_an_le : a n ≤ n * a n := by
        have : 1 * a n ≤ n * a n := Nat.mul_le_mul_right (a n) hn
        rw [one_mul] at this
        exact this
      exact le_trans h_term h_an_le
    · push_neg at h_pow
      have h_min : min (2 ^ k) (n.choose k) = 2 ^ k := min_eq_left h_pow
      rw [h_min]
      by_cases h_pow_succ : 2 ^ (k + 1) ≤ n.choose (k + 1)
      · have h_min_succ : min (2 ^ (k + 1)) (n.choose (k + 1)) = 2 ^ (k + 1) := min_eq_left h_pow_succ
        rw [h_min_succ] at h_ih
        have h_pow_le : 2 ^ k ≤ 2 ^ (k + 1) := by
          have : 2 ^ k * 1 ≤ 2 ^ k * 2 := Nat.mul_le_mul_left (2 ^ k) (by decide)
          rw [mul_one, ← pow_succ] at this
          exact this
        exact le_trans h_pow_le h_ih
      · push_neg at h_pow_succ
        have h_min_succ : min (2 ^ (k + 1)) (n.choose (k + 1)) = n.choose (k + 1) := min_eq_right (le_of_lt h_pow_succ)
        rw [h_min_succ] at h_ih
        have h_mem_succ : k + 1 ∈ Finset.Icc 1 n := by
          simp only [Finset.mem_Icc]
          exact ⟨hk_succ_ge1, hk_succ_le⟩
        have h_term := a_term_le_a n (k + 1) h_mem_succ
        have h_mod_succ : (n.choose (k + 1)) % (2 ^ (k + 1)) = n.choose (k + 1) := Nat.mod_eq_of_lt h_pow_succ
        rw [h_mod_succ] at h_term
        have h_choose_le := choose_le_n_mul_choose_succ n k hk_lt
        have h_mul_le : n * n.choose (k + 1) ≤ n * a n := Nat.mul_le_mul_left n h_term
        have h_total := le_trans h_choose_le h_mul_le
        exact le_trans h_pow h_total

lemma M_le_n_mul_a (n : ℕ) (hn : 1 ≤ n) : M n ≤ n * a n := by
  dsimp [M]
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_Icc] at hk
  exact min_le_n_mul_a_of_delta n (n - k) hn k hk.1 hk.2 rfl


end Oeis386660

open Oeis386660


-- Conjecture based on OEIS A386660, comment C.
/--
oeis_386660_conjecture_0: The limit of $a(n)^{1/n}$ exists.
The numerical evidence suggests a limit of approximately $1.7086...$
-/
theorem oeis_386660_conjecture_0 :
  ∃ L : ℝ, Filter.Tendsto (fun n => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds L) := by
  rcases M_tendsto with ⟨L, hM⟩
  use L
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  let g (n : ℕ) : ℝ := if n = 0 then f 0 else (M n : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ))
  let h (n : ℕ) : ℝ := if n = 0 then f 0 else (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ))
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds L) := by
    have h_n_pow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
      exact tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
    have h_M_pow : Filter.Tendsto (fun n : ℕ => (M n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds L) := hM
    have h_div : Filter.Tendsto (fun n : ℕ => (M n : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds (L / 1)) := by
      exact Filter.Tendsto.div h_M_pow h_n_pow (by norm_num)
    rw [div_one] at h_div
    apply Filter.Tendsto.congr' _ h_div
    have h_eq : (fun n => g n) =ᶠ[Filter.atTop] (fun n => (M n : ℝ) ^ (1 / (n : ℝ)) / (n : ℝ) ^ (1 / (n : ℝ))) := by
      filter_upwards [Filter.eventually_ge_atTop 1]
      intro n hn
      have hn0 : n ≠ 0 := by omega
      dsimp [g]
      rw [if_neg hn0]
    exact h_eq.symm
  have hh_tendsto : Filter.Tendsto h Filter.atTop (nhds L) := by
    have h_n_pow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 1) := by
      exact tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
    have h_M_pow : Filter.Tendsto (fun n : ℕ => (M n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds L) := hM
    have h_mul : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds (1 * L)) := by
      exact Filter.Tendsto.mul h_n_pow h_M_pow
    rw [one_mul] at h_mul
    apply Filter.Tendsto.congr' _ h_mul
    have h_eq : (fun n => h n) =ᶠ[Filter.atTop] (fun n => (n : ℝ) ^ (1 / (n : ℝ)) * (M n : ℝ) ^ (1 / (n : ℝ))) := by
      filter_upwards [Filter.eventually_ge_atTop 1]
      intro n hn
      have hn0 : n ≠ 0 := by omega
      dsimp [h]
      rw [if_neg hn0]
    exact h_eq.symm
  have h_gf : g ≤ f := by
    intro n
    by_cases hn : n = 0
    · subst hn
      dsimp [g, f]
      simp
    · have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      dsimp [g, f]
      rw [if_neg hn]
      have h_le := M_le_n_mul_a n h1
      have h_le_real : (M n : ℝ) ≤ (n : ℝ) * (a n : ℝ) := by exact_mod_cast h_le
      have h_pos_n : 0 < (n : ℝ) := by positivity
      have h_div_le : (M n : ℝ) / (n : ℝ) ≤ (a n : ℝ) := by
        rw [div_le_iff₀ h_pos_n]
        linarith
      have h_rpow_le : ((M n : ℝ) / (n : ℝ)) ^ (1 / (n : ℝ)) ≤ (a n : ℝ) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) h_div_le (by positivity)
      rw [Real.div_rpow (by positivity) (by positivity)] at h_rpow_le
      exact h_rpow_le
  have h_fh : f ≤ h := by
    intro n
    by_cases hn : n = 0
    · subst hn
      dsimp [h, f]
      simp
    · have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      dsimp [h, f]
      rw [if_neg hn]
      have h_le := a_le_n_mul_M n h1
      have h_le_real : (a n : ℝ) ≤ (n : ℝ) * (M n : ℝ) := by exact_mod_cast h_le
      have h_rpow_le : (a n : ℝ) ^ (1 / (n : ℝ)) ≤ ((n : ℝ) * (M n : ℝ)) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) h_le_real (by positivity)
      rw [Real.mul_rpow (by positivity) (by positivity)] at h_rpow_le
      exact h_rpow_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg_tendsto hh_tendsto h_gf h_fh
