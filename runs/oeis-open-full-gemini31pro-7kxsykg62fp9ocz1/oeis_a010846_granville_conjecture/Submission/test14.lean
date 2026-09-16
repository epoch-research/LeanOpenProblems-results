import FormalConjectures.Util.ProblemImports

open Finset

def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors n) |>.card

lemma a_prime_le_two {p : ℕ} (hp : p.Prime) : a p ≤ 2 := by
  have : (Icc 1 p).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors p) ⊆ {1, p} := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    rcases hk with ⟨⟨h1, hpk⟩, hsub⟩
    rw [hp.primeFactors] at hsub
    rw [mem_insert, mem_singleton]
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · right
      have hk_gt1 : 1 < k := lt_of_le_of_ne h1 (Ne.symm hk1)
      have hex : ∃ q, q.Prime ∧ q ∣ k := Nat.exists_prime_and_dvd hk_gt1.ne'
      rcases hex with ⟨q, hq, hqk⟩
      have hq_mem : q ∈ k.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hq, hqk, _root_.ne_of_gt (lt_trans zero_lt_one hk_gt1)⟩
      have hqp : q ∈ ({p} : Finset ℕ) := hsub hq_mem
      rw [mem_singleton] at hqp
      subst hqp
      exact le_antisymm hpk (Nat.le_of_dvd (lt_trans zero_lt_one hk_gt1) hqk)
  calc
    a p = ((Icc 1 p).filter (fun k => Nat.primeFactors k ⊆ Nat.primeFactors p)).card := rfl
    _ ≤ ({1, p} : Finset ℕ).card := card_le_card this
    _ ≤ 2 := by
      calc
        ({1, p} : Finset ℕ).card ≤ ({p} : Finset ℕ).card + 1 := card_insert_le 1 {p}
        _ = 1 + 1 := by rw [card_singleton]
        _ = 2 := rfl

lemma exp_four_lt_81 : Real.exp 4 < 81 := by
  calc
    Real.exp 4 = Real.exp (4 : ℕ) := by norm_cast
    _ = Real.exp 1 ^ (4 : ℕ) := (Real.exp_one_pow 4).symm
    _ < (3 : ℝ) ^ (4 : ℕ) := by
      gcongr
      exact Real.exp_one_lt_three
    _ = 81 := by norm_num

lemma log_gt_four {p : ℕ} (hp : 81 ≤ p) : 4 < Real.log (p : ℝ) := by
  rw [← Real.exp_lt_exp]
  calc
    Real.exp 4 < 81 := exp_four_lt_81
    _ ≤ (p : ℝ) := Nat.cast_le.mpr hp
    _ = Real.exp (Real.log (p : ℝ)) := (Real.exp_log (by positivity)).symm

lemma sqrt_log_gt_two {x : ℝ} (hx : 4 < x) : 2 < x ^ (1/2 : ℝ) := by
  calc
    (2 : ℝ) = 4 ^ (1/2 : ℝ) := by norm_num
    _ < x ^ (1/2 : ℝ) := by
      apply Real.rpow_lt_rpow (by norm_num) hx (by norm_num)

theorem disproof : ¬ (
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n
) := by
  intro h
  have h_eps : (0 : ℝ) < 1/2 := by norm_num
  rcases h (1/2) h_eps with ⟨N, hN⟩
  have h_inf := Nat.exists_infinite_primes (max N 81)
  rcases h_inf with ⟨p, hp_ge, hp⟩
  have hp_N : N ≤ p := le_trans (le_max_left N 81) hp_ge
  have hp_81 : 81 ≤ p := le_trans (le_max_right N 81) hp_ge
  have H := hN p hp_N
  have H2 : (Real.log p) ^ (1/2 : ℝ) ≤ a p := by
    calc
      (Real.log p) ^ (1/2 : ℝ) = (Real.log p) ^ (1 - 1/2 : ℝ) := by norm_num
      _ ≤ a p := H
  have h_a_le_2 : a p ≤ 2 := a_prime_le_two hp
  have h_a_le_2_R : (a p : ℝ) ≤ 2 := Nat.cast_le.mpr h_a_le_2
  have h_gt_2 : 2 < (Real.log p) ^ (1/2 : ℝ) := sqrt_log_gt_two (log_gt_four hp_81)
  linarith
