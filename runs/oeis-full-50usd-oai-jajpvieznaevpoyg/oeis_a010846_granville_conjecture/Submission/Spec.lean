import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

lemma a_prime_le_two (p : ℕ) (hp : Nat.Prime p) : a p ≤ 2 := by
  unfold a
  have hsub : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆ ({1, p} : Finset ℕ) := by
    intro k hk
    rw [mem_filter] at hk
    have hkI := (mem_Icc.mp hk.1)
    by_cases h1 : k = 1
    · simp [h1]
    · have hklt : 1 < k := lt_of_le_of_ne hkI.1 (Ne.symm h1)
      obtain ⟨q, hq⟩ := (Nat.nonempty_primeFactors.mpr hklt)
      have hqp : q ∈ primeFactors p := hk.2 hq
      have hqeq : q = p := by
        simpa [hp.primeFactors] using hqp
      have hpdvd : p ∣ k := by
        simpa [hqeq] using Nat.dvd_of_mem_primeFactors hq
      have hp_le_k : p ≤ k := Nat.le_of_dvd (by omega) hpdvd
      have hkp : k = p := le_antisymm hkI.2 hp_le_k
      simp [hkp]
  calc
    ((Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p)).card ≤ ({1, p} : Finset ℕ).card := card_le_card hsub
    _ = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simp [hp.ne_one.symm]

lemma big_log_half {p : ℕ} (hp : (Real.exp 4) < (p : ℝ)) :
    (2:ℝ) < (Real.log p) ^ ((2:ℝ)⁻¹) := by
  have hp_pos : 0 < (p : ℝ) := lt_trans (Real.exp_pos 4) hp
  have hlog : (4:ℝ) < Real.log (p : ℝ) := (Real.lt_log_iff_exp_lt hp_pos).2 hp
  have hsq : (2:ℝ) ^ (2:ℝ) < Real.log (p : ℝ) := by
    norm_num
    exact hlog
  exact (Real.lt_rpow_inv_iff_of_pos (by norm_num) (le_of_lt (lt_trans (by norm_num : (0:ℝ) < 4) hlog)) (by norm_num : (0:ℝ) < (2:ℝ))).2 hsq

/--
The stated unconditional lower bound is false: at large primes `p`, the value of `a p` is at
most `2`, while `(log p)^(1/2)` is larger than `2`.
-/
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  obtain ⟨N, hN⟩ := h (1/2 : ℝ) (by norm_num)
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp 4)
  obtain ⟨p, hp_ge, hpprime⟩ := Nat.exists_infinite_primes (max N M)
  have hNp : N ≤ p := le_trans (le_max_left N M) hp_ge
  have hMp : M ≤ p := le_trans (le_max_right N M) hp_ge
  have hpexp : Real.exp 4 < (p : ℝ) := hM.trans_le (Nat.cast_le.mpr hMp)
  have hbig : (2:ℝ) < (Real.log p) ^ (1 - (1/2 : ℝ)) := by
    convert big_log_half hpexp using 2
    norm_num
  have hle : (Real.log p) ^ (1 - (1/2 : ℝ)) ≤ (a p : ℝ) := hN p hNp
  have hap : (a p : ℝ) ≤ (2:ℝ) := by
    exact_mod_cast a_prime_le_two p hpprime
  linarith
